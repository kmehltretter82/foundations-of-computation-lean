import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.InPlaceDecoderCopier
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.RejectPaddingCleaner
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.Shapes
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base

/-!
# Count-window input-materializer prefix pipeline

Composes branch padding cleanup, guarded three-tape emission, output-length
allocation, in-place Boolean-word decoding, and post-decode suffix copying.
The endpoint is the exact common source for the remaining branch field phases.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat

open CanonicalLayouts.DovetailLayoutScanner
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat

def allocatorTail (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  InPlaceDecoder.fieldTail
    (ParsedLayoutBits L)
    (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)

def copiedDataWord (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  List.append (ParsedLayoutBits L)
    (false ::
      countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)

theorem false_cons_structuredSuffixTail
    (useAccept : Bool) (L : DovetailLayout) :
    false :: countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L =
      List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L) := by
  rcases stageNatBits_cons_false L.stage with ⟨stageTail, hstage⟩
  rw [countWindowPostFieldDecodedPrefixStructuredSuffixTail, hstage]
  rfl
  done

theorem copiedDataWord_accept_decomp (L : DovetailLayout) :
    copiedDataWord true L =
      List.append (ParsedLayoutBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (configurationFieldBits L.rejectConfig [])
            (selectedProjectionPaddedTailCleanupSelectedHitBits true L))) := by
  rw [copiedDataWord, false_cons_structuredSuffixTail]
  simp [countWindowPostFieldDecodedPrefixMaterializerPayload,
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits]
  done

theorem copiedDataWord_reject_decomp (L : DovetailLayout) :
    copiedDataWord false L =
      List.append (ParsedLayoutBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (configurationFieldBits L.rejectConfig [])) := by
  rw [copiedDataWord, false_cons_structuredSuffixTail]
  simp [countWindowPostFieldDecodedPrefixMaterializerPayload,
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload,
    selectedProjectionPaddedTailCleanupSelectedConfigBits]
  done

theorem sourceWord_eq_allocatorRawWord
    (useAccept : Bool) (L : DovetailLayout) :
    sourceWord useAccept L =
      OutputLengthAllocator.rawWord
        (ParsedLayoutBits L).length (allocatorTail useAccept L) := by
  unfold sourceWord allocatorTail OutputLengthAllocator.rawWord
    InPlaceDecoder.fieldTail boolWordRawBitsDecoderHeaderBits
    boolWordRawBitsDecoderEncodedFieldBits
  simp [encodeCodeSymbolAsInput, List.append_assoc]
  done

def postEmitterDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    OutputLengthAllocator.loweredDescription
    InPlaceDecoderCopier.loweredDescription

theorem postEmitterDescription_subroutineReady :
    postEmitterDescription.SubroutineReady := by
  exact
    canonicalPrimitiveSeqDescription_subroutineReady
      OutputLengthAllocator.loweredDescription_subroutineReady
      InPlaceDecoderCopier.loweredDescription_subroutineReady

theorem postEmitterDescription_haltsFromTapeEquiv
    (useAccept : Bool) (L : DovetailLayout) :
    postEmitterDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (Tape.input (sourceWord useAccept L)) Tape.blank Tape.blank)
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append
            (ParsedLayoutBits L)
            (false ::
              countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L))
          [])) := by
  simpa [postEmitterDescription, allocatorTail,
      sourceWord_eq_allocatorRawWord] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      OutputLengthAllocator.loweredDescription_subroutineReady
      InPlaceDecoderCopier.loweredDescription_subroutineReady
      (OutputLengthAllocator.loweredDescription_haltsFromTapeEquiv
        (ParsedLayoutBits L).length (allocatorTail useAccept L))
      (InPlaceDecoderCopier.loweredDescription_haltsFromTapeEquiv
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L))

def embeddedPrefixDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    StructuredConstructionTargets.structured3InputEmbeddingEmitterDescription
    postEmitterDescription

theorem embeddedPrefixDescription_subroutineReady :
    embeddedPrefixDescription.SubroutineReady := by
  exact
    canonicalPrimitiveSeqDescription_subroutineReady
      StructuredConstructionTargets.structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.left
      postEmitterDescription_subroutineReady

theorem embeddingEmitter_haltsFromTapeEquiv
    (useAccept : Bool) (L : DovetailLayout) :
    StructuredConstructionTargets.structured3InputEmbeddingEmitterDescription.HaltsFromTapeEquiv
      (Tape.input (sourceWord useAccept L))
      (encodedGuardedStructured3Tapes
        (Tape.input (sourceWord useAccept L)) Tape.blank Tape.blank) := by
  simpa [StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget,
      structured3InputMaterializerTargetTape] using
    (StructuredConstructionTargets.structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.right
      (sourceWord useAccept L)).toEquiv

theorem embeddedPrefixDescription_haltsFromTapeEquiv
    (useAccept : Bool) (L : DovetailLayout) :
    embeddedPrefixDescription.HaltsFromTapeEquiv
      (Tape.input (sourceWord useAccept L))
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append
            (ParsedLayoutBits L)
            (false ::
              countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L))
          [])) := by
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      StructuredConstructionTargets.structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.left
      postEmitterDescription_subroutineReady
      (embeddingEmitter_haltsFromTapeEquiv useAccept L)
      (postEmitterDescription_haltsFromTapeEquiv useAccept L)

theorem acceptSource_equiv_input
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput true) :
    Tape.Equiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        true input)
      (Tape.input (sourceWord true input.L)) := by
  change
    Tape.Equiv
      (rightEdgeRewindTargetTape
        (sourceWord true input.L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          true input.L input.deletedTail))
      (Tape.input (sourceWord true input.L))
  rw [sourcePadding_accept_closedForm, sourceWord_cons]
  exact
    RejectPaddingCleaner.rightEdgeRewindTargetTape_replicate_equiv_input_cons
      false
      (List.append [false, false, false]
        (List.append
          (boolWordRawBitsDecoderEncodedFieldBits (ParsedLayoutBits input.L))
          (false ::
            countWindowPostFieldDecodedPrefixStructuredSuffixTail
              true input.L)))
      (input.deletedTail.length + 7)
  done

theorem embeddedPrefixDescription_haltsFromTapeEquiv_accept
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput true) :
    embeddedPrefixDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        true input)
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits input.L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail true input.L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append
            (ParsedLayoutBits input.L)
            (false ::
              countWindowPostFieldDecodedPrefixStructuredSuffixTail
                true input.L))
          [])) := by
  rcases embeddedPrefixDescription_haltsFromTapeEquiv true input.L with
    ⟨actual, hactual, hactualEquiv⟩
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm (acceptSource_equiv_input input)) hactual with
    ⟨actual', hactual', hactual'Equiv⟩
  exact
    ⟨actual', hactual',
      Tape.Equiv.trans hactual'Equiv hactualEquiv⟩
  done

def rejectPrefixDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    RejectPaddingCleaner.cleanAndRewindDescription
    embeddedPrefixDescription

theorem rejectPrefixDescription_subroutineReady :
    rejectPrefixDescription.SubroutineReady := by
  exact
    canonicalPrimitiveSeqDescription_subroutineReady
      RejectPaddingCleaner.cleanAndRewindDescription_subroutineReady
      embeddedPrefixDescription_subroutineReady

theorem rejectPrefixDescription_haltsFromTapeEquiv
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput false) :
    rejectPrefixDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits input.L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail false input.L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append
            (ParsedLayoutBits input.L)
            (false ::
              countWindowPostFieldDecodedPrefixStructuredSuffixTail
                false input.L))
          [])) := by
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      RejectPaddingCleaner.cleanAndRewindDescription_subroutineReady
      embeddedPrefixDescription_subroutineReady
      (RejectPaddingCleaner.cleanAndRewindDescription_rejectDetachedHitCleanerSpec.right
        input)
      (embeddedPrefixDescription_haltsFromTapeEquiv false input.L)

end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
