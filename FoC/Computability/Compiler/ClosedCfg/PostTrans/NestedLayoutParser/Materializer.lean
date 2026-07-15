import FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutShape
import FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutParser.Materializer.SuffixMaterializer
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

/-!
# Nested-layout materializer adapter

This module adapts the shared canonical Bool-word suffix materializer to the
padded merge source.  The only target-specific finite table rewrites the outer
transition header to the decoder's canonical header.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace NestedLayoutMaterializer

def suffixTail (p : SelectedMergeEmitterPayload) : Word Bool :=
  (SelectedMergePaddedEmitterOuterSuffixBits p).tail

theorem outerSuffixBits_eq_parsedInnerOuterSuffixBits
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterOuterSuffixBits p =
      SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p := by
  rw [SelectedMergePaddedEmitterOuterSuffixBits_eq_stageFieldBits]
  rw [SelectedMergePaddedEmitterParsedInnerOuterSuffixBits]
  rw [SelectedMergePaddedEmitterOuterStageSuffixBits,
    SelectedMergePaddedEmitterOuterStageSuffixCode]
  rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
  simp [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
    encodeCodeWordAsInput]

theorem outerSuffixBits_eq_false_cons_suffixTail
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterOuterSuffixBits p =
      false :: suffixTail p := by
  rcases SelectedMergePaddedEmitterOuterSuffixBits_cons_false p with
    ⟨tail, htail⟩
  simp [suffixTail, htail]

def transitionHeaderBits : Word Bool :=
  [false, false, false, true]

def canonicalHeaderBits : Word Bool :=
  [false, false, false, false]

theorem sourceBits_eq_header_encodedField_suffix
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.sourceBits p =
      List.append transitionHeaderBits
        (List.append
          (boolWordRawBitsDecoderEncodedFieldBits p.S.input)
          (false :: suffixTail p)) := by
  rw [SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  rw [SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits]
  rw [← SelectedMergeEmitterPayload.input_eq_parsedLayoutBits p]
  rw [CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits]
  rw [outerSuffixBits_eq_false_cons_suffixTail]
  simp [transitionHeaderBits,
    boolWordRawBitsDecoderEncodedFieldBits, encodeCodeSymbolAsInput,
    List.append_assoc]

def flatSourceTape
    (header bits suffix : Word Bool) : Tape Bool :=
  rightEdgeRewindTargetTape
    (List.append header
      (List.append
        (boolWordRawBitsDecoderEncodedFieldBits bits)
        (false :: suffix)))
    [none]

theorem canonicalFlatSourceTape_eq_decoderSourceTape
    (bits suffix : Word Bool) :
    flatSourceTape canonicalHeaderBits bits suffix =
      boolWordRawBitsDecoderSourceTape bits suffix [none] := by
  rfl

theorem rewindTargetPaddedTape_eq_flatSourceTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape
        (SelectedMergePaddedEmitterCleanup.sourceBits p) =
      flatSourceTape transitionHeaderBits p.S.input (suffixTail p) := by
  rw [sourceBits_eq_header_encodedField_suffix]
  rfl

theorem sourceRewindDescription_haltsFrom_publicSource
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
      (flatSourceTape transitionHeaderBits p.S.input (suffixTail p)) := by
  rw [← SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceFieldsTape]
  rw [← rewindTargetPaddedTape_eq_flatSourceTape]
  exact sourceRewindDescription_haltsFrom_afterHitPaddedTape p

theorem dovetailLayoutFieldBits_nil_append
    (L : DovetailLayout) (suffix : Word Bool) :
    List.append
        (CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits L [])
        suffix =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits L
        suffix := by
  simp [CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.append_assoc]

theorem contiguousOutputBits_eq_targetBits
    (p : SelectedMergeEmitterPayload) :
    List.append p.S.input (false :: suffixTail p) =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits p.L
        (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p) := by
  rw [SelectedMergeEmitterPayload.input_eq_parsedLayoutBits]
  rw [← outerSuffixBits_eq_parsedInnerOuterSuffixBits]
  rw [← outerSuffixBits_eq_false_cons_suffixTail]
  rw [ParsedLayoutBits, DovetailLayout.encode]
  rw [CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_eq_encodeAppend]
  exact dovetailLayoutFieldBits_nil_append _ _

def projectedOutputTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  Tape.input (List.append p.S.input (false :: suffixTail p))

theorem projectedOutputTape_equiv_targetTape
    (p : SelectedMergeEmitterPayload) :
    Tape.Equiv (projectedOutputTape p)
      (DovetailInitialLayoutInitializer.tapeAtCells []
        ((CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits p.L
          (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)).map
            some)) := by
  rw [projectedOutputTape]
  rw [← contiguousOutputBits_eq_targetBits]
  rw [SelectedMergeEmitterPayload.input_eq_parsedLayoutBits]
  rcases parsedLayoutBits_eq_false_false_tail p.L with ⟨tail, htail⟩
  simp [htail, Tape.input,
    DovetailInitialLayoutInitializer.tapeAtCells, Tape.Equiv]

def headerCanonicalizerDescription : MachineDescription where
  stateCount := 9
  start := 0
  halt := 8
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 1 (some false) (some false) Direction.right 2
    , transition 2 (some false) (some false) Direction.right 3
    , transition 3 (some true) (some false) Direction.right 4
    , transition 4 none none Direction.left 5
    , transition 4 (some false) (some false) Direction.left 5
    , transition 4 (some true) (some true) Direction.left 5
    , transition 5 none none Direction.left 6
    , transition 5 (some false) (some false) Direction.left 6
    , transition 5 (some true) (some true) Direction.left 6
    , transition 6 none none Direction.left 7
    , transition 6 (some false) (some false) Direction.left 7
    , transition 6 (some true) (some true) Direction.left 7
    , transition 7 none none Direction.left 8
    , transition 7 (some false) (some false) Direction.left 8
    , transition 7 (some true) (some true) Direction.left 8 ]

theorem headerCanonicalizerDescription_subroutineReady :
    headerCanonicalizerDescription.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    headerCanonicalizerDescription
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem headerCanonicalizerDescription_run
    (bits suffix : Word Bool) :
    headerCanonicalizerDescription.runConfig 8
        { state := headerCanonicalizerDescription.start
          tape := flatSourceTape transitionHeaderBits bits suffix } =
      { state := headerCanonicalizerDescription.halt
        tape := flatSourceTape canonicalHeaderBits bits suffix } := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.stageNatBits_cons_false
        bits.length with
    ⟨stageTail, hstage⟩
  simp [headerCanonicalizerDescription, flatSourceTape,
    transitionHeaderBits, canonicalHeaderBits,
    boolWordRawBitsDecoderEncodedFieldBits, rightEdgeRewindTargetTape,
    CommonGround.FiniteTransducers.tapeAtCells, hstage,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight, List.map_append, List.append_assoc]

theorem headerCanonicalizerDescription_haltsFromTape
    (bits suffix : Word Bool) :
    headerCanonicalizerDescription.HaltsFromTape
      (flatSourceTape transitionHeaderBits bits suffix)
      (flatSourceTape canonicalHeaderBits bits suffix) := by
  refine ⟨8, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.state
        (headerCanonicalizerDescription_run bits suffix)
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.tape
        (headerCanonicalizerDescription_run bits suffix)

theorem canonicalFlatSource_move_left_move_right
    (bits suffix : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (flatSourceTape canonicalHeaderBits bits suffix)) =
      flatSourceTape canonicalHeaderBits bits suffix := by
  simpa [flatSourceTape, canonicalHeaderBits] using
    rightEdgeRewindTargetTape_move_left_move_right_cons
      false
      (false :: false :: false ::
        List.append (boolWordRawBitsDecoderEncodedFieldBits bits)
          (false :: suffix))
      [none]

def frontDescription : MachineDescription :=
  canonicalSeqDescription
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription
    headerCanonicalizerDescription

theorem frontDescription_subroutineReady :
    frontDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription_subroutineReady
    headerCanonicalizerDescription_subroutineReady

theorem transitionFlatSource_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (flatSourceTape transitionHeaderBits p.S.input (suffixTail p))) =
      flatSourceTape transitionHeaderBits p.S.input (suffixTail p) := by
  rw [← rewindTargetPaddedTape_eq_flatSourceTape]
  exact
    SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape_move_left_move_right
      (SelectedMergePaddedEmitterCleanup.sourceBits p)

theorem frontDescription_haltsFromTape
    (p : SelectedMergeEmitterPayload) :
    frontDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
      (flatSourceTape canonicalHeaderBits p.S.input (suffixTail p)) := by
  exact canonicalSeqDescription_haltsFromTape_of_haltsFromTape
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription_subroutineReady
    headerCanonicalizerDescription_subroutineReady
    (sourceRewindDescription_haltsFrom_publicSource p)
    (transitionFlatSource_move_left_move_right p)
    (headerCanonicalizerDescription_haltsFromTape
      p.S.input (suffixTail p))

def CanonicalBoolWordSuffixMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (bits suffix : Word Bool),
      materializer.HaltsFromTapeEquiv
        (boolWordRawBitsDecoderSourceTape bits suffix [none])
        (Tape.input (List.append bits (false :: suffix)))

def CanonicalBoolWordSuffixMaterializerConstruction : Prop :=
  exists materializer : MachineDescription,
    CanonicalBoolWordSuffixMaterializerSpec materializer

def description (materializer : MachineDescription) : MachineDescription :=
  canonicalSeqDescription frontDescription materializer

theorem description_subroutineReady
    {materializer : MachineDescription}
    (hmaterializer : materializer.SubroutineReady) :
    (description materializer).SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    frontDescription_subroutineReady hmaterializer

theorem description_haltsFromTapeEquiv
    {materializer : MachineDescription}
    (hmaterializer :
      CanonicalBoolWordSuffixMaterializerSpec materializer)
    (p : SelectedMergeEmitterPayload) :
    (description materializer).HaltsFromTapeEquiv
      (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
      (projectedOutputTape p) := by
  exact canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
    frontDescription_subroutineReady hmaterializer.left
    (frontDescription_haltsFromTape p)
    (by
      simpa [canonicalFlatSourceTape_eq_decoderSourceTape] using
        canonicalFlatSource_move_left_move_right p.S.input (suffixTail p))
    (hmaterializer.right p.S.input (suffixTail p))

end NestedLayoutMaterializer
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
