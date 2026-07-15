import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.Initializer
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.CloseoutFinishRuns
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.CloseoutStatic
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.PaddedTape2Projector
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.Contracts

/-! Direct mixed-source construction producing the joined source-rest output. -/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

open Structured.MultiTapeLowering

def directJoinedAssemblyOutputDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription directJoinedInitializerDescription
    (canonicalPrimitiveSeqDescription
      loweredStructuredLiveTailEmitterDescription
      (canonicalPrimitiveSeqDescription
        DirectJoinedCloseout.loweredDescription
        CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription))

theorem directJoinedAssemblyOutputDescription_subroutineReady :
    directJoinedAssemblyOutputDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    directJoinedInitializerDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      loweredStructuredLiveTailEmitterDescription_subroutineReady_static
      (canonicalPrimitiveSeqDescription_subroutineReady
        DirectJoinedCloseout.loweredDescription_subroutineReady
        CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription_subroutineReady))

theorem directJoinedCloseoutLowered_haltsFrom_emitterFinal
    (p : AssemblySourceRestLiveTailEmitterParam) :
    DirectJoinedCloseout.loweredDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedFinalTape p)
      (DirectJoinedCloseout.assemblyCloseoutEncodedFinalTape p) := by
  simpa [DirectJoinedCloseout.loweredDescription,
    DirectJoinedCloseout.loweredCloseoutDescription] using
    DirectJoinedCloseout.loweredCloseoutDescription_haltsFrom_emitterFinal
      DirectJoinedCloseout.description_wellFormed
      DirectJoinedCloseout.description_haltTransitionFree
      DirectJoinedCloseout.description_supported p

theorem directJoinedOutputBits_eq_joinedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    List.append (structuredLiveTailEmitterAssemblyOutputPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p) =
      assemblySourceRestFinishJoinedOutput
        p.w p.sourceRestBits p.stage := by
  cases p
  unfold structuredLiveTailEmitterAssemblyOutputPrefix
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestFinishJoinedOutput
  rw [assemblySourceRestFinishTargetPrefixBits_eq_prefixQuote_append_restQuote]
  exact List.append_assoc _ _ _

theorem directJoinedOutputBits_ne_nil
    (p : AssemblySourceRestLiveTailEmitterParam) :
    List.append (structuredLiveTailEmitterAssemblyOutputPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p) ≠ [] := by
  intro hempty
  have hlen := congrArg List.length hempty
  rw [List.length_nil] at hlen
  simp [DirectJoinedCloseout.assemblyOutputPrefix_length] at hlen

theorem directJoinedProjector_haltsFrom_closeout
    (p : AssemblySourceRestLiveTailEmitterParam) :
    CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription.HaltsFromTapeEquiv
      (DirectJoinedCloseout.assemblyCloseoutEncodedFinalTape p)
      (Tape.input
        (List.append (structuredLiveTailEmitterAssemblyOutputPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p))) := by
  let bits :=
    List.append (structuredLiveTailEmitterAssemblyOutputPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
  have hbits : bits ≠ [] := by
    simpa [bits] using directJoinedOutputBits_ne_nil p
  cases h : bits with
  | nil =>
      exact False.elim (hbits h)
  | cons first rest =>
      have hbitsEq :
          List.append (structuredLiveTailEmitterAssemblyOutputPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p) =
            first :: rest := by
        simpa [bits] using h
      have houtputTape :
          DirectJoinedCloseout.assemblyCloseoutOutputTape p =
            CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.paddedNonemptyWordTape
              first rest := by
        unfold DirectJoinedCloseout.assemblyCloseoutOutputTape
          DirectJoinedCloseout.paddedWordTape
          CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.paddedNonemptyWordTape
        rw [hbitsEq]
      have hencoded :
          DirectJoinedCloseout.assemblyCloseoutEncodedFinalTape p =
            encodedGuardedStructured3Tapes
              (DirectJoinedCloseout.assemblyCloseoutSourceTape p)
              (DirectJoinedCloseout.assemblyCloseoutScratchTape p)
              (CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.paddedNonemptyWordTape
                first rest) := by
        simp [DirectJoinedCloseout.assemblyCloseoutEncodedFinalTape,
          DirectJoinedCloseout.assemblyCloseoutFinalTapes,
          encodedGuardedStructured3Tapes, houtputTape]
      have hproject :=
        CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription_haltsFromTapeEquiv_padded
          (DirectJoinedCloseout.assemblyCloseoutSourceTape p)
          (DirectJoinedCloseout.assemblyCloseoutScratchTape p)
          first rest
      rw [hencoded, hbitsEq]
      exact hproject

theorem directJoinedAssemblyOutputDescription_haltsFrom_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    directJoinedAssemblyOutputDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblySourceTape p)
      (Tape.input
        (assemblySourceRestFinishJoinedOutput
          p.w p.sourceRestBits p.stage)) := by
  have hcloseProject :
      (canonicalPrimitiveSeqDescription
        DirectJoinedCloseout.loweredDescription
        CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription).HaltsFromTapeEquiv
          (structuredLiveTailEmitterAssemblyEncodedFinalTape p)
          (Tape.input
            (List.append (structuredLiveTailEmitterAssemblyOutputPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p))) :=
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      DirectJoinedCloseout.loweredDescription_subroutineReady
      CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription_subroutineReady
      (directJoinedCloseoutLowered_haltsFrom_emitterFinal p)
      (directJoinedProjector_haltsFrom_closeout p)
  have hemitterCloseProject :
      (canonicalPrimitiveSeqDescription
        loweredStructuredLiveTailEmitterDescription
        (canonicalPrimitiveSeqDescription
          DirectJoinedCloseout.loweredDescription
          CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription)).HaltsFromTapeEquiv
          (structuredLiveTailEmitterAssemblyEncodedInitialTape p)
          (Tape.input
            (List.append (structuredLiveTailEmitterAssemblyOutputPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p))) :=
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      loweredStructuredLiveTailEmitterDescription_subroutineReady_static
      (canonicalPrimitiveSeqDescription_subroutineReady
        DirectJoinedCloseout.loweredDescription_subroutineReady
        CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription_subroutineReady)
      (loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded_static p)
      hcloseProject
  have hrun :=
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      directJoinedInitializerDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        loweredStructuredLiveTailEmitterDescription_subroutineReady_static
        (canonicalPrimitiveSeqDescription_subroutineReady
          DirectJoinedCloseout.loweredDescription_subroutineReady
          CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector.endpointTape2ProjectorDescription_subroutineReady))
      (directJoinedInitializerDescription_haltsFrom_assembly p)
      hemitterCloseProject
  rw [directJoinedOutputBits_eq_joinedOutput p] at hrun
  exact hrun

theorem directJoinedAssemblyOutputDescription_haltsFrom_assemblyWithOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    directJoinedAssemblyOutputDescription.HaltsFromTapeWithOutput
      (structuredLiveTailEmitterAssemblySourceTape p)
      (assemblySourceRestFinishJoinedOutput
        p.w p.sourceRestBits p.stage) := by
  have hrun :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
      (directJoinedAssemblyOutputDescription_haltsFrom_assembly p)
  have hnormalized :
      Tape.normalizedOutput
          (Tape.input
            (assemblySourceRestFinishJoinedOutput
              p.w p.sourceRestBits p.stage)) =
        assemblySourceRestFinishJoinedOutput
          p.w p.sourceRestBits p.stage := by
    cases assemblySourceRestFinishJoinedOutput
        p.w p.sourceRestBits p.stage <;>
      simp [Tape.normalizedOutput, Tape.cells, Tape.input, Tape.blank,
        Function.comp_def]
  rw [hnormalized] at hrun
  exact hrun

theorem structuredLiveTailEmitterAssemblySourceTape_eq_defaultedInternalMarker
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblySourceTape p =
      MixedParserStackRewriterDefaultedInternalMarkerTape
        p.w p.sourceRestBits
        (preservingCellPassCellBits p.sourceRestBits) p.stage := by
  rw [MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape]
  rfl

theorem directJoinedAssemblyOutputDescription_spec :
    MixedParserStackSourceRestFinishAssemblyOutputSpec
      directJoinedAssemblyOutputDescription := by
  refine ⟨directJoinedAssemblyOutputDescription_subroutineReady, ?_⟩
  intro w sourceRestBits stage
  let p : AssemblySourceRestLiveTailEmitterParam :=
    { w := w, sourceRestBits := sourceRestBits, stage := stage }
  rw [← structuredLiveTailEmitterAssemblySourceTape_eq_defaultedInternalMarker p]
  simpa [p] using
    directJoinedAssemblyOutputDescription_haltsFrom_assemblyWithOutput p

theorem directJoinedSourceRestFinishAssemblyOutputConstruction :
    MixedParserStackSourceRestFinishAssemblyOutputConstruction :=
  ⟨directJoinedAssemblyOutputDescription,
    directJoinedAssemblyOutputDescription_spec⟩

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
