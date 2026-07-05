import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.Main
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.Cleanup
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.PhaseAdapters
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.PhaseRunner
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner closed-handoff assembly

This module assembles the selected primitive constructions into the public
closed-handoff and bounded-runner construction scaffolds.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
Selected projection enters phase assembly through the finite-description
padded/equivalence route.  The old exact/right-shifted selected-projection
adapter path has been removed rather than kept as a compatibility import.

The exact/right-shifted selected-merge primitive scaffold chain is false: the
merge phase intentionally preserves simulator-layout scratch structure that is
only equivalent to the parsed dovetail layout.  The live config-runner scaffold
therefore uses the equivalence-based merge phase contract from the
finite-description construction module instead of requiring an exact parsed
layout tape.
-/
theorem configRunnerPhaseEquivConstruction_scaffold_of_selectedProjection
    (hprojection : SelectedProjectionFiniteDescriptionConstruction) :
    ConfigRunnerPhaseEquivConstruction := by
  intro accept reject
  rcases hprojection true with
    ⟨acceptProject, hacceptProject⟩
  rcases hprojection false with
    ⟨rejectProject, hrejectProject⟩
  rcases fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner
      accept with
    ⟨acceptSim, hacceptSim⟩
  rcases fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner
      reject with
    ⟨rejectSim, hrejectSim⟩
  rcases selectedMergeEquivConstruction_scaffold true with
    ⟨acceptMerge, hacceptMerge⟩
  rcases selectedMergeEquivConstruction_scaffold false with
    ⟨rejectMerge, hrejectMerge⟩
  exact
    ⟨SelectedProjectionPhaseFromOutputTape acceptProject,
      acceptSim,
      acceptMerge,
      SelectedProjectionPhaseFromOutputTape rejectProject,
      rejectSim,
      rejectMerge,
      AcceptProjectionSpec_of_selected hacceptProject,
      hacceptSim,
      acceptMergeEquivSpec_of_selected hacceptMerge,
      RejectProjectionSpec_of_selected hrejectProject,
      hrejectSim,
      rejectMergeEquivSpec_of_selected hrejectMerge⟩

theorem configRunnerPhaseEquivConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    ConfigRunnerPhaseEquivConstruction :=
  configRunnerPhaseEquivConstruction_scaffold_of_selectedProjection
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem configRunnerPhaseEquivConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    ConfigRunnerPhaseEquivConstruction :=
  configRunnerPhaseEquivConstruction_scaffold_of_selectedProjection
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem configRunnerPhaseEquivConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    ConfigRunnerPhaseEquivConstruction :=
  configRunnerPhaseEquivConstruction_scaffold_of_selectedProjection
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem configRunnerPhaseEquivConstruction_scaffold :
    ConfigRunnerPhaseEquivConstruction :=
  configRunnerPhaseEquivConstruction_scaffold_of_selectedProjection
    selectedProjectionFiniteDescriptionConstruction_scaffold

def ConfigRunnerFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  seqSubroutine closed
    ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem configRunnerFromClosedHandoff_spec
    {accept reject closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    AcceptRejectConfigRunnerSpec accept reject
      (ConfigRunnerFromClosedHandoff closed) := by
  let identity := ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hidentityReady : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      seqSubroutine_subroutineReady
        hclosedReady hidentityReady
  constructor
  · intro L
    have htransform :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            (DovetailLayout.encode L) =
          some
            (DovetailLayout.encode
              (BoundedRunLayout accept reject L)) := by
      simpa [PairedRecognizerDovetailLayoutCode,
        BoundedRunLayout] using
        DovetailLayout.runCodePrimitive_encode
          accept reject L
    exact TapeCodeCheckedPhaseFromClosedHandoff_forward hclosed htransform
  · intro L T hhalt
    have htransform :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            (DovetailLayout.encode L) =
          some
            (DovetailLayout.encode
              (BoundedRunLayout accept reject L)) := by
      simpa [PairedRecognizerDovetailLayoutCode,
        BoundedRunLayout] using
        DovetailLayout.runCodePrimitive_encode
          accept reject L
    exact TapeCodeCheckedPhaseFromClosedHandoff_closed_equiv hclosed htransform hhalt

theorem acceptRejectConfigRunnerConstruction_scaffold_of_selectedProjection
    (hprojection : SelectedProjectionFiniteDescriptionConstruction) :
    AcceptRejectConfigRunnerConstruction := by
  exact
    acceptRejectConfigRunnerConstruction_of_phaseEquivConstruction
      (configRunnerPhaseEquivConstruction_scaffold_of_selectedProjection
        hprojection)

theorem acceptRejectConfigRunnerConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    AcceptRejectConfigRunnerConstruction :=
  acceptRejectConfigRunnerConstruction_scaffold_of_selectedProjection
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem acceptRejectConfigRunnerConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    AcceptRejectConfigRunnerConstruction :=
  acceptRejectConfigRunnerConstruction_scaffold_of_selectedProjection
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem acceptRejectConfigRunnerConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    AcceptRejectConfigRunnerConstruction :=
  acceptRejectConfigRunnerConstruction_scaffold_of_selectedProjection
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem acceptRejectConfigRunnerConstruction_scaffold :
    AcceptRejectConfigRunnerConstruction :=
  acceptRejectConfigRunnerConstruction_scaffold_of_selectedProjection
    selectedProjectionFiniteDescriptionConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
