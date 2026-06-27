import FoC.Computability.Compiler.Core.CommonGround
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner closed-handoff assembly

This module assembles the selected primitive constructions into the public
closed-handoff and bounded-runner construction scaffolds.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

theorem selectedProjectionPrimitiveClosedHandoffConstruction_of_rightShifted
    (h : SelectedProjectionPrimitiveRightShiftedConstruction) :
    SelectedProjectionPrimitiveClosedHandoffConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
      hrunner
      (by
        intro code out htransform
        rcases
            SelectedProjectionPrimitive_transform_eq_some_cons
              htransform with
          ⟨tail, hout⟩
        exact ⟨MachineCodeSymbol.header, tail, hout⟩)

theorem selectedMergePrimitiveClosedHandoffConstruction_of_rightShifted
    (h : SelectedMergePrimitiveRightShiftedConstruction) :
    SelectedMergePrimitiveClosedHandoffConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
      hrunner
      (by
        intro code out htransform
        rcases
            SelectedMergePrimitive_transform_eq_some_cons
              htransform with
          ⟨tail, hout⟩
        exact ⟨MachineCodeSymbol.transition, tail, hout⟩)

theorem selectedProjectionPrimitiveClosedHandoffConstruction_scaffold :
    SelectedProjectionPrimitiveClosedHandoffConstruction :=
  selectedProjectionPrimitiveClosedHandoffConstruction_of_rightShifted
    selectedProjectionPrimitiveRightShiftedConstruction_scaffold

theorem selectedProjectionRejectPrimitiveClosedHandoffConstruction_scaffold :
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedProjectionPrimitive false)
        closed tapeCodePrimitiveCodeWordHandoffMove :=
  selectedProjectionPrimitiveClosedHandoffConstruction_scaffold false

theorem selectedProjectionAcceptPrimitiveClosedHandoffConstruction_scaffold :
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedProjectionPrimitive true)
        closed tapeCodePrimitiveCodeWordHandoffMove :=
  selectedProjectionPrimitiveClosedHandoffConstruction_scaffold true

theorem acceptProjectionPrimitiveClosedHandoffConstruction_scaffold :
    AcceptProjectionPrimitiveClosedHandoffConstruction := by
  exact
    acceptProjectionPrimitiveClosedHandoffConstruction_of_selected
      selectedProjectionPrimitiveClosedHandoffConstruction_scaffold

theorem rejectProjectionPrimitiveClosedHandoffConstruction_scaffold :
    RejectProjectionPrimitiveClosedHandoffConstruction := by
  exact
    rejectProjectionPrimitiveClosedHandoffConstruction_of_selected
      selectedProjectionPrimitiveClosedHandoffConstruction_scaffold

/-!
The exact/right-shifted selected-merge primitive scaffold chain is false: the
merge phase intentionally preserves simulator-layout scratch structure that is
only equivalent to the parsed dovetail layout.  The live config-runner scaffold
therefore uses the equivalence-based merge phase contract from the
finite-description construction module instead of requiring an exact parsed
layout tape.
-/
theorem configRunnerPhaseEquivConstruction_scaffold :
    ConfigRunnerPhaseEquivConstruction := by
  intro accept reject
  rcases selectedProjectionFiniteDescriptionConstruction_scaffold true with
    ⟨acceptProject, hacceptProject⟩
  rcases selectedProjectionFiniteDescriptionConstruction_scaffold false with
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

def ConfigRunnerFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine closed
    MachineDescription.ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem configRunnerFromClosedHandoff_spec
    {accept reject closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    AcceptRejectConfigRunnerSpec accept reject
      (ConfigRunnerFromClosedHandoff closed) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hidentityReady : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hclosedReady hidentityReady
  constructor
  · intro L
    have htransform :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            (MachineDescription.DovetailLayout.encode L) =
          some
            (MachineDescription.DovetailLayout.encode
              (BoundedRunLayout accept reject L)) := by
      simpa [PairedRecognizerDovetailLayoutCode,
        BoundedRunLayout] using
        MachineDescription.DovetailLayout.runCodePrimitive_encode
          accept reject L
    exact TapeCodeCheckedPhaseFromClosedHandoff_forward hclosed htransform
  · intro L T hhalt
    have htransform :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            (MachineDescription.DovetailLayout.encode L) =
          some
            (MachineDescription.DovetailLayout.encode
              (BoundedRunLayout accept reject L)) := by
      simpa [PairedRecognizerDovetailLayoutCode,
        BoundedRunLayout] using
        MachineDescription.DovetailLayout.runCodePrimitive_encode
          accept reject L
    exact TapeCodeCheckedPhaseFromClosedHandoff_closed_equiv hclosed htransform hhalt

theorem acceptRejectConfigRunnerConstruction_of_closedHandoffConstruction
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction) :
    AcceptRejectConfigRunnerConstruction := by
  intro accept reject
  rcases h accept reject with ⟨closed, hclosed⟩
  exact
    ⟨ConfigRunnerFromClosedHandoff closed,
      configRunnerFromClosedHandoff_spec hclosed⟩

theorem acceptRejectConfigRunnerConstruction_scaffold :
    AcceptRejectConfigRunnerConstruction := by
  exact
    acceptRejectConfigRunnerConstruction_of_phaseEquivConstruction
      configRunnerPhaseEquivConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
