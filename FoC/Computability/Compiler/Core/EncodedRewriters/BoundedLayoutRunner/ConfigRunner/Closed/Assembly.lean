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

theorem selectedMergePrimitiveClosedHandoffConstruction_finite_scaffold :
    SelectedMergePrimitiveClosedHandoffConstruction :=
  selectedMergePrimitiveClosedHandoffConstruction_of_rightShifted
    selectedMergePrimitiveRightShiftedConstruction_scaffold

theorem rejectMergePrimitiveClosedHandoffConstruction_finite_scaffold :
    RejectMergePrimitiveClosedHandoffConstruction :=
  rejectMergePrimitiveClosedHandoffConstruction_of_selected
    selectedMergePrimitiveClosedHandoffConstruction_finite_scaffold

def AcceptMergePrimitiveClosedHandoffFiniteMachineConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptMergePrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

theorem acceptMergePrimitiveClosedHandoffConstruction_of_finiteMachine
    (h : AcceptMergePrimitiveClosedHandoffFiniteMachineConstruction) :
    AcceptMergePrimitiveClosedHandoffConstruction :=
  h

-- Actual finite parser/emitter table for the accept-side merge rewriter.
theorem acceptMergePrimitiveClosedHandoffFiniteMachineConstruction_scaffold :
    AcceptMergePrimitiveClosedHandoffFiniteMachineConstruction :=
  acceptMergePrimitiveClosedHandoffConstruction_of_selected
    selectedMergePrimitiveClosedHandoffConstruction_finite_scaffold

theorem acceptMergePrimitiveClosedHandoffConstruction_finite_scaffold :
    AcceptMergePrimitiveClosedHandoffConstruction := by
  exact
    acceptMergePrimitiveClosedHandoffConstruction_of_finiteMachine
      acceptMergePrimitiveClosedHandoffFiniteMachineConstruction_scaffold

theorem selectedMergeRejectPrimitiveClosedHandoffConstruction_scaffold :
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedMergePrimitive false)
        closed tapeCodePrimitiveCodeWordHandoffMove := by
  rcases rejectMergePrimitiveClosedHandoffConstruction_finite_scaffold with
    ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := RejectMergePrimitive)
      (Q := SelectedMergePrimitive false)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem selectedMergeAcceptPrimitiveClosedHandoffConstruction_scaffold :
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedMergePrimitive true)
        closed tapeCodePrimitiveCodeWordHandoffMove := by
  rcases acceptMergePrimitiveClosedHandoffConstruction_finite_scaffold with
    ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := AcceptMergePrimitive)
      (Q := SelectedMergePrimitive true)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem selectedMergePrimitiveClosedHandoffConstruction_scaffold :
    SelectedMergePrimitiveClosedHandoffConstruction := by
  intro useAccept
  cases useAccept
  · exact selectedMergeRejectPrimitiveClosedHandoffConstruction_scaffold
  · exact selectedMergeAcceptPrimitiveClosedHandoffConstruction_scaffold

theorem acceptProjectionPrimitiveClosedHandoffConstruction_scaffold :
    AcceptProjectionPrimitiveClosedHandoffConstruction := by
  exact
    acceptProjectionPrimitiveClosedHandoffConstruction_of_selected
      selectedProjectionPrimitiveClosedHandoffConstruction_scaffold

theorem acceptMergePrimitiveClosedHandoffConstruction_scaffold :
    AcceptMergePrimitiveClosedHandoffConstruction := by
  exact acceptMergePrimitiveClosedHandoffConstruction_finite_scaffold

theorem rejectProjectionPrimitiveClosedHandoffConstruction_scaffold :
    RejectProjectionPrimitiveClosedHandoffConstruction := by
  exact
    rejectProjectionPrimitiveClosedHandoffConstruction_of_selected
      selectedProjectionPrimitiveClosedHandoffConstruction_scaffold

theorem rejectMergePrimitiveClosedHandoffConstruction_scaffold :
    RejectMergePrimitiveClosedHandoffConstruction := by
  exact rejectMergePrimitiveClosedHandoffConstruction_finite_scaffold

theorem configRunnerPrimitiveClosedHandoffConstruction_scaffold :
    ConfigRunnerPrimitiveClosedHandoffConstruction := by
  exact
    configRunnerPrimitiveClosedHandoffConstruction_of_parts
      acceptProjectionPrimitiveClosedHandoffConstruction_scaffold
      acceptMergePrimitiveClosedHandoffConstruction_scaffold
      rejectProjectionPrimitiveClosedHandoffConstruction_scaffold
      rejectMergePrimitiveClosedHandoffConstruction_scaffold

theorem configRunnerPhaseConstruction_scaffold :
    ConfigRunnerPhaseConstruction :=
  configRunnerPhaseConstruction_of_primitiveClosedHandoff
    fixedDescriptionBoundedSimulatorCanonicalConstruction_scaffold_configRunner
    configRunnerPrimitiveClosedHandoffConstruction_scaffold

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
    acceptRejectConfigRunnerConstruction_of_phaseConstruction
      configRunnerPhaseConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
