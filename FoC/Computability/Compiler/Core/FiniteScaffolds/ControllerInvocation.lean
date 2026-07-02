import FoC.Computability.Compiler.Core.FiniteScaffolds.Basic

set_option doc.verso true

/-!
# Finite-source dovetail scaffolds

This module is part of the finite-source manifest for the dovetail controller
route.  It keeps concrete finite construction leaves separated from the wrapper
that re-exports them.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
The last controller-loop leaves are composition machines rather than
single-primitive encoded rewriters: one invokes the total stage-attempt
subroutine after projecting a stage input, and one sequences initializer,
invoker, result emitter, and continuer into the finite search driver.
-/

def PairedRecognizerDovetailStageAttemptInvocationForwardSpec
    (attempt encoder invoker : MachineDescription) : Prop :=
  forall C : DovetailControllerLayout,
  forall result : Word Bool,
    encoder.HaltsWithOutput
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C)) ∧
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result)) ->
    invoker.HaltsWithOutput
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult
            C result)))

def PairedRecognizerDovetailStageAttemptInvocationClosedSpec
    (attempt encoder invoker : MachineDescription) : Prop :=
  forall C : DovetailControllerLayout,
  forall result : Word Bool,
    invoker.HaltsWithOutput
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult
              C result))) ->
      encoder.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C)) ∧
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (encodeCodeWordAsInput
            (encodeBoolWord result))

theorem pairedRecognizerDovetailStageAttemptInvocationRealizes_of_forward_closed
    {attempt encoder invoker : MachineDescription}
    (hready : invoker.SubroutineReady)
    (hforward :
      PairedRecognizerDovetailStageAttemptInvocationForwardSpec
        attempt encoder invoker)
    (hclosed :
      PairedRecognizerDovetailStageAttemptInvocationClosedSpec
        attempt encoder invoker) :
    PairedRecognizerDovetailStageAttemptInvocationRealizes
      attempt encoder invoker := by
  constructor
  · exact hready
  · intro C result
    constructor
    · exact hclosed C result
    · exact hforward C result

def PairedRecognizerDovetailStageAttemptInvocationConstructionData :
    Prop :=
  forall attempt encoder : MachineDescription,
    attempt.SubroutineReady ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    exists invoker : MachineDescription,
      invoker.SubroutineReady ∧
        PairedRecognizerDovetailStageAttemptInvocationForwardSpec
          attempt encoder invoker ∧
        PairedRecognizerDovetailStageAttemptInvocationClosedSpec
          attempt encoder invoker

theorem pairedRecognizerDovetailStageAttemptInvocationConstruction_of_data
    (h :
      PairedRecognizerDovetailStageAttemptInvocationConstructionData) :
    PairedRecognizerDovetailStageAttemptInvocationConstruction := by
  intro attempt encoder hattempt hencoder
  rcases h attempt encoder hattempt hencoder with
    ⟨invoker, hready, hforward, hclosed⟩
  exact
    ⟨invoker,
      pairedRecognizerDovetailStageAttemptInvocationRealizes_of_forward_closed
        hready hforward hclosed⟩

/--
Protected core needed by the stage-attempt invoker.  The finite table may
compute the controller stage input itself; the separate encoder contract is
only needed to expose the public closed/forward specification.
-/
def PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
    (attempt invoker : MachineDescription) : Prop :=
  invoker.SubroutineReady ∧
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult
                C result))) <->
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (encodeCodeWordAsInput
            (encodeBoolWord result))

/--
Construction target for the protected core: preserve/reconstruct the controller
stage-input fields while running the attempt on the canonical stage-input word,
then emit the controller layout with the attempt result installed.
-/
def PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists invoker : MachineDescription,
        PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
          attempt invoker

def PairedRecognizerDovetailStageAttemptFramedRunInvocationForwardSpec
    (attempt invoker : MachineDescription) : Prop :=
  CommonGround.ControllerInvocation.StageAttemptFramedForwardSpec
    attempt invoker

def PairedRecognizerDovetailStageAttemptFramedRunInvocationClosedSpec
    (attempt invoker : MachineDescription) : Prop :=
  CommonGround.ControllerInvocation.StageAttemptFramedClosedSpec
    attempt invoker

/--
Framed run contract for the protected stage-attempt wrapper.  This is the
narrow machine leaf left after the public adapter: the wrapper must simulate
the concrete {lean}`attempt.runConfig` from the canonical controller stage
input, keep the controller layout outside that simulated work area, and emit
the controller layout with exactly the simulated boolean-word result installed.
-/
def PairedRecognizerDovetailStageAttemptFramedRunInvocationRealizes
    (attempt invoker : MachineDescription) : Prop :=
  CommonGround.ControllerInvocation.StageAttemptFramedRealizes
    attempt invoker

def PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData :
    Prop :=
  CommonGround.ControllerInvocation.StageAttemptFramedConstruction

private def PairedRecognizerDovetailStageAttemptWitnessedRunInvocationForwardSpec
    (attempt invoker : MachineDescription) : Prop :=
  CommonGround.ControllerInvocation.StageAttemptWitnessedForwardSpec
    attempt invoker

private def PairedRecognizerDovetailStageAttemptWitnessedRunInvocationRealizes
    (attempt invoker : MachineDescription) : Prop :=
  CommonGround.ControllerInvocation.StageAttemptWitnessedRealizes
    attempt invoker

private def PairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData :
    Prop :=
  CommonGround.ControllerInvocation.StageAttemptWitnessedConstruction

private theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_of_protected
    (h :
      PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData) :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨invoker, hinvoker⟩
  refine ⟨invoker, ?_⟩
  constructor
  · exact hinvoker.left
  · constructor
    · intro C result hrun
      exact (hinvoker.right C result).mpr hrun
    · intro C result hrun
      exact (hinvoker.right C result).mp hrun

theorem pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_of_framedRun
    (h :
      PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData) :
    PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨invoker, hinvoker⟩
  refine ⟨invoker, ?_⟩
  constructor
  · exact hinvoker.left
  · intro C result
    constructor
    · intro hrun
      exact hinvoker.right.right C result hrun
    · intro hrun
      exact hinvoker.right.left C result hrun

theorem pairedRecognizerDovetailStageAttemptInvocationConstructionData_of_protected
    (h :
      PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData) :
    PairedRecognizerDovetailStageAttemptInvocationConstructionData := by
  intro attempt encoder hattempt hencoder
  rcases h attempt hattempt with ⟨invoker, hinvoker⟩
  refine ⟨invoker, hinvoker.left, ?_, ?_⟩
  · intro C result hrun
    exact (hinvoker.right C result).mpr hrun.right
  · intro C result hrun
    constructor
    · exact
        tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
          hencoder
          (pairedRecognizerDovetailControllerStageInputCode_encode C)
    · exact (hinvoker.right C result).mp hrun

/--
Finite-machine leaf for witnessed controller stage-attempt invocation.  This is
the concrete transition-table obligation after CommonGround has named the
controller-layout encodings and the witnessed-run contract.
-/
private theorem controllerStageAttemptWitnessedInvocationConstruction_leaf :
    CommonGround.ControllerInvocation.StageAttemptWitnessedConstruction := by
  sorry

private theorem pairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData_finite_leaf :
    PairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData :=
  controllerStageAttemptWitnessedInvocationConstruction_leaf

/--
Finite-machine leaf for the framed protected stage-attempt wrapper.  This is
packaging around the witnessed-run leaf: the public framed contract uses an
existential run witness in its forward half.
-/
private theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_finite_leaf :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData := by
  intro attempt hattempt
  rcases
      pairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData_finite_leaf
        attempt hattempt with
    ⟨invoker, hready, hforward, hclosed⟩
  refine ⟨invoker, hready, ?_, hclosed⟩
  intro C result hrun
  rcases hrun with ⟨n, hn⟩
  exact hforward C result n hn

/-- Protected packaging of the framed stage-attempt wrapper leaf. -/
private theorem pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_finite_leaf :
    PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData :=
  pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_of_framedRun
    pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_finite_leaf

/--
Framed-run packaging of the protected stage-attempt wrapper leaf.
-/
theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_scaffold :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData := by
  exact
    pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_finite_leaf

theorem pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_scaffold :
    PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData :=
  pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_of_framedRun
    pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_scaffold

/--
Finite-machine leaf for invoking one total stage-attempt subroutine after
encoding the controller stage input.
-/
theorem pairedRecognizerDovetailStageAttemptInvocationConstructionData_scaffold :
    PairedRecognizerDovetailStageAttemptInvocationConstructionData :=
  pairedRecognizerDovetailStageAttemptInvocationConstructionData_of_protected
    pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_scaffold

theorem pairedRecognizerDovetailStageAttemptInvocationConstruction_scaffold :
    PairedRecognizerDovetailStageAttemptInvocationConstruction :=
  pairedRecognizerDovetailStageAttemptInvocationConstruction_of_data
    pairedRecognizerDovetailStageAttemptInvocationConstructionData_scaffold

theorem pairedRecognizerDovetailStageAttemptInvocationHandoffConstruction_scaffold :
    PairedRecognizerDovetailStageAttemptInvocationHandoffConstruction :=
  pairedRecognizerDovetailStageAttemptInvocationHandoffConstruction_of_output
    pairedRecognizerDovetailStageAttemptInvocationConstruction_scaffold

theorem pairedRecognizerDovetailControllerResultEmitterConstruction_scaffold :
    PairedRecognizerDovetailControllerResultEmitterConstruction :=
  pairedRecognizerDovetailControllerResultEmitterConstruction_of_encodedRewriter
    encodedControllerResultEmitterRewriterConstruction_scaffold

theorem pairedRecognizerDovetailControllerContinueConstruction_scaffold :
    PairedRecognizerDovetailControllerContinueConstruction :=
  pairedRecognizerDovetailControllerContinueConstruction_of_encodedRewriter
    encodedControllerContinueRewriterConstruction_scaffold

end Computability
end FoC
