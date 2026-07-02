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
  CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
    attempt invoker

theorem pairedRecognizerDovetailStageAttemptProtectedInvocation_attempt_output_functional
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (C : DovetailControllerLayout)
    {result1 result2 : Word Bool}
    (h1 :
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result1)))
    (h2 :
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result2))) :
    result1 = result2 := by
  exact
    CommonGround.ControllerInvocation.stageAttemptProtected_attempt_output_functional
      hinvoker C h1 h2

theorem pairedRecognizerDovetailStageAttemptProtectedInvocation_attempt_outputIn_functional
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (C : DovetailControllerLayout)
    {result1 result2 : Word Bool} {n1 n2 : Nat}
    (h1 :
      attempt.HaltsWithOutputIn n1
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result1)))
    (h2 :
      attempt.HaltsWithOutputIn n2
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result2))) :
    result1 = result2 :=
  CommonGround.ControllerInvocation.stageAttemptProtected_attempt_outputIn_functional
    hinvoker C h1 h2

theorem pairedRecognizerDovetailStageAttemptProtectedInvocation_rawOutput_functional
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (C : DovetailControllerLayout)
    {result1 result2 out1 out2 : Word Bool}
    (h1 :
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result1)))
    (h2 :
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result2)))
    (hraw1 :
      PairedRecognizerDovetailControllerRawOutput result1 = some out1)
    (hraw2 :
      PairedRecognizerDovetailControllerRawOutput result2 = some out2) :
    out1 = out2 := by
  exact
    CommonGround.ControllerInvocation.stageAttemptProtected_rawOutput_functional
      hinvoker C h1 h2 hraw1 hraw2

theorem pairedRecognizerDovetailStageAttemptProtectedInvocation_rawOutputIn_functional
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (C : DovetailControllerLayout)
    {result1 result2 out1 out2 : Word Bool} {n1 n2 : Nat}
    (h1 :
      attempt.HaltsWithOutputIn n1
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result1)))
    (h2 :
      attempt.HaltsWithOutputIn n2
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result2)))
    (hraw1 :
      PairedRecognizerDovetailControllerRawOutput result1 = some out1)
    (hraw2 :
      PairedRecognizerDovetailControllerRawOutput result2 = some out2) :
    out1 = out2 := by
  exact
    CommonGround.ControllerInvocation.stageAttemptProtected_rawOutputIn_functional
      hinvoker C h1 h2 hraw1 hraw2

theorem pairedRecognizerDovetailStageAttemptProtectedInvocation_rawOutput_bool_functional
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (C : DovetailControllerLayout)
    {result1 result2 : Word Bool} {b1 b2 : Bool}
    (h1 :
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result1)))
    (h2 :
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result2)))
    (hraw1 :
      PairedRecognizerDovetailControllerRawOutput result1 = some [b1])
    (hraw2 :
      PairedRecognizerDovetailControllerRawOutput result2 = some [b2]) :
    b1 = b2 := by
  exact
    CommonGround.ControllerInvocation.stageAttemptProtected_rawOutput_bool_functional
      hinvoker C h1 h2 hraw1 hraw2

theorem pairedRecognizerDovetailStageAttemptProtectedInvocation_rawOutputIn_bool_functional
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (C : DovetailControllerLayout)
    {result1 result2 : Word Bool} {b1 b2 : Bool} {n1 n2 : Nat}
    (h1 :
      attempt.HaltsWithOutputIn n1
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result1)))
    (h2 :
      attempt.HaltsWithOutputIn n2
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result2)))
    (hraw1 :
      PairedRecognizerDovetailControllerRawOutput result1 = some [b1])
    (hraw2 :
      PairedRecognizerDovetailControllerRawOutput result2 = some [b2]) :
    b1 = b2 := by
  exact
    CommonGround.ControllerInvocation.stageAttemptProtected_rawOutputIn_bool_functional
      hinvoker C h1 h2 hraw1 hraw2

/--
Construction target for the protected core: preserve/reconstruct the controller
stage-input fields while running the attempt on the canonical stage-input word,
then emit the controller layout with the attempt result installed.
-/
def PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData :
    Prop :=
  CommonGround.ControllerInvocation.StageAttemptProtectedConstruction

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
  CommonGround.ControllerInvocation.FramedSubroutineInvocationRealizes
    attempt invoker

def PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData :
    Prop :=
  CommonGround.ControllerInvocation.FramedSubroutineInvocationConstruction

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
    PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData :=
  CommonGround.ControllerInvocation.stageAttemptFramedConstruction_of_protected
    h

theorem pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_of_framedRun
    (h :
      PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData) :
    PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData :=
  CommonGround.ControllerInvocation.stageAttemptProtectedConstruction_of_framed
    h

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
Finite-machine leaf for the framed protected stage-attempt wrapper.  This is
the remaining transition-table obligation after CommonGround has named the
protected/framed/witnessed controller-invocation contracts.
-/
private theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_finite_leaf :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData := by
  sorry

/--
Finite-machine leaf for witnessed controller stage-attempt invocation.  This is
now packaging around the framed protected wrapper construction.
-/
private theorem controllerStageAttemptWitnessedInvocationConstruction_leaf :
    CommonGround.ControllerInvocation.StageAttemptWitnessedConstruction := by
  exact
    CommonGround.ControllerInvocation.stageAttemptWitnessedConstruction_of_framed
      pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_finite_leaf

private theorem pairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData_finite_leaf :
    PairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData :=
  controllerStageAttemptWitnessedInvocationConstruction_leaf

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
