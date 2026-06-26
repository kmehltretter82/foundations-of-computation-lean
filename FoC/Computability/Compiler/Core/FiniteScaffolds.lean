import FoC.Computability.Compiler.Core.ControllerResultEmitter
import FoC.Computability.Compiler.Core.ControllerInputInitializer
import FoC.Computability.Compiler.Core.ControllerResultContinue

set_option doc.verso true

/-!
# Finite-source dovetail scaffolds

This file is the finite-source manifest for the dovetail controller route.  It
does not define new encodings; it connects the concrete encoded rewriter leaves
to the paired-recognizer construction targets used by the closeout theorems.
-/

namespace FoC
namespace Computability

open Languages

/-- Forward half of an output-compiled tape-code primitive subroutine. -/
def TapeCodePrimitiveOutputCompiledForwardSpec
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    P.transform code = some out ->
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)

/-- Closed half of an output-compiled tape-code primitive subroutine. -/
def TapeCodePrimitiveOutputCompiledClosedSpec
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) ->
      P.transform code = some out

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_of_forward_closed
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hready : D.SubroutineReady)
    (hforward : TapeCodePrimitiveOutputCompiledForwardSpec P D)
    (hclosed : TapeCodePrimitiveOutputCompiledClosedSpec P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D := by
  constructor
  · constructor
    · exact hready.left
    · intro code out
      constructor
      · exact hclosed code out
      · exact hforward code out
  · exact hready.right

theorem encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_forward_closed
    {P : MachineDescription.TapeCodePrimitive}
    (h :
      exists D : MachineDescription,
        D.SubroutineReady ∧
          TapeCodePrimitiveOutputCompiledForwardSpec P D ∧
          TapeCodePrimitiveOutputCompiledClosedSpec P D) :
    EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction P := by
  rcases h with ⟨D, hready, hforward, hclosed⟩
  exact
    ⟨D,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_of_forward_closed
        hready hforward hclosed⟩

/-!
**Controller encoded leaves.**  These are the finite transition-table
obligations that are specific to the controller loop rather than to the
dovetail layout subroutines.  The projection and result-emitter machines are
already available from their concrete descriptions; the initializer and
continue-result code-word subroutine remain as concrete leaves.
-/

section EncodedControllerLeaves

/-- Controller input initializer data, already stated in the public contract. -/
def EncodedControllerInputInitializerConstructionData :
    Prop :=
  exists initializer : MachineDescription,
    PairedRecognizerDovetailControllerInputInitializerRealizes initializer

theorem encodedControllerInputInitializerRewriterConstruction_of_data
    (h : EncodedControllerInputInitializerConstructionData) :
    EncodedControllerInputInitializerRewriterConstruction := by
  rcases h with ⟨initializer, hinitializer⟩
  exact ⟨initializer, hinitializer.left, hinitializer.right⟩

theorem encodedControllerInputInitializerConstructionData_scaffold :
    EncodedControllerInputInitializerConstructionData := by
  exact controllerInputInitializerConstruction_scaffold

theorem encodedControllerInputInitializerRewriterConstruction_scaffold :
    EncodedControllerInputInitializerRewriterConstruction :=
  encodedControllerInputInitializerRewriterConstruction_of_data
    encodedControllerInputInitializerConstructionData_scaffold

theorem encodedControllerStageInputProjectionRewriterConstruction_scaffold :
    EncodedControllerStageInputProjectionRewriterConstruction :=
  encodedControllerStageInputProjectionRewriterConstruction_of_codeWordSubroutine
    ControllerStageInputProjection.encodedControllerStageInputProjectionCodeWordSubroutineConstruction_scaffold

theorem encodedControllerResultEmitterRewriterConstruction_scaffold :
    EncodedControllerResultEmitterRewriterConstruction :=
  encodedControllerResultEmitterRewriterConstruction_of_description

/--
Controller-result continuation data in the generic forward/closed primitive
format used by the code-word subroutine adapter.
-/
def EncodedControllerResultContinueConstructionData :
    Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      TapeCodePrimitiveOutputCompiledForwardSpec
        PairedRecognizerDovetailControllerResultContinueCode
        continuer ∧
      TapeCodePrimitiveOutputCompiledClosedSpec
        PairedRecognizerDovetailControllerResultContinueCode
        continuer

theorem encodedControllerResultContinueCodeWordSubroutineConstruction_of_data
    (h : EncodedControllerResultContinueConstructionData) :
    EncodedControllerResultContinueCodeWordSubroutineConstruction :=
  encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_forward_closed
    h

theorem encodedControllerResultContinueConstructionData_scaffold :
    EncodedControllerResultContinueConstructionData := by
  exact controllerResultContinueConstruction_scaffold

theorem encodedControllerResultContinueCodeWordSubroutineConstruction_scaffold :
    EncodedControllerResultContinueCodeWordSubroutineConstruction :=
  encodedControllerResultContinueCodeWordSubroutineConstruction_of_data
    encodedControllerResultContinueConstructionData_scaffold

theorem encodedControllerContinueRewriterConstruction_scaffold :
    EncodedControllerContinueRewriterConstruction :=
  encodedControllerContinueRewriterConstruction_of_resultContinueCodeWordSubroutine
    encodedControllerResultContinueCodeWordSubroutineConstruction_scaffold

end EncodedControllerLeaves

/-!
**Contract bridges.**  The encoded rewriter contracts are stated in terms of
canonical code-word input and output.  The paired-recognizer construction
targets use the same machines packaged as output-compiled subroutines or as
controller component realizers.  These lemmas keep that repackaging explicit,
so the final scaffold section can name only construction dependencies.
-/

section ContractBridges

private theorem encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
    {P : MachineDescription.TapeCodePrimitive}
    (h : EncodedTapeCodePrimitiveRewriterConstruction P) :
    EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction P := by
  rcases h with ⟨rewriter, hready, hspec⟩
  exact ⟨rewriter, ⟨⟨hready.left, hspec⟩, hready.right⟩⟩

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailStageInputToInitialLayoutRewriterConstruction) :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction := by
  intro accept reject
  exact
    encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
      (P := PairedRecognizerDovetailInitialLayoutCode accept reject)
      (h accept reject)

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailLayoutBoundedRunnerRewriterConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction := by
  intro accept reject
  exact
    encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
      (P := PairedRecognizerDovetailLayoutCode accept reject)
      (h accept reject)

theorem pairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction_of_encodedRewriter
    (h :
      EncodedDovetailTotalOutputEmitterRewriterConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction :=
  h

theorem pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction) :
    PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction :=
  h

theorem pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction :=
  h

theorem pairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailTotalOutputEmitterHandoffRewriterConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction :=
  h

theorem pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction) :
    PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction :=
  h

theorem pairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction :=
  h

theorem pairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction :=
  h

theorem pairedRecognizerDovetailControllerInputInitializerConstruction_of_encodedRewriter
    (h : EncodedControllerInputInitializerRewriterConstruction) :
    PairedRecognizerDovetailControllerInputInitializerConstruction :=
  h

theorem pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_encodedRewriter
    (h : EncodedControllerStageInputProjectionRewriterConstruction) :
    PairedRecognizerDovetailControllerStageInputEncoderConstruction :=
  encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
    (P := PairedRecognizerDovetailControllerStageInputCodePrimitive) h

theorem pairedRecognizerDovetailControllerResultEmitterConstruction_of_encodedRewriter
    (h : EncodedControllerResultEmitterRewriterConstruction) :
    PairedRecognizerDovetailControllerResultEmitterConstruction :=
  h

theorem pairedRecognizerDovetailControllerContinueConstruction_of_encodedRewriter
    (h : EncodedControllerContinueRewriterConstruction) :
    PairedRecognizerDovetailControllerContinueConstruction :=
  h

end ContractBridges

/-!
**Finite-source scaffold exports.**  These declarations are the remaining concrete
machine-construction leaves for the paired-recognizer dovetail controller
route. They are intentionally narrow: the source programs and controller layout
are the fixed finite targets above, not arbitrary staged programs or arbitrary
tape-code primitives.
-/

section FiniteSourceScaffoldExports

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction :=
  pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_closedHandoff
    (pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
      encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold)

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_closedHandoff
    (pairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
      encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold)

theorem pairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction_scaffold :
    PairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction :=
  pairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction_of_encodedRewriter
    encodedDovetailTotalOutputEmitterRewriterConstruction_scaffold

theorem pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailControllerInputInitializerConstruction_scaffold :
    PairedRecognizerDovetailControllerInputInitializerConstruction :=
  pairedRecognizerDovetailControllerInputInitializerConstruction_of_encodedRewriter
    encodedControllerInputInitializerRewriterConstruction_scaffold

theorem pairedRecognizerDovetailControllerStageInputEncoderConstruction_scaffold :
    PairedRecognizerDovetailControllerStageInputEncoderConstruction :=
  pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_encodedRewriter
    encodedControllerStageInputProjectionRewriterConstruction_scaffold

/-!
The last controller-loop leaves are composition machines rather than
single-primitive encoded rewriters: one invokes the total stage-attempt
subroutine after projecting a stage input, and one sequences initializer,
invoker, result emitter, and continuer into the finite search driver.
-/

def PairedRecognizerDovetailStageAttemptInvocationForwardSpec
    (attempt encoder invoker : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
  forall result : Word Bool,
    encoder.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C)) ∧
      attempt.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWord result)) ->
    invoker.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode
          (MachineDescription.DovetailControllerLayout.withResult
            C result)))

def PairedRecognizerDovetailStageAttemptInvocationClosedSpec
    (attempt encoder invoker : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
  forall result : Word Bool,
    invoker.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.withResult
              C result))) ->
      encoder.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C)) ∧
        attempt.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWord result))

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
    forall C : MachineDescription.DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode
              (MachineDescription.DovetailControllerLayout.withResult
                C result))) <->
        attempt.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWord result))

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
  forall C : MachineDescription.DovetailControllerLayout,
  forall result : Word Bool,
    (exists n : Nat,
      attempt.HaltsWithOutputIn n
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWord result))) ->
    invoker.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode
          (MachineDescription.DovetailControllerLayout.withResult
            C result)))

def PairedRecognizerDovetailStageAttemptFramedRunInvocationClosedSpec
    (attempt invoker : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
  forall result : Word Bool,
    invoker.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.withResult
              C result))) ->
      exists n : Nat,
        attempt.HaltsWithOutputIn n
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWord result))

/--
Framed run contract for the protected stage-attempt wrapper.  This is the
narrow machine leaf left after the public adapter: the wrapper must simulate
the concrete {lean}`attempt.runConfig` from the canonical controller stage
input, keep the controller layout outside that simulated work area, and emit
the controller layout with exactly the simulated boolean-word result installed.
-/
def PairedRecognizerDovetailStageAttemptFramedRunInvocationRealizes
    (attempt invoker : MachineDescription) : Prop :=
  invoker.SubroutineReady ∧
    PairedRecognizerDovetailStageAttemptFramedRunInvocationForwardSpec
      attempt invoker ∧
    PairedRecognizerDovetailStageAttemptFramedRunInvocationClosedSpec
      attempt invoker

def PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists invoker : MachineDescription,
        PairedRecognizerDovetailStageAttemptFramedRunInvocationRealizes
          attempt invoker

private def PairedRecognizerDovetailStageAttemptWitnessedRunInvocationForwardSpec
    (attempt invoker : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
  forall result : Word Bool,
  forall n : Nat,
    attempt.HaltsWithOutputIn n
      (MachineDescription.encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageInputCode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeBoolWord result)) ->
    invoker.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode
          (MachineDescription.DovetailControllerLayout.withResult
            C result)))

private def PairedRecognizerDovetailStageAttemptWitnessedRunInvocationRealizes
    (attempt invoker : MachineDescription) : Prop :=
  invoker.SubroutineReady ∧
    PairedRecognizerDovetailStageAttemptWitnessedRunInvocationForwardSpec
      attempt invoker ∧
    PairedRecognizerDovetailStageAttemptFramedRunInvocationClosedSpec
      attempt invoker

private def PairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists invoker : MachineDescription,
        PairedRecognizerDovetailStageAttemptWitnessedRunInvocationRealizes
          attempt invoker

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
Narrow finite-machine leaf for the framed protected stage-attempt wrapper.  The
forward half is stated against a concrete witnessed {lean}`attempt` run, so the
remaining transition-table obligation is exactly to preserve the controller
stage input while invoking that run and then emit
{lean}`MachineDescription.DovetailControllerLayout.withResult`.
-/
private theorem pairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData_finite_leaf :
    PairedRecognizerDovetailStageAttemptWitnessedRunInvocationConstructionData := by
  sorry

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

def PairedRecognizerDovetailFiniteStageLoopForwardSpec
    (attempt decider : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b : Bool,
    (exists limit : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]) ->
      decider.HaltsWithOutput w [b]

def PairedRecognizerDovetailFiniteStageLoopClosedSpec
    (attempt decider : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b : Bool,
    decider.HaltsWithOutput w [b] ->
      exists limit : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_forward_closed
    {attempt decider : MachineDescription}
    (hwell : decider.WellFormed)
    (hforward :
      PairedRecognizerDovetailFiniteStageLoopForwardSpec
        attempt decider)
    (hclosed :
      PairedRecognizerDovetailFiniteStageLoopClosedSpec
        attempt decider) :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider := by
  constructor
  · exact hwell
  · intro w b
    constructor
    · exact hclosed w b
    · exact hforward w b

def PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData :
    Prop :=
  forall attempt initializer encoder invoker emitter continuer :
      MachineDescription,
    attempt.SubroutineReady ->
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    PairedRecognizerDovetailStageAttemptInvocationRealizes
      attempt encoder invoker ->
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter ->
    PairedRecognizerDovetailControllerContinueRealizes
      continuer ->
    exists decider : MachineDescription,
      decider.WellFormed ∧
        PairedRecognizerDovetailFiniteStageLoopForwardSpec
          attempt decider ∧
        PairedRecognizerDovetailFiniteStageLoopClosedSpec
          attempt decider

def PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData :
    Prop :=
  forall attempt initializer invoker emitter continuer : MachineDescription,
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer ->
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker ->
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter ->
    PairedRecognizerDovetailControllerContinueRealizes
      continuer ->
    exists decider : MachineDescription,
      decider.WellFormed ∧
        PairedRecognizerDovetailFiniteStageLoopForwardSpec
          attempt decider ∧
        PairedRecognizerDovetailFiniteStageLoopClosedSpec
          attempt decider

theorem pairedRecognizerDovetailStageAttemptProtectedInvocationRealizes_of_invocation
    {attempt encoder invoker : MachineDescription}
    (hencoder :
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        PairedRecognizerDovetailControllerStageInputCodePrimitive
        encoder)
    (hinvoker :
      PairedRecognizerDovetailStageAttemptInvocationRealizes
        attempt encoder invoker) :
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker := by
  constructor
  · exact hinvoker.left
  · intro C result
    constructor
    · intro hrun
      exact ((hinvoker.right C result).mp hrun).right
    · intro hrun
      exact
        (hinvoker.right C result).mpr
          ⟨tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
              hencoder
              (pairedRecognizerDovetailControllerStageInputCode_encode C),
            hrun⟩

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_of_protected
    (h :
      PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData) :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData := by
  intro attempt initializer encoder invoker emitter continuer
    _hattempt hinitializer hencoder hinvoker hemitter hcontinuer
  exact
    h attempt initializer invoker emitter continuer
      hinitializer
      (pairedRecognizerDovetailStageAttemptProtectedInvocationRealizes_of_invocation
        hencoder hinvoker)
      hemitter hcontinuer

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_of_data
    (h :
      PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData) :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstruction := by
  intro attempt initializer encoder invoker emitter continuer
    hattempt hinitializer hencoder hinvoker hemitter hcontinuer
  rcases h attempt initializer encoder invoker emitter continuer
      hattempt hinitializer hencoder hinvoker hemitter hcontinuer with
    ⟨decider, hwell, hforward, hclosed⟩
  exact
    ⟨decider,
      pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_forward_closed
        hwell hforward hclosed⟩

private def pairedRecognizerDovetailFiniteStageLoopStageLayout
    (w : Word Bool) (limit : Nat) :
    MachineDescription.DovetailControllerLayout :=
  { input := w, stage := limit, result := [] }

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerForwardSpec
    (initializer invoker emitter decider : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b : Bool,
    (exists limit : Nat,
      exists result : Word Bool,
        initializer.HaltsWithOutput w
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerInitialCode w)) ∧
          invoker.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (pairedRecognizerDovetailFiniteStageLoopStageLayout
                  w limit)))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.withResult
                  (pairedRecognizerDovetailFiniteStageLoopStageLayout
                    w limit)
                  result))) ∧
          emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.withResult
                  (pairedRecognizerDovetailFiniteStageLoopStageLayout
                    w limit)
                  result)))
            [b]) ->
      decider.HaltsWithOutput w [b]

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerClosedSpec
    (initializer invoker emitter decider : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b : Bool,
    decider.HaltsWithOutput w [b] ->
      exists limit : Nat,
      exists result : Word Bool,
        initializer.HaltsWithOutput w
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerInitialCode w)) ∧
          invoker.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (pairedRecognizerDovetailFiniteStageLoopStageLayout
                  w limit)))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.withResult
                  (pairedRecognizerDovetailFiniteStageLoopStageLayout
                    w limit)
                  result))) ∧
          emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.withResult
                  (pairedRecognizerDovetailFiniteStageLoopStageLayout
                    w limit)
                  result)))
            [b]

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerContinueSpec
    (continuer : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    PairedRecognizerDovetailControllerRawOutput C.result = none ->
      continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)))

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes
    (initializer invoker emitter continuer decider : MachineDescription) :
    Prop :=
  decider.WellFormed ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerContinueSpec
      continuer ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerForwardSpec
      initializer invoker emitter decider ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerClosedSpec
      initializer invoker emitter decider

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerSearchDriverData :
    Prop :=
  forall attempt : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider

private theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes_of_searchDriver
    {attempt initializer invoker emitter continuer decider : MachineDescription}
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider)
    (hinitializer :
      PairedRecognizerDovetailControllerInputInitializerRealizes
        initializer)
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (hemitter :
      PairedRecognizerDovetailControllerResultEmitterRealizes
        emitter)
    (hcontinuer :
      PairedRecognizerDovetailControllerContinueRealizes
        continuer) :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes
      initializer invoker emitter continuer decider := by
  rcases hdriver with ⟨hwell, hdriverSpec⟩
  refine ⟨hwell, ?_, ?_, ?_⟩
  · intro C hraw
    exact (hcontinuer.right C).mpr hraw
  · intro w b hstage
    rcases hstage with
      ⟨limit, result, _hinitialized, hinvoked, hemitted⟩
    apply (hdriverSpec w b).mpr
    refine ⟨limit, result, ?_, ?_⟩
    · exact (hinvoker.right
        (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
        result).mp hinvoked
    · exact (hemitter.right
        (MachineDescription.DovetailControllerLayout.withResult
          (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
          result)
        b).mp hemitted
  · intro w b hhalt
    rcases (hdriverSpec w b).mp hhalt with
      ⟨limit, result, hattempt, hraw⟩
    refine ⟨limit, result, hinitializer.right w, ?_, ?_⟩
    · exact (hinvoker.right
        (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
        result).mpr hattempt
    · exact (hemitter.right
        (MachineDescription.DovetailControllerLayout.withResult
          (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
          result)
        b).mpr hraw

private theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerConstructionData_of_searchDriver
    (hsearch :
      PairedRecognizerDovetailFiniteStageLoopProtectedSequencerSearchDriverData) :
    forall attempt initializer invoker emitter continuer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes
        initializer ->
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker ->
      PairedRecognizerDovetailControllerResultEmitterRealizes
        emitter ->
      PairedRecognizerDovetailControllerContinueRealizes
        continuer ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes
          initializer invoker emitter continuer decider := by
  intro attempt initializer invoker emitter continuer
    hinitializer hinvoker hemitter hcontinuer
  rcases hsearch attempt with ⟨decider, hdriver⟩
  exact
    ⟨decider,
      pairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes_of_searchDriver
        hdriver hinitializer hinvoker hemitter hcontinuer⟩

private theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerConstructionData_finite_leaf :
    forall attempt initializer invoker emitter continuer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes
        initializer ->
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker ->
      PairedRecognizerDovetailControllerResultEmitterRealizes
        emitter ->
      PairedRecognizerDovetailControllerContinueRealizes
        continuer ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes
          initializer invoker emitter continuer decider := by
  apply
    pairedRecognizerDovetailFiniteStageLoopProtectedSequencerConstructionData_of_searchDriver
  intro attempt
  -- Remaining finite-table obligation: build the unbounded controller search
  -- driver for the protected stage-attempt machine.
  sorry

/--
Finite-machine leaf for sequencing initializer, protected invocation, result
emission, and continuation into the finite controller loop.
-/
theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData_scaffold :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData := by
  intro attempt initializer invoker emitter continuer
    hinitializer hinvoker hemitter hcontinuer
  rcases
      pairedRecognizerDovetailFiniteStageLoopProtectedSequencerConstructionData_finite_leaf
        attempt initializer invoker emitter continuer
        hinitializer hinvoker hemitter hcontinuer with
    ⟨decider, hwell, _hcontinue, hforward, hclosed⟩
  refine ⟨decider, hwell, ?_, ?_⟩
  · intro w b hsearch
    rcases hsearch with ⟨limit, result, hattempt, hraw⟩
    let C :=
      pairedRecognizerDovetailFiniteStageLoopStageLayout w limit
    apply hforward w b
    refine ⟨limit, result, hinitializer.right w, ?_, ?_⟩
    · exact (hinvoker.right C result).mpr hattempt
    · exact (hemitter.right
        (MachineDescription.DovetailControllerLayout.withResult C result)
        b).mpr (by
          simpa [C, MachineDescription.DovetailControllerLayout.withResult]
            using hraw)
  · intro w b hhalt
    rcases hclosed w b hhalt with
      ⟨limit, result, _hinitialized, hinvoked, hemitted⟩
    let C :=
      pairedRecognizerDovetailFiniteStageLoopStageLayout w limit
    refine ⟨limit, result, ?_, ?_⟩
    · exact (hinvoker.right C result).mp (by
        simpa [C] using hinvoked)
    · exact (hemitter.right
        (MachineDescription.DovetailControllerLayout.withResult C result)
        b).mp (by
          simpa [C] using hemitted)

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData :=
  pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_of_protected
    pairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData_scaffold

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstruction :=
  pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_of_data
    pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_scaffold

theorem pairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction :=
  pairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction_of_output
    pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold

theorem pairedRecognizerDovetailFiniteStageLoopControllerConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction :=
  pairedRecognizerDovetailFiniteStageLoopControllerConstruction_of_components
    pairedRecognizerDovetailControllerInputInitializerConstruction_scaffold
    pairedRecognizerDovetailControllerStageInputEncoderConstruction_scaffold
    pairedRecognizerDovetailStageAttemptInvocationConstruction_scaffold
    pairedRecognizerDovetailControllerResultEmitterConstruction_scaffold
    pairedRecognizerDovetailControllerContinueConstruction_scaffold
    pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold

end FiniteSourceScaffoldExports

end Computability
end FoC
