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

def TapeCodePrimitiveOutputCompiledForwardSpec
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    P.transform code = some out ->
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)

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

def PairedRecognizerDovetailStageAttemptInvocationForwardConstructionData :
    Prop :=
  forall attempt encoder : MachineDescription,
    attempt.SubroutineReady ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    exists invoker : MachineDescription,
      invoker.SubroutineReady ∧
        PairedRecognizerDovetailStageAttemptInvocationForwardSpec
          attempt encoder invoker

def PairedRecognizerDovetailStageAttemptInvocationClosedConstructionData :
    Prop :=
  forall attempt encoder invoker : MachineDescription,
    attempt.SubroutineReady ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    invoker.SubroutineReady ->
    PairedRecognizerDovetailStageAttemptInvocationForwardSpec
      attempt encoder invoker ->
    PairedRecognizerDovetailStageAttemptInvocationClosedSpec
      attempt encoder invoker

theorem pairedRecognizerDovetailStageAttemptInvocationConstructionData_of_forward_closed
    (hforward :
      PairedRecognizerDovetailStageAttemptInvocationForwardConstructionData)
    (hclosed :
      PairedRecognizerDovetailStageAttemptInvocationClosedConstructionData) :
    PairedRecognizerDovetailStageAttemptInvocationConstructionData := by
  intro attempt encoder hattempt hencoder
  rcases hforward attempt encoder hattempt hencoder with
    ⟨invoker, hready, hforwardSpec⟩
  exact
    ⟨invoker, hready, hforwardSpec,
      hclosed attempt encoder invoker hattempt hencoder hready
        hforwardSpec⟩

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

theorem pairedRecognizerDovetailStageAttemptInvocationForwardConstructionData_scaffold :
    PairedRecognizerDovetailStageAttemptInvocationForwardConstructionData := by
  sorry

theorem pairedRecognizerDovetailStageAttemptInvocationClosedConstructionData_scaffold :
    PairedRecognizerDovetailStageAttemptInvocationClosedConstructionData := by
  sorry

theorem pairedRecognizerDovetailStageAttemptInvocationConstructionData_scaffold :
    PairedRecognizerDovetailStageAttemptInvocationConstructionData := by
  exact
    pairedRecognizerDovetailStageAttemptInvocationConstructionData_of_forward_closed
      pairedRecognizerDovetailStageAttemptInvocationForwardConstructionData_scaffold
      pairedRecognizerDovetailStageAttemptInvocationClosedConstructionData_scaffold

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

def PairedRecognizerDovetailFiniteStageLoopForwardConstructionData :
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
          attempt decider

def PairedRecognizerDovetailFiniteStageLoopClosedConstructionData :
    Prop :=
  forall attempt initializer encoder invoker emitter continuer decider :
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
    decider.WellFormed ->
    PairedRecognizerDovetailFiniteStageLoopForwardSpec
      attempt decider ->
    PairedRecognizerDovetailFiniteStageLoopClosedSpec
      attempt decider

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_of_forward_closed
    (hforward :
      PairedRecognizerDovetailFiniteStageLoopForwardConstructionData)
    (hclosed :
      PairedRecognizerDovetailFiniteStageLoopClosedConstructionData) :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData := by
  intro attempt initializer encoder invoker emitter continuer
    hattempt hinitializer hencoder hinvoker hemitter hcontinuer
  rcases hforward attempt initializer encoder invoker emitter continuer
      hattempt hinitializer hencoder hinvoker hemitter hcontinuer with
    ⟨decider, hwell, hforwardSpec⟩
  exact
    ⟨decider, hwell, hforwardSpec,
      hclosed attempt initializer encoder invoker emitter continuer decider
        hattempt hinitializer hencoder hinvoker hemitter hcontinuer hwell
        hforwardSpec⟩

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

theorem pairedRecognizerDovetailFiniteStageLoopForwardConstructionData_scaffold :
    PairedRecognizerDovetailFiniteStageLoopForwardConstructionData := by
  sorry

theorem pairedRecognizerDovetailFiniteStageLoopClosedConstructionData_scaffold :
    PairedRecognizerDovetailFiniteStageLoopClosedConstructionData := by
  sorry

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData := by
  exact
    pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_of_forward_closed
      pairedRecognizerDovetailFiniteStageLoopForwardConstructionData_scaffold
      pairedRecognizerDovetailFiniteStageLoopClosedConstructionData_scaffold

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
