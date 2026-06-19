import FoC.Computability.Compiler.Core.ControllerResultEmitter

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

/-!
**Controller encoded leaves.**  These are the finite transition-table
obligations that are specific to the controller loop rather than to the
dovetail layout subroutines.  The projection and result-emitter machines are
already available from their concrete descriptions; the initializer and
continue-result code-word subroutine remain as concrete leaves.
-/

section EncodedControllerLeaves

theorem encodedControllerInputInitializerRewriterConstruction_scaffold :
    EncodedControllerInputInitializerRewriterConstruction := by
  sorry

theorem encodedControllerStageInputProjectionRewriterConstruction_scaffold :
    EncodedControllerStageInputProjectionRewriterConstruction :=
  encodedControllerStageInputProjectionRewriterConstruction_of_codeWordSubroutine
    ControllerStageInputProjection.encodedControllerStageInputProjectionCodeWordSubroutineConstruction_scaffold

theorem encodedControllerResultEmitterRewriterConstruction_scaffold :
    EncodedControllerResultEmitterRewriterConstruction :=
  encodedControllerResultEmitterRewriterConstruction_of_description

theorem encodedControllerResultContinueCodeWordSubroutineConstruction_scaffold :
    EncodedControllerResultContinueCodeWordSubroutineConstruction := by
  sorry

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

theorem pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailTotalOutputEmitterRewriterConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction :=
  encodedTapeCodePrimitiveOutputCompiledSubroutineConstruction_of_rewriter
    (P := PairedRecognizerDovetailTotalOutputCode) h

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

theorem pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction :=
  pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_of_closedHandoff
    (pairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
      encodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction_scaffold)

theorem pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailTotalOutputEmitterHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold

theorem pairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction :=
  pairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction_scaffold

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

theorem pairedRecognizerDovetailStageAttemptInvocationConstruction_scaffold :
    PairedRecognizerDovetailStageAttemptInvocationConstruction := by
  sorry

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

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstruction := by
  sorry

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
