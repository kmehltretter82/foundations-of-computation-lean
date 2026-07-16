import FoC.Computability.Compiler.Core.ControllerCloseout
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts
import FoC.Computability.Compiler.Core.EncRewriters.BoundedLayoutRunner
import FoC.Computability.Compiler.Core.EncRewriters.InitialLayout
import FoC.Computability.Compiler.Core.EncRewriters.TotalOutputEmitter

set_option doc.verso true

/-!
# Encoded rewriter contracts
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
**Canonical parser and rewriter families.**  The finite-source layer uses a
fixed family of code-word parsers and rewriters for the canonical encodings of
the dovetail controller, rather than a generic compiler for arbitrary
{name}`TapeCodePrimitive` values.  The declarations below state the concrete
finite transition-table contracts for those machine families.
-/

def EncodedCodeWordCanonicalRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    recognizer.SubroutineReady ∧
      forall bits : Word Bool,
      forall code : Word MachineCodeSymbol,
        recognizer.HaltsWithOutput bits
            (encodeCodeWordAsInput code) <->
          decodeCodeWordAsInput bits = some code

theorem encodedCodeWordCanonicalRecognizerConstruction_scaffold :
    EncodedCodeWordCanonicalRecognizerConstruction := by
  refine
    ⟨ExactIdentityDescription,
      ⟨exactIdentityDescription_wellFormed,
        exactIdentityDescription_haltTransitionFree⟩,
      ?_⟩
  intro bits code
  constructor
  · intro h
    have hbits :
        encodeCodeWordAsInput code = bits :=
      (exactIdentityDescription_haltsWithOutput_iff
        bits (encodeCodeWordAsInput code)).mp h
    rw [← hbits]
    exact
      decodeCodeWordAsInput_encodeCodeWordAsInput code
  · intro h
    have hbits :
        bits = encodeCodeWordAsInput code :=
      decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput h
    rw [hbits]
    exact
      (exactIdentityDescription_haltsWithOutput_iff
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput code)).mpr rfl

def EncodedDovetailStageInputToInitialLayoutRewriterConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      initializer.SubroutineReady ∧
        forall code out : Word MachineCodeSymbol,
          initializer.HaltsWithOutput
              (encodeCodeWordAsInput code)
              (encodeCodeWordAsInput out) <->
            (PairedRecognizerDovetailInitialLayoutCode
              accept reject).transform code = some out

def EncodedDovetailLayoutBoundedRunnerRewriterConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      runner.SubroutineReady ∧
        forall code out : Word MachineCodeSymbol,
          runner.HaltsWithOutput
              (encodeCodeWordAsInput code)
              (encodeCodeWordAsInput out) <->
            (PairedRecognizerDovetailLayoutCode
              accept reject).transform code = some out

/-!
**Encoded rewriter handoff.**  Several controller components are ordinary
code-word transducers: they consume a canonical encoded
{name}`MachineCodeSymbol` word and produce another one.  For those components,
an output-compiled subroutine already gives the exact encoded rewriter
interface.  The construction bridges reuse that interface instead of restating
the encoded input/output behavior.
-/

def EncodedTapeCodePrimitiveRewriterConstruction
    (P : TapeCodePrimitive) : Prop :=
  exists rewriter : MachineDescription,
    rewriter.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        rewriter.HaltsWithOutput
            (encodeCodeWordAsInput code)
            (encodeCodeWordAsInput out) <->
          P.transform code = some out

def EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction
    (P : TapeCodePrimitive) : Prop :=
  exists rewriter : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P rewriter

theorem encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine
    {P : TapeCodePrimitive}
    (h : EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction P) :
    EncodedTapeCodePrimitiveRewriterConstruction P := by
  rcases h with ⟨rewriter, hrewriter⟩
  exact
    ⟨rewriter,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
        hrewriter,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_iff
        hrewriter⟩

theorem encodedTapeCodePrimitiveRewriterConstruction_of_closedHandoffCompiledSubroutine
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    EncodedTapeCodePrimitiveRewriterConstruction P :=
  ⟨D,
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady h,
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithOutput_iff
      h⟩

def EncodedControllerInputInitializerRewriterConstruction :
    Prop :=
  exists initializer : MachineDescription,
    initializer.SubroutineReady ∧
      forall w : Word Bool,
        initializer.HaltsWithOutput w
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerInitialCode w))

def EncodedControllerStageInputProjectionRewriterConstruction :
    Prop :=
  exists encoder : MachineDescription,
    encoder.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        encoder.HaltsWithOutput
            (encodeCodeWordAsInput code)
            (encodeCodeWordAsInput out) <->
          PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
            code = some out

def EncodedControllerResultEmitterRewriterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    emitter.SubroutineReady ∧
      forall C : DovetailControllerLayout,
      forall b : Bool,
        emitter.HaltsWithOutput
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode C))
            [b] <->
          PairedRecognizerDovetailControllerRawOutput C.result = some [b]

def EncodedControllerContinueRewriterConstruction :
    Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      forall C : DovetailControllerLayout,
        continuer.HaltsWithOutput
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode C))
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                (DovetailControllerLayout.nextStage C))) <->
          PairedRecognizerDovetailControllerRawOutput C.result = none

def EncodedControllerStageInputProjectionCodeWordSubroutineConstruction :
    Prop :=
  EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction
    PairedRecognizerDovetailControllerStageInputCodePrimitive

def EncodedControllerResultContinueCodeWordSubroutineConstruction :
    Prop :=
  EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction
    PairedRecognizerDovetailControllerResultContinueCode

theorem encodedControllerStageInputProjectionRewriterConstruction_of_codeWordSubroutine
    (h :
      EncodedControllerStageInputProjectionCodeWordSubroutineConstruction) :
    EncodedControllerStageInputProjectionRewriterConstruction :=
  encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine h

theorem encodedControllerContinueRewriterConstruction_of_resultContinueCodeWordSubroutine
    (h : EncodedControllerResultContinueCodeWordSubroutineConstruction) :
    EncodedControllerContinueRewriterConstruction := by
  rcases
      encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine h with
    ⟨continuer, hready, hspec⟩
  refine ⟨continuer, hready, ?_⟩
  intro C
  exact
    Iff.trans
      (hspec (DovetailControllerLayout.encode C)
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.nextStage C)))
      pairedRecognizerDovetailControllerResultContinueCode_encode_nextStage_iff

/-!
The stage-input initializer still has an exact closed-handoff contract.  The
bounded-layout runner intentionally uses the normalized output-compiled
contract: its padded/equivalence machine may shrink the physical tape window,
so an exact closed-handoff target would over-constrain the implementation.  The
total-output emitter is also a normalized output component.
-/

theorem pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction := by
  intro accept reject
  exact
    EncRewriters.InitialLayout.closedHandoffCompiledSubroutine
      accept reject

theorem encodedDovetailStageInputToInitialLayoutRewriterConstruction_scaffold :
    EncodedDovetailStageInputToInitialLayoutRewriterConstruction := by
  intro accept reject
  rcases
      pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_scaffold
        accept reject with
    ⟨initializer, hinitializer⟩
  exact
    encodedTapeCodePrimitiveRewriterConstruction_of_closedHandoffCompiledSubroutine
      hinitializer

theorem encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold_of_finiteDescription
    (hfinite :
      EncRewriters.BoundedLayoutRunner.FiniteDescriptionConstruction) :
    EncodedDovetailLayoutBoundedRunnerRewriterConstruction := by
  intro accept reject
  rcases
      EncRewriters.BoundedLayoutRunner.outputCompiledSubroutine_of_finiteDescriptionConstruction
        hfinite
        accept reject with
    ⟨runner, hrunner⟩
  exact
    encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine
      ⟨runner, hrunner⟩

theorem encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold_of_selectedProjection
    (hprojection :
      EncRewriters.BoundedLayoutRunner.SelectedProjectionFiniteDescriptionConstruction) :
    EncodedDovetailLayoutBoundedRunnerRewriterConstruction :=
  encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold_of_finiteDescription
    (EncRewriters.BoundedLayoutRunner.finiteDescriptionConstruction_scaffold_of_selectedProjection
      hprojection)

theorem encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      EncRewriters.BoundedLayoutRunner.SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    EncodedDovetailLayoutBoundedRunnerRewriterConstruction :=
  encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold_of_finiteDescription
    (EncRewriters.BoundedLayoutRunner.finiteDescriptionConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      EncRewriters.BoundedLayoutRunner.SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      EncRewriters.BoundedLayoutRunner.SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    EncodedDovetailLayoutBoundedRunnerRewriterConstruction :=
  encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold_of_finiteDescription
    (EncRewriters.BoundedLayoutRunner.finiteDescriptionConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold :
    EncodedDovetailLayoutBoundedRunnerRewriterConstruction :=
  encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold_of_finiteDescription
    EncRewriters.BoundedLayoutRunner.finiteDescriptionConstruction_scaffold

end Computability
end FoC
