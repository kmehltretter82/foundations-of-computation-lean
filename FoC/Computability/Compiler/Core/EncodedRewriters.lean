import FoC.Computability.Compiler.Core.ControllerCloseout
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner
import FoC.Computability.Compiler.Core.EncodedRewriters.InitialLayout
import FoC.Computability.Compiler.Core.EncodedRewriters.TotalOutputEmitter

set_option doc.verso true

/-!
# Encoded rewriter contracts
-/

namespace FoC
namespace Computability

open Languages

/-!
**Milestone 2 parser/rewriter leaves.**  The remaining finite-source work is
not a generic compiler for arbitrary {name}`MachineDescription.TapeCodePrimitive`
values.  It is a fixed family of code-word parsers and rewriters for the
canonical encodings used by the dovetail controller.  The declarations below
name those finite transition-table obligations explicitly.  Each one is a
single concrete machine family over the existing encodings, and the older
scaffold names are derived from them rather than carrying anonymous broad
holes.
-/

def EncodedCodeWordCanonicalRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    recognizer.SubroutineReady ∧
      forall bits : Word Bool,
      forall code : Word MachineCodeSymbol,
        recognizer.HaltsWithOutput bits
            (MachineDescription.encodeCodeWordAsInput code) <->
          MachineDescription.decodeCodeWordAsInput bits = some code

theorem encodedCodeWordCanonicalRecognizerConstruction_scaffold :
    EncodedCodeWordCanonicalRecognizerConstruction := by
  refine
    ⟨MachineDescription.ExactIdentityDescription,
      ⟨MachineDescription.exactIdentityDescription_wellFormed,
        MachineDescription.exactIdentityDescription_haltTransitionFree⟩,
      ?_⟩
  intro bits code
  constructor
  · intro h
    have hbits :
        MachineDescription.encodeCodeWordAsInput code = bits :=
      (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        bits (MachineDescription.encodeCodeWordAsInput code)).mp h
    rw [← hbits]
    exact
      MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput code
  · intro h
    have hbits :
        bits = MachineDescription.encodeCodeWordAsInput code :=
      MachineDescription.decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput h
    rw [hbits]
    exact
      (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

def EncodedDovetailStageInputToInitialLayoutRewriterConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      initializer.SubroutineReady ∧
        forall code out : Word MachineCodeSymbol,
          initializer.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput out) <->
            (PairedRecognizerDovetailInitialLayoutCode
              accept reject).transform code = some out

def EncodedDovetailLayoutBoundedRunnerRewriterConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      runner.SubroutineReady ∧
        forall code out : Word MachineCodeSymbol,
          runner.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput out) <->
            (PairedRecognizerDovetailLayoutCode
              accept reject).transform code = some out

def EncodedDovetailTotalOutputEmitterRewriterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      PairedRecognizerDovetailTotalOutputCode emitter

def EncodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction

def EncodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction

def EncodedDovetailTotalOutputEmitterHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction

def EncodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction

def EncodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction

def EncodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction

/-!
**Encoded rewriter handoff.**  Several controller components are ordinary
code-word transducers: they consume a canonical encoded
{name}`MachineCodeSymbol` word and produce another one.  For those components,
an output-compiled subroutine already gives the exact encoded rewriter
interface, so the remaining leaves can target subroutine construction instead
of restating the encoded input/output behavior.
-/

def EncodedTapeCodePrimitiveRewriterConstruction
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  exists rewriter : MachineDescription,
    rewriter.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        rewriter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out

def EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  exists rewriter : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P rewriter

theorem encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine
    {P : MachineDescription.TapeCodePrimitive}
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
    {P : MachineDescription.TapeCodePrimitive}
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
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerInitialCode w))

def EncodedControllerStageInputProjectionRewriterConstruction :
    Prop :=
  exists encoder : MachineDescription,
    encoder.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        encoder.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
            code = some out

def EncodedControllerResultEmitterRewriterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    emitter.SubroutineReady ∧
      forall C : MachineDescription.DovetailControllerLayout,
      forall b : Bool,
        emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode C))
            [b] <->
          PairedRecognizerDovetailControllerRawOutput C.result = some [b]

def EncodedControllerContinueRewriterConstruction :
    Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      forall C : MachineDescription.DovetailControllerLayout,
        continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode C))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.nextStage C))) <->
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
      (hspec (MachineDescription.DovetailControllerLayout.encode C)
        (MachineDescription.DovetailControllerLayout.encode
          (MachineDescription.DovetailControllerLayout.nextStage C)))
      pairedRecognizerDovetailControllerResultContinueCode_encode_nextStage_iff

/-!
The first two stage-attempt components are routed through closed handoff
subroutines.  The total-output emitter is the final shrinking phase, so it only
uses the normalized output-compiled contract.
-/

theorem encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold :
    EncodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction := by
  intro accept reject
  exact
    EncodedRewriters.InitialLayout.closedHandoffCompiledSubroutine
      accept reject

theorem encodedDovetailStageInputToInitialLayoutRewriterConstruction_scaffold :
    EncodedDovetailStageInputToInitialLayoutRewriterConstruction := by
  intro accept reject
  rcases
      encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold
        accept reject with
    ⟨initializer, hinitializer⟩
  exact
    encodedTapeCodePrimitiveRewriterConstruction_of_closedHandoffCompiledSubroutine
      hinitializer

theorem encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold :
    EncodedDovetailLayoutBoundedRunnerRewriterConstruction := by
  intro accept reject
  rcases
      EncodedRewriters.BoundedLayoutRunner.outputCompiledSubroutine
        accept reject with
    ⟨runner, hrunner⟩
  exact
    encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine
      ⟨runner, hrunner⟩

/--
Closed-handoff bounded-runner construction.  This is the remaining
finite-machine leaf for the bounded layout runner; the nearby handoff theorem
below is only adapter glue over this target.
-/
theorem encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold :
    EncodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction := by
  sorry

theorem encodedDovetailTotalOutputEmitterRewriterConstruction_scaffold :
    EncodedDovetailTotalOutputEmitterRewriterConstruction := by
  exact EncodedRewriters.TotalOutputEmitter.outputRealizedSubroutine

theorem encodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction_scaffold :
    EncodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction :=
  pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_of_closedHandoff
    encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold

theorem encodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction_scaffold :
    EncodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_of_closedHandoff
    encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold

end Computability
end FoC
