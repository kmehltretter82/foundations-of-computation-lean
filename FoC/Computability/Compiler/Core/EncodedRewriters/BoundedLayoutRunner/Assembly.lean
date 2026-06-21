import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Emitter

set_option doc.verso true

/-!
# Bounded-layout runner assembly

The assembly leaf sequences the parser, configuration runner, and emitter
phases into the public
{name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.Spec)}`Spec`
for
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

theorem exactIdentityDescription_subroutineReady :
    MachineDescription.ExactIdentityDescription.SubroutineReady :=
  ⟨MachineDescription.exactIdentityDescription_wellFormed,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem exactIdentityDescription_reaches
    (T : Tape Bool) :
    exists n : Nat,
      MachineDescription.ExactIdentityDescription.runConfig n
          { state := MachineDescription.ExactIdentityDescription.start
            tape := T } =
        { state := MachineDescription.ExactIdentityDescription.halt
          tape := T } :=
  ⟨0, rfl⟩

theorem exactIdentityDescription_runConfig_from_start
    (n : Nat) (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.runConfig n
        { state := MachineDescription.ExactIdentityDescription.start
          tape := T } =
      { state := MachineDescription.ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [MachineDescription.ExactIdentityDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition]

theorem parsedLayoutTape_move_left_move_right
    (L : MachineDescription.DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right (ParsedLayoutTape L)) =
      ParsedLayoutTape L := by
  rcases EncodedRewriters.dovetailLayout_encode_cons L with
    ⟨tail, htail⟩
  unfold ParsedLayoutTape ParsedLayoutBits
  rw [htail]
  exact
    EncodedRewriters.tape_move_left_move_right_input_encodeCodeWordAsInput_cons
      MachineCodeSymbol.transition tail

theorem configRunnerOutputTape_move_left_move_right
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (ConfigRunnerOutputTape accept reject L)) =
      ConfigRunnerOutputTape accept reject L := by
  exact
    parsedLayoutTape_move_left_move_right
      (BoundedRunLayout accept reject L)

def PhaseAssemblyConstruction : Prop :=
  forall accept reject : MachineDescription,
    LayoutCheckedParserConstruction ->
      (exists configRunner : MachineDescription,
        AcceptRejectConfigRunnerSpec accept reject configRunner) ->
        (exists emitter : MachineDescription,
          OutputEmitterSpec accept reject emitter) ->
          exists runner : MachineDescription,
            Spec accept reject runner

theorem phaseAssemblyConstruction_scaffold :
    PhaseAssemblyConstruction := by
  sorry

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  intro accept reject
  exact
    phaseAssemblyConstruction_scaffold
      accept reject
      layoutCheckedParserConstruction_scaffold
      (acceptRejectConfigRunnerConstruction_scaffold accept reject)
      (outputEmitterConstruction_scaffold accept reject)

theorem rightShiftedOutputCompiledConstruction_scaffold :
    RightShiftedOutputCompiledConstruction := by
  intro accept reject
  rcases finiteDescriptionConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  exact
    ⟨runner,
      rightShiftedOutputCompiled_of_spec hrunner⟩

theorem closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists runner : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove := by
  rcases finiteDescriptionConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    closedHandoffCompiledSubroutineByDescription_of_spec hrunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
