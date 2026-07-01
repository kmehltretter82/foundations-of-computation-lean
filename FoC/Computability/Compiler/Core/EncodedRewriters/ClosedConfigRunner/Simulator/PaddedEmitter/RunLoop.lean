import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.RunLoop.SourceShape

set_option doc.verso true

/-!
# Padded simulator scaffold emitter run loop
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner

open CommonGround.SeqComposition

namespace FixedDescriptionBoundedSimulator
namespace PaddedEmitter

namespace RunLoop

/--
Post-scanner run-loop contract for the padded fixed-description simulator
emitter.

The scanner has already validated and restored the source simulator layout and
the head is at the terminal blank just to the right of the restored word.  The
finite-machine obligation is to run the fixed description for the encoded stage
bound, compute the accumulated hit bit including stage zero, and emit the exact
scratch-padded output tape.
-/
def Spec
    (D runLoop : MachineDescription) : Prop :=
  runLoop.SubroutineReady ∧
    forall L : SimulatorLayout,
      runLoop.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells
          ((SimulatorLayout.asBoolInput L).reverse.map some) [])
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def Construction : Prop :=
  forall D : MachineDescription,
    exists runLoop : MachineDescription,
      Spec D runLoop

end RunLoop

namespace PostRewind

def Spec
    (D postRewind : MachineDescription) : Prop :=
  postRewind.SubroutineReady ∧
    forall L : SimulatorLayout,
      postRewind.HaltsFromTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          (SimulatorLayout.asBoolInput L))
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def Construction : Prop :=
  forall D : MachineDescription,
    exists postRewind : MachineDescription,
      Spec D postRewind

end PostRewind

namespace ReturnToRightShiftedInput

theorem haltsFrom_sourceRewindTarget_cons_cons_configRunner
    (first second : Bool) (rest : Word Bool) :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltsFromTape
      (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        (first :: second :: rest))
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (first :: second :: rest)) := by
  refine ⟨3, ?_⟩
  constructor
  · cases first <;> cases second <;>
      simp [
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches,
        keepMove, transition, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, Tape.moveRight]
  · cases first <;> cases second <;>
      simp [
        FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches,
        keepMove, transition, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, Tape.moveRight]

theorem haltsFrom_sourceRewindTarget_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltsFromTape
      (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        (SimulatorLayout.asBoolInput L))
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L)) := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [hbits] at hlen
      | cons second tail =>
          simpa [hbits] using
            haltsFrom_sourceRewindTarget_cons_cons_configRunner
              first second tail

end ReturnToRightShiftedInput

namespace PostRewind

def fromAfterRightShiftedInput
    (afterRight : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
    afterRight

theorem spec_of_afterRightShiftedInput
    {D afterRight : MachineDescription}
    (hafterRight :
      AfterRightShiftedInput.Spec D afterRight) :
    Spec D (fromAfterRightShiftedInput afterRight) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hafterRight.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hafterRight.left
        (ReturnToRightShiftedInput.haltsFrom_sourceRewindTarget_configRunner
          L)
        (RightShiftedSourceTape.move_left_move_right_simulator_configRunner
          L)
        (hafterRight.right L)

theorem construction_of_afterRightShiftedInput
    (hafterRight :
      AfterRightShiftedInput.Construction) :
    Construction := by
  intro D
  rcases hafterRight D with ⟨afterRight, hafterRightD⟩
  exact
    ⟨fromAfterRightShiftedInput afterRight,
      spec_of_afterRightShiftedInput hafterRightD⟩

end PostRewind

namespace AfterRightShiftedInput

/--
Run-loop entry point for the after-right-shifted padded emitter leaf.

The transition-table obligation itself lives in
{name}`finiteMachineCore`, which is upstream of this sequencing module and
therefore does not depend on the terminal/emitter scaffolds that consume this
theorem.
-/
theorem finiteMachine : Construction := by
  exact finiteMachineCore

end AfterRightShiftedInput

namespace PostRewind

theorem construction : Construction :=
  construction_of_afterRightShiftedInput
    AfterRightShiftedInput.finiteMachine

end PostRewind

namespace RunLoop

def fromPostRewind
    (postRewind : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner
    postRewind

theorem spec_of_postRewind
    {D postRewind : MachineDescription}
    (hpostRewind :
      PostRewind.Spec D postRewind) :
    Spec D (fromPostRewind postRewind) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_subroutineReady_configRunner
        hpostRewind.left
  · intro L
    have hrewindRun :
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.HaltsFromTape
          (DovetailInitialLayoutInitializer.tapeAtCells
            ((SimulatorLayout.asBoolInput L).reverse.map some) [])
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
            L) := by
      simpa [fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner]
        using
          fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltsFromTape_configRunner
            false L
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
                L)) =
          FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
            (SimulatorLayout.asBoolInput L) := by
      rw [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L]
      rfl
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_subroutineReady_configRunner
        hpostRewind.left
        hrewindRun
        hbridge
        (hpostRewind.right L)

theorem construction_of_postRewind
    (hpostRewind :
      PostRewind.Construction) :
    Construction := by
  intro D
  rcases hpostRewind D with ⟨postRewind, hpostRewindD⟩
  exact
    ⟨fromPostRewind postRewind,
      spec_of_postRewind hpostRewindD⟩

theorem construction : Construction :=
  construction_of_postRewind PostRewind.construction

end RunLoop

end PaddedEmitter
end FixedDescriptionBoundedSimulator

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
