import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.SimulatorScaffold.Padded.Emitter.Terminal

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

def FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 1
    , transition 1 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.right 2 ]

def FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindSourceTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells (bits.reverse.map some) []

def FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells [none]
    (List.append (bits.map some) [none])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_wellFormed_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner.transitions)
      (stateCount :=
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner.transitions)
      (by decide)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_haltTransitionFree_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner.transitions)
    (state :=
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner.halt)
    (by decide)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner.SubroutineReady :=
  ⟨fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_wellFormed_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_haltTransitionFree_configRunner⟩

private abbrev FDBSPaddedEmitterSourceRewind_configRunner :=
  FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_run_scan_configRunner
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    FDBSPaddedEmitterSourceRewind_configRunner.runConfig
        (leftBits.length + 1)
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftBits.map some)
              (some current :: rightCells) } =
      { state := 1
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells []
            (none ::
              List.append
                ((List.append leftBits.reverse [current]).map some)
                rightCells) } := by
  induction leftBits generalizing current rightCells with
  | nil =>
      cases current <;>
        simp [FDBSPaddedEmitterSourceRewind_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          FDBSPaddedEmitterSourceRewind_configRunner.runConfig 1
              { state := 1
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((next :: rest).map some)
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some)
                  (some next :: some current :: rightCells) } := by
        cases current <;>
          simp [FDBSPaddedEmitterSourceRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_step_finish_configRunner
    (bits : Word Bool) :
    FDBSPaddedEmitterSourceRewind_configRunner.runConfig 1
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (none :: List.append (bits.map some) [none]) } =
      { state := FDBSPaddedEmitterSourceRewind_configRunner.halt
        tape :=
          FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
            bits } := by
  cases bits with
  | nil =>
      simp [FDBSPaddedEmitterSourceRewind_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveRight, Tape.write]
  | cons bit rest =>
      cases bit <;>
        simp [FDBSPaddedEmitterSourceRewind_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveRight, Tape.write]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_run_from_leftStack_configRunner
    (leftStack : Word Bool) :
    FDBSPaddedEmitterSourceRewind_configRunner.runConfig
        (leftStack.length + 2)
        { state := FDBSPaddedEmitterSourceRewind_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftStack.map some) [] } =
      { state := FDBSPaddedEmitterSourceRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (leftStack.reverse.map some) [none]) } := by
  cases leftStack with
  | nil =>
      simp [FDBSPaddedEmitterSourceRewind_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstart :
          FDBSPaddedEmitterSourceRewind_configRunner.runConfig 1
              { state := FDBSPaddedEmitterSourceRewind_configRunner.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((current :: rest).map some) [] } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some) [some current, none] } := by
        cases current <;>
          simp [FDBSPaddedEmitterSourceRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [
        fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_run_scan_configRunner
          rest current [none]]
      simpa [
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
        List.map_append, List.append_assoc] using
        fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_step_finish_configRunner
          (List.append rest.reverse [current])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_run_configRunner
    (bits : Word Bool) :
    FDBSPaddedEmitterSourceRewind_configRunner.runConfig (bits.length + 2)
        { state := FDBSPaddedEmitterSourceRewind_configRunner.start
          tape :=
            FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindSourceTape_configRunner
              bits } =
      { state := FDBSPaddedEmitterSourceRewind_configRunner.halt
        tape :=
          FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
            bits } := by
  simpa [
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindSourceTape_configRunner,
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner] using
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_run_from_leftStack_configRunner
      bits.reverse

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_haltsFromTape_configRunner
    (bits : Word Bool) :
    FDBSPaddedEmitterSourceRewind_configRunner.HaltsFromTape
      (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindSourceTape_configRunner
        bits)
      (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        bits) := by
  refine ⟨bits.length + 2, ?_⟩
  constructor
  · rw [
      fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_run_configRunner]
  · rw [
      fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_run_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewind_halts_terminal_configRunner
    (L : SimulatorLayout) :
    FDBSPaddedEmitterSourceRewind_configRunner.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells
        ((SimulatorLayout.asBoolInput L).reverse.map some) [])
      (DovetailInitialLayoutInitializer.tapeAtCells [none]
        (List.append ((SimulatorLayout.asBoolInput L).map some) [none])) := by
  simpa [
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindSourceTape_configRunner,
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner] using
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_haltsFromTape_configRunner
      (SimulatorLayout.asBoolInput L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_move_left_move_right_cons_cons_configRunner
    (first second : Bool) (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
            (first :: second :: rest))) =
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        (first :: second :: rest) := by
  cases first <;> cases second <;>
    simp [
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_move_left_move_right_simulator_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
            (SimulatorLayout.asBoolInput L))) =
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        (SimulatorLayout.asBoolInput L) := by
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
            fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_move_left_move_right_cons_cons_configRunner
              first second tail

/--
Post-scanner run-loop contract for the padded fixed-description simulator
emitter.

The scanner has already validated and restored the source simulator layout and
the head is at the terminal blank just to the right of the restored word.  The
finite-machine obligation is to run the fixed description for the encoded stage
bound, compute the accumulated hit bit including stage zero, and emit the exact
scratch-padded output tape.
-/
def FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopSpec_configRunner
    (D runLoop : MachineDescription) : Prop :=
  runLoop.SubroutineReady ∧
    forall L : SimulatorLayout,
      runLoop.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells
          ((SimulatorLayout.asBoolInput L).reverse.map some) [])
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists runLoop : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopSpec_configRunner
        D runLoop

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindSpec_configRunner
    (D postRewind : MachineDescription) : Prop :=
  postRewind.SubroutineReady ∧
    forall L : SimulatorLayout,
      postRewind.HaltsFromTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          (SimulatorLayout.asBoolInput L))
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists postRewind : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindSpec_configRunner
        D postRewind

def FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.right
    (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
      bits)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterReturnToRightShiftedInput_haltsFrom_sourceRewindTarget_cons_cons_configRunner
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

theorem fixedDescriptionBoundedSimulatorPaddedEmitterReturnToRightShiftedInput_haltsFrom_sourceRewindTarget_configRunner
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
            fixedDescriptionBoundedSimulatorPaddedEmitterReturnToRightShiftedInput_haltsFrom_sourceRewindTarget_cons_cons_configRunner
              first second tail

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_move_left_move_right_cons_cons_configRunner
    (first second : Bool) (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
            (first :: second :: rest))) =
      FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (first :: second :: rest) := by
  cases first <;> cases second <;> cases rest <;>
    simp [
      FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner,
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_move_left_move_right_simulator_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
            (SimulatorLayout.asBoolInput L))) =
      FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L) := by
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
            fixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_move_left_move_right_cons_cons_configRunner
              first second tail

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterRightShiftedInputSpec_configRunner
    (D afterRight : MachineDescription) : Prop :=
  afterRight.SubroutineReady ∧
    forall L : SimulatorLayout,
      afterRight.HaltsFromTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
          (SimulatorLayout.asBoolInput L))
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterRightShiftedInputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists afterRight : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterRightShiftedInputSpec_configRunner
        D afterRight

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindFromAfterRightShiftedInput_configRunner
    (afterRight : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
    afterRight

theorem fixedDescriptionBoundedSimulatorPaddedEmitterPostRewindSpec_of_afterRightShiftedInput_configRunner
    {D afterRight : MachineDescription}
    (hafterRight :
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterRightShiftedInputSpec_configRunner
        D afterRight) :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindSpec_configRunner
      D
      (FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindFromAfterRightShiftedInput_configRunner
        afterRight) := by
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
        (fixedDescriptionBoundedSimulatorPaddedEmitterReturnToRightShiftedInput_haltsFrom_sourceRewindTarget_configRunner
          L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_move_left_move_right_simulator_configRunner
          L)
        (hafterRight.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterPostRewindConstruction_of_afterRightShiftedInput_configRunner
    (hafterRight :
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterRightShiftedInputConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindConstruction_configRunner := by
  intro D
  rcases hafterRight D with ⟨afterRight, hafterRightD⟩
  exact
    ⟨FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindFromAfterRightShiftedInput_configRunner
      afterRight,
      fixedDescriptionBoundedSimulatorPaddedEmitterPostRewindSpec_of_afterRightShiftedInput_configRunner
        hafterRightD⟩

/--
Remaining hard finite-machine leaf for the padded simulator emitter.

At this point the validated simulator-layout source has been rewound and the
head is in the right-shifted handoff position.  The leaf must decode the source
fields, run the fixed description for the encoded stage count while accounting
for the stage-zero hit check, and emit the exact scratch-padded output tape.
-/
theorem fixedDescriptionBoundedSimulatorPaddedEmitterAfterRightShiftedInputConstruction_finiteMachine_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterAfterRightShiftedInputConstruction_configRunner := by
  intro D
  sorry

def FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopFromPostRewind_configRunner
    (postRewind : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_configRunner
    postRewind

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRunLoopSpec_of_postRewind_configRunner
    {D postRewind : MachineDescription}
    (hpostRewind :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindSpec_configRunner
        D postRewind) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopSpec_configRunner
      D
      (FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopFromPostRewind_configRunner
        postRewind) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_subroutineReady_configRunner
        hpostRewind.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindDescription_subroutineReady_configRunner
        hpostRewind.left
        (fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewind_halts_terminal_configRunner
          L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_move_left_move_right_simulator_configRunner
          L)
        (hpostRewind.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRunLoopConstruction_of_postRewind_configRunner
    (hpostRewind :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopConstruction_configRunner := by
  intro D
  rcases hpostRewind D with ⟨postRewind, hpostRewindD⟩
  exact
    ⟨FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopFromPostRewind_configRunner
      postRewind,
      fixedDescriptionBoundedSimulatorPaddedEmitterRunLoopSpec_of_postRewind_configRunner
        hpostRewindD⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterPostRewindConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRewindConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterPostRewindConstruction_of_afterRightShiftedInput_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterAfterRightShiftedInputConstruction_finiteMachine_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRunLoopConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterRunLoopConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterRunLoopConstruction_of_postRewind_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterPostRewindConstruction_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
