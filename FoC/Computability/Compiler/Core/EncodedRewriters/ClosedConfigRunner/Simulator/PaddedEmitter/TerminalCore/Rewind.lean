import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Core

set_option doc.verso true

/-!
# Padded simulator terminal rewind

This module isolates the concrete finite-machine construction that rewinds a
terminal padded-emitter tape back to the normalized terminal source tape.  The
broader terminal contracts compose this rewind with the remaining field/FST and
scratch emitters.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindSpec_configRunner
    (rewind : MachineDescription) : Prop :=
  rewind.SubroutineReady ∧
    forall explicitLeftBlank : Bool,
    forall L : SimulatorLayout,
      rewind.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
          explicitLeftBlank L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner :
    Prop :=
  exists rewind : MachineDescription,
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindSpec_configRunner
      rewind

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner :
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

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_wellFormed_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.transitions)
      (stateCount :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.transitions)
      (by decide)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltTransitionFree_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.transitions)
    (state :=
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.halt)
    (by decide)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.SubroutineReady :=
  ⟨fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_wellFormed_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltTransitionFree_configRunner⟩

private abbrev FDBSPaddedEmitterTerminalRewind_configRunner :=
  FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_scan_configRunner
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig
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
        simp [FDBSPaddedEmitterTerminalRewind_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
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
          simp [FDBSPaddedEmitterTerminalRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_scan_explicitBlank_configRunner
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig
        (leftBits.length + 1)
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (leftBits.map some) [none])
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
        simp [FDBSPaddedEmitterTerminalRewind_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
              { state := 1
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: rightCells) } := by
        cases current <;>
          simp [FDBSPaddedEmitterTerminalRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_step_finish_configRunner
    (bits : Word Bool) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (none :: List.append (bits.map some) [none]) } =
      { state := FDBSPaddedEmitterTerminalRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (bits.map some) [none]) } := by
  cases bits with
  | nil =>
      simp [FDBSPaddedEmitterTerminalRewind_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveRight, Tape.write]
  | cons bit rest =>
      cases bit <;>
        simp [FDBSPaddedEmitterTerminalRewind_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveRight, Tape.write]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_from_leftStack_configRunner
    (leftStack : Word Bool) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig
        (leftStack.length + 2)
        { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftStack.map some) [] } =
      { state := FDBSPaddedEmitterTerminalRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (leftStack.reverse.map some) [none]) } := by
  cases leftStack with
  | nil =>
      simp [FDBSPaddedEmitterTerminalRewind_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
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
          FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
              { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((current :: rest).map some) [] } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some)
                  (some current :: none :: []) } := by
        cases current <;>
          simp [FDBSPaddedEmitterTerminalRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_scan_configRunner
          rest current [none]]
      simpa [List.map_append, List.append_assoc] using
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_step_finish_configRunner
          (List.append rest.reverse [current])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_from_leftStack_explicitBlank_configRunner
    (leftStack : Word Bool) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig
        (leftStack.length + 2)
        { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (leftStack.map some) [none]) [] } =
      { state := FDBSPaddedEmitterTerminalRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (leftStack.reverse.map some) [none]) } := by
  cases leftStack with
  | nil =>
      simp [FDBSPaddedEmitterTerminalRewind_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
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
          FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
              { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (List.append ((current :: rest).map some) [none]) [] } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (List.append (rest.map some) [none])
                  (some current :: none :: []) } := by
        cases current <;>
          simp [FDBSPaddedEmitterTerminalRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_scan_explicitBlank_configRunner
          rest current [none]]
      simpa [List.map_append, List.append_assoc] using
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_step_finish_configRunner
          (List.append rest.reverse [current])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_configRunner
    (explicitLeftBlank : Bool) (bits : Word Bool) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig (bits.length + 2)
        { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (bits.reverse.map some)
                (if explicitLeftBlank then [none] else [])) [] } =
      { state := FDBSPaddedEmitterTerminalRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (bits.map some) [none]) } := by
  cases explicitLeftBlank
  · simpa [List.append_nil] using
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_from_leftStack_configRunner
        bits.reverse
  · simpa [List.map_append] using
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_from_leftStack_explicitBlank_configRunner
        bits.reverse

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltsFromTape_configRunner
    (explicitLeftBlank : Bool) (L : SimulatorLayout) :
    FDBSPaddedEmitterTerminalRewind_configRunner.HaltsFromTape
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
        explicitLeftBlank L)
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L) := by
  refine ⟨(SimulatorLayout.asBoolInput L).length + 2, ?_⟩
  constructor
  · simpa [
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner] using
      congrArg Configuration.state
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_configRunner
          explicitLeftBlank (SimulatorLayout.asBoolInput L))
  · simpa [
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner] using
      congrArg Configuration.tape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_configRunner
          explicitLeftBlank (SimulatorLayout.asBoolInput L))

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner :=
  ⟨FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_subroutineReady_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltsFromTape_configRunner⟩

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
