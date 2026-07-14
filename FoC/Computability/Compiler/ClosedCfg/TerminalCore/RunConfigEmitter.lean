import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Specs
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.TerminalAdapter

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

/-!
# Terminal run-config field emitter

This module connects the restored terminal source to the checked run-config
pipeline while keeping its output in the honest tape-equivalence currency.
The retired exact scratch/FST facade is intentionally absent: downstream
consumers observe the normalized output word, not a canonical blank-window
representative.
-/

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
    (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.left
    (DovetailInitialLayoutInitializer.tapeAtCells
      (List.append ((SimulatorLayout.asBoolInput L).reverse.map some)
        [none]) [none])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_eq_pipelineSource_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
        L =
      RunConfigEmitterCore.InputMaterializer.rightEndLeftSourceTape
        (SimulatorLayout.asBoolInput L) := by
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_move_left_move_right_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
            L)) =
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
        L := by
  exact
    Tape.move_left_move_right_eq_self_of_right_cons
      (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
        L)
      (cell := none) (right := [])
      (by
        unfold FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
        cases hleft : (SimulatorLayout.asBoolInput L).reverse.map some <;>
          simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.move,
            Tape.moveLeft])

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftSpec_configRunner
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall L : SimulatorLayout,
      scanner.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L)

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_configRunner :
    Prop :=
  exists scanner : MachineDescription,
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftSpec_configRunner
      scanner

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0 ]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_wellFormed_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.transitions)
      (stateCount :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.transitions)
      (by decide)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_haltTransitionFree_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.transitions)
    (state :=
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.halt)
    (by decide)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.SubroutineReady :=
  ⟨fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_wellFormed_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_haltTransitionFree_configRunner⟩

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftHaltTape_configRunner
    (leftRev : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (DovetailInitialLayoutInitializer.tapeAtCells
      (List.append (bits.reverse.map some) leftRev) [none])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_run_configRunner
    (leftRev : List (Option Bool)) (bits : Word Bool) :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.runConfig
        (bits.length + 1)
        { state :=
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev
              (List.append (bits.map some) [none]) } =
      { state :=
          FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.halt
        tape :=
          fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftHaltTape_configRunner
            leftRev bits } := by
  induction bits generalizing leftRev with
  | nil =>
      simp [
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner,
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftHaltTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.runConfig
              1
              { state :=
                  FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells leftRev
                    (List.append ((bit :: rest).map some) [none]) } =
            { state :=
                FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.start
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (some bit :: leftRev)
                  (List.append (rest.map some) [none]) } := by
        cases bit <;>
          cases rest <;>
          simp [
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftHaltTape_configRunner,
        List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: leftRev)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftHaltTape_eq_configRunner
    (L : SimulatorLayout) :
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftHaltTape_configRunner
        [none] (SimulatorLayout.asBoolInput L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
        L := by
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_haltsFromTape_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner.HaltsFromTape
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L)
      (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
        L) := by
  refine ⟨(SimulatorLayout.asBoolInput L).length + 1, ?_⟩
  have hrun :=
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_run_configRunner
      [none] (SimulatorLayout.asBoolInput L)
  constructor
  · simpa [
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftHaltTape_eq_configRunner]
      using congrArg Configuration.state hrun
  · simpa [
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftHaltTape_eq_configRunner]
      using congrArg Configuration.tape hrun

/-- Scan the restored terminal source to the last bit before its terminal blank. -/
theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_configRunner :=
  ⟨FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_subroutineReady_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftDescription_haltsFromTape_configRunner⟩

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_configRunner
    (D postScan : MachineDescription) : Prop :=
  postScan.SubroutineReady ∧
    forall L : SimulatorLayout,
      postScan.HaltsFromTapeEquiv
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists postScan : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_configRunner
        D postScan

theorem fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivConstruction_of_fullPipeline_configRunner
    (hfull : RunConfigEmitterCore.FullPipeline.Construction) :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivConstruction_configRunner := by
  intro D
  rcases
      (RunConfigEmitterCore.FullPipeline.terminalConstruction_of_fullPipeline
        hfull) D with
    ⟨postScan, hpostScan⟩
  refine ⟨postScan, hpostScan.left, ?_⟩
  intro L
  simpa only [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_eq_pipelineSource_configRunner]
    using hpostScan.right L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_of_rightEndLeft_configRunner
    (hscan :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_configRunner)
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_configRunner := by
  rcases hscan with ⟨scanner, hscanner⟩
  intro D
  rcases hpost D with ⟨postScan, hpostScan⟩
  refine ⟨SeqViaCanonical scanner postScan, ?_⟩
  constructor
  · exact SeqViaCanonical_subroutineReady hscanner.left hpostScan.left
  intro L
  apply SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
  · exact hscanner.left
  · exact hpostScan.left
  · exact (hscanner.right L).toEquiv
  · simpa only [
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_move_left_move_right_configRunner]
      using
        Tape.Equiv.refl
          (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
            L)
  · exact hpostScan.right L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_of_fullPipeline_configRunner
    (hfull : RunConfigEmitterCore.FullPipeline.Construction) :
    FixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_of_rightEndLeft_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_core_configRunner
    (fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivConstruction_of_fullPipeline_configRunner
      hfull)

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
