import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Adapters
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.FieldTapes

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
# Terminal run-config field emitter

This module isolates the finite-machine leaf that must turn the FST source
encoding of terminal simulator fields into the field-FST target containing the
fixed description run result.  Terminal source tapes are adapted to that FST
source shape by exact tape equality.
-/

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
    (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.left
    (DovetailInitialLayoutInitializer.tapeAtCells
      (List.append ((SimulatorLayout.asBoolInput L).reverse.map some)
        [none]) [none])

-- The post-scan leaf starts on the last source bit immediately left of the
-- terminal blank; its visible cells are still the canonical field source.
theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_cells_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L) =
      none ::
        List.append ((SimulatorLayout.asBoolInput L).map some) [none] := by
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
        Tape.move, Tape.moveLeft, hbits]
  | cons bit rest =>
      cases hrev : rest.reverse with
      | nil =>
          have hrest : rest = [] := by
            simpa using congrArg List.reverse hrev
          simp [
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
            Tape.move, Tape.moveLeft, hbits, hrest]
      | cons head tail =>
          have hrest : rest = (head :: tail).reverse := by
            rw [← hrev, List.reverse_reverse]
          simp [
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
            Tape.move, Tape.moveLeft, hbits, hrest, List.map_reverse,
            List.append_assoc]

-- The same source bits are preserved after scanning to the right-end-left
-- position; only the head location changes.
theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_normalizedOutput_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L) =
      SimulatorLayout.asBoolInput L := by
  rw [Tape.normalizedOutput]
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_cells_configRunner]
  cases SimulatorLayout.asBoolInput L <;>
    simp [Function.comp_def]

-- Expanded field form for the source boundary consumed by the remaining
-- post-scan run-config emitter leaf.
theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_cells_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend L.input
                (encodeNatAppend L.stage
                  (encodeConfigurationAppend L.config
                    (encodeBoolAppend L.hit []))))).map some)
          [none] := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_cells_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

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

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchSpec_configRunner
    (D postScan : MachineDescription) : Prop :=
  postScan.SubroutineReady ∧
    forall L : SimulatorLayout,
      postScan.HaltsFromTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists postScan : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchSpec_configRunner
        D postScan

/--
Post-scan finite-table leaf: parse the encoded simulator layout from the
right-end-left position, run the fixed description, and emit the exact
scratch-padded output.
-/
theorem fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_configRunner := by
  intro D
  sorry

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceSpec_configRunner
        D body

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_of_rightEndLeft_configRunner
    (hscan :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_configRunner)
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_configRunner := by
  rcases hscan with ⟨scanner, hscanner⟩
  intro D
  rcases hpost D with ⟨postScan, hpostScan⟩
  refine ⟨SeqViaCanonical scanner postScan, ?_⟩
  constructor
  · exact SeqViaCanonical_subroutineReady hscanner.left hpostScan.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hscanner.left
        hpostScan.left
        (hscanner.right L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_move_left_move_right_configRunner
          L)
        (hpostScan.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_of_rightEndLeft_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_core_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_core_configRunner

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceSpec_configRunner
        D body

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceConstruction_of_source_configRunner
    (hsource :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceConstruction_configRunner := by
  intro D
  rcases hsource D with ⟨body, hbody⟩
  refine
    ⟨SeqViaCanonical
      CommonGround.FiniteTransducers.leftMoveOnceDescription
      body, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        CommonGround.FiniteTransducers.leftMoveOnceDescription_subroutineReady
        hbody.left
  · intro L
    have hleft :
        CommonGround.FiniteTransducers.leftMoveOnceDescription.HaltsFromTape
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
            L) := by
      simpa [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L] using
        CommonGround.FiniteTransducers.leftMoveOnceDescription_haltsFromTape
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        CommonGround.FiniteTransducers.leftMoveOnceDescription_subroutineReady
        hbody.left
        hleft
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L)
        (hbody.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_of_scratch_configRunner
    (hscratch :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_configRunner := by
  intro D
  rcases hscratch D with ⟨body, hbody⟩
  refine ⟨seqSubroutine body ExactIdentityDescription Direction.right, ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        hbody.left
        CommonGround.Identity.exactIdentityDescription_subroutineReady
  · intro L
    have hidentity :
        exists nB : Nat,
          ExactIdentityDescription.runConfig nB
              { state := ExactIdentityDescription.start,
                tape :=
                  Tape.move Direction.right
                    (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
                      D L) } =
            { state := ExactIdentityDescription.halt,
              tape :=
                FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
                  D L } := by
      rcases
          CommonGround.Identity.exactIdentityDescription_run_from_start
            (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
              D L) with
        ⟨nB, hnB⟩
      exact ⟨nB, by
        simpa [
          FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner] using
          hnB⟩
    simpa using
      seqSubroutine_haltsFromTape_of_haltsFromTape
        hbody.left
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        (hbody.right L)
        hidentity

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_of_rightScratch_configRunner
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner := by
  intro D
  rcases hright D with ⟨rightBody, hrightBody⟩
  refine ⟨rightBody, hrightBody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_eq_FSTTargetTape_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner]
    using hrightBody.right L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_of_rightShiftedFields_configRunner
    (fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_of_rightScratch_configRunner
      (fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_of_scratch_configRunner
        (fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceConstruction_of_source_configRunner
          fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_core_configRunner)))

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_of_FSTSourceToField_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_core_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
