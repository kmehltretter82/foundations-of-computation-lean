import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.ProjectionPadded.InputQuoter.Shape

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

def preservingCellPassZeroBits : Word Bool :=
  [false, true, false, true]

def preservingCellPassOneBits : Word Bool :=
  [false, true, true, false]

/--
One slice of the exact input quoter finite leaf.  State {lit}`7` is the raw-word
payload pass state used by the controller-initial quoter.  Unlike that
emitter's destructive cell pass, this table erases the current source bit only
as a temporary return marker, appends the encoded payload cell to the output
area, restores the source bit, and returns to state {lit}`7` at the next source
cell.
-/
def PreservingCellPassDescription : MachineDescription where
  stateCount := 30
  start := 7
  halt := 29
  transitions :=
    [ transition 7 (some false) none Direction.right 10
    , transition 7 (some true) none Direction.right 20
    , transition 7 none none Direction.right 29
    , transition 10 (some false) (some false) Direction.right 10
    , transition 10 (some true) (some true) Direction.right 10
    , transition 10 none none Direction.right 11
    , transition 11 (some false) (some false) Direction.right 11
    , transition 11 (some true) (some true) Direction.right 11
    , transition 11 none (some false) Direction.right 12
    , transition 12 none (some true) Direction.right 13
    , transition 13 none (some false) Direction.right 14
    , transition 14 none (some true) Direction.right 15
    , transition 15 none none Direction.left 17
    , transition 17 (some false) (some false) Direction.left 17
    , transition 17 (some true) (some true) Direction.left 17
    , transition 17 none none Direction.left 16
    , transition 16 (some false) (some false) Direction.left 16
    , transition 16 (some true) (some true) Direction.left 16
    , transition 16 none (some false) Direction.right 7
    , transition 20 (some false) (some false) Direction.right 20
    , transition 20 (some true) (some true) Direction.right 20
    , transition 20 none none Direction.right 21
    , transition 21 (some false) (some false) Direction.right 21
    , transition 21 (some true) (some true) Direction.right 21
    , transition 21 none (some false) Direction.right 22
    , transition 22 none (some true) Direction.right 23
    , transition 23 none (some true) Direction.right 24
    , transition 24 none (some false) Direction.right 25
    , transition 25 none none Direction.left 27
    , transition 27 (some false) (some false) Direction.left 27
    , transition 27 (some true) (some true) Direction.left 27
    , transition 27 none none Direction.left 26
    , transition 26 (some false) (some false) Direction.left 26
    , transition 26 (some true) (some true) Direction.left 26
    , transition 26 none (some true) Direction.right 7
    ]

private abbrev PCP := PreservingCellPassDescription
private abbrev SIMS :=
  DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription

theorem preservingCellPassDescription_wellFormed :
    PCP.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := PCP.transitions)
      (stateCount := PCP.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := PCP.transitions)
      (by decide)

theorem preservingCellPassDescription_haltTransitionFree :
    PCP.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := PCP.transitions)
    (state := PCP.halt)
    (by decide)

theorem preservingCellPassDescription_subroutineReady :
    PCP.SubroutineReady :=
  ⟨preservingCellPassDescription_wellFormed,
    preservingCellPassDescription_haltTransitionFree⟩

theorem preservingCellPassDescription_run_scan10
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    PCP.runConfig
        (rest.length + 1)
        (config 10 leftRev
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none]))) =
      config 11
        (none :: List.append (rest.reverse.map some) leftRev)
        (List.append (output.map some) [none]) := by
  induction rest generalizing leftRev with
  | nil =>
      simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
      cases output <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              (config 10 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 10 (some false :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              (config 10 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 10 (some true :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem preservingCellPassDescription_run_scan20
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    PCP.runConfig
        (rest.length + 1)
        (config 20 leftRev
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none]))) =
      config 21
        (none :: List.append (rest.reverse.map some) leftRev)
        (List.append (output.map some) [none]) := by
  induction rest generalizing leftRev with
  | nil =>
      simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
      cases output <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              (config 20 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 20 (some false :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              (config 20 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 20 (some true :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem preservingCellPassDescription_run_scan11
    (leftRev : List (Option Bool)) (output : Word Bool) :
    PCP.runConfig
        (output.length + 1)
        (config 11 leftRev (List.append (output.map some) [none])) =
      config 12
        (some false :: List.append (output.reverse.map some) leftRev)
        [] := by
  induction output generalizing leftRev with
  | nil =>
      simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              (config 11 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 11 (some false :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              (config 11 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 11 (some true :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem preservingCellPassDescription_run_scan21
    (leftRev : List (Option Bool)) (output : Word Bool) :
    PCP.runConfig
        (output.length + 1)
        (config 21 leftRev (List.append (output.map some) [none])) =
      config 22
        (some false :: List.append (output.reverse.map some) leftRev)
        [] := by
  induction output generalizing leftRev with
  | nil =>
      simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              (config 21 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 21 (some false :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              (config 21 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 21 (some true :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [PCP, PreservingCellPassDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem preservingCellPassDescription_run_writeZero12
    (leftRev : List (Option Bool)) (rawRev output : Word Bool) :
    PCP.runConfig 4
        (config 12
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rawRev.map some) (none :: leftRev)))
          []) =
      { state := 17
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            (List.append (rawRev.map some) (none :: leftRev))
            (List.append [true, false, true, false] output.reverse)
            [none] } := by
  simp [PCP, PreservingCellPassDescription,
    controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
    config, tapeAtCells, runConfig, stepConfig, lookupTransition,
    Matches, transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem preservingCellPassDescription_run_writeOne22
    (leftRev : List (Option Bool)) (rawRev output : Word Bool) :
    PCP.runConfig 4
        (config 22
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rawRev.map some) (none :: leftRev)))
          []) =
      { state := 27
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            (List.append (rawRev.map some) (none :: leftRev))
            (List.append [false, true, true, false] output.reverse)
            [none] } := by
  simp [PCP, PreservingCellPassDescription,
    controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
    config, tapeAtCells, runConfig, stepConfig, lookupTransition,
    Matches, transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem preservingCellPassDescription_run_scan17
    (leftRev : List (Option Bool)) (rawRev outputRev : Word Bool)
    (right : List (Option Bool)) :
    PCP.runConfig
        (outputRev.length + 1)
        { state := 17
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) (none :: leftRev))
              outputRev right } =
      { state := 16
        tape :=
          controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
            leftRev rawRev
            (none :: List.append (outputRev.reverse.map some) right) } := by
  induction outputRev generalizing right with
  | nil =>
      simp [PCP, PreservingCellPassDescription,
        controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
        controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        tapeAtCells, runConfig, stepConfig, lookupTransition, Matches,
        transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      cases rawRev <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              { state := 17
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (false :: rest) right } =
            { state := 17
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some false :: right) } := by
          simp [PCP, PreservingCellPassDescription,
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            tapeAtCells, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              { state := 17
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (true :: rest) right } =
            { state := 17
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some true :: right) } := by
          simp [PCP, PreservingCellPassDescription,
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            tapeAtCells, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem preservingCellPassDescription_run_scan27
    (leftRev : List (Option Bool)) (rawRev outputRev : Word Bool)
    (right : List (Option Bool)) :
    PCP.runConfig
        (outputRev.length + 1)
        { state := 27
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) (none :: leftRev))
              outputRev right } =
      { state := 26
        tape :=
          controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
            leftRev rawRev
            (none :: List.append (outputRev.reverse.map some) right) } := by
  induction outputRev generalizing right with
  | nil =>
      simp [PCP, PreservingCellPassDescription,
        controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
        controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        tapeAtCells, runConfig, stepConfig, lookupTransition, Matches,
        transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      cases rawRev <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              { state := 27
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (false :: rest) right } =
            { state := 27
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some false :: right) } := by
          simp [PCP, PreservingCellPassDescription,
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            tapeAtCells, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              { state := 27
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (true :: rest) right } =
            { state := 27
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some true :: right) } := by
          simp [PCP, PreservingCellPassDescription,
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            tapeAtCells, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem preservingCellPassDescription_run_return16
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) :
    PCP.runConfig
        (scanRev.length + 1)
        { state := 16
          tape :=
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
              leftRev scanRev right } =
      config 7 (some false :: leftRev)
        (List.append (scanRev.reverse.map some) right) := by
  induction scanRev generalizing right with
  | nil =>
      simp [PCP, PreservingCellPassDescription,
        controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        config, tapeAtCells, runConfig, stepConfig, lookupTransition,
        Matches, transition, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
      cases right <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              { state := 16
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (false :: rest) right } =
            { state := 16
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some false :: right) } := by
          simp [PCP, PreservingCellPassDescription,
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            tapeAtCells, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              { state := 16
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (true :: rest) right } =
            { state := 16
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some true :: right) } := by
          simp [PCP, PreservingCellPassDescription,
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            tapeAtCells, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem preservingCellPassDescription_run_return26
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) :
    PCP.runConfig
        (scanRev.length + 1)
        { state := 26
          tape :=
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
              leftRev scanRev right } =
      config 7 (some true :: leftRev)
        (List.append (scanRev.reverse.map some) right) := by
  induction scanRev generalizing right with
  | nil =>
      simp [PCP, PreservingCellPassDescription,
        controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        config, tapeAtCells, runConfig, stepConfig, lookupTransition,
        Matches, transition, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
      cases right <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              { state := 26
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (false :: rest) right } =
            { state := 26
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some false :: right) } := by
          simp [PCP, PreservingCellPassDescription,
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            tapeAtCells, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [runConfig_add]
        have hfirst :
            PCP.runConfig 1
              { state := 26
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (true :: rest) right } =
            { state := 26
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some true :: right) } := by
          simp [PCP, PreservingCellPassDescription,
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            tapeAtCells, runConfig, stepConfig, lookupTransition,
            Matches, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem preservingCellPassDescription_run_cell_false
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ∃ steps : Nat,
      PCP.runConfig steps
        (config 7 leftRev
          (some false ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 7 (some false :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output preservingCellPassZeroBits).map some)
              [none])) := by
  let outputRev : Word Bool :=
    List.append [true, false, true, false] output.reverse
  refine
    ⟨1 +
      ((rest.length + 1) +
        ((output.length + 1) +
          (4 + ((outputRev.length + 1) + (rest.reverse.length + 1))))),
      ?_⟩
  rw [runConfig_add]
  have hfirst :
      PCP.runConfig 1
        (config 7 leftRev
          (some false ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 10 (none :: leftRev)
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none])) := by
    simp [PCP, PreservingCellPassDescription,
      config, tapeAtCells, runConfig, stepConfig, lookupTransition,
      Matches, transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]
    cases rest <;> rfl
  rw [hfirst]
  rw [runConfig_add]
  rw [preservingCellPassDescription_run_scan10]
  rw [runConfig_add]
  rw [preservingCellPassDescription_run_scan11]
  rw [runConfig_add]
  change
    PCP.runConfig
      ((outputRev.length + 1) + (rest.reverse.length + 1))
      (PCP.runConfig 4
        (config 12
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rest.reverse.map some)
                (none :: leftRev))) [])) =
        config 7 (some false :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output preservingCellPassZeroBits).map some)
              [none]))
  rw [preservingCellPassDescription_run_writeZero12]
  rw [runConfig_add]
  change
    PCP.runConfig
      (rest.reverse.length + 1)
      (PCP.runConfig
        (outputRev.length + 1)
        { state := 17
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rest.reverse.map some) (none :: leftRev))
              (List.append [true, false, true, false] output.reverse)
              [none] }) =
      config 7 (some false :: leftRev)
        (List.append (rest.map some)
          (none :: List.append
            ((List.append output preservingCellPassZeroBits).map some)
            [none]))
  rw [preservingCellPassDescription_run_scan17]
  rw [preservingCellPassDescription_run_return16]
  simp [outputRev, preservingCellPassZeroBits, List.map_append,
    List.append_assoc]

theorem preservingCellPassDescription_run_cell_true
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ∃ steps : Nat,
      PCP.runConfig steps
        (config 7 leftRev
          (some true ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 7 (some true :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output preservingCellPassOneBits).map some)
              [none])) := by
  let outputRev : Word Bool :=
    List.append [false, true, true, false] output.reverse
  refine
    ⟨1 +
      ((rest.length + 1) +
        ((output.length + 1) +
          (4 + ((outputRev.length + 1) + (rest.reverse.length + 1))))),
      ?_⟩
  rw [runConfig_add]
  have hfirst :
      PCP.runConfig 1
        (config 7 leftRev
          (some true ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 20 (none :: leftRev)
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none])) := by
    simp [PCP, PreservingCellPassDescription,
      config, tapeAtCells, runConfig, stepConfig, lookupTransition,
      Matches, transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]
    cases rest <;> rfl
  rw [hfirst]
  rw [runConfig_add]
  rw [preservingCellPassDescription_run_scan20]
  rw [runConfig_add]
  rw [preservingCellPassDescription_run_scan21]
  rw [runConfig_add]
  change
    PCP.runConfig
      ((outputRev.length + 1) + (rest.reverse.length + 1))
      (PCP.runConfig 4
        (config 22
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rest.reverse.map some)
                (none :: leftRev))) [])) =
        config 7 (some true :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output preservingCellPassOneBits).map some)
              [none]))
  rw [preservingCellPassDescription_run_writeOne22]
  rw [runConfig_add]
  change
    PCP.runConfig
      (rest.reverse.length + 1)
      (PCP.runConfig
        (outputRev.length + 1)
        { state := 27
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rest.reverse.map some) (none :: leftRev))
              (List.append [false, true, true, false] output.reverse)
              [none] }) =
      config 7 (some true :: leftRev)
        (List.append (rest.map some)
          (none :: List.append
            ((List.append output preservingCellPassOneBits).map some)
            [none]))
  rw [preservingCellPassDescription_run_scan27]
  rw [preservingCellPassDescription_run_return26]
  simp [outputRev, preservingCellPassOneBits, List.map_append,
    List.append_assoc]

def preservingCellPassCellBits : Word Bool -> Word Bool
  | [] => []
  | false :: rest =>
      List.append preservingCellPassZeroBits
        (preservingCellPassCellBits rest)
  | true :: rest =>
      List.append preservingCellPassOneBits
        (preservingCellPassCellBits rest)

theorem preservingCellPassCellBits_append_suffix
    (cells : Word Bool) (suffix : Word MachineCodeSymbol) :
    List.append (preservingCellPassCellBits cells)
        (encodeCodeWordAsInput suffix) =
      encodeCodeWordAsInput
        (encodeCellsAppend (cells.map some) suffix) := by
  induction cells with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b
      · simpa [preservingCellPassCellBits, preservingCellPassZeroBits,
          encodeCellsAppend, encodeCellAppend, encodeCell,
          encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          List.append_assoc] using ih
      · simpa [preservingCellPassCellBits, preservingCellPassOneBits,
          encodeCellsAppend, encodeCellAppend, encodeCell,
          encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          List.append_assoc] using ih

theorem preservingCellPassDescription_run_cells
    (leftRev : List (Option Bool)) (cells output : Word Bool) :
    ∃ steps : Nat,
      PCP.runConfig steps
        (config 7 leftRev
          (List.append (cells.map some)
            (none :: List.append (output.map some) [none]))) =
        config 7
          (List.append (cells.reverse.map some) leftRev)
          (none :: List.append
            ((List.append output
              (preservingCellPassCellBits cells)).map some)
            [none]) := by
  induction cells generalizing leftRev output with
  | nil =>
      exact ⟨0, by simp [runConfig, preservingCellPassCellBits]⟩
  | cons b rest ih =>
      cases b
      · rcases preservingCellPassDescription_run_cell_false
          leftRev rest output with
          ⟨cellSteps, hcell⟩
        rcases ih (some false :: leftRev)
            (List.append output preservingCellPassZeroBits) with
          ⟨restSteps, hrest⟩
        refine ⟨cellSteps + restSteps, ?_⟩
        rw [runConfig_add]
        change
          PCP.runConfig restSteps
            (PCP.runConfig cellSteps
              (config 7 leftRev
                (some false :: List.append (rest.map some)
                  (none :: List.append (output.map some) [none])))) =
            config 7
              (List.append ((false :: rest).reverse.map some) leftRev)
              (none :: List.append
                ((List.append output
                  (preservingCellPassCellBits (false :: rest))).map some)
                [none])
        rw [hcell]
        rw [hrest]
        simp [preservingCellPassCellBits, preservingCellPassZeroBits,
          List.reverse_cons, List.map_append, List.append_assoc]
      · rcases preservingCellPassDescription_run_cell_true
          leftRev rest output with
          ⟨cellSteps, hcell⟩
        rcases ih (some true :: leftRev)
            (List.append output preservingCellPassOneBits) with
          ⟨restSteps, hrest⟩
        refine ⟨cellSteps + restSteps, ?_⟩
        rw [runConfig_add]
        change
          PCP.runConfig restSteps
            (PCP.runConfig cellSteps
              (config 7 leftRev
                (some true :: List.append (rest.map some)
                  (none :: List.append (output.map some) [none])))) =
            config 7
              (List.append ((true :: rest).reverse.map some) leftRev)
              (none :: List.append
                ((List.append output
                  (preservingCellPassCellBits (true :: rest))).map some)
                [none])
        rw [hcell]
        rw [hrest]
        simp [preservingCellPassCellBits, preservingCellPassOneBits,
          List.reverse_cons, List.map_append, List.append_assoc]

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
