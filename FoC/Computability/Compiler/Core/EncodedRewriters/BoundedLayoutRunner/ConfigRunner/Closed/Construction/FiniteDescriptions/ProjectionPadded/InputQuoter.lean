import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.ProjectionPadded.Shape

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionInputQuoterExactSourceTape
    (L : DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append
      ((List.append
        (encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits
            L.input L.stage)
          (SelectedProjectionTailProjector.sourceRestFieldBits L))).map
        some)
      [none])

def SelectedProjectionInputQuoterExactTargetTape
    (L : DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
      L).reverse.map some)
    ((List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage)
      (SelectedProjectionTailProjector.sourceRestFieldBits L)).map some)

theorem parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape
    (L : DovetailLayout) :
    ParsedLayoutCheckedTape L =
      SelectedProjectionInputQuoterExactSourceTape L := by
  rw [SelectedProjectionInputQuoterExactSourceTape,
    SelectedProjectionTailProjector.parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestFieldBits]

theorem sourceTape_outputPrefix_eq_inputQuoterExactTargetTape
    (L : DovetailLayout) :
    SelectedProjectionTailProjector.sourceTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some) =
      SelectedProjectionInputQuoterExactTargetTape L := by
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceTape_outputPrefix_eq_stageInputSourceRestFieldBits]

theorem selectedProjectionInputQuoterExactSourceTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionInputQuoterExactSourceTape L) =
      ParsedLayoutBits L := by
  rw [← parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape L]
  exact parsedLayoutCheckedTape_normalizedOutput L

theorem selectedProjectionInputQuoterExactTargetTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionInputQuoterExactTargetTape L) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (ParsedLayoutBits L)
            (SelectedProjectionTailProjector.sourceSuffix L)) := by
  rw [← sourceTape_outputPrefix_eq_inputQuoterExactTargetTape L]
  exact
    SelectedProjectionTailProjector.sourceTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix
      L

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

/--
Finite skeleton for the exact input-quoter assembly layer.  The high states
consume the fixed {lit}`transition` symbol and the first two bits of the
stage-input field, replacing the second stage-input bit with the scanner
marker.  Control then drops into the existing marked stage-input scanner at
state {lit}`0`; state {lit}`210` is the important internal boundary where the
scanner has consumed the input prefix and the stage nat, leaving the
source-rest suffix under the head.
-/
def AssemblySkeletonDescription : MachineDescription where
  stateCount := 2000
  start := 1800
  halt := 1999
  transitions :=
    [ transition 1800 (some false) (some false) Direction.right 1801
    , transition 1801 (some false) (some false) Direction.right 1802
    , transition 1802 (some false) (some false) Direction.right 1803
    , transition 1803 (some true) (some true) Direction.right 1804
    , transition 1804 (some false) (some false) Direction.right 1805
    , transition 1805 (some false) none Direction.right 0
    ] ++ SIMS.transitions

private abbrev ASM := AssemblySkeletonDescription

theorem assemblySkeletonDescription_wellFormed :
    ASM.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ASM.transitions)
      (stateCount := ASM.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ASM.transitions)
      (by native_decide)

theorem assemblySkeletonDescription_haltTransitionFree :
    ASM.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ASM.transitions)
    (state := ASM.halt)
    (by native_decide)

theorem assemblySkeletonDescription_subroutineReady :
    ASM.SubroutineReady :=
  ⟨assemblySkeletonDescription_wellFormed,
    assemblySkeletonDescription_haltTransitionFree⟩

theorem runConfig_eq_of_transitions
    {D E : MachineDescription}
    (htrans : D.transitions = E.transitions)
    (n : Nat) (c : Configuration) :
    D.runConfig n c = E.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      simp only [runConfig]
      have hstep : D.stepConfig c = E.stepConfig c := by
        unfold stepConfig lookupTransition
        rw [htrans]
      rw [hstep]
      cases E.stepConfig c with
      | none => rfl
      | some next => exact ih next

theorem assemblySkeletonDescription_lookupTransition_eq_scanner
    (state : Nat) (read : Option Bool) (hstate : state < 1800) :
    ASM.lookupTransition state read = SIMS.lookupTransition state read := by
  have h1800' : 1800 ≠ state := by omega
  have h1801' : 1801 ≠ state := by omega
  have h1802' : 1802 ≠ state := by omega
  have h1803' : 1803 ≠ state := by omega
  have h1804' : 1804 ≠ state := by omega
  have h1805' : 1805 ≠ state := by omega
  cases read <;>
    simp [ASM, AssemblySkeletonDescription, lookupTransition, Matches,
      transition, h1800', h1801', h1802', h1803', h1804', h1805']

theorem assemblySkeletonDescription_stepConfig_eq_scanner
    (c : Configuration) (hstate : c.state < 1800) :
    ASM.stepConfig c = SIMS.stepConfig c := by
  unfold stepConfig
  rw [assemblySkeletonDescription_lookupTransition_eq_scanner
    c.state (Tape.read c.tape) hstate]

theorem assemblySkeletonDescription_runConfig_eq_scanner
    (n : Nat) (c : Configuration)
    (hstate : c.state < SIMS.stateCount) :
    ASM.runConfig n c = SIMS.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      simp only [runConfig]
      have hlt1800 : c.state < 1800 := by
        have hs : SIMS.stateCount = 1000 := rfl
        omega
      rw [assemblySkeletonDescription_stepConfig_eq_scanner c hlt1800]
      cases hstep : SIMS.stepConfig c with
      | none => rfl
      | some next =>
          exact ih next
            (stepConfig_state_bound
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputMarkedScannerDescription_wellFormed
              hstep)

def markedTailStartConfigWithBase
    (leftTail : List (Option Bool)) (tail : Word Bool) :
    Configuration :=
  { state := SIMS.start
    tape :=
      Tape.move Direction.right
        (tapeAtCells (some false :: leftTail)
          (none :: tail.map some)) }

def transitionPrefixLeftTail : List (Option Bool) :=
  [some true, some false, some false, some false]

theorem assemblySkeletonDescription_run_prefix_to_marked_tail
    (tail : Word Bool) :
    ASM.runConfig 6
        (config ASM.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                [false, false]))
            (tail.map some))) =
      markedTailStartConfigWithBase transitionPrefixLeftTail tail := by
  cases tail <;>
    simp [ASM, AssemblySkeletonDescription,
      SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      markedTailStartConfigWithBase, transitionPrefixLeftTail,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem assemblySkeletonDescription_run_prefix_to_stageInput_tail
    (w : Word Bool) (stage : Nat) (sourceRestBits : Word Bool) :
    ASM.runConfig 6
        (config ASM.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                (DovetailInitialLayoutInitializer.stageInputBits
                  w stage)))
            (sourceRestBits.map some))) =
      markedTailStartConfigWithBase transitionPrefixLeftTail
        (List.append
          (DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage)
          sourceRestBits) := by
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [show
      List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (false :: false ::
            DovetailInitialLayoutInitializer.stageInputSecondBitTail
              w stage) =
        List.append
          (List.append
            (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
            [false, false])
          (DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage) by
      simp [encodeCodeSymbolAsInput]]
  simpa [List.map_append, List.append_assoc] using
    assemblySkeletonDescription_run_prefix_to_marked_tail
      (List.append
        (DovetailInitialLayoutInitializer.stageInputSecondBitTail
          w stage)
        sourceRestBits)

theorem assemblySkeletonDescription_run_marked_tail_done_stageNat_to_state200_withBase
    (stage : Nat) (suffixBits : Word Bool)
    (leftTail : List (Option Bool)) :
    ASM.runConfig 18
        (markedTailStartConfigWithBase leftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              suffixBits)) =
      config 200
        (List.append [some true, some true, none, some false]
          leftTail)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (suffixBits.map some)) := by
  cases stage <;>
    simp [ASM, AssemblySkeletonDescription, markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
      encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblySkeletonDescription_run_marked_tail_tick_to_state120_withBase
    (bits : Word Bool) (leftTail : List (Option Bool)) :
    ASM.runConfig 6
        (markedTailStartConfigWithBase leftTail
          (true :: false :: bits)) =
      config 120
        (List.append [none, some true, none, some false] leftTail)
        (bits.map some) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · simp [markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
    generalize bits.map some = cells
    cases cells <;> rfl
  · simp [markedTailStartConfigWithBase, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state200_tick
    (left right : List (Option Bool)) :
    ASM.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
              some)
            right)) =
      config 200
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [ASM, AssemblySkeletonDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblySkeletonDescription_run_state200_done_to_state210
    (left right : List (Option Bool)) :
    ASM.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
              some)
            right)) =
      config 210
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [ASM, AssemblySkeletonDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblySkeletonDescription_run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    ASM.runConfig (4 * stage + 4)
        (config 200 left
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).map some)
            right)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        assemblySkeletonDescription_run_state200_done_to_state210
          left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        omega]
      rw [runConfig_add]
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (stage + 1)).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some) by
          simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
            encodeCodeSymbolAsInput]]
      change
        ASM.runConfig (4 * stage + 4)
          (ASM.runConfig 4
            (config 200 left
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage).map some)
                  right)))) =
          config 210
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                (stage + 1)).reverse.map some)
              left)
            right
      rw [assemblySkeletonDescription_run_state200_tick]
      have h := ih
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
        encodeCodeSymbolAsInput, List.reverse_append, List.map_append,
        List.append_assoc] using h

theorem assemblySkeletonDescription_run_empty_stageInput_to_sourceRest_boundary
    (stage : Nat) (sourceRestBits : Word Bool) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    ([] : Word Bool) stage)))
              (sourceRestBits.map some))) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))
          (sourceRestBits.map some) := by
  refine ⟨6 + (18 + (4 * stage + 4)), ?_⟩
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_prefix_to_stageInput_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  change
    ASM.runConfig (18 + (4 * stage + 4))
        (markedTailStartConfigWithBase transitionPrefixLeftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              sourceRestBits)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append [some true, some true, none, some false]
            transitionPrefixLeftTail))
        (sourceRestBits.map some)
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_marked_tail_done_stageNat_to_state200_withBase]
  rw [assemblySkeletonDescription_run_state200_stageNat_to_state210]

end SelectedProjectionInputQuoterFiniteLeaf

def SelectedProjectionInputQuoterExactShapeSpec
    (quoter : MachineDescription) : Prop :=
  quoter.SubroutineReady ∧
    forall L : DovetailLayout,
      quoter.HaltsFromTape
        (SelectedProjectionInputQuoterExactSourceTape L)
        (SelectedProjectionInputQuoterExactTargetTape L)

def SelectedProjectionInputQuoterExactShapeConstruction : Prop :=
  exists quoter : MachineDescription,
    SelectedProjectionInputQuoterExactShapeSpec quoter

theorem selectedProjectionInputQuoterSpec_of_exactShape
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterExactShapeSpec quoter) :
    SelectedProjectionInputQuoterSpec quoter := by
  constructor
  · exact hquoter.left
  · intro L
    have hrun := hquoter.right L
    rw [parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape L]
    rw [sourceTape_outputPrefix_eq_inputQuoterExactTargetTape L]
    exact hrun

theorem selectedProjectionInputQuoterConstruction_of_exactShape
    (h : SelectedProjectionInputQuoterExactShapeConstruction) :
    SelectedProjectionInputQuoterConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact
    ⟨quoter,
      selectedProjectionInputQuoterSpec_of_exactShape hquoter⟩

/--
Finite-machine leaf for selected projection under the equivalence-based phase
contract.  The checked parser supplies the canonical checked parsed-layout
input.  This first phase quotes the input field and positions the remaining
layout fields for the selected padded tail emitter.
-/
theorem selectedProjectionInputQuoterExactShapeConstruction_scaffold :
    SelectedProjectionInputQuoterExactShapeConstruction := by
  sorry

theorem selectedProjectionInputQuoterConstruction_scaffold :
    SelectedProjectionInputQuoterConstruction :=
  selectedProjectionInputQuoterConstruction_of_exactShape
    selectedProjectionInputQuoterExactShapeConstruction_scaffold

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
