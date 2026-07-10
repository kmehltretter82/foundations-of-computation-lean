import FoC.Computability.Compiler.Structured.Lowering.CursorSeek

set_option doc.verso true

/-!
# Structured cursor head-cell routines
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Scan right through encoded logical cells until the two-cell head marker is
found.  The machine halts back on the first marker cell.
-/
def cursorScanToHeadMarkerDescription : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ { source := 0
        read := some false
        write := some false
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some true
        write := some true
        move := Direction.right
        target := 2 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.right
        target := 0 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 0 }
    , { source := 2
        read := some false
        write := some false
        move := Direction.right
        target := 0 }
    , { source := 2
        read := some true
        write := some true
        move := Direction.left
        target := 3 } ]

theorem cursorScanToHeadMarkerDescription_wellFormed :
    cursorScanToHeadMarkerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := cursorScanToHeadMarkerDescription.transitions)
      (stateCount := cursorScanToHeadMarkerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := cursorScanToHeadMarkerDescription.transitions)
      (by decide)

theorem cursorScanToHeadMarkerDescription_haltTransitionFree :
    cursorScanToHeadMarkerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := cursorScanToHeadMarkerDescription.transitions)
    (state := cursorScanToHeadMarkerDescription.halt)
    (by decide)

theorem cursorScanToHeadMarkerDescription_subroutineReady :
    cursorScanToHeadMarkerDescription.SubroutineReady :=
  ⟨cursorScanToHeadMarkerDescription_wellFormed,
    cursorScanToHeadMarkerDescription_haltTransitionFree⟩

private theorem cursorScanToHeadMarkerDescription_run_cell
    (cell : Option Bool) (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig 2
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode cell) suffix) } =
      { state := cursorScanToHeadMarkerDescription.start
        tape :=
          tapeAtCells
            (List.append (logicalCellCode cell).reverse left)
            suffix } := by
  cases cell with
  | none =>
      cases suffix <;>
        simp [cursorScanToHeadMarkerDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, logicalCellCode,
          tapeAtCells, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]
  | some bit =>
      cases bit <;> cases suffix <;>
        simp [cursorScanToHeadMarkerDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, logicalCellCode,
          tapeAtCells, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]

private theorem cursorScanToHeadMarkerDescription_run_cell_assoc
    (cell : Option Bool) (left middle suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig 2
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append
                (List.append (logicalCellCode cell) middle)
                suffix) } =
      { state := cursorScanToHeadMarkerDescription.start
        tape :=
          tapeAtCells
            (List.append (logicalCellCode cell).reverse left)
            (List.append middle suffix) } := by
  simpa [List.append_assoc] using
    cursorScanToHeadMarkerDescription_run_cell cell left
      (List.append middle suffix)

private theorem cursorScanToHeadMarkerDescription_run_cells
    (cells : List (Option Bool))
    (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig (2 * cells.length)
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append (logicalCellListCode cells)
                (List.append headMarkerCells suffix)) } =
      { state := cursorScanToHeadMarkerDescription.start
        tape :=
          tapeAtCells
            (List.append (logicalCellListCode cells).reverse left)
            (List.append headMarkerCells suffix) } := by
  induction cells generalizing left with
  | nil =>
      simp [MachineDescription.runConfig, logicalCellListCode]
  | cons cell rest ih =>
      rw [show 2 * (cell :: rest).length =
          2 + 2 * rest.length by
        simp [Nat.mul_add, Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      simp only [logicalCellListCode_cons]
      rw [cursorScanToHeadMarkerDescription_run_cell_assoc]
      simpa [List.reverse_append, List.append_assoc] using
          ih (List.append (logicalCellCode cell).reverse left)

private theorem cursorScanToHeadMarkerDescription_run_marker
    (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig 2
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append headMarkerCells suffix) } =
      { state := cursorScanToHeadMarkerDescription.halt
        tape :=
          tapeAtCells left
            (List.append headMarkerCells suffix) } := by
  cases suffix <;>
    simp [cursorScanToHeadMarkerDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      headMarkerCells, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem cursorScanToHeadMarkerDescription_run_to_marker
    (cells : List (Option Bool))
    (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig
        (2 * cells.length + 2)
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append (logicalCellListCode cells)
                (List.append headMarkerCells suffix)) } =
      { state := cursorScanToHeadMarkerDescription.halt
        tape :=
          tapeAtCells
            (List.append (logicalCellListCode cells).reverse left)
            (List.append headMarkerCells suffix) } := by
  rw [MachineDescription.runConfig_add]
  rw [cursorScanToHeadMarkerDescription_run_cells]
  rw [cursorScanToHeadMarkerDescription_run_marker]

theorem cursorScanToHeadMarkerDescription_haltsFromTape
    (cells : List (Option Bool))
    (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.HaltsFromTape
      (tapeAtCells left
        (List.append (logicalCellListCode cells)
          (List.append headMarkerCells suffix)))
      (tapeAtCells
        (List.append (logicalCellListCode cells).reverse left)
        (List.append headMarkerCells suffix)) := by
  refine ⟨2 * cells.length + 2, ?_⟩
  constructor <;>
    rw [cursorScanToHeadMarkerDescription_run_to_marker]

theorem cursorScanToHeadMarkerDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeSegmentEntry logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadMarker logical tapeIndex physical)
      cursorScanToHeadMarkerDescription where
  subroutineReady :=
    cursorScanToHeadMarkerDescription_subroutineReady
  realizes := by
    intro logical Tin hentry
    rcases hentry with ⟨T, rest, hdrop, hTin⟩
    let suffix :=
      List.append (logicalCellCode T.head)
        (List.append (logicalCellListCode T.right)
          (encodedStructuredTapeCells rest))
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (logicalCellListCode T.left.reverse)))
        (List.append headMarkerCells suffix)
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        cursorScanToHeadMarkerDescription_haltsFromTape
          T.left.reverse
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells).reverse
          suffix
      simpa [Tout, suffix, tapeAtEncodedSplit, logicalTapeCode,
        List.reverse_append, List.append_assoc] using hrun
    · exact ⟨T, rest, hdrop, rfl⟩

/-- Move from the first head-marker cell to the first encoded head-cell bit. -/
def cursorMoveHeadMarkerToCellDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := some true
        write := some true
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 2 } ]

theorem cursorMoveHeadMarkerToCellDescription_wellFormed :
    cursorMoveHeadMarkerToCellDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := cursorMoveHeadMarkerToCellDescription.transitions)
      (stateCount := cursorMoveHeadMarkerToCellDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := cursorMoveHeadMarkerToCellDescription.transitions)
      (by decide)

theorem cursorMoveHeadMarkerToCellDescription_haltTransitionFree :
    cursorMoveHeadMarkerToCellDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := cursorMoveHeadMarkerToCellDescription.transitions)
    (state := cursorMoveHeadMarkerToCellDescription.halt)
    (by decide)

theorem cursorMoveHeadMarkerToCellDescription_subroutineReady :
    cursorMoveHeadMarkerToCellDescription.SubroutineReady :=
  ⟨cursorMoveHeadMarkerToCellDescription_wellFormed,
    cursorMoveHeadMarkerToCellDescription_haltTransitionFree⟩

theorem cursorMoveHeadMarkerToCellDescription_run
    (left suffix : List (Option Bool)) :
    cursorMoveHeadMarkerToCellDescription.runConfig 2
        { state := cursorMoveHeadMarkerToCellDescription.start
          tape :=
            tapeAtCells left
              (List.append headMarkerCells suffix) } =
      { state := cursorMoveHeadMarkerToCellDescription.halt
        tape :=
          tapeAtCells (List.append headMarkerCells.reverse left)
            suffix } := by
  cases suffix <;>
    simp [cursorMoveHeadMarkerToCellDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      headMarkerCells, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem cursorMoveHeadMarkerToCellDescription_haltsFromTape
    (left suffix : List (Option Bool)) :
    cursorMoveHeadMarkerToCellDescription.HaltsFromTape
      (tapeAtCells left (List.append headMarkerCells suffix))
      (tapeAtCells (List.append headMarkerCells.reverse left)
        suffix) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [cursorMoveHeadMarkerToCellDescription_run]

theorem cursorMoveHeadMarkerToCellDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadMarker logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      cursorMoveHeadMarkerToCellDescription where
  subroutineReady :=
    cursorMoveHeadMarkerToCellDescription_subroutineReady
  realizes := by
    intro logical Tin hmarker
    rcases hmarker with ⟨T, rest, hdrop, hTin⟩
    let suffix :=
      List.append (logicalCellCode T.head)
        (List.append (logicalCellListCode T.right)
          (encodedStructuredTapeCells rest))
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (List.append (logicalCellListCode T.left.reverse)
              headMarkerCells)))
        suffix
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        cursorMoveHeadMarkerToCellDescription_haltsFromTape
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (logicalCellListCode T.left.reverse))).reverse
          suffix
      simpa [Tout, suffix, tapeAtEncodedSplit,
        List.reverse_append, List.append_assoc] using hrun
    · exact ⟨T, rest, hdrop, rfl⟩

def logicalCellCodeFirstPhysical
    (cell : Option Bool) : Option Bool :=
  match cell with
  | none => some false
  | some false => some false
  | some true => some true

def logicalCellCodeSecondPhysical
    (cell : Option Bool) : Option Bool :=
  match cell with
  | none => some false
  | some false => some true
  | some true => some false

theorem logicalCellCode_eq_pair
    (cell : Option Bool) :
    logicalCellCode cell =
      [logicalCellCodeFirstPhysical cell,
        logicalCellCodeSecondPhysical cell] := by
  cases cell with
  | none => rfl
  | some bit =>
      cases bit <;> rfl

/--
Check that the encoded head-cell code equals the expected logical cell and
halt back on the first bit of that code.
-/
def readHeadCellCodeDescription
    (expected : Option Bool) : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := logicalCellCodeFirstPhysical expected
        write := logicalCellCodeFirstPhysical expected
        move := Direction.right
        target := 1 }
    , { source := 1
        read := logicalCellCodeSecondPhysical expected
        write := logicalCellCodeSecondPhysical expected
        move := Direction.left
        target := 2 } ]

theorem readHeadCellCodeDescription_wellFormed
    (expected : Option Bool) :
    (readHeadCellCodeDescription expected).WellFormed := by
  cases expected with
  | none =>
      refine ⟨by decide, by decide, by decide, ?_, ?_⟩
      · exact transition_wellFormed_of_all
          (l := (readHeadCellCodeDescription none).transitions)
          (stateCount := (readHeadCellCodeDescription none).stateCount)
          (by decide)
      · exact transition_deterministic_of_all
          (l := (readHeadCellCodeDescription none).transitions)
          (by decide)
  | some bit =>
      cases bit
      · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
        · exact transition_wellFormed_of_all
            (l := (readHeadCellCodeDescription (some false)).transitions)
            (stateCount :=
              (readHeadCellCodeDescription (some false)).stateCount)
            (by decide)
        · exact transition_deterministic_of_all
            (l := (readHeadCellCodeDescription (some false)).transitions)
            (by decide)
      · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
        · exact transition_wellFormed_of_all
            (l := (readHeadCellCodeDescription (some true)).transitions)
            (stateCount :=
              (readHeadCellCodeDescription (some true)).stateCount)
            (by decide)
        · exact transition_deterministic_of_all
            (l := (readHeadCellCodeDescription (some true)).transitions)
            (by decide)

theorem readHeadCellCodeDescription_haltTransitionFree
    (expected : Option Bool) :
    (readHeadCellCodeDescription expected).HaltTransitionFree := by
  cases expected with
  | none =>
      exact transition_notFrom_of_all
        (l := (readHeadCellCodeDescription none).transitions)
        (state := (readHeadCellCodeDescription none).halt)
        (by decide)
  | some bit =>
      cases bit
      · exact transition_notFrom_of_all
          (l := (readHeadCellCodeDescription (some false)).transitions)
          (state := (readHeadCellCodeDescription (some false)).halt)
          (by decide)
      · exact transition_notFrom_of_all
          (l := (readHeadCellCodeDescription (some true)).transitions)
          (state := (readHeadCellCodeDescription (some true)).halt)
          (by decide)

theorem readHeadCellCodeDescription_subroutineReady
    (expected : Option Bool) :
    (readHeadCellCodeDescription expected).SubroutineReady :=
  ⟨readHeadCellCodeDescription_wellFormed expected,
    readHeadCellCodeDescription_haltTransitionFree expected⟩

theorem readHeadCellCodeDescription_run
    (expected : Option Bool)
    (left suffix : List (Option Bool)) :
    (readHeadCellCodeDescription expected).runConfig 2
        { state := (readHeadCellCodeDescription expected).start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode expected) suffix) } =
      { state := (readHeadCellCodeDescription expected).halt
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode expected) suffix) } := by
  cases expected with
  | none =>
      cases suffix <;>
        simp [readHeadCellCodeDescription, logicalCellCode,
          logicalCellCodeFirstPhysical,
          logicalCellCodeSecondPhysical,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some bit =>
      cases bit <;> cases suffix <;>
        simp [readHeadCellCodeDescription, logicalCellCode,
          logicalCellCodeFirstPhysical,
          logicalCellCodeSecondPhysical,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem readHeadCellCodeDescription_haltsFromTape
    (expected : Option Bool)
    (left suffix : List (Option Bool)) :
    (readHeadCellCodeDescription expected).HaltsFromTape
      (tapeAtCells left
        (List.append (logicalCellCode expected) suffix))
      (tapeAtCells left
        (List.append (logicalCellCode expected) suffix)) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [readHeadCellCodeDescription_run]

theorem readHeadCellCodeDescription_contract
    (tapeIndex : Nat) (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadCellCodeWithRead logical tapeIndex expected physical)
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      (readHeadCellCodeDescription expected) where
  subroutineReady :=
    readHeadCellCodeDescription_subroutineReady expected
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨T, rest, hdrop, hread, hTin⟩
    let suffix :=
      List.append (logicalCellListCode T.right)
        (encodedStructuredTapeCells rest)
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (List.append (logicalCellListCode T.left.reverse)
              headMarkerCells)))
        (List.append (logicalCellCode T.head) suffix)
    exists Tout
    constructor
    · have hhead : T.head = expected := hread
      rw [hTin, hhead]
      have hrun :=
        readHeadCellCodeDescription_haltsFromTape expected
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (List.append (logicalCellListCode T.left.reverse)
                headMarkerCells))).reverse
          suffix
      simpa [Tout, suffix, tapeAtEncodedSplit, hhead,
        List.reverse_append, List.append_assoc] using hrun
    · exact ⟨T, rest, hdrop, rfl⟩

/--
Overwrite the encoded two-bit head-cell code and halt back on its first bit.
The physical cursor location is preserved; the represented logical tape head
cell changes.
-/
def writeHeadCellCodeDescription
    (cell : Option Bool) : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := none
        write := logicalCellCodeFirstPhysical cell
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some false
        write := logicalCellCodeFirstPhysical cell
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some true
        write := logicalCellCodeFirstPhysical cell
        move := Direction.right
        target := 1 }
    , { source := 1
        read := none
        write := logicalCellCodeSecondPhysical cell
        move := Direction.left
        target := 2 }
    , { source := 1
        read := some false
        write := logicalCellCodeSecondPhysical cell
        move := Direction.left
        target := 2 }
    , { source := 1
        read := some true
        write := logicalCellCodeSecondPhysical cell
        move := Direction.left
        target := 2 } ]

theorem writeHeadCellCodeDescription_wellFormed
    (cell : Option Bool) :
    (writeHeadCellCodeDescription cell).WellFormed := by
  cases cell with
  | none =>
      refine ⟨by decide, by decide, by decide, ?_, ?_⟩
      · exact transition_wellFormed_of_all
          (l := (writeHeadCellCodeDescription none).transitions)
          (stateCount := (writeHeadCellCodeDescription none).stateCount)
          (by decide)
      · exact transition_deterministic_of_all
          (l := (writeHeadCellCodeDescription none).transitions)
          (by decide)
  | some bit =>
      cases bit
      · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
        · exact transition_wellFormed_of_all
            (l := (writeHeadCellCodeDescription (some false)).transitions)
            (stateCount :=
              (writeHeadCellCodeDescription (some false)).stateCount)
            (by decide)
        · exact transition_deterministic_of_all
            (l := (writeHeadCellCodeDescription (some false)).transitions)
            (by decide)
      · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
        · exact transition_wellFormed_of_all
            (l := (writeHeadCellCodeDescription (some true)).transitions)
            (stateCount :=
              (writeHeadCellCodeDescription (some true)).stateCount)
            (by decide)
        · exact transition_deterministic_of_all
            (l := (writeHeadCellCodeDescription (some true)).transitions)
            (by decide)

theorem writeHeadCellCodeDescription_haltTransitionFree
    (cell : Option Bool) :
    (writeHeadCellCodeDescription cell).HaltTransitionFree := by
  cases cell with
  | none =>
      exact transition_notFrom_of_all
        (l := (writeHeadCellCodeDescription none).transitions)
        (state := (writeHeadCellCodeDescription none).halt)
        (by decide)
  | some bit =>
      cases bit
      · exact transition_notFrom_of_all
          (l := (writeHeadCellCodeDescription (some false)).transitions)
          (state := (writeHeadCellCodeDescription (some false)).halt)
          (by decide)
      · exact transition_notFrom_of_all
          (l := (writeHeadCellCodeDescription (some true)).transitions)
          (state := (writeHeadCellCodeDescription (some true)).halt)
          (by decide)

theorem writeHeadCellCodeDescription_subroutineReady
    (cell : Option Bool) :
    (writeHeadCellCodeDescription cell).SubroutineReady :=
  ⟨writeHeadCellCodeDescription_wellFormed cell,
    writeHeadCellCodeDescription_haltTransitionFree cell⟩

theorem writeHeadCellCodeDescription_run
    (oldCell newCell : Option Bool)
    (left suffix : List (Option Bool)) :
    (writeHeadCellCodeDescription newCell).runConfig 2
        { state := (writeHeadCellCodeDescription newCell).start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode oldCell) suffix) } =
      { state := (writeHeadCellCodeDescription newCell).halt
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode newCell) suffix) } := by
  cases oldCell with
  | none =>
      cases newCell with
      | none =>
          cases suffix <;>
            simp [writeHeadCellCodeDescription, logicalCellCode,
              logicalCellCodeFirstPhysical,
              logicalCellCodeSecondPhysical,
              MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, tapeAtCells, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
      | some newBit =>
          cases newBit <;> cases suffix <;>
            simp [writeHeadCellCodeDescription, logicalCellCode,
              logicalCellCodeFirstPhysical,
              logicalCellCodeSecondPhysical,
              MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, tapeAtCells, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some oldBit =>
      cases oldBit <;>
        cases newCell with
        | none =>
            cases suffix <;>
              simp [writeHeadCellCodeDescription, logicalCellCode,
                logicalCellCodeFirstPhysical,
                logicalCellCodeSecondPhysical,
                MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, tapeAtCells, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
        | some newBit =>
            cases newBit <;> cases suffix <;>
              simp [writeHeadCellCodeDescription, logicalCellCode,
                logicalCellCodeFirstPhysical,
                logicalCellCodeSecondPhysical,
                MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, tapeAtCells, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem writeHeadCellCodeDescription_haltsFromTape
    (oldCell newCell : Option Bool)
    (left suffix : List (Option Bool)) :
    (writeHeadCellCodeDescription newCell).HaltsFromTape
      (tapeAtCells left
        (List.append (logicalCellCode oldCell) suffix))
      (tapeAtCells left
        (List.append (logicalCellCode newCell) suffix)) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [writeHeadCellCodeDescription_run]

theorem writeHeadCellCodeDescription_contract
    (tapeIndex : Nat) (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.writeHeadCell tapeIndex cell).apply logical)
          tapeIndex physical)
      (writeHeadCellCodeDescription cell) where
  subroutineReady :=
    writeHeadCellCodeDescription_subroutineReady cell
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨T, rest, hdrop, hTin⟩
    let suffix :=
      List.append (logicalCellListCode T.right)
        (encodedStructuredTapeCells rest)
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (List.append (logicalCellListCode T.left.reverse)
              headMarkerCells)))
        (List.append (logicalCellCode cell) suffix)
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        writeHeadCellCodeDescription_haltsFromTape
          T.head cell
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (List.append (logicalCellListCode T.left.reverse)
                headMarkerCells))).reverse
          suffix
      simpa [Tout, suffix, tapeAtEncodedSplit,
        List.reverse_append, List.append_assoc] using hrun
    · have htapeAt :
          Description.tapeAt logical tapeIndex = T :=
        description_tapeAt_eq_of_drop_eq_cons hdrop
      refine ⟨Tape.write cell T, rest, ?_, ?_⟩
      · simpa [PhysicalPrimitive.apply, htapeAt] using
          replaceTapeAt_drop_eq_of_drop_eq_cons
            (replacement := Tape.write cell T) hdrop
      · simp [Tout, suffix, tapeAtEncodedSplit,
          PhysicalPrimitive.apply, htapeAt,
          encodedPrefixBeforeTape_replaceTapeAt_eq, Tape.write,
          List.append_assoc]

def AtTapeHeadCellCodeWithLeftNeighbor
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists previous : Option Bool,
  exists leftRest : List (Option Bool),
  exists current : Option Bool,
  exists right : List (Option Bool),
  exists rest : List (Tape Bool),
    logical.drop tapeIndex =
      { left := previous :: leftRest
        head := current
        right := right } :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (List.append
                (logicalCellListCode (previous :: leftRest).reverse)
                headMarkerCells)))
          (List.append (logicalCellCode current)
            (List.append (logicalCellListCode right)
              (encodedStructuredTapeCells rest)))

def AtTapeHeadCellCodeWithRightNeighbor
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists current : Option Bool,
  exists next : Option Bool,
  exists left : List (Option Bool),
  exists rightRest : List (Option Bool),
  exists rest : List (Tape Bool),
    logical.drop tapeIndex =
      { left := left
        head := current
        right := next :: rightRest } :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (List.append (logicalCellListCode left.reverse)
                headMarkerCells)))
          (List.append (logicalCellCode current)
            (List.append
              (logicalCellListCode (next :: rightRest))
              (encodedStructuredTapeCells rest)))

def AtTapeHeadCellCodeAtLeftBoundary
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists current : Option Bool,
  exists right : List (Option Bool),
  exists rest : List (Tape Bool),
    logical.drop tapeIndex =
      { left := []
        head := current
        right := right } :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells headMarkerCells))
          (List.append (logicalCellCode current)
            (List.append (logicalCellListCode right)
              (encodedStructuredTapeCells rest)))

def AtTapeHeadCellCodeAtRightBoundary
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists current : Option Bool,
  exists left : List (Option Bool),
  exists rest : List (Tape Bool),
    logical.drop tapeIndex =
      { left := left
        head := current
        right := [] } :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (List.append (logicalCellListCode left.reverse)
                headMarkerCells)))
          (List.append (logicalCellCode current)
            (encodedStructuredTapeCells rest))

theorem atTapeHeadCellCode_left_cases
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (h : AtTapeHeadCellCode logical tapeIndex physical) :
    AtTapeHeadCellCodeWithLeftNeighbor logical tapeIndex physical ∨
      AtTapeHeadCellCodeAtLeftBoundary logical tapeIndex physical := by
  rcases h with ⟨T, rest, hdrop, hphysical⟩
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          right
          exact ⟨head, right, rest, hdrop, by
            simpa using! hphysical⟩
      | cons previous leftRest =>
          left
          exact ⟨previous, leftRest, head, right, rest, hdrop,
            by simpa using hphysical⟩

theorem atTapeHeadCellCode_right_cases
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (h : AtTapeHeadCellCode logical tapeIndex physical) :
    AtTapeHeadCellCodeWithRightNeighbor logical tapeIndex physical ∨
      AtTapeHeadCellCodeAtRightBoundary logical tapeIndex physical := by
  rcases h with ⟨T, rest, hdrop, hphysical⟩
  cases T with
  | mk left head right =>
      cases right with
      | nil =>
          right
          exact ⟨head, left, rest, hdrop, by
            simpa using! hphysical⟩
      | cons next rightRest =>
          left
          exact ⟨head, next, left, rightRest, rest, hdrop,
            by simpa using hphysical⟩

private theorem logicalTapesHaveGuardCells_of_drop_eq_cons
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {T : Tape Bool} {rest : List (Tape Bool)}
    (hguards : LogicalTapesHaveGuardCells logical)
    (hdrop : logical.drop tapeIndex = T :: rest) :
    LogicalTapeHasGuardCells T := by
  apply hguards
  exact List.mem_of_mem_drop (by
    rw [hdrop]
    simp)

private theorem logicalTapeAtHasGuardCells_of_drop_eq_cons
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {T : Tape Bool} {rest : List (Tape Bool)}
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex)
    (hdrop : logical.drop tapeIndex = T :: rest) :
    LogicalTapeHasGuardCells T := by
  rcases hguards with ⟨T', rest', hdrop', hguard⟩
  rw [hdrop] at hdrop'
  cases hdrop'
  exact hguard

theorem atTapeHeadCellCode_to_leftNeighbor_of_guardCells
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex)
    (h : AtTapeHeadCellCode logical tapeIndex physical) :
    AtTapeHeadCellCodeWithLeftNeighbor
      logical tapeIndex physical := by
  rcases h with ⟨T, rest, hdrop, hphysical⟩
  have hguard :
      LogicalTapeHasGuardCells T :=
    logicalTapeAtHasGuardCells_of_drop_eq_cons hguards hdrop
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          have hleft : ([] : List (Option Bool)) ≠ [] := by
            simpa [LogicalTapeHasLeftGuard] using hguard.left
          exact False.elim (hleft rfl)
      | cons previous leftRest =>
          exact
            ⟨previous, leftRest, head, right, rest, hdrop,
              by simpa using hphysical⟩

theorem atTapeHeadCellCode_to_rightNeighbor_of_guardCells
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex)
    (h : AtTapeHeadCellCode logical tapeIndex physical) :
    AtTapeHeadCellCodeWithRightNeighbor
      logical tapeIndex physical := by
  rcases h with ⟨T, rest, hdrop, hphysical⟩
  have hguard :
      LogicalTapeHasGuardCells T :=
    logicalTapeAtHasGuardCells_of_drop_eq_cons hguards hdrop
  cases T with
  | mk left head right =>
      cases right with
      | nil =>
          have hright : ([] : List (Option Bool)) ≠ [] := by
            simpa [LogicalTapeHasRightGuard] using hguard.right
          exact False.elim (hright rfl)
      | cons next rightRest =>
          exact
            ⟨head, next, left, rightRest, rest, hdrop,
              by simpa using hphysical⟩

theorem guardedAtTapeHeadCellCode_to_leftNeighbor
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (h : AtTapeHeadCellCode
        (guardLogicalTapes logical) tapeIndex physical) :
    AtTapeHeadCellCodeWithLeftNeighbor
      (guardLogicalTapes logical) tapeIndex physical := by
  rcases h with ⟨T, rest, hdrop, hphysical⟩
  have hguard :
      LogicalTapeHasGuardCells T :=
    logicalTapesHaveGuardCells_of_drop_eq_cons
      (guardLogicalTapes_haveGuardCells logical) hdrop
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          have hleft : ([] : List (Option Bool)) ≠ [] := by
            simpa [LogicalTapeHasLeftGuard] using hguard.left
          exact False.elim (hleft rfl)
      | cons previous leftRest =>
          exact
            ⟨previous, leftRest, head, right, rest, hdrop,
              by simpa using hphysical⟩

theorem guardedAtTapeHeadCellCode_to_rightNeighbor
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (h : AtTapeHeadCellCode
        (guardLogicalTapes logical) tapeIndex physical) :
    AtTapeHeadCellCodeWithRightNeighbor
      (guardLogicalTapes logical) tapeIndex physical := by
  rcases h with ⟨T, rest, hdrop, hphysical⟩
  have hguard :
      LogicalTapeHasGuardCells T :=
    logicalTapesHaveGuardCells_of_drop_eq_cons
      (guardLogicalTapes_haveGuardCells logical) hdrop
  cases T with
  | mk left head right =>
      cases right with
      | nil =>
          have hright : ([] : List (Option Bool)) ≠ [] := by
            simpa [LogicalTapeHasRightGuard] using hguard.right
          exact False.elim (hright rfl)
      | cons next rightRest =>
          exact
            ⟨head, next, left, rightRest, rest, hdrop,
              by simpa using hphysical⟩

/--
Move a head marker one logical cell to the left by swapping the marker with the
two-cell code immediately before it.

This routine handles the guarded case only: the source shape must expose an
actual encoded left-neighbor cell.  Boundary moves need a separate expansion
routine because the current tight segment encoding has no spare encoded blank
inside the segment.
-/
def moveHeadLeftLocalDescription : MachineDescription where
  stateCount := 17
  start := 0
  halt := 16
  transitions :=
    [ { source := 0, read := none, write := none,
        move := Direction.left, target := 1 }
    , { source := 0, read := some false, write := some false,
        move := Direction.left, target := 1 }
    , { source := 0, read := some true, write := some true,
        move := Direction.left, target := 1 }
    , { source := 1, read := some true, write := some true,
        move := Direction.left, target := 2 }
    , { source := 2, read := some true, write := some true,
        move := Direction.left, target := 3 }
    , { source := 3, read := some false, write := some false,
        move := Direction.left, target := 4 }
    , { source := 3, read := some true, write := some true,
        move := Direction.left, target := 5 }
    , { source := 4, read := some false, write := some true,
        move := Direction.right, target := 6 }
    , { source := 4, read := some true, write := some true,
        move := Direction.right, target := 7 }
    , { source := 5, read := some false, write := some true,
        move := Direction.right, target := 8 }
    , { source := 5, read := some true, write := some true,
        move := Direction.right, target := 9 }
    , { source := 6, read := some false, write := some true,
        move := Direction.right, target := 10 }
    , { source := 7, read := some false, write := some true,
        move := Direction.right, target := 11 }
    , { source := 8, read := some true, write := some true,
        move := Direction.right, target := 12 }
    , { source := 9, read := some true, write := some true,
        move := Direction.right, target := 13 }
    , { source := 10, read := some true, write := some false,
        move := Direction.right, target := 14 }
    , { source := 11, read := some true, write := some true,
        move := Direction.right, target := 14 }
    , { source := 12, read := some true, write := some false,
        move := Direction.right, target := 15 }
    , { source := 13, read := some true, write := some true,
        move := Direction.right, target := 15 }
    , { source := 14, read := some true, write := some false,
        move := Direction.left, target := 16 }
    , { source := 15, read := some true, write := some true,
        move := Direction.left, target := 16 } ]

theorem moveHeadLeftLocalDescription_wellFormed :
    moveHeadLeftLocalDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := moveHeadLeftLocalDescription.transitions)
      (stateCount := moveHeadLeftLocalDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := moveHeadLeftLocalDescription.transitions)
      (by decide)

theorem moveHeadLeftLocalDescription_haltTransitionFree :
    moveHeadLeftLocalDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := moveHeadLeftLocalDescription.transitions)
    (state := moveHeadLeftLocalDescription.halt)
    (by decide)

theorem moveHeadLeftLocalDescription_subroutineReady :
    moveHeadLeftLocalDescription.SubroutineReady :=
  ⟨moveHeadLeftLocalDescription_wellFormed,
    moveHeadLeftLocalDescription_haltTransitionFree⟩

theorem moveHeadLeftLocalDescription_run
    (previous current : Option Bool)
    (left suffix : List (Option Bool)) :
    moveHeadLeftLocalDescription.runConfig 8
        { state := moveHeadLeftLocalDescription.start
          tape :=
            tapeAtCells
              (List.append headMarkerCells.reverse
                (List.append (logicalCellCode previous).reverse left))
              (List.append (logicalCellCode current) suffix) } =
      { state := moveHeadLeftLocalDescription.halt
        tape :=
          tapeAtCells (List.append headMarkerCells.reverse left)
            (List.append (logicalCellCode previous)
              (List.append (logicalCellCode current) suffix)) } := by
  cases previous with
  | none =>
      cases current with
      | none =>
          cases suffix <;>
            simp [moveHeadLeftLocalDescription, logicalCellCode,
              headMarkerCells, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, tapeAtCells, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
      | some bit =>
          cases bit <;> cases suffix <;>
            simp [moveHeadLeftLocalDescription, logicalCellCode,
              headMarkerCells, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, tapeAtCells, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some previousBit =>
      cases previousBit <;>
        cases current with
        | none =>
            cases suffix <;>
              simp [moveHeadLeftLocalDescription, logicalCellCode,
                headMarkerCells, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, tapeAtCells, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
        | some bit =>
            cases bit <;> cases suffix <;>
              simp [moveHeadLeftLocalDescription, logicalCellCode,
                headMarkerCells, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, tapeAtCells, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem moveHeadLeftLocalDescription_haltsFromTape
    (previous current : Option Bool)
    (left suffix : List (Option Bool)) :
    moveHeadLeftLocalDescription.HaltsFromTape
      (tapeAtCells
        (List.append headMarkerCells.reverse
          (List.append (logicalCellCode previous).reverse left))
        (List.append (logicalCellCode current) suffix))
      (tapeAtCells (List.append headMarkerCells.reverse left)
        (List.append (logicalCellCode previous)
          (List.append (logicalCellCode current) suffix))) := by
  refine ⟨8, ?_⟩
  constructor <;>
    rw [moveHeadLeftLocalDescription_run]

theorem moveHeadLeftLocalDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadCellCodeWithLeftNeighbor logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
            logical)
          tapeIndex physical)
      moveHeadLeftLocalDescription where
  subroutineReady := moveHeadLeftLocalDescription_subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hsource with
      ⟨previous, leftRest, current, right, rest, hdrop, hTin⟩
    let oldTape : Tape Bool :=
      { left := previous :: leftRest
        head := current
        right := right }
    let movedTape : Tape Bool :=
      Tape.move Direction.left oldTape
    let suffix :=
      List.append (logicalCellListCode right)
        (encodedStructuredTapeCells rest)
    let leftBase :=
      List.append
        (encodedPrefixBeforeTape logical tapeIndex)
        (List.append tapeSeparatorCells
          (logicalCellListCode leftRest.reverse))
    let Tout :=
      tapeAtEncodedSplit
        (List.append leftBase headMarkerCells)
        (List.append (logicalCellCode previous)
          (List.append (logicalCellCode current) suffix))
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        moveHeadLeftLocalDescription_haltsFromTape
          previous current leftBase.reverse suffix
      simpa [Tout, leftBase, suffix, tapeAtEncodedSplit,
        oldTape, logicalCellListCode, List.reverse_cons,
        logicalCellListBits,
        List.reverse_append, List.append_assoc] using hrun
    · have htapeAt :
          Description.tapeAt logical tapeIndex = oldTape := by
        simpa [oldTape] using
          description_tapeAt_eq_of_drop_eq_cons hdrop
      refine ⟨movedTape, rest, ?_, ?_⟩
      · simpa [PhysicalPrimitive.apply, htapeAt, movedTape,
          oldTape, HeadMove.apply, Tape.move, Tape.moveLeft] using
          replaceTapeAt_drop_eq_of_drop_eq_cons
            (replacement := movedTape) hdrop
      · simp [Tout, leftBase, suffix, tapeAtEncodedSplit,
          PhysicalPrimitive.apply, htapeAt, movedTape, oldTape,
          HeadMove.apply, Tape.move, Tape.moveLeft,
          logicalCellListBits,
          encodedPrefixBeforeTape_replaceTapeAt_eq,
          List.append_assoc]

/--
Move a head marker one logical cell to the right by swapping the marker with
the two-cell code immediately after it.

As for {name}`moveHeadLeftLocalDescription`, this is the guarded local case:
the source shape must expose an actual encoded right-neighbor cell.
-/
def moveHeadRightLocalDescription : MachineDescription where
  stateCount := 17
  start := 0
  halt := 16
  transitions :=
    [ { source := 0, read := some false, write := some true,
        move := Direction.right, target := 1 }
    , { source := 0, read := some true, write := some true,
        move := Direction.right, target := 2 }
    , { source := 1, read := some false, write := some true,
        move := Direction.left, target := 3 }
    , { source := 1, read := some true, write := some true,
        move := Direction.left, target := 4 }
    , { source := 2, read := some false, write := some true,
        move := Direction.left, target := 5 }
    , { source := 2, read := some true, write := some true,
        move := Direction.left, target := 6 }
    , { source := 3, read := some true, write := some true,
        move := Direction.left, target := 7 }
    , { source := 4, read := some true, write := some true,
        move := Direction.left, target := 8 }
    , { source := 5, read := some true, write := some true,
        move := Direction.left, target := 9 }
    , { source := 6, read := some true, write := some true,
        move := Direction.left, target := 10 }
    , { source := 7, read := some true, write := some false,
        move := Direction.left, target := 11 }
    , { source := 8, read := some true, write := some true,
        move := Direction.left, target := 11 }
    , { source := 9, read := some true, write := some false,
        move := Direction.left, target := 12 }
    , { source := 10, read := some true, write := some true,
        move := Direction.left, target := 12 }
    , { source := 11, read := some true, write := some false,
        move := Direction.right, target := 13 }
    , { source := 12, read := some true, write := some true,
        move := Direction.right, target := 13 }
    , { source := 13, read := some false, write := some false,
        move := Direction.right, target := 14 }
    , { source := 13, read := some true, write := some true,
        move := Direction.right, target := 14 }
    , { source := 14, read := some true, write := some true,
        move := Direction.right, target := 15 }
    , { source := 15, read := some true, write := some true,
        move := Direction.right, target := 16 } ]

theorem moveHeadRightLocalDescription_wellFormed :
    moveHeadRightLocalDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := moveHeadRightLocalDescription.transitions)
      (stateCount := moveHeadRightLocalDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := moveHeadRightLocalDescription.transitions)
      (by decide)

theorem moveHeadRightLocalDescription_haltTransitionFree :
    moveHeadRightLocalDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := moveHeadRightLocalDescription.transitions)
    (state := moveHeadRightLocalDescription.halt)
    (by decide)

theorem moveHeadRightLocalDescription_subroutineReady :
    moveHeadRightLocalDescription.SubroutineReady :=
  ⟨moveHeadRightLocalDescription_wellFormed,
    moveHeadRightLocalDescription_haltTransitionFree⟩

theorem moveHeadRightLocalDescription_run
    (current next : Option Bool)
    (left suffix : List (Option Bool)) :
    moveHeadRightLocalDescription.runConfig 8
        { state := moveHeadRightLocalDescription.start
          tape :=
            tapeAtCells (List.append headMarkerCells.reverse left)
              (List.append (logicalCellCode current)
                (List.append (logicalCellCode next) suffix)) } =
      { state := moveHeadRightLocalDescription.halt
        tape :=
          tapeAtCells
            (List.append headMarkerCells.reverse
              (List.append (logicalCellCode current).reverse left))
            (List.append (logicalCellCode next) suffix) } := by
  cases current with
  | none =>
      cases next with
      | none =>
          cases suffix <;>
            simp [moveHeadRightLocalDescription, logicalCellCode,
              headMarkerCells, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, tapeAtCells, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
      | some bit =>
          cases bit <;> cases suffix <;>
            simp [moveHeadRightLocalDescription, logicalCellCode,
              headMarkerCells, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, tapeAtCells, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some currentBit =>
      cases currentBit <;>
        cases next with
        | none =>
            cases suffix <;>
              simp [moveHeadRightLocalDescription, logicalCellCode,
                headMarkerCells, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, tapeAtCells, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
        | some bit =>
            cases bit <;> cases suffix <;>
              simp [moveHeadRightLocalDescription, logicalCellCode,
                headMarkerCells, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, tapeAtCells, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem moveHeadRightLocalDescription_haltsFromTape
    (current next : Option Bool)
    (left suffix : List (Option Bool)) :
    moveHeadRightLocalDescription.HaltsFromTape
      (tapeAtCells
        (List.append headMarkerCells.reverse left)
        (List.append (logicalCellCode current)
          (List.append (logicalCellCode next) suffix)))
      (tapeAtCells
        (List.append headMarkerCells.reverse
          (List.append (logicalCellCode current).reverse left))
        (List.append (logicalCellCode next) suffix)) := by
  refine ⟨8, ?_⟩
  constructor <;>
    rw [moveHeadRightLocalDescription_run]

theorem moveHeadRightLocalDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadCellCodeWithRightNeighbor logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
            logical)
          tapeIndex physical)
      moveHeadRightLocalDescription where
  subroutineReady := moveHeadRightLocalDescription_subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hsource with
      ⟨current, next, left, rightRest, rest, hdrop, hTin⟩
    let oldTape : Tape Bool :=
      { left := left
        head := current
        right := next :: rightRest }
    let movedTape : Tape Bool :=
      Tape.move Direction.right oldTape
    let suffix :=
      List.append (logicalCellListCode rightRest)
        (encodedStructuredTapeCells rest)
    let leftBase :=
      List.append
        (encodedPrefixBeforeTape logical tapeIndex)
        (List.append tapeSeparatorCells
          (logicalCellListCode left.reverse))
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (List.append leftBase (logicalCellCode current))
          headMarkerCells)
        (List.append (logicalCellCode next) suffix)
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        moveHeadRightLocalDescription_haltsFromTape
          current next leftBase.reverse suffix
      simpa [Tout, leftBase, suffix, tapeAtEncodedSplit,
        oldTape, logicalCellListCode, logicalCellListBits,
        List.reverse_append, List.append_assoc] using hrun
    · have htapeAt :
          Description.tapeAt logical tapeIndex = oldTape := by
        simpa [oldTape] using
          description_tapeAt_eq_of_drop_eq_cons hdrop
      refine ⟨movedTape, rest, ?_, ?_⟩
      · simpa [PhysicalPrimitive.apply, htapeAt, movedTape,
          oldTape, HeadMove.apply, Tape.move, Tape.moveRight] using
          replaceTapeAt_drop_eq_of_drop_eq_cons
            (replacement := movedTape) hdrop
      · simp [Tout, leftBase, suffix, tapeAtEncodedSplit,
          PhysicalPrimitive.apply, htapeAt, movedTape, oldTape,
          HeadMove.apply, Tape.move, Tape.moveRight,
          logicalCellListBits,
          encodedPrefixBeforeTape_replaceTapeAt_eq,
          List.append_assoc]


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
