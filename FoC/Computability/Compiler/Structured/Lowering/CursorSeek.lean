import FoC.Computability.Compiler.Structured.Lowering.FiniteMachineTactics

set_option doc.verso true

/-!
# Structured cursor seek routines
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-- Preserve the current physical cell and move once. -/
def cursorMoveOnceDescription (move : Direction) :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        read := none
        write := none
        move := move
        target := 1 }
    , { source := 0
        read := some false
        write := some false
        move := move
        target := 1 }
    , { source := 0
        read := some true
        write := some true
        move := move
        target := 1 } ]

theorem cursorMoveOnceDescription_subroutineReady
    (move : Direction) :
    (cursorMoveOnceDescription move).SubroutineReady := by
  cases move <;>
    exact machineDescription_subroutineReady_of_transition_checks
      (cursorMoveOnceDescription _)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

theorem cursorMoveOnceDescription_wellFormed
    (move : Direction) :
    (cursorMoveOnceDescription move).WellFormed :=
  (cursorMoveOnceDescription_subroutineReady move).left

theorem cursorMoveOnceDescription_haltTransitionFree
    (move : Direction) :
    (cursorMoveOnceDescription move).HaltTransitionFree :=
  (cursorMoveOnceDescription_subroutineReady move).right

theorem cursorMoveOnceDescription_run
    (move : Direction) (T : Tape Bool) :
    (cursorMoveOnceDescription move).runConfig 1
        { state := (cursorMoveOnceDescription move).start
          tape := T } =
      { state := (cursorMoveOnceDescription move).halt
        tape := Tape.move move T } := by
  cases move <;>
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            machine_step [cursorMoveOnceDescription]
        | some bit =>
            cases bit <;>
              machine_step [cursorMoveOnceDescription]

theorem cursorMoveOnceDescription_haltsFromTape
    (move : Direction) (T : Tape Bool) :
    (cursorMoveOnceDescription move).HaltsFromTape T
      (Tape.move move T) := by
  refine ⟨1, ?_⟩
  constructor <;>
    rw [cursorMoveOnceDescription_run]

/--
Scan left inside one encoded tape segment and halt back on the segment's
opening separator.

The machine assumes it starts on a nonblank encoded cell to the right of the
opening separator.  On the separator it performs a right/left bounce, because
ordinary {name}`MachineDescription` transitions cannot stay in place.
-/
def returnToOpeningSeparatorDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := some false
        write := some false
        move := Direction.left
        target := 0 }
    , { source := 0
        read := some true
        write := some true
        move := Direction.left
        target := 0 }
    , { source := 0
        read := none
        write := none
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.left
        target := 2 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.left
        target := 2 } ]

theorem returnToOpeningSeparatorDescription_wellFormed :
    returnToOpeningSeparatorDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := returnToOpeningSeparatorDescription.transitions)
      (stateCount := returnToOpeningSeparatorDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := returnToOpeningSeparatorDescription.transitions)
      (by decide)

theorem returnToOpeningSeparatorDescription_haltTransitionFree :
    returnToOpeningSeparatorDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := returnToOpeningSeparatorDescription.transitions)
    (state := returnToOpeningSeparatorDescription.halt)
    (by decide)

theorem returnToOpeningSeparatorDescription_subroutineReady :
    returnToOpeningSeparatorDescription.SubroutineReady :=
  ⟨returnToOpeningSeparatorDescription_wellFormed,
    returnToOpeningSeparatorDescription_haltTransitionFree⟩

private theorem returnToOpeningSeparatorDescription_step_bit
    (left right : List (Option Bool)) (previous current : Bool) :
    returnToOpeningSeparatorDescription.runConfig 1
        { state := returnToOpeningSeparatorDescription.start
          tape := tapeAtCells (some previous :: left)
            (some current :: right) } =
      { state := returnToOpeningSeparatorDescription.start
        tape := tapeAtCells left
          (some previous :: some current :: right) } := by
  cases previous <;> cases current <;> cases right <;>
    machine_step [returnToOpeningSeparatorDescription]

private theorem returnToOpeningSeparatorDescription_step_current
    (left right : List (Option Bool)) (current : Bool) :
    returnToOpeningSeparatorDescription.runConfig 1
        { state := returnToOpeningSeparatorDescription.start
          tape := tapeAtCells (none :: left) (some current :: right) } =
      { state := returnToOpeningSeparatorDescription.start
        tape := tapeAtCells left (none :: some current :: right) } := by
  cases current <;> cases right <;>
    machine_step [returnToOpeningSeparatorDescription]

private theorem returnToOpeningSeparatorDescription_run_finish
    (left right : List (Option Bool)) (current : Bool) :
    returnToOpeningSeparatorDescription.runConfig 2
        { state := returnToOpeningSeparatorDescription.start
          tape := tapeAtCells left (none :: some current :: right) } =
      { state := returnToOpeningSeparatorDescription.halt
        tape := tapeAtCells left (none :: some current :: right) } := by
  cases current <;> cases left <;> cases right <;>
    machine_step [returnToOpeningSeparatorDescription]

theorem returnToOpeningSeparatorDescription_run
    (scanStack : Word Bool) (current : Bool)
    (leftBase right : List (Option Bool)) :
    returnToOpeningSeparatorDescription.runConfig
        (scanStack.length + 3)
        { state := returnToOpeningSeparatorDescription.start
          tape :=
            tapeAtCells
              (List.append (scanStack.map some) (none :: leftBase))
              (some current :: right) } =
      { state := returnToOpeningSeparatorDescription.halt
        tape :=
          tapeAtCells leftBase
            (none ::
              List.append (scanStack.reverse.map some)
                (some current :: right)) } := by
  induction scanStack generalizing current right with
  | nil =>
      change
        returnToOpeningSeparatorDescription.runConfig (1 + 2)
            { state := returnToOpeningSeparatorDescription.start
              tape := tapeAtCells (none :: leftBase)
                (some current :: right) } =
          { state := returnToOpeningSeparatorDescription.halt
            tape := tapeAtCells leftBase
              (none :: some current :: right) }
      rw [MachineDescription.runConfig_add]
      rw [returnToOpeningSeparatorDescription_step_current]
      simpa using
        returnToOpeningSeparatorDescription_run_finish
          leftBase right current
  | cons previous rest ih =>
      rw [show (previous :: rest).length + 3 =
          1 + (rest.length + 3) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      change
        returnToOpeningSeparatorDescription.runConfig
            (rest.length + 3)
            (returnToOpeningSeparatorDescription.runConfig 1
              { state := returnToOpeningSeparatorDescription.start
                tape :=
                  tapeAtCells
                    (some previous ::
                      List.append (rest.map some) (none :: leftBase))
                    (some current :: right) }) =
          { state := returnToOpeningSeparatorDescription.halt
            tape :=
              tapeAtCells leftBase
                (none ::
                  List.append
                    ((previous :: rest).reverse.map some)
                    (some current :: right)) }
      rw [returnToOpeningSeparatorDescription_step_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using ih previous (some current :: right)

theorem returnToOpeningSeparatorDescription_haltsFromTape
    (scanStack : Word Bool) (current : Bool)
    (leftBase right : List (Option Bool)) :
    returnToOpeningSeparatorDescription.HaltsFromTape
      (tapeAtCells
        (List.append (scanStack.map some) (none :: leftBase))
        (some current :: right))
      (tapeAtCells leftBase
        (none ::
          List.append (scanStack.reverse.map some)
            (some current :: right))) := by
  refine ⟨scanStack.length + 3, ?_⟩
  constructor <;>
    rw [returnToOpeningSeparatorDescription_run]

private theorem le_length_of_drop_eq_cons
    {α : Type u} {xs : List α} {index : Nat}
    {head : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    index ≤ xs.length := by
  induction index generalizing xs with
  | zero =>
      exact Nat.zero_le xs.length
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          exact Nat.succ_le_succ (ih hdrop)

theorem returnToOpeningSeparatorDescription_contract_headMarker
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadMarker logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator logical tapeIndex physical)
      returnToOpeningSeparatorDescription where
  subroutineReady :=
    returnToOpeningSeparatorDescription_subroutineReady
  realizes := by
    intro logical Tin hmarker
    rcases hmarker with ⟨T, rest, hdrop, hTin⟩
    let leftBits := logicalCellListBits T.left.reverse
    let scanStack := leftBits.reverse
    let suffix :=
      List.append (logicalCellCode T.head)
        (List.append (logicalCellListCode T.right)
          (encodedStructuredTapeCells rest))
    let Tout :=
      tapeAtEncodedSplit
        (encodedPrefixBeforeTape logical tapeIndex)
        (List.append tapeSeparatorCells
          (List.append (logicalTapeCode T)
            (encodedStructuredTapeCells rest)))
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        returnToOpeningSeparatorDescription_haltsFromTape
          scanStack true
          (encodedPrefixBeforeTape logical tapeIndex).reverse
          (some true :: suffix)
      simpa [Tout, scanStack, leftBits, suffix, tapeAtEncodedSplit,
        logicalTapeCode, headMarkerCells, tapeSeparatorCells,
        List.reverse_append, List.map_reverse, List.append_assoc] using
        hrun
    · constructor
      · exact le_length_of_drop_eq_cons hdrop
      · simp [Tout, tapeAtEncodedSplit, encodedSuffixFromTape, hdrop,
          tapeSeparatorCells]

theorem returnToOpeningSeparatorDescription_contract_headCell
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator logical tapeIndex physical)
      returnToOpeningSeparatorDescription where
  subroutineReady :=
    returnToOpeningSeparatorDescription_subroutineReady
  realizes := by
    intro logical Tin hcell
    rcases hcell with ⟨T, rest, hdrop, hTin⟩
    rcases logicalCellBits_exists_cons T.head with
      ⟨headBit, headRest, hheadBits⟩
    let leftBits := logicalCellListBits T.left.reverse
    let scanStack := List.append [true, true] leftBits.reverse
    let suffix :=
      List.append (logicalCellListCode T.right)
        (encodedStructuredTapeCells rest)
    let Tout :=
      tapeAtEncodedSplit
        (encodedPrefixBeforeTape logical tapeIndex)
        (List.append tapeSeparatorCells
          (List.append (logicalTapeCode T)
            (encodedStructuredTapeCells rest)))
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        returnToOpeningSeparatorDescription_haltsFromTape
          scanStack headBit
          (encodedPrefixBeforeTape logical tapeIndex).reverse
          (List.append (headRest.map some) suffix)
      simpa [Tout, scanStack, leftBits, suffix, tapeAtEncodedSplit,
        logicalTapeCode, hheadBits, headMarkerCells, tapeSeparatorCells,
        List.reverse_append, List.map_reverse, List.map_append,
        List.append_assoc] using hrun
    · constructor
      · exact le_length_of_drop_eq_cons hdrop
      · simp [Tout, tapeAtEncodedSplit, encodedSuffixFromTape, hdrop,
          tapeSeparatorCells]

/--
Scan right over the nonblank encoded cells of one logical tape segment, then
bounce left/right so the final halted head is exactly on the next separator.
-/
def cursorScanToNextSeparatorDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := some false
        write := some false
        move := Direction.right
        target := 0 }
    , { source := 0
        read := some true
        write := some true
        move := Direction.right
        target := 0 }
    , { source := 0
        read := none
        write := none
        move := Direction.left
        target := 1 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.right
        target := 2 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 2 } ]

theorem cursorScanToNextSeparatorDescription_wellFormed :
    cursorScanToNextSeparatorDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := cursorScanToNextSeparatorDescription.transitions)
      (stateCount := cursorScanToNextSeparatorDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := cursorScanToNextSeparatorDescription.transitions)
      (by decide)

theorem cursorScanToNextSeparatorDescription_haltTransitionFree :
    cursorScanToNextSeparatorDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := cursorScanToNextSeparatorDescription.transitions)
    (state := cursorScanToNextSeparatorDescription.halt)
    (by decide)

theorem cursorScanToNextSeparatorDescription_subroutineReady :
    cursorScanToNextSeparatorDescription.SubroutineReady :=
  ⟨cursorScanToNextSeparatorDescription_wellFormed,
    cursorScanToNextSeparatorDescription_haltTransitionFree⟩

private theorem cursorScanToNextSeparatorDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    cursorScanToNextSeparatorDescription.runConfig 1
        { state := cursorScanToNextSeparatorDescription.start
          tape := tapeAtCells left (some bit :: right) } =
      { state := cursorScanToNextSeparatorDescription.start
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    machine_step [cursorScanToNextSeparatorDescription]

private theorem cursorScanToNextSeparatorDescription_run_scan
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    cursorScanToNextSeparatorDescription.runConfig bits.length
        { state := cursorScanToNextSeparatorDescription.start
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: suffix)) } =
      { state := cursorScanToNextSeparatorDescription.start
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        cursorScanToNextSeparatorDescription.runConfig rest.length
            (cursorScanToNextSeparatorDescription.runConfig 1
              { state := cursorScanToNextSeparatorDescription.start
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: suffix)) }) =
          { state := cursorScanToNextSeparatorDescription.start
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: suffix) }
      rw [cursorScanToNextSeparatorDescription_step_bit left
        (List.append (rest.map some) (none :: suffix)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem reverse_map_some_append_exists_cons
    (bit : Bool) (rest : Word Bool)
    (left : List (Option Bool)) :
    exists head : Bool, exists tail : List (Option Bool),
      List.append ((bit :: rest).reverse.map some) left =
        some head :: tail := by
  induction rest generalizing bit left with
  | nil =>
      exact ⟨bit, left, rfl⟩
  | cons next rest ih =>
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih next (some bit :: left)

private theorem cursorScanToNextSeparatorDescription_run_finish
    (bit : Bool) (left suffix : List (Option Bool)) :
    cursorScanToNextSeparatorDescription.runConfig 2
        { state := cursorScanToNextSeparatorDescription.start
          tape := tapeAtCells (some bit :: left) (none :: suffix) } =
      { state := cursorScanToNextSeparatorDescription.halt
        tape := tapeAtCells (some bit :: left) (none :: suffix) } := by
  cases bit <;> cases left <;> cases suffix <;>
    machine_step [cursorScanToNextSeparatorDescription]

theorem cursorScanToNextSeparatorDescription_run_to_next
    (bit : Bool) (rest : Word Bool)
    (left suffix : List (Option Bool)) :
    cursorScanToNextSeparatorDescription.runConfig
        ((bit :: rest).length + 2)
        { state := cursorScanToNextSeparatorDescription.start
          tape :=
            tapeAtCells left
              (List.append ((bit :: rest).map some)
                (none :: suffix)) } =
      { state := cursorScanToNextSeparatorDescription.halt
        tape :=
          tapeAtCells
            (List.append ((bit :: rest).reverse.map some) left)
            (none :: suffix) } := by
  rw [MachineDescription.runConfig_add]
  rw [cursorScanToNextSeparatorDescription_run_scan]
  rcases reverse_map_some_append_exists_cons bit rest left with
    ⟨head, tail, hleft⟩
  rw [hleft]
  exact cursorScanToNextSeparatorDescription_run_finish head tail suffix

theorem cursorScanToNextSeparatorDescription_haltsFromTape
    (bit : Bool) (rest : Word Bool)
    (left suffix : List (Option Bool)) :
    cursorScanToNextSeparatorDescription.HaltsFromTape
      (tapeAtCells left
        (List.append ((bit :: rest).map some) (none :: suffix)))
      (tapeAtCells
        (List.append ((bit :: rest).reverse.map some) left)
        (none :: suffix)) := by
  refine ⟨(bit :: rest).length + 2, ?_⟩
  constructor <;>
    rw [cursorScanToNextSeparatorDescription_run_to_next]

theorem cursorScanToNextSeparatorDescription_contract_segmentEntry_to_exit
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeSegmentEntry logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSegmentExit logical tapeIndex physical)
      cursorScanToNextSeparatorDescription where
  subroutineReady :=
    cursorScanToNextSeparatorDescription_subroutineReady
  realizes := by
    intro logical Tin hentry
    rcases hentry with ⟨T, rest, hdrop, hTin⟩
    rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
    rcases encodedStructuredTapeCells_startsWith_separator rest with
      ⟨suffix, hsuffix⟩
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells)
          (logicalTapeCode T))
        (encodedStructuredTapeCells rest)
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        cursorScanToNextSeparatorDescription_haltsFromTape bit bits
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells).reverse
          suffix
      simpa [Tout, tapeAtEncodedSplit, logicalTapeCode_eq_map_some T,
        hbits, hsuffix, tapeSeparatorCells, List.reverse_append,
        List.map_reverse, List.append_assoc] using hrun
    · exact ⟨T, rest, hdrop, rfl⟩

/--
Seek from the separator before an existing segment to the separator immediately
after that segment.
-/
def cursorSeekNextSeparatorDescription : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ { source := 0
        read := none
        write := none
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 1 }
    , { source := 1
        read := none
        write := none
        move := Direction.left
        target := 2 }
    , { source := 2
        read := some false
        write := some false
        move := Direction.right
        target := 3 }
    , { source := 2
        read := some true
        write := some true
        move := Direction.right
        target := 3 } ]

theorem cursorSeekNextSeparatorDescription_wellFormed :
    cursorSeekNextSeparatorDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := cursorSeekNextSeparatorDescription.transitions)
      (stateCount := cursorSeekNextSeparatorDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := cursorSeekNextSeparatorDescription.transitions)
      (by decide)

theorem cursorSeekNextSeparatorDescription_haltTransitionFree :
    cursorSeekNextSeparatorDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := cursorSeekNextSeparatorDescription.transitions)
    (state := cursorSeekNextSeparatorDescription.halt)
    (by decide)

theorem cursorSeekNextSeparatorDescription_subroutineReady :
    cursorSeekNextSeparatorDescription.SubroutineReady :=
  ⟨cursorSeekNextSeparatorDescription_wellFormed,
    cursorSeekNextSeparatorDescription_haltTransitionFree⟩

private theorem cursorSeekNextSeparatorDescription_step_entry
    (left right : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.runConfig 1
        { state := cursorSeekNextSeparatorDescription.start
          tape := tapeAtCells left (none :: right) } =
      { state := 1
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    machine_step [cursorSeekNextSeparatorDescription]

private theorem cursorSeekNextSeparatorDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    cursorSeekNextSeparatorDescription.runConfig 1
        { state := 1
          tape := tapeAtCells left (some bit :: right) } =
      { state := 1
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    machine_step [cursorSeekNextSeparatorDescription]

private theorem cursorSeekNextSeparatorDescription_run_scan
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: suffix)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        cursorSeekNextSeparatorDescription.runConfig rest.length
            (cursorSeekNextSeparatorDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: suffix)) }) =
          { state := 1
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: suffix) }
      rw [cursorSeekNextSeparatorDescription_step_bit left
        (List.append (rest.map some) (none :: suffix)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem cursorSeekNextSeparatorDescription_run_finish
    (bit : Bool) (left suffix : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.runConfig 2
        { state := 1
          tape := tapeAtCells (some bit :: left) (none :: suffix) } =
      { state := cursorSeekNextSeparatorDescription.halt
        tape := tapeAtCells (some bit :: left) (none :: suffix) } := by
  cases bit <;> cases left <;> cases suffix <;>
    machine_step [cursorSeekNextSeparatorDescription]

theorem cursorSeekNextSeparatorDescription_run_to_next
    (bit : Bool) (rest : Word Bool)
    (left suffix : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.runConfig
        ((bit :: rest).length + 3)
        { state := cursorSeekNextSeparatorDescription.start
          tape :=
            tapeAtCells left
              (none ::
                List.append ((bit :: rest).map some)
                  (none :: suffix)) } =
      { state := cursorSeekNextSeparatorDescription.halt
        tape :=
          tapeAtCells
            (List.append ((bit :: rest).reverse.map some)
              (none :: left))
            (none :: suffix) } := by
  rw [show (bit :: rest).length + 3 =
      1 + ((bit :: rest).length + 2) by
    simp [Nat.add_assoc, Nat.add_left_comm]]
  rw [MachineDescription.runConfig_add]
  rw [cursorSeekNextSeparatorDescription_step_entry]
  rw [MachineDescription.runConfig_add]
  rw [cursorSeekNextSeparatorDescription_run_scan]
  rcases reverse_map_some_append_exists_cons bit rest (none :: left) with
    ⟨head, tail, hleft⟩
  rw [hleft]
  exact cursorSeekNextSeparatorDescription_run_finish head tail suffix

theorem cursorSeekNextSeparatorDescription_haltsFromTape
    (bit : Bool) (rest : Word Bool)
    (left suffix : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.HaltsFromTape
      (tapeAtCells left
        (none ::
          List.append ((bit :: rest).map some) (none :: suffix)))
      (tapeAtCells
        (List.append ((bit :: rest).reverse.map some) (none :: left))
        (none :: suffix)) := by
  refine ⟨(bit :: rest).length + 3, ?_⟩
  constructor <;>
    rw [cursorSeekNextSeparatorDescription_run_to_next]

theorem cursorSeekNextSeparatorDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator logical (tapeIndex + 1) physical)
      cursorSeekNextSeparatorDescription where
  subroutineReady :=
    cursorSeekNextSeparatorDescription_subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨hseparator, T, rest, hdrop⟩
    rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
    rcases encodedStructuredTapeCells_startsWith_separator rest with
      ⟨suffix, hsuffix⟩
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells)
          (logicalTapeCode T))
        (encodedStructuredTapeCells rest)
    exists Tout
    constructor
    · rcases hseparator with ⟨_hle, hTin⟩
      rw [hTin]
      have hrun :=
        cursorSeekNextSeparatorDescription_haltsFromTape bit bits
          (encodedPrefixBeforeTape logical tapeIndex).reverse suffix
      simpa [Tout, tapeAtEncodedSplit, encodedSuffixFromTape, hdrop,
        logicalTapeCode_eq_map_some T, hbits, hsuffix,
        tapeSeparatorCells, List.reverse_append, List.map_reverse,
        List.append_assoc] using hrun
    · exact atTapeSegmentExit_to_atTapeSeparator_succ
        ⟨T, rest, hdrop, rfl⟩

/-- Fixed seek from the canonical block start to tape 1. -/
def seekTape1Description : MachineDescription :=
  cursorSeekNextSeparatorDescription

theorem seekTape1Description_contract :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtTapeSeparator logical 1 physical)
      seekTape1Description :=
  cursorSeekNextSeparatorDescription_contract 0

/--
Fixed seek from the canonical block start to tape 2.

This is a concrete two-segment scanner.  It is intentionally separate from the
single-segment scanner because this layer still has no verified subroutine
composition operator for {name}`MachineDescription`.
-/
def seekTape2Description : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ { source := 0
        read := none
        write := none
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 1 }
    , { source := 1
        read := none
        write := none
        move := Direction.right
        target := 2 }
    , { source := 2
        read := some false
        write := some false
        move := Direction.right
        target := 2 }
    , { source := 2
        read := some true
        write := some true
        move := Direction.right
        target := 2 }
    , { source := 2
        read := none
        write := none
        move := Direction.left
        target := 3 }
    , { source := 3
        read := some false
        write := some false
        move := Direction.right
        target := 4 }
    , { source := 3
        read := some true
        write := some true
        move := Direction.right
        target := 4 } ]

theorem seekTape2Description_wellFormed :
    seekTape2Description.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := seekTape2Description.transitions)
      (stateCount := seekTape2Description.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := seekTape2Description.transitions)
      (by decide)

theorem seekTape2Description_haltTransitionFree :
    seekTape2Description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := seekTape2Description.transitions)
    (state := seekTape2Description.halt)
    (by decide)

theorem seekTape2Description_subroutineReady :
    seekTape2Description.SubroutineReady :=
  ⟨seekTape2Description_wellFormed,
    seekTape2Description_haltTransitionFree⟩

private theorem seekTape2Description_step_entry
    (left right : List (Option Bool)) :
    seekTape2Description.runConfig 1
        { state := seekTape2Description.start
          tape := tapeAtCells left (none :: right) } =
      { state := 1
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    machine_step [seekTape2Description]

private theorem seekTape2Description_step_bit_first
    (left right : List (Option Bool)) (bit : Bool) :
    seekTape2Description.runConfig 1
        { state := 1
          tape := tapeAtCells left (some bit :: right) } =
      { state := 1
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    machine_step [seekTape2Description]

private theorem seekTape2Description_run_scan_first
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    seekTape2Description.runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: suffix)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        seekTape2Description.runConfig rest.length
            (seekTape2Description.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: suffix)) }) =
          { state := 1
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: suffix) }
      rw [seekTape2Description_step_bit_first left
        (List.append (rest.map some) (none :: suffix)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem seekTape2Description_step_between
    (left right : List (Option Bool)) :
    seekTape2Description.runConfig 1
        { state := 1
          tape := tapeAtCells left (none :: right) } =
      { state := 2
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    machine_step [seekTape2Description]

private theorem seekTape2Description_step_bit_second
    (left right : List (Option Bool)) (bit : Bool) :
    seekTape2Description.runConfig 1
        { state := 2
          tape := tapeAtCells left (some bit :: right) } =
      { state := 2
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    machine_step [seekTape2Description]

private theorem seekTape2Description_run_scan_second
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    seekTape2Description.runConfig bits.length
        { state := 2
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: suffix)) } =
      { state := 2
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        seekTape2Description.runConfig rest.length
            (seekTape2Description.runConfig 1
              { state := 2
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: suffix)) }) =
          { state := 2
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: suffix) }
      rw [seekTape2Description_step_bit_second left
        (List.append (rest.map some) (none :: suffix)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem seekTape2Description_run_finish
    (bit : Bool) (left suffix : List (Option Bool)) :
    seekTape2Description.runConfig 2
        { state := 2
          tape := tapeAtCells (some bit :: left) (none :: suffix) } =
      { state := seekTape2Description.halt
        tape := tapeAtCells (some bit :: left) (none :: suffix) } := by
  cases bit <;> cases left <;> cases suffix <;>
    machine_step [seekTape2Description]

theorem seekTape2Description_run_to_second
    (firstBit : Bool) (firstRest : Word Bool)
    (secondBit : Bool) (secondRest : Word Bool)
    (left suffix : List (Option Bool)) :
    seekTape2Description.runConfig
        (1 + ((firstBit :: firstRest).length +
          (1 + ((secondBit :: secondRest).length + 2))))
        { state := seekTape2Description.start
          tape :=
            tapeAtCells left
              (none ::
                List.append ((firstBit :: firstRest).map some)
                  (none ::
                    List.append ((secondBit :: secondRest).map some)
                      (none :: suffix))) } =
      { state := seekTape2Description.halt
        tape :=
          tapeAtCells
            (List.append ((secondBit :: secondRest).reverse.map some)
              (none ::
                List.append ((firstBit :: firstRest).reverse.map some)
                  (none :: left)))
            (none :: suffix) } := by
  rw [MachineDescription.runConfig_add]
  rw [seekTape2Description_step_entry]
  rw [MachineDescription.runConfig_add]
  rw [seekTape2Description_run_scan_first]
  rw [MachineDescription.runConfig_add]
  rw [seekTape2Description_step_between]
  rw [MachineDescription.runConfig_add]
  rw [seekTape2Description_run_scan_second]
  rcases reverse_map_some_append_exists_cons secondBit secondRest
      (none ::
        List.append ((firstBit :: firstRest).reverse.map some)
          (none :: left)) with
    ⟨head, tail, hleft⟩
  rw [hleft]
  exact seekTape2Description_run_finish head tail suffix

theorem seekTape2Description_haltsFromTape
    (firstBit : Bool) (firstRest : Word Bool)
    (secondBit : Bool) (secondRest : Word Bool)
    (left suffix : List (Option Bool)) :
    seekTape2Description.HaltsFromTape
      (tapeAtCells left
        (none ::
          List.append ((firstBit :: firstRest).map some)
            (none ::
              List.append ((secondBit :: secondRest).map some)
                (none :: suffix))))
      (tapeAtCells
        (List.append ((secondBit :: secondRest).reverse.map some)
          (none ::
            List.append ((firstBit :: firstRest).reverse.map some)
              (none :: left)))
        (none :: suffix)) := by
  refine
    ⟨1 + ((firstBit :: firstRest).length +
      (1 + ((secondBit :: secondRest).length + 2))), ?_⟩
  constructor <;>
    rw [seekTape2Description_run_to_second]

theorem seekTape2Description_contract_three :
    CursorRoutineContract
      (fun logical physical =>
        exists T : Tape Bool, exists U : Tape Bool,
        exists V : Tape Bool,
          logical = [T, U, V] ∧ AtEncodedBlockStart logical physical)
      (fun logical physical =>
        AtTapeSeparator logical 2 physical)
      seekTape2Description where
  subroutineReady := seekTape2Description_subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨T, U, V, hlogical, hstart⟩
    subst hlogical
    rcases logicalTapeBits_exists_cons T with
      ⟨firstBit, firstRest, hfirstBits⟩
    rcases logicalTapeBits_exists_cons U with
      ⟨secondBit, secondRest, hsecondBits⟩
    rcases encodedStructuredTapeCells_startsWith_separator [V] with
      ⟨suffix, hsuffix⟩
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (List.append
            (List.append tapeSeparatorCells (logicalTapeCode T))
            tapeSeparatorCells)
          (logicalTapeCode U))
        (encodedStructuredTapeCells [V])
    exists Tout
    constructor
    · rcases hstart with ⟨_hle, hTin⟩
      rw [hTin]
      have hrun :=
        seekTape2Description_haltsFromTape
          firstBit firstRest secondBit secondRest [] suffix
      simpa [Tout, tapeAtEncodedSplit, encodedPrefixBeforeTape,
        encodedSuffixFromTape, logicalTapeCode_eq_map_some T,
        logicalTapeCode_eq_map_some U, hfirstBits, hsecondBits,
        hsuffix, tapeSeparatorCells, List.reverse_append,
        List.map_reverse, List.append_assoc] using hrun
    · refine ⟨?_, ?_⟩
      · change 2 ≤ 3
        decide
      simp [Tout, tapeAtEncodedSplit, encodedPrefixBeforeTape,
        encodedSuffixFromTape, List.append_assoc]

theorem seekTape2Description_contract :
    CursorRoutineContract
      (fun logical physical =>
        exists T : Tape Bool, exists U : Tape Bool,
        exists rest : List (Tape Bool),
          logical = T :: U :: rest ∧ AtEncodedBlockStart logical physical)
      (fun logical physical =>
        AtTapeSeparator logical 2 physical)
      seekTape2Description where
  subroutineReady := seekTape2Description_subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨T, U, rest, hlogical, hstart⟩
    subst hlogical
    rcases logicalTapeBits_exists_cons T with
      ⟨firstBit, firstRest, hfirstBits⟩
    rcases logicalTapeBits_exists_cons U with
      ⟨secondBit, secondRest, hsecondBits⟩
    rcases encodedStructuredTapeCells_startsWith_separator rest with
      ⟨suffix, hsuffix⟩
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (List.append
            (List.append tapeSeparatorCells (logicalTapeCode T))
            tapeSeparatorCells)
          (logicalTapeCode U))
        (encodedStructuredTapeCells rest)
    exists Tout
    constructor
    · rcases hstart with ⟨_hle, hTin⟩
      rw [hTin]
      have hrun :=
        seekTape2Description_haltsFromTape
          firstBit firstRest secondBit secondRest [] suffix
      simpa [Tout, tapeAtEncodedSplit, encodedPrefixBeforeTape,
        encodedSuffixFromTape, logicalTapeCode_eq_map_some T,
        logicalTapeCode_eq_map_some U, hfirstBits, hsecondBits,
        hsuffix, tapeSeparatorCells, List.reverse_append,
        List.map_reverse, List.append_assoc] using hrun
    · refine ⟨?_, ?_⟩
      · simp
      simp [Tout, tapeAtEncodedSplit, encodedPrefixBeforeTape,
        encodedSuffixFromTape, List.append_assoc]

/--
Moving right once from an existing tape separator enters that tape segment.
This is the first concrete cursor-to-cursor routine used by later seek
machines.
-/
theorem cursorMoveRightDescription_contract_separator_to_segmentEntry
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSegmentEntry logical tapeIndex physical)
      (cursorMoveOnceDescription Direction.right) where
  subroutineReady :=
    cursorMoveOnceDescription_subroutineReady Direction.right
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨hseparator, T, rest, hdrop⟩
    exists Tape.move Direction.right Tin
    constructor
    · exact cursorMoveOnceDescription_haltsFromTape Direction.right Tin
    · rcases hseparator with ⟨_hle, hTin⟩
      refine ⟨T, rest, hdrop, ?_⟩
      rw [hTin]
      have hmove :
          Tape.move Direction.right
            (tapeAtCells
              (encodedPrefixBeforeTape logical tapeIndex).reverse
              (none ::
                List.append (logicalTapeCode T)
                  (encodedStructuredTapeCells rest))) =
            tapeAtCells
              (none ::
                (encodedPrefixBeforeTape logical tapeIndex).reverse)
              (List.append (logicalTapeCode T)
                (encodedStructuredTapeCells rest)) := by
        cases hcells :
            List.append (logicalTapeCode T)
              (encodedStructuredTapeCells rest) <;>
          rfl
      simpa [tapeAtEncodedSplit, encodedSuffixFromTape, hdrop,
        tapeSeparatorCells, List.reverse_append] using hmove
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
