import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Composition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Primitives

set_option doc.verso true

/-!
# Structured cursor contracts
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Cursor-level physical routines
-/

/--
Cursor position immediately after the separator that opens a logical tape
segment.  This is the first executable cursor boundary after
{name}`AtTapeSeparator`: a one-tape machine can move right from a separator
into the segment, then later scan for the head marker or next separator.
-/
def AtTapeSegmentEntry
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells)
          (List.append (logicalTapeCode T)
            (encodedStructuredTapeCells rest))

/--
Cursor position on the separator immediately after a logical tape segment.

This is intentionally stated with the same {lit}`drop tapeIndex = T :: rest`
witness as {name}`AtTapeSegmentEntry`; a later bridge can identify this with
{lit}`AtTapeSeparator logical (tapeIndex + 1)`.
-/
def AtTapeSegmentExit
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (List.append
              (encodedPrefixBeforeTape logical tapeIndex)
              tapeSeparatorCells)
            (logicalTapeCode T))
          (encodedStructuredTapeCells rest)

/-- A separator cursor whose selected tape segment exists. -/
def AtExistingTapeSeparator
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  AtTapeSeparator logical tapeIndex physical ∧
    exists T : Tape Bool, exists rest : List (Tape Bool),
      logical.drop tapeIndex = T :: rest

def AtTapeHeadCellCodeWithRead
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (expected : Option Bool) (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      Tape.read T = expected ∧
        physical =
          tapeAtEncodedSplit
            (List.append
              (encodedPrefixBeforeTape logical tapeIndex)
              (List.append tapeSeparatorCells
                (List.append (logicalCellListCode T.left.reverse)
                  headMarkerCells)))
            (List.append (logicalCellCode T.head)
              (List.append (logicalCellListCode T.right)
                (encodedStructuredTapeCells rest)))

private theorem replaceTapeAt_take_eq
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (replacement : Tape Bool) :
    (replaceTapeAt tapeIndex replacement logical).take tapeIndex =
      logical.take tapeIndex := by
  induction tapeIndex generalizing logical with
  | zero =>
      cases logical <;> rfl
  | succ tapeIndex ih =>
      cases logical with
      | nil => rfl
      | cons T rest =>
          simp [replaceTapeAt, ih]

theorem replaceTapeAt_drop_eq_of_drop_eq_cons
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {T replacement : Tape Bool} {rest : List (Tape Bool)}
    (hdrop : logical.drop tapeIndex = T :: rest) :
    (replaceTapeAt tapeIndex replacement logical).drop tapeIndex =
      replacement :: rest := by
  induction tapeIndex generalizing logical with
  | zero =>
      cases logical with
      | nil =>
          simp at hdrop
      | cons U tail =>
          simp at hdrop
          rcases hdrop with ⟨rfl, rfl⟩
          rfl
  | succ tapeIndex ih =>
      cases logical with
      | nil =>
          simp at hdrop
      | cons U tail =>
          simp at hdrop
          exact ih hdrop

theorem encodedPrefixBeforeTape_replaceTapeAt_eq
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (replacement : Tape Bool) :
    encodedPrefixBeforeTape
        (replaceTapeAt tapeIndex replacement logical) tapeIndex =
      encodedPrefixBeforeTape logical tapeIndex := by
  simp [encodedPrefixBeforeTape, replaceTapeAt_take_eq]

private theorem list_getD_eq_of_drop_eq_cons
    {α : Type u} {xs : List α} {index : Nat}
    {head fallback : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    xs.getD index fallback = head := by
  induction index generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          rcases hdrop with ⟨rfl, rfl⟩
          rfl
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          exact ih hdrop

theorem description_tapeAt_eq_of_drop_eq_cons
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {T : Tape Bool} {rest : List (Tape Bool)}
    (hdrop : logical.drop tapeIndex = T :: rest) :
    Description.tapeAt logical tapeIndex = T := by
  exact list_getD_eq_of_drop_eq_cons
    (fallback := Tape.blank) hdrop

private theorem take_succ_eq_take_append_of_drop_eq_cons
    {α : Type u} {xs : List α} {index : Nat}
    {head : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    xs.take (index + 1) = xs.take index ++ [head] := by
  induction index generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          rcases hdrop with ⟨rfl, rfl⟩
          rfl
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          have htail :
              rest.take (index + 1) =
                rest.take index ++ [head] :=
            ih hdrop
          simpa [List.take_succ_cons, List.append_assoc] using
            congrArg (fun cells => x :: cells) htail

private theorem drop_succ_eq_tail_of_drop_eq_cons
    {α : Type u} {xs : List α} {index : Nat}
    {head : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    xs.drop (index + 1) = tail := by
  induction index generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          rcases hdrop with ⟨rfl, rfl⟩
          rfl
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          exact ih hdrop

private theorem succ_le_length_of_drop_eq_cons
    {α : Type u} {xs : List α} {index : Nat}
    {head : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    index + 1 ≤ xs.length := by
  induction index generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          have hrest : index + 1 ≤ rest.length :=
            ih hdrop
          simpa [Nat.add_assoc, Nat.succ_eq_add_one] using
            Nat.succ_le_succ hrest

theorem atTapeSegmentExit_to_atTapeSeparator_succ
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (h : AtTapeSegmentExit logical tapeIndex physical) :
    AtTapeSeparator logical (tapeIndex + 1) physical := by
  rcases h with ⟨T, rest, hdrop, hphysical⟩
  constructor
  · exact succ_le_length_of_drop_eq_cons hdrop
  · rw [hphysical]
    have htake :
        logical.take (tapeIndex + 1) =
          logical.take tapeIndex ++ [T] :=
      take_succ_eq_take_append_of_drop_eq_cons hdrop
    have hdropSucc :
        logical.drop (tapeIndex + 1) = rest :=
      drop_succ_eq_tail_of_drop_eq_cons hdrop
    simp [tapeAtEncodedSplit,
      encodedPrefixBeforeTape, encodedSuffixFromTape, htake, hdropSucc,
      List.append_assoc]

/--
Contract for a concrete cursor routine.

Unlike {name}`PhysicalPrimitiveContract`, this does not force the routine to
start and end at the canonical block boundary.  It is the lower-level shape
needed by real physical seek/scan routines.
-/
structure CursorRoutineContract
    (source target : List (Tape Bool) -> Tape Bool -> Prop)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
    forall Tin : Tape Bool,
      source logical Tin ->
        exists Tout : Tape Bool,
          machine.HaltsFromTape Tin Tout ∧ target logical Tout

/--
Concrete zero-step cursor machine.

This is useful for already-at-boundary routines, notably the fixed
{lit}`seekTape 0` case from the canonical encoded block start.
-/
def cursorNoopDescription : MachineDescription where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem cursorNoopDescription_wellFormed :
    cursorNoopDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro t ht
    simp [cursorNoopDescription] at ht
  · intro t _u ht _hu _hkey
    simp [cursorNoopDescription] at ht

theorem cursorNoopDescription_haltTransitionFree :
    cursorNoopDescription.HaltTransitionFree := by
  intro t ht
  simp [cursorNoopDescription] at ht

theorem cursorNoopDescription_subroutineReady :
    cursorNoopDescription.SubroutineReady :=
  ⟨cursorNoopDescription_wellFormed,
    cursorNoopDescription_haltTransitionFree⟩

theorem cursorNoopDescription_haltsFromTape
    (T : Tape Bool) :
    cursorNoopDescription.HaltsFromTape T T := by
  refine ⟨0, ?_⟩
  constructor <;> rfl

theorem cursorNoopDescription_contract
    (P : List (Tape Bool) -> Tape Bool -> Prop) :
    CursorRoutineContract P P cursorNoopDescription where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical Tin hsource
    exact ⟨Tin, cursorNoopDescription_haltsFromTape Tin, hsource⟩

theorem cursorNoopDescription_refreshes_guardSlackEndpoint_of_canonical
    {primitives : List PhysicalPrimitive}
    {source target canonicalTarget : List (Tape Bool)}
    {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target
        physical)
    (hcanonical :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source
        canonicalTarget (encodedGuardedStructuredTapes canonicalTarget)) :
    cursorNoopDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  have hphysical :
      physical = encodedGuardedStructuredTapes canonicalTarget :=
    PhysicalPrimitiveSequenceGuardSlackEndpoint.physical_eq
      hendpoint hcanonical
  have htarget : target = canonicalTarget :=
    PhysicalPrimitiveSequenceGuardSlackEndpoint.target_eq
      hendpoint hcanonical
  rw [hphysical, htarget]
  exact
    MachineDescription.HaltsFromTape.toEquiv
      (cursorNoopDescription_haltsFromTape
        (encodedGuardedStructuredTapes canonicalTarget))

theorem cursorNoopDescription_refreshes_guardSlackEndpointEquiv_of_canonical
    {primitives : List PhysicalPrimitive}
    {source target canonicalTarget : List (Tape Bool)}
    {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source
        target physical)
    (hcanonical :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source
        canonicalTarget (encodedGuardedStructuredTapes canonicalTarget)) :
    cursorNoopDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  rcases hendpoint with ⟨exactPhysical, hexact, hequiv⟩
  rcases
      cursorNoopDescription_refreshes_guardSlackEndpoint_of_canonical
        hexact hcanonical with
    ⟨actualOut, hhalts, hout⟩
  rcases
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := cursorNoopDescription)
        (Tin := exactPhysical)
        (Tin' := physical)
        (Tout := actualOut)
        (Tape.Equiv.symm hequiv)
        hhalts with
    ⟨transportedOut, htransported, htransportedEquiv⟩
  exact
    ⟨transportedOut, htransported,
      Tape.Equiv.trans htransportedEquiv hout⟩

theorem cursorNoopDescription_refreshes_actionPrimitivesAt_zero_stay_guardSlackEndpoint_singleton
    (write? : Option (Option Bool)) (T : Tape Bool)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.stay } : TapeAction))
        [T] target physical) :
    cursorNoopDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  let action : TapeAction :=
    { write? := write?, move := HeadMove.stay }
  have hcanonical :
      PhysicalPrimitiveSequenceGuardSlackEndpoint
        (actionPrimitivesAt 0 action)
        [T] [action.apply T]
        (encodedGuardedStructuredTapes [action.apply T]) := by
    simpa [action] using
      actionPrimitivesAt_zero_stay_guardSlackEndpoint_canonical_singleton
        write? T
  have hphysical :
      physical = encodedGuardedStructuredTapes [action.apply T] :=
    PhysicalPrimitiveSequenceGuardSlackEndpoint.physical_eq
      hendpoint hcanonical
  have htarget : target = [action.apply T] :=
    PhysicalPrimitiveSequenceGuardSlackEndpoint.target_eq
      hendpoint hcanonical
  rw [hphysical, htarget]
  exact
    MachineDescription.HaltsFromTape.toEquiv
      (cursorNoopDescription_haltsFromTape
        (encodedGuardedStructuredTapes [action.apply T]))

theorem cursorNoopDescription_refreshes_actionPrimitivesAt_zero_stay_guardSlackEndpointEquiv_singleton
    (write? : Option (Option Bool)) (T : Tape Bool)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.stay } : TapeAction))
        [T] target physical) :
    cursorNoopDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  rcases hendpoint with ⟨exactPhysical, hexact, hequiv⟩
  rcases
      cursorNoopDescription_refreshes_actionPrimitivesAt_zero_stay_guardSlackEndpoint_singleton
        write? T hexact with
    ⟨actualOut, hhalts, hout⟩
  rcases
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := cursorNoopDescription)
        (Tin := exactPhysical)
        (Tin' := physical)
        (Tout := actualOut)
        (Tape.Equiv.symm hequiv)
        hhalts with
    ⟨transportedOut, htransported, htransportedEquiv⟩
  exact
    ⟨transportedOut, htransported,
      Tape.Equiv.trans htransportedEquiv hout⟩

theorem cursorNoopDescription_refreshes_actionPrimitivesAt_zero_left_guardSlackEndpoint_singleton_of_left_cons
    (write? : Option (Option Bool))
    (cell : Option Bool) (left : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool))
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.left } : TapeAction))
        [({ left := cell :: left, head := head, right := right } : Tape Bool)]
        target physical) :
    cursorNoopDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  cursorNoopDescription_refreshes_guardSlackEndpoint_of_canonical
    hendpoint
    (actionPrimitivesAt_zero_left_guardSlackEndpoint_canonical_singleton_of_left_cons
      write? cell left head right)

theorem cursorNoopDescription_refreshes_actionPrimitivesAt_zero_left_guardSlackEndpointEquiv_singleton_of_left_cons
    (write? : Option (Option Bool))
    (cell : Option Bool) (left : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool))
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.left } : TapeAction))
        [({ left := cell :: left, head := head, right := right } : Tape Bool)]
        target physical) :
    cursorNoopDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  cursorNoopDescription_refreshes_guardSlackEndpointEquiv_of_canonical
    hendpoint
    (actionPrimitivesAt_zero_left_guardSlackEndpoint_canonical_singleton_of_left_cons
      write? cell left head right)

theorem cursorNoopDescription_refreshes_actionPrimitivesAt_zero_right_guardSlackEndpoint_singleton_of_right_cons
    (write? : Option (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (cell : Option Bool) (right : List (Option Bool))
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.right } : TapeAction))
        [({ left := left, head := head, right := cell :: right } : Tape Bool)]
        target physical) :
    cursorNoopDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  cursorNoopDescription_refreshes_guardSlackEndpoint_of_canonical
    hendpoint
    (actionPrimitivesAt_zero_right_guardSlackEndpoint_canonical_singleton_of_right_cons
      write? left head cell right)

theorem cursorNoopDescription_refreshes_actionPrimitivesAt_zero_right_guardSlackEndpointEquiv_singleton_of_right_cons
    (write? : Option (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (cell : Option Bool) (right : List (Option Bool))
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.right } : TapeAction))
        [({ left := left, head := head, right := cell :: right } : Tape Bool)]
        target physical) :
    cursorNoopDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  cursorNoopDescription_refreshes_guardSlackEndpointEquiv_of_canonical
    hendpoint
    (actionPrimitivesAt_zero_right_guardSlackEndpoint_canonical_singleton_of_right_cons
      write? left head cell right)

/--
Repair the singleton right-boundary slack shape by appending one encoded blank
logical cell at the right edge of the only segment, then rewinding to the
canonical block-start separator.
-/
def rightBoundaryGuardSlackRefreshDescription : MachineDescription where
  stateCount := 7
  start := 0
  halt := 6
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
        write := some false
        move := Direction.right
        target := 2 }
    , { source := 2
        read := none
        write := some false
        move := Direction.right
        target := 3 }
    , { source := 3
        read := none
        write := none
        move := Direction.left
        target := 4 }
    , { source := 4
        read := some false
        write := some false
        move := Direction.left
        target := 4 }
    , { source := 4
        read := some true
        write := some true
        move := Direction.left
        target := 4 }
    , { source := 4
        read := none
        write := none
        move := Direction.right
        target := 5 }
    , { source := 5
        read := some false
        write := some false
        move := Direction.left
        target := 6 }
    , { source := 5
        read := some true
        write := some true
        move := Direction.left
        target := 6 } ]

theorem rightBoundaryGuardSlackRefreshDescription_wellFormed :
    rightBoundaryGuardSlackRefreshDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightBoundaryGuardSlackRefreshDescription.transitions)
      (stateCount := rightBoundaryGuardSlackRefreshDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightBoundaryGuardSlackRefreshDescription.transitions)
      (by decide)

theorem rightBoundaryGuardSlackRefreshDescription_haltTransitionFree :
    rightBoundaryGuardSlackRefreshDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightBoundaryGuardSlackRefreshDescription.transitions)
    (state := rightBoundaryGuardSlackRefreshDescription.halt)
    (by decide)

theorem rightBoundaryGuardSlackRefreshDescription_subroutineReady :
    rightBoundaryGuardSlackRefreshDescription.SubroutineReady :=
  ⟨rightBoundaryGuardSlackRefreshDescription_wellFormed,
    rightBoundaryGuardSlackRefreshDescription_haltTransitionFree⟩

private theorem rightBoundaryGuardSlackRefreshDescription_run_enter
    (bits : Word Bool) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 1
        { state := rightBoundaryGuardSlackRefreshDescription.start
          tape :=
            tapeAtCells [] (none :: List.append (bits.map some) [none]) } =
      { state := 1
        tape :=
          tapeAtCells [none] (List.append (bits.map some) [none]) } := by
  cases bits with
  | nil =>
      simp [rightBoundaryGuardSlackRefreshDescription,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest =>
      cases bit <;>
        simp [rightBoundaryGuardSlackRefreshDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rightBoundaryGuardSlackRefreshDescription_run_scan_right
    (bits : Word Bool) (left : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells left (List.append (bits.map some) [none]) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left) [none] } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      simp only [List.map_cons]
      have hstep :
          rightBoundaryGuardSlackRefreshDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells left
                    (List.append (some bit :: rest.map some) [none]) } =
            { state := 1
              tape :=
                tapeAtCells (some bit :: left)
                  (List.append (rest.map some) [none]) } := by
        cases bit <;> cases rest <;>
          simp [rightBoundaryGuardSlackRefreshDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem rightBoundaryGuardSlackRefreshDescription_run_append_blank_cell
    (left : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 3
        { state := 1
          tape := tapeAtCells left [none] } =
      { state := 4
        tape := tapeAtCells (some false :: left) [some false, none] } := by
  simp [rightBoundaryGuardSlackRefreshDescription,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

private theorem rightBoundaryGuardSlackRefreshDescription_run_scan_left
    (leftStack : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    rightBoundaryGuardSlackRefreshDescription.runConfig
        (leftStack.length + 1)
        { state := 4
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: right) } =
      { state := 4
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                right) } := by
  induction leftStack generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        simp [rightBoundaryGuardSlackRefreshDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 =
          1 + (rest.length + 1) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          rightBoundaryGuardSlackRefreshDescription.runConfig 1
              { state := 4
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: right) } =
            { state := 4
              tape :=
                tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: right) } := by
        cases current <;> cases next <;> cases right <;>
          simp [rightBoundaryGuardSlackRefreshDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: right)

private theorem rightBoundaryGuardSlackRefreshDescription_run_finish
    (bits : Word Bool) :
    rightBoundaryGuardSlackRefreshDescription.runConfig 2
        { state := 4
          tape :=
            tapeAtCells []
              (none ::
                List.append
                  ((List.append bits [false, false]).map some)
                  [none]) } =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                [none]) } := by
  cases bits with
  | nil =>
      simp [rightBoundaryGuardSlackRefreshDescription,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight]
  | cons bit rest =>
      cases bit <;>
        simp [rightBoundaryGuardSlackRefreshDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]

theorem rightBoundaryGuardSlackRefreshDescription_run_to_target
    (bits : Word Bool) :
    rightBoundaryGuardSlackRefreshDescription.runConfig
        (1 + (bits.length +
          (3 + ((false :: bits.reverse).length + 1 + 2))))
        { state := rightBoundaryGuardSlackRefreshDescription.start
          tape :=
            tapeAtCells [] (none :: List.append (bits.map some) [none]) } =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                [none]) } := by
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_enter]
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_scan_right]
  rw [MachineDescription.runConfig_add]
  rw [rightBoundaryGuardSlackRefreshDescription_run_append_blank_cell]
  rw [MachineDescription.runConfig_add]
  change
    rightBoundaryGuardSlackRefreshDescription.runConfig 2
        (rightBoundaryGuardSlackRefreshDescription.runConfig
          ((false :: bits.reverse).length + 1)
          { state := 4
            tape :=
              tapeAtCells
                (List.append ((false :: bits.reverse).map some) [none])
                [some false, none] }) =
      { state := rightBoundaryGuardSlackRefreshDescription.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append bits [false, false]).map some)
                [none]) }
  rw [rightBoundaryGuardSlackRefreshDescription_run_scan_left]
  simpa [List.reverse_cons, List.map_append, List.append_assoc] using
    rightBoundaryGuardSlackRefreshDescription_run_finish bits

theorem rightBoundaryGuardSlackRefreshDescription_haltsFromPayload
    (bits : Word Bool) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTape
      (tapeAtCells [] (none :: List.append (bits.map some) [none]))
      (tapeAtCells []
        (none ::
          List.append ((List.append bits [false, false]).map some)
            [none])) := by
  refine
    ⟨1 + (bits.length +
      (3 + ((false :: bits.reverse).length + 1 + 2))), ?_⟩
  constructor <;>
    rw [rightBoundaryGuardSlackRefreshDescription_run_to_target]

theorem rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundarySlackSingleton
    (left : List (Option Bool)) (head : Option Bool) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTape
      (encodedStructuredTapes
        [({ left := left, head := head, right := [] } : Tape Bool)])
      (encodedStructuredTapes
        [({ left := left, head := head, right := [none] } : Tape Bool)]) := by
  simpa [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, logicalTapeBits, logicalCellListBits,
    logicalCellListBits_append, logicalCellBits, tapeSeparatorCells,
    List.map_append, List.append_assoc] using
    rightBoundaryGuardSlackRefreshDescription_haltsFromPayload
      (logicalTapeBits
        ({ left := left, head := head, right := [] } : Tape Bool))

theorem rightBoundaryGuardSlackRefreshDescription_refreshes_actionPrimitivesAt_zero_right_guardSlackEndpoint_singleton_of_right_nil
    (write? : Option (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.right } : TapeAction))
        [({ left := left, head := head, right := [] } : Tape Bool)]
        target physical) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  let source : Tape Bool :=
    { left := left, head := head, right := [] }
  let action : TapeAction :=
    { write? := write?, move := HeadMove.right }
  let slack : Tape Bool :=
    { left := tapeActionWrittenHead write? head :: (left ++ [none])
      head := none
      right := [] }
  let canonical : Tape Bool :=
    { left := tapeActionWrittenHead write? head :: (left ++ [none])
      head := none
      right := [none] }
  have hcanonicalEndpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint
        (actionPrimitivesAt 0 action) [source] [action.apply source]
        (encodedStructuredTapes [slack]) := by
    simpa [action, source, slack,
      actionPrimitivesAt_zero_right_guardSlackPhysical_eq_boundaryRightSlack_singleton]
      using
        actionPrimitivesAt_zero_right_guardSlackEndpoint_singleton
          write? source
  have hphysical : physical = encodedStructuredTapes [slack] :=
    PhysicalPrimitiveSequenceGuardSlackEndpoint.physical_eq
      hendpoint hcanonicalEndpoint
  have htarget : target = [action.apply source] :=
    PhysicalPrimitiveSequenceGuardSlackEndpoint.target_eq
      hendpoint hcanonicalEndpoint
  have hguarded :
      encodedGuardedStructuredTapes [action.apply source] =
        encodedStructuredTapes [canonical] := by
    simpa [action, source, canonical] using
      actionPrimitivesAt_zero_right_guardedTarget_eq_boundaryRightCanonical_singleton
        write? left head
  rw [hphysical, htarget, hguarded]
  exact
    MachineDescription.HaltsFromTape.toEquiv
      (rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundarySlackSingleton
        slack.left slack.head)

theorem rightBoundaryGuardSlackRefreshDescription_refreshes_actionPrimitivesAt_zero_right_guardSlackEndpointEquiv_singleton_of_right_nil
    (write? : Option (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.right } : TapeAction))
        [({ left := left, head := head, right := [] } : Tape Bool)]
        target physical) :
    rightBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  rcases hendpoint with ⟨exactPhysical, hexact, hequiv⟩
  rcases
      rightBoundaryGuardSlackRefreshDescription_refreshes_actionPrimitivesAt_zero_right_guardSlackEndpoint_singleton_of_right_nil
        write? left head hexact with
    ⟨actualOut, hhalts, hout⟩
  rcases
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := rightBoundaryGuardSlackRefreshDescription)
        (Tin := exactPhysical)
        (Tin' := physical)
        (Tout := actualOut)
        (Tape.Equiv.symm hequiv)
        hhalts with
    ⟨transportedOut, htransported, htransportedEquiv⟩
  exact
    ⟨transportedOut, htransported,
      Tape.Equiv.trans htransportedEquiv hout⟩

private def leftBoundaryGuardSlackShiftPairState
    (first second : Bool) : Nat :=
  match first, second with
  | false, false => 4
  | false, true => 5
  | true, false => 6
  | true, true => 7

private def leftBoundaryGuardSlackShiftTailState
    (second : Bool) : Nat :=
  match second with
  | false => 8
  | true => 9

/--
Shift a singleton left-boundary slack segment two physical Boolean cells to the
right, writing the encoded blank logical cell at the segment start.  The
routine halts at the new right-edge blank; callers compose it with the standard
right-edge rewind to return to block start.
-/
def leftBoundaryGuardSlackShiftDescription : MachineDescription where
  stateCount := 11
  start := 0
  halt := 10
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
        target := 2 }
    , { source := 1
        read := some true
        write := some false
        move := Direction.right
        target := 3 }
    , { source := 2
        read := some false
        write := some false
        move := Direction.right
        target := 4 }
    , { source := 2
        read := some true
        write := some false
        move := Direction.right
        target := 5 }
    , { source := 3
        read := some false
        write := some false
        move := Direction.right
        target := 6 }
    , { source := 3
        read := some true
        write := some false
        move := Direction.right
        target := 7 }
    , { source := 4
        read := some false
        write := some false
        move := Direction.right
        target := 4 }
    , { source := 4
        read := some true
        write := some false
        move := Direction.right
        target := 5 }
    , { source := 4
        read := none
        write := some false
        move := Direction.right
        target := 8 }
    , { source := 5
        read := some false
        write := some false
        move := Direction.right
        target := 6 }
    , { source := 5
        read := some true
        write := some false
        move := Direction.right
        target := 7 }
    , { source := 5
        read := none
        write := some false
        move := Direction.right
        target := 9 }
    , { source := 6
        read := some false
        write := some true
        move := Direction.right
        target := 4 }
    , { source := 6
        read := some true
        write := some true
        move := Direction.right
        target := 5 }
    , { source := 6
        read := none
        write := some true
        move := Direction.right
        target := 8 }
    , { source := 7
        read := some false
        write := some true
        move := Direction.right
        target := 6 }
    , { source := 7
        read := some true
        write := some true
        move := Direction.right
        target := 7 }
    , { source := 7
        read := none
        write := some true
        move := Direction.right
        target := 9 }
    , { source := 8
        read := none
        write := some false
        move := Direction.right
        target := 10 }
    , { source := 9
        read := none
        write := some true
        move := Direction.right
        target := 10 } ]

theorem leftBoundaryGuardSlackShiftDescription_wellFormed :
    leftBoundaryGuardSlackShiftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftBoundaryGuardSlackShiftDescription.transitions)
      (stateCount := leftBoundaryGuardSlackShiftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftBoundaryGuardSlackShiftDescription.transitions)
      (by decide)

theorem leftBoundaryGuardSlackShiftDescription_haltTransitionFree :
    leftBoundaryGuardSlackShiftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftBoundaryGuardSlackShiftDescription.transitions)
    (state := leftBoundaryGuardSlackShiftDescription.halt)
    (by decide)

theorem leftBoundaryGuardSlackShiftDescription_subroutineReady :
    leftBoundaryGuardSlackShiftDescription.SubroutineReady :=
  ⟨leftBoundaryGuardSlackShiftDescription_wellFormed,
    leftBoundaryGuardSlackShiftDescription_haltTransitionFree⟩

private theorem leftBoundaryGuardSlackShiftDescription_run_initial
    (first second : Bool) (rest : Word Bool) :
    leftBoundaryGuardSlackShiftDescription.runConfig 3
        { state := leftBoundaryGuardSlackShiftDescription.start
          tape :=
            tapeAtCells []
              (none ::
                List.append ((first :: second :: rest).map some) [none]) } =
      { state := leftBoundaryGuardSlackShiftPairState first second
        tape :=
          tapeAtCells
            (List.append (([false, false] : Word Bool).reverse.map some)
              [none])
            (List.append (rest.map some) [none]) } := by
  cases first <;> cases second <;> cases rest <;>
    simp [leftBoundaryGuardSlackShiftDescription,
      leftBoundaryGuardSlackShiftPairState, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop_bit
    (pref rest : Word Bool) (first second current : Bool) :
    leftBoundaryGuardSlackShiftDescription.runConfig 1
        { state := leftBoundaryGuardSlackShiftPairState first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) [none])
              (List.append ((current :: rest).map some) [none]) } =
      { state := leftBoundaryGuardSlackShiftPairState second current
        tape :=
          tapeAtCells
            (List.append ((List.append pref [first]).reverse.map some)
              [none])
            (List.append (rest.map some) [none]) } := by
  cases first <;> cases second <;> cases current <;> cases rest <;>
    simp [leftBoundaryGuardSlackShiftDescription,
      leftBoundaryGuardSlackShiftPairState, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, List.reverse_append]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop_finish
    (pref : Word Bool) (first second : Bool) :
    leftBoundaryGuardSlackShiftDescription.runConfig 2
        { state := leftBoundaryGuardSlackShiftPairState first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) [none]) [none] } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append pref [first, second]).reverse.map some)
              [none])
            [none] } := by
  cases first <;> cases second <;>
    simp [leftBoundaryGuardSlackShiftDescription,
      leftBoundaryGuardSlackShiftPairState,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.reverse_append]

private theorem leftBoundaryGuardSlackShiftDescription_run_loop
    (rest : Word Bool) (pref : Word Bool)
    (first second : Bool) :
    leftBoundaryGuardSlackShiftDescription.runConfig (rest.length + 2)
        { state := leftBoundaryGuardSlackShiftPairState first second
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some) [none])
              (List.append (rest.map some) [none]) } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append pref (first :: second :: rest)).reverse.map some)
              [none])
            [none] } := by
  induction rest generalizing pref first second with
  | nil =>
      simpa [List.append_assoc] using
        leftBoundaryGuardSlackShiftDescription_run_loop_finish
          pref first second
  | cons current rest ih =>
      rw [show (current :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [leftBoundaryGuardSlackShiftDescription_run_loop_bit]
      simpa [List.append_assoc] using
        ih (List.append pref [first]) second current

theorem leftBoundaryGuardSlackShiftDescription_run_to_rightEdge
    (first second : Bool) (rest : Word Bool) :
    leftBoundaryGuardSlackShiftDescription.runConfig
        (3 + (rest.length + 2))
        { state := leftBoundaryGuardSlackShiftDescription.start
          tape :=
            tapeAtCells []
              (none ::
                List.append ((first :: second :: rest).map some) [none]) } =
      { state := leftBoundaryGuardSlackShiftDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append ([false, false] : Word Bool)
                (first :: second :: rest)).reverse.map some)
              [none])
            [none] } := by
  rw [MachineDescription.runConfig_add]
  rw [leftBoundaryGuardSlackShiftDescription_run_initial]
  simpa [List.append_assoc] using
    leftBoundaryGuardSlackShiftDescription_run_loop
      rest ([false, false] : Word Bool) first second

theorem leftBoundaryGuardSlackShiftDescription_haltsFromPayload
    (first second : Bool) (rest : Word Bool) :
    leftBoundaryGuardSlackShiftDescription.HaltsFromTape
      (tapeAtCells []
        (none ::
          List.append ((first :: second :: rest).map some) [none]))
      (tapeAtCells
        (List.append
          ((List.append ([false, false] : Word Bool)
            (first :: second :: rest)).reverse.map some)
          [none])
        [none]) := by
  refine ⟨3 + (rest.length + 2), ?_⟩
  constructor <;>
    rw [leftBoundaryGuardSlackShiftDescription_run_to_rightEdge]

private theorem leftBoundaryGuardSlackShift_rightEdge_equiv_rewindSource
    (bits : Word Bool) :
    Tape.Equiv
      (tapeAtCells (List.append (bits.reverse.map some) [none]) [none])
      (rightEdgeRewindSourceTape bits []) := by
  simp [rightEdgeRewindSourceTape, tapeAtCells, Tape.Equiv,
    dropTrailingNone_append_none]

def leftBoundaryGuardSlackRefreshDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      leftBoundaryGuardSlackShiftDescription
      rightEdgeRewindDescription)
    leftMoveOnceDescription

theorem leftBoundaryGuardSlackRefreshDescription_subroutineReady :
    leftBoundaryGuardSlackRefreshDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      leftBoundaryGuardSlackShiftDescription_subroutineReady
      rightEdgeRewindDescription_subroutineReady)
    leftMoveOnceDescription_subroutineReady

theorem leftBoundaryGuardSlackRefreshDescription_haltsFromPayload
    (first second : Bool) (rest : Word Bool) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (tapeAtCells []
        (none ::
          List.append ((first :: second :: rest).map some) [none]))
      (tapeAtCells []
        (none ::
          List.append
            ((List.append ([false, false] : Word Bool)
              (first :: second :: rest)).map some)
            [none])) := by
  let shifted : Word Bool :=
    List.append ([false, false] : Word Bool) (first :: second :: rest)
  let Tmid : Tape Bool :=
    tapeAtCells (List.append (shifted.reverse.map some) [none]) [none]
  let Trewound : Tape Bool :=
    rightEdgeRewindTargetTape shifted []
  have hshift :
      leftBoundaryGuardSlackShiftDescription.HaltsFromTape
        (tapeAtCells []
          (none ::
            List.append ((first :: second :: rest).map some) [none]))
        Tmid := by
    simpa [Tmid, shifted] using
      leftBoundaryGuardSlackShiftDescription_haltsFromPayload
        first second rest
  have hrewind :
      rightEdgeRewindDescription.HaltsFromTapeEquiv Tmid Trewound := by
    exact
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := rightEdgeRewindDescription)
        (Tin := rightEdgeRewindSourceTape shifted [])
        (Tin' := Tmid)
        (Tout := Trewound)
        (Tape.Equiv.symm
          (leftBoundaryGuardSlackShift_rightEdge_equiv_rewindSource
            shifted))
        (by
          simpa [Trewound] using
            rightEdgeRewindDescription_haltsFromTape shifted [])
  have hshiftThenRewind :
      (canonicalPrimitiveSeqDescription
        leftBoundaryGuardSlackShiftDescription
        rightEdgeRewindDescription).HaltsFromTapeEquiv
          (tapeAtCells []
            (none ::
              List.append ((first :: second :: rest).map some) [none]))
          Trewound :=
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      leftBoundaryGuardSlackShiftDescription_subroutineReady
      rightEdgeRewindDescription_subroutineReady
      (MachineDescription.HaltsFromTape.toEquiv hshift)
      hrewind
  have hleft :
      leftMoveOnceDescription.HaltsFromTape Trewound
        (tapeAtCells []
          (none ::
            List.append (shifted.map some) [none])) := by
    simpa [Trewound, rightEdgeRewindTargetTape, tapeAtCells,
      Tape.move, Tape.moveLeft] using
      leftMoveOnceDescription_haltsFromTape Trewound
  simpa [leftBoundaryGuardSlackRefreshDescription, shifted] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        leftBoundaryGuardSlackShiftDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady)
      leftMoveOnceDescription_subroutineReady
      hshiftThenRewind
      (MachineDescription.HaltsFromTape.toEquiv hleft)

theorem leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundarySlackSingleton
    (head : Option Bool) (right : List (Option Bool)) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv
      (encodedStructuredTapes
        [({ left := [], head := head, right := right } : Tape Bool)])
      (encodedStructuredTapes
        [({ left := [none], head := head, right := right } :
          Tape Bool)]) := by
  simpa [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, logicalTapeBits, logicalCellListBits,
    logicalCellListBits_append, logicalCellBits, tapeSeparatorCells,
    List.map_append, List.append_assoc] using
    leftBoundaryGuardSlackRefreshDescription_haltsFromPayload true true
      (List.append (logicalCellBits head) (logicalCellListBits right))

theorem leftBoundaryGuardSlackRefreshDescription_refreshes_actionPrimitivesAt_zero_left_guardSlackEndpoint_singleton_of_left_nil
    (write? : Option (Option Bool))
    (head : Option Bool) (right : List (Option Bool))
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.left } : TapeAction))
        [({ left := [], head := head, right := right } : Tape Bool)]
        target physical) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  let source : Tape Bool :=
    { left := [], head := head, right := right }
  let action : TapeAction :=
    { write? := write?, move := HeadMove.left }
  let slack : Tape Bool :=
    { left := []
      head := none
      right := tapeActionWrittenHead write? head :: (right ++ [none]) }
  let canonical : Tape Bool :=
    { left := [none]
      head := none
      right := tapeActionWrittenHead write? head :: (right ++ [none]) }
  have hcanonicalEndpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint
        (actionPrimitivesAt 0 action) [source] [action.apply source]
        (encodedStructuredTapes [slack]) := by
    simpa [action, source, slack,
      actionPrimitivesAt_zero_left_guardSlackPhysical_eq_boundaryLeftSlack_singleton]
      using
        actionPrimitivesAt_zero_left_guardSlackEndpoint_singleton
          write? source
  have hphysical : physical = encodedStructuredTapes [slack] :=
    PhysicalPrimitiveSequenceGuardSlackEndpoint.physical_eq
      hendpoint hcanonicalEndpoint
  have htarget : target = [action.apply source] :=
    PhysicalPrimitiveSequenceGuardSlackEndpoint.target_eq
      hendpoint hcanonicalEndpoint
  have hguarded :
      encodedGuardedStructuredTapes [action.apply source] =
        encodedStructuredTapes [canonical] := by
    simpa [action, source, canonical] using
      actionPrimitivesAt_zero_left_guardedTarget_eq_boundaryLeftCanonical_singleton
        write? head right
  rw [hphysical, htarget, hguarded]
  exact
    leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundarySlackSingleton
      slack.head slack.right

theorem leftBoundaryGuardSlackRefreshDescription_refreshes_actionPrimitivesAt_zero_left_guardSlackEndpointEquiv_singleton_of_left_nil
    (write? : Option (Option Bool))
    (head : Option Bool) (right : List (Option Bool))
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv
        (actionPrimitivesAt 0
          ({ write? := write?, move := HeadMove.left } : TapeAction))
        [({ left := [], head := head, right := right } : Tape Bool)]
        target physical) :
    leftBoundaryGuardSlackRefreshDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  rcases hendpoint with ⟨exactPhysical, hexact, hequiv⟩
  rcases
      leftBoundaryGuardSlackRefreshDescription_refreshes_actionPrimitivesAt_zero_left_guardSlackEndpoint_singleton_of_left_nil
        write? head right hexact with
    ⟨actualOut, hhalts, hout⟩
  rcases
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := leftBoundaryGuardSlackRefreshDescription)
        (Tin := exactPhysical)
        (Tin' := physical)
        (Tout := actualOut)
        (Tape.Equiv.symm hequiv)
        hhalts with
    ⟨transportedOut, htransported, htransportedEquiv⟩
  exact
    ⟨transportedOut, htransported,
      Tape.Equiv.trans htransportedEquiv hout⟩

/-- The concrete fixed-index seek routine for tape 0 at block start. -/
def seekTape0Description : MachineDescription :=
  cursorNoopDescription

theorem seekTape0Description_physicalPrimitiveContract :
    PhysicalPrimitiveContract (PhysicalPrimitive.seekTape 0)
      seekTape0Description where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical _henabled
    exact cursorNoopDescription_haltsFromTape
      (encodedStructuredTapes logical)

/-- Guarded-layout version of the fixed tape-0 seek no-op. -/
theorem seekTape0Description_physicalPrimitiveGuardedContract :
    PhysicalPrimitiveGuardedContract (PhysicalPrimitive.seekTape 0)
      seekTape0Description where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical _henabled
    exact cursorNoopDescription_haltsFromTape
      (encodedGuardedStructuredTapes logical)

/-- Return-to-block-start is also a no-op once the caller is already there. -/
def returnBlockStartNoopDescription : MachineDescription :=
  cursorNoopDescription

theorem returnBlockStartNoopDescription_physicalPrimitiveContract :
    PhysicalPrimitiveContract PhysicalPrimitive.returnToBlockStart
      returnBlockStartNoopDescription where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical _henabled
    exact cursorNoopDescription_haltsFromTape
      (encodedStructuredTapes logical)

/-- Guarded-layout version of the block-start no-op. -/
theorem returnBlockStartNoopDescription_physicalPrimitiveGuardedContract :
    PhysicalPrimitiveGuardedContract PhysicalPrimitive.returnToBlockStart
      returnBlockStartNoopDescription where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical _henabled
    exact cursorNoopDescription_haltsFromTape
      (encodedGuardedStructuredTapes logical)


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
