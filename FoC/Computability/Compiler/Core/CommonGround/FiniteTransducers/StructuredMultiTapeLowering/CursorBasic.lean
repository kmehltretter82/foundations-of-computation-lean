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
