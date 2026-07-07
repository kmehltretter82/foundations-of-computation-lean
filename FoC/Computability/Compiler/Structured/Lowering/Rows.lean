import FoC.Computability.Compiler.Structured.Lowering.CursorBasic
import FoC.Computability.Compiler.Structured.Lowering.PrimitivePipelines

set_option doc.verso true

/-!
# Structured row lowerings
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Concrete row machines
-/

/--
Compatibility exact row machine for a three-tape row whose actions are all
{name}`TapeAction.stay`.

New row-compiler APIs use the guarded/equivalence contracts below.  This
zero-step no-op remains useful as a tight exact baseline and for older helper
theorems that still mention {name}`LowersTransition`.
-/
def stayRow3Description (_t : Transition) : MachineDescription :=
  cursorNoopDescription

/--
Stay-capable version of the all-stay three-tape row machine.

This is intentionally a no-transition stay machine: it validates the
Milestone-8 stay-contract path without changing the existing exact
{lit}`cursorNoopDescription` row.
-/
def stayRow3DescriptionWithStay (_t : Transition) :
    MachineDescriptionWithStay where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem stayRow3DescriptionWithStay_wellFormed
    (t : Transition) :
    (stayRow3DescriptionWithStay t).WellFormed := by
  simp [stayRow3DescriptionWithStay, MachineDescriptionWithStay.WellFormed,
    MachineDescriptionWithStay.Deterministic]

theorem stayRow3DescriptionWithStay_haltTransitionFree
    (t : Transition) :
    (stayRow3DescriptionWithStay t).HaltTransitionFree := by
  intro row hrow
  simp [stayRow3DescriptionWithStay] at hrow

theorem stayRow3DescriptionWithStay_subroutineReady
    (t : Transition) :
    (stayRow3DescriptionWithStay t).SubroutineReady :=
  ⟨stayRow3DescriptionWithStay_wellFormed t,
    stayRow3DescriptionWithStay_haltTransitionFree t⟩

theorem stayRow3DescriptionWithStay_haltsFromTape
    (t : Transition) (T : Tape Bool) :
    (stayRow3DescriptionWithStay t).HaltsFromTape T T := by
  refine ⟨0, ?_⟩
  simp [MachineDescriptionWithStay.HaltsFromTapeIn,
    MachineDescriptionWithStay.runConfig, stayRow3DescriptionWithStay]

theorem stayRow3DescriptionWithStay_compile_subroutineReady
    (t : Transition) :
    (stayRow3DescriptionWithStay t).compile.SubroutineReady := by
  constructor
  · simp [stayRow3DescriptionWithStay, MachineDescriptionWithStay.compile,
      MachineDescriptionWithStay.compileTransitions,
      MachineDescription.WellFormed, MachineDescription.Deterministic]
  · intro row hrow
    simp [stayRow3DescriptionWithStay, MachineDescriptionWithStay.compile,
      MachineDescriptionWithStay.compileTransitions] at hrow

private theorem list_eq_three_of_length_eq_three
    {α : Type u} {xs : List α}
    (h : xs.length = 3) :
    exists a : α, exists b : α, exists c : α,
      xs = [a, b, c] := by
  cases xs with
  | nil =>
      simp at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp at h
      | cons b rest =>
          cases rest with
          | nil =>
              simp at h
          | cons c rest =>
              cases rest with
              | nil =>
                  exact ⟨a, b, c, rfl⟩
              | cons _d _rest =>
                  simp at h

theorem applyActions_three_stay
    (D : Description) (hD : D.tapeCount = 3)
    (T U V : Tape Bool) :
    D.applyActions
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]
        [T, U, V] =
      [T, U, V] := by
  rw [Description.applyActions_three D hD]
  simp [TapeAction.stay, TapeAction.apply, HeadMove.apply]

theorem stayRow3Description_lowersTransition
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersTransition D t (stayRow3Description t) where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro c hc _hsource _hreads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        change
          cursorNoopDescription.HaltsFromTape
            (encodedStructuredTapes [T, U, V])
            (encodedStructuredTapes
              (D.applyActions t.actions [T, U, V]))
        rw [hactions, applyActions_three_stay D hD T U V]
        exact cursorNoopDescription_haltsFromTape
          (encodedStructuredTapes [T, U, V])

theorem stayRow3Description_lowersGuardedTransition
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersGuardedTransition D t (stayRow3Description t) where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro c hc _hsource _hreads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        change
          cursorNoopDescription.HaltsFromTape
            (encodedGuardedStructuredTapes [T, U, V])
            (encodedGuardedStructuredTapes
              (D.applyActions t.actions [T, U, V]))
        rw [hactions, applyActions_three_stay D hD T U V]
        exact cursorNoopDescription_haltsFromTape
          (encodedGuardedStructuredTapes [T, U, V])

theorem stayRow3DescriptionWithStay_lowersTransition
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersTransitionWithStay D t (stayRow3DescriptionWithStay t) where
  subroutineReady := stayRow3DescriptionWithStay_subroutineReady t
  realizes := by
    intro c hc _hsource _hreads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        change
          (stayRow3DescriptionWithStay t).HaltsFromTape
            (encodedStructuredTapes [T, U, V])
            (encodedStructuredTapes
              (D.applyActions t.actions [T, U, V]))
        rw [hactions, applyActions_three_stay D hD T U V]
        exact stayRow3DescriptionWithStay_haltsFromTape t
          (encodedStructuredTapes [T, U, V])

theorem stayRow3DescriptionWithStay_lowersGuardedTransition
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersGuardedTransitionWithStay D t
      (stayRow3DescriptionWithStay t) where
  subroutineReady := stayRow3DescriptionWithStay_subroutineReady t
  realizes := by
    intro c hc _hsource _hreads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        change
          (stayRow3DescriptionWithStay t).HaltsFromTape
            (encodedGuardedStructuredTapes [T, U, V])
            (encodedGuardedStructuredTapes
              (D.applyActions t.actions [T, U, V]))
        rw [hactions, applyActions_three_stay D hD T U V]
        exact stayRow3DescriptionWithStay_haltsFromTape t
          (encodedGuardedStructuredTapes [T, U, V])

theorem stayRow3DescriptionWithStay_lowersTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersTransitionEquiv D t
      ((stayRow3DescriptionWithStay t).compile) :=
  LowersTransitionWithStay.toCompiledEquiv
    (stayRow3DescriptionWithStay_lowersTransition D t hD hactions)
    (stayRow3DescriptionWithStay_compile_subroutineReady t)

theorem stayRow3DescriptionWithStay_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersGuardedTransitionEquiv D t
      ((stayRow3DescriptionWithStay t).compile) :=
  LowersGuardedTransitionWithStay.toCompiledEquiv
    (stayRow3DescriptionWithStay_lowersGuardedTransition
      D t hD hactions)
    (stayRow3DescriptionWithStay_compile_subroutineReady t)

/--
Concrete guarded row lowering for three-tape rows whose actions all use
structured {lit}`stay`, with optional writes on each tape.

This is the first nontrivial guarded row theorem: it checks all three reads,
performs the three optional writes, and returns to the canonical guarded block
boundary.
-/
theorem readWriteStayRow3Description_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionEquiv D t
      (readWriteStayRow3Description read0 read1 read2
        write0? write1? write2?) :=
  let action0 : TapeAction :=
    { write? := write0?, move := HeadMove.stay }
  let action1 : TapeAction :=
    { write? := write1?, move := HeadMove.stay }
  let action2 : TapeAction :=
    { write? := write2?, move := HeadMove.stay }
  have hsequence :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (transitionPrimitiveSequenceOfRow3 t)
        (readWriteStayRow3Description read0 read1 read2
          write0? write1? write2?) := by
    cases t with
    | mk source reads actions target =>
        simp [transitionPrimitiveSequenceOfRow3] at hreads hactions ⊢
        cases hreads
        cases hactions
        exact
          readWriteStayRow3Description_physicalPrimitiveSequenceGuardedContractEquiv
            read0 read1 read2 write0? write1? write2?
  guardedPrimitiveSequence3_lowersGuardedTransitionEquiv
    (hsequence := hsequence)
    hD read0 read1 read2 action0 action1 action2
    hreads hactions

theorem readWriteStayRow3Description_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteStayRow3Description read0 read1 read2
        write0? write1? write2?) :=
  (readWriteStayRow3Description_lowersGuardedTransitionEquiv
    D t hD read0 read1 read2 write0? write1? write2?
    hreads hactions).toLogicalEquiv

/--
Concrete guarded row lowering where tape 0 and tape 1 stay, and tape 2 is the
final local action.

The endpoint uses {name}`LowersGuardedTransitionLogicalEquiv` because the tape
2 action may consume guard slack when it moves left or right.
-/
theorem readWriteStayStayMove2Row3Description_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move2 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := move2 } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteStayStayMove2Row3Description read0 read1 read2
        write0? write1? write2? move2) :=
  let action0 : TapeAction :=
    { write? := write0?, move := HeadMove.stay }
  let action1 : TapeAction :=
    { write? := write1?, move := HeadMove.stay }
  let action2 : TapeAction :=
    { write? := write2?, move := move2 }
  have hsequence :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        (transitionPrimitiveSequenceOfRow3 t)
        (readWriteStayStayMove2Row3Description read0 read1 read2
          write0? write1? write2? move2) := by
    cases t with
    | mk source reads actions target =>
        simp [transitionPrimitiveSequenceOfRow3] at hreads hactions ⊢
        cases hreads
        cases hactions
        exact
          readWriteStayStayMove2Row3Description_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
            read0 read1 read2 write0? write1? write2? move2
  guardedPrimitiveSequence3_lowersGuardedTransitionLogicalEquiv
    (hsequence := hsequence)
    hD read0 read1 read2 action0 action1 action2
    hreads hactions

/--
Concrete guarded row lowering where tape 0 and tape 2 stay, and tape 1 is
scheduled as the final local action.

The physical sequence reorders the independent tape-2 stay action before the
tape-1 action so the only guard-consuming move, if present, is last.
-/
theorem readWriteStayMove1StayRow3Description_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move1 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := move1 }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteStayMove1StayRow3Description read0 read1 read2
        write0? write1? write2? move1) :=
  let action0 : TapeAction :=
    { write? := write0?, move := HeadMove.stay }
  let action1 : TapeAction :=
    { write? := write1?, move := move1 }
  let action2 : TapeAction :=
    { write? := write2?, move := HeadMove.stay }
  have hsequence :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        (transitionPrimitiveSequence3Action1Last read0 read1 read2
          action0 action1 action2)
        (readWriteStayMove1StayRow3Description read0 read1 read2
          write0? write1? write2? move1) :=
    readWriteStayMove1StayRow3Description_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      read0 read1 read2 write0? write1? write2? move1
  primitiveSequence3_lowersGuardedTransitionLogicalEquiv
    (hsequence := hsequence)
    hD read0 read1 read2 action0 action1 action2
    hreads hactions
    (by
      intro T U V hread0 hread1 hread2
      exact
        physicalPrimitiveSequenceEnabled_transitionPrimitiveSequence3Action1Last
          read0 read1 read2 action0 action1 action2
          T U V hread0 hread1 hread2)
    (by
      intro T U V
      exact
        applyPhysicalPrimitiveSequence_transitionPrimitiveSequence3Action1Last
          read0 read1 read2 action0 action1 action2 T U V)

/--
Concrete guarded row lowering where tape 1 and tape 2 stay, and tape 0 is
scheduled as the final local action.
-/
theorem readWriteMove0StayStayRow3Description_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move0 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := move0 }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteMove0StayStayRow3Description read0 read1 read2
        write0? write1? write2? move0) :=
  let action0 : TapeAction :=
    { write? := write0?, move := move0 }
  let action1 : TapeAction :=
    { write? := write1?, move := HeadMove.stay }
  let action2 : TapeAction :=
    { write? := write2?, move := HeadMove.stay }
  have hsequence :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        (transitionPrimitiveSequence3Action0Last read0 read1 read2
          action0 action1 action2)
        (readWriteMove0StayStayRow3Description read0 read1 read2
          write0? write1? write2? move0) :=
    readWriteMove0StayStayRow3Description_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      read0 read1 read2 write0? write1? write2? move0
  primitiveSequence3_lowersGuardedTransitionLogicalEquiv
    (hsequence := hsequence)
    hD read0 read1 read2 action0 action1 action2
    hreads hactions
    (by
      intro T U V hread0 hread1 hread2
      exact
        physicalPrimitiveSequenceEnabled_transitionPrimitiveSequence3Action0Last
          read0 read1 read2 action0 action1 action2
          T U V hread0 hread1 hread2)
    (by
      intro T U V
      exact
        applyPhysicalPrimitiveSequence_transitionPrimitiveSequence3Action0Last
          read0 read1 read2 action0 action1 action2 T U V)

/--
Extract the concrete read/write/stay lowering machine directly from a
transition row.

Rows outside this currently supported fragment map to the no-op placeholder;
the theorem below only exposes this definition under hypotheses proving the
row has three reads and three {lit}`stay` actions.
-/
def readWriteStayRow3DescriptionOfRow
    (t : Transition) : MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? HeadMove.stay
    , TapeAction.mk write1? HeadMove.stay
    , TapeAction.mk write2? HeadMove.stay ] =>
      readWriteStayRow3Description read0 read1 read2
        write0? write1? write2?
  | _, _ => cursorNoopDescription

/--
Row-shaped wrapper for
{name}`readWriteStayRow3Description_lowersGuardedTransitionEquiv`.

This is the API a later row selector can use: the machine is chosen from the
row itself, while the proof only needs to establish that the row lies in the
supported read/write/stay fragment.
-/
theorem readWriteStayRow3DescriptionOfRow_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionEquiv D t
      (readWriteStayRow3DescriptionOfRow t) := by
  cases t with
  | mk source reads actions target =>
      simp [readWriteStayRow3DescriptionOfRow] at hreads hactions ⊢
      cases hreads
      cases hactions
      exact
        readWriteStayRow3Description_lowersGuardedTransitionEquiv
          D
          { source := source
            reads := [read0, read1, read2]
            actions :=
              [ { write? := write0?, move := HeadMove.stay }
              , { write? := write1?, move := HeadMove.stay }
              , { write? := write2?, move := HeadMove.stay } ]
            target := target }
          hD read0 read1 read2 write0? write1? write2?
          rfl rfl

theorem readWriteStayRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteStayRow3DescriptionOfRow t) :=
  (readWriteStayRow3DescriptionOfRow_lowersGuardedTransitionEquiv
    D t hD read0 read1 read2 write0? write1? write2?
    hreads hactions).toLogicalEquiv

/--
Extract the tape-2-final row lowering machine directly from a transition row.

This covers rows whose first two actions stay and whose final tape-2 action is
any local move.  The fallback branch is intentionally opaque; callers only use
this definition under hypotheses proving the row is in the supported fragment.
-/
def readWriteStayStayMove2Row3DescriptionOfRow
    (t : Transition) : MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? HeadMove.stay
    , TapeAction.mk write1? HeadMove.stay
    , TapeAction.mk write2? move2 ] =>
      readWriteStayStayMove2Row3Description read0 read1 read2
        write0? write1? write2? move2
  | _, _ => cursorNoopDescription

theorem readWriteStayStayMove2Row3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move2 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := move2 } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteStayStayMove2Row3DescriptionOfRow t) := by
  cases t with
  | mk source reads actions target =>
      simp [readWriteStayStayMove2Row3DescriptionOfRow]
        at hreads hactions ⊢
      cases hreads
      cases hactions
      exact
        readWriteStayStayMove2Row3Description_lowersGuardedTransitionLogicalEquiv
          D
          { source := source
            reads := [read0, read1, read2]
            actions :=
              [ { write? := write0?, move := HeadMove.stay }
              , { write? := write1?, move := HeadMove.stay }
              , { write? := write2?, move := move2 } ]
            target := target }
          hD read0 read1 read2 write0? write1? write2?
          move2 rfl rfl

/--
Extract the tape-1-final row lowering machine directly from a transition row.
-/
def readWriteStayMove1StayRow3DescriptionOfRow
    (t : Transition) : MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? HeadMove.stay
    , TapeAction.mk write1? move1
    , TapeAction.mk write2? HeadMove.stay ] =>
      readWriteStayMove1StayRow3Description read0 read1 read2
        write0? write1? write2? move1
  | _, _ => cursorNoopDescription

theorem readWriteStayMove1StayRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move1 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := move1 }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteStayMove1StayRow3DescriptionOfRow t) := by
  cases t with
  | mk source reads actions target =>
      simp [readWriteStayMove1StayRow3DescriptionOfRow]
        at hreads hactions ⊢
      cases hreads
      cases hactions
      exact
        readWriteStayMove1StayRow3Description_lowersGuardedTransitionLogicalEquiv
          D
          { source := source
            reads := [read0, read1, read2]
            actions :=
              [ { write? := write0?, move := HeadMove.stay }
              , { write? := write1?, move := move1 }
              , { write? := write2?, move := HeadMove.stay } ]
            target := target }
          hD read0 read1 read2 write0? write1? write2?
          move1 rfl rfl

/--
Extract the tape-0-final row lowering machine directly from a transition row.
-/
def readWriteMove0StayStayRow3DescriptionOfRow
    (t : Transition) : MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? move0
    , TapeAction.mk write1? HeadMove.stay
    , TapeAction.mk write2? HeadMove.stay ] =>
      readWriteMove0StayStayRow3Description read0 read1 read2
        write0? write1? write2? move0
  | _, _ => cursorNoopDescription

theorem readWriteMove0StayStayRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move0 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := move0 }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteMove0StayStayRow3DescriptionOfRow t) := by
  cases t with
  | mk source reads actions target =>
      simp [readWriteMove0StayStayRow3DescriptionOfRow]
        at hreads hactions ⊢
      cases hreads
      cases hactions
      exact
        readWriteMove0StayStayRow3Description_lowersGuardedTransitionLogicalEquiv
          D
          { source := source
            reads := [read0, read1, read2]
            actions :=
              [ { write? := write0?, move := move0 }
              , { write? := write1?, move := HeadMove.stay }
              , { write? := write2?, move := HeadMove.stay } ]
            target := target }
          hD read0 read1 read2 write0? write1? write2?
          move0 rfl rfl

/--
Row selector for the currently supported guarded three-tape fragment.

The supported fragment allows all three actions to stay, or exactly one tape
to use an arbitrary local move while the other two stay.  Non-supported rows
map to a no-op placeholder; the theorems below expose this selector only under
shape hypotheses proving the row is supported.
-/
def readWriteSingleMoveRow3DescriptionOfRow
    (t : Transition) : MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? HeadMove.stay
    , TapeAction.mk write1? HeadMove.stay
    , TapeAction.mk write2? HeadMove.stay ] =>
      readWriteStayRow3Description read0 read1 read2
        write0? write1? write2?
  | [read0, read1, read2],
    [ TapeAction.mk write0? move0
    , TapeAction.mk write1? HeadMove.stay
    , TapeAction.mk write2? HeadMove.stay ] =>
      readWriteMove0StayStayRow3Description read0 read1 read2
        write0? write1? write2? move0
  | [read0, read1, read2],
    [ TapeAction.mk write0? HeadMove.stay
    , TapeAction.mk write1? move1
    , TapeAction.mk write2? HeadMove.stay ] =>
      readWriteStayMove1StayRow3Description read0 read1 read2
        write0? write1? write2? move1
  | [read0, read1, read2],
    [ TapeAction.mk write0? HeadMove.stay
    , TapeAction.mk write1? HeadMove.stay
    , TapeAction.mk write2? move2 ] =>
      readWriteStayStayMove2Row3Description read0 read1 read2
        write0? write1? write2? move2
  | _, _ => cursorNoopDescription

/--
Shape predicate for the currently implemented three-tape row fragment.

The row may have optional writes on every tape.  At most one tape may perform
a non-stay move; that moving tape is scheduled last by the selected physical
row machine.
-/
inductive SupportedSingleMoveRow3
    (t : Transition) : Prop where
  | move0
      (read0 read1 read2 : Option Bool)
      (write0? write1? write2? : Option (Option Bool))
      (move0 : HeadMove)
      (hreads : t.reads = [read0, read1, read2])
      (hactions :
        t.actions =
          [ { write? := write0?, move := move0 }
          , { write? := write1?, move := HeadMove.stay }
          , { write? := write2?, move := HeadMove.stay } ]) :
      SupportedSingleMoveRow3 t
  | move1
      (read0 read1 read2 : Option Bool)
      (write0? write1? write2? : Option (Option Bool))
      (move1 : HeadMove)
      (hreads : t.reads = [read0, read1, read2])
      (hactions :
        t.actions =
          [ { write? := write0?, move := HeadMove.stay }
          , { write? := write1?, move := move1 }
          , { write? := write2?, move := HeadMove.stay } ]) :
      SupportedSingleMoveRow3 t
  | move2
      (read0 read1 read2 : Option Bool)
      (write0? write1? write2? : Option (Option Bool))
      (move2 : HeadMove)
      (hreads : t.reads = [read0, read1, read2])
      (hactions :
        t.actions =
          [ { write? := write0?, move := HeadMove.stay }
          , { write? := write1?, move := HeadMove.stay }
          , { write? := write2?, move := move2 } ]) :
      SupportedSingleMoveRow3 t

/-- Boolean recognizer for {name}`SupportedSingleMoveRow3`. -/
def supportsSingleMoveRow3
    (t : Transition) : Bool :=
  match t.reads, t.actions with
  | [_read0, _read1, _read2],
    [ TapeAction.mk _write0? move0
    , TapeAction.mk _write1? move1
    , TapeAction.mk _write2? move2 ] =>
      match move0, move1, move2 with
      | _, HeadMove.stay, HeadMove.stay => true
      | HeadMove.stay, _, HeadMove.stay => true
      | HeadMove.stay, HeadMove.stay, _ => true
      | _, _, _ => false
  | _, _ => false

theorem supportsSingleMoveRow3_eq_true_of_supported
    {t : Transition}
    (h : SupportedSingleMoveRow3 t) :
    supportsSingleMoveRow3 t = true := by
  cases h with
  | move0 read0 read1 read2 write0? write1? write2? move0 hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [supportsSingleMoveRow3] at hreads hactions ⊢
          cases hreads
          cases hactions
          cases move0 <;> rfl
  | move1 read0 read1 read2 write0? write1? write2? move1 hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [supportsSingleMoveRow3] at hreads hactions ⊢
          cases hreads
          cases hactions
          cases move1 <;> rfl
  | move2 read0 read1 read2 write0? write1? write2? move2 hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [supportsSingleMoveRow3] at hreads hactions ⊢
          cases hreads
          cases hactions
          cases move2 <;> rfl

theorem supportedSingleMoveRow3_of_supports_eq_true
    {t : Transition}
    (h : supportsSingleMoveRow3 t = true) :
    SupportedSingleMoveRow3 t := by
  cases t with
  | mk source reads actions target =>
      cases reads with
      | nil =>
          simp [supportsSingleMoveRow3] at h
      | cons read0 reads1 =>
          cases reads1 with
          | nil =>
              simp [supportsSingleMoveRow3] at h
          | cons read1 reads2 =>
              cases reads2 with
              | nil =>
                  simp [supportsSingleMoveRow3] at h
              | cons read2 reads3 =>
                  cases reads3 with
                  | nil =>
                      cases actions with
                      | nil =>
                          simp [supportsSingleMoveRow3] at h
                      | cons action0 actions1 =>
                          cases action0 with
                          | mk write0? move0 =>
                              cases actions1 with
                              | nil =>
                                  simp [supportsSingleMoveRow3] at h
                              | cons action1 actions2 =>
                                  cases action1 with
                                  | mk write1? move1 =>
                                      cases actions2 with
                                      | nil =>
                                          simp [supportsSingleMoveRow3] at h
                                      | cons action2 actions3 =>
                                          cases action2 with
                                          | mk write2? move2 =>
                                              cases actions3 with
                                              | nil =>
                                                  cases move0 <;>
                                                    cases move1 <;>
                                                      cases move2 <;>
                                                        simp [supportsSingleMoveRow3] at h ⊢
                                                  all_goals
                                                    first
                                                    | exact
                                                        SupportedSingleMoveRow3.move0
                                                          read0 read1 read2
                                                          write0? write1?
                                                          write2? HeadMove.stay
                                                          rfl rfl
                                                    | exact
                                                        SupportedSingleMoveRow3.move0
                                                          read0 read1 read2
                                                          write0? write1?
                                                          write2? HeadMove.left
                                                          rfl rfl
                                                    | exact
                                                        SupportedSingleMoveRow3.move0
                                                          read0 read1 read2
                                                          write0? write1?
                                                          write2? HeadMove.right
                                                          rfl rfl
                                                    | exact
                                                        SupportedSingleMoveRow3.move1
                                                          read0 read1 read2
                                                          write0? write1?
                                                          write2? HeadMove.left
                                                          rfl rfl
                                                    | exact
                                                        SupportedSingleMoveRow3.move1
                                                          read0 read1 read2
                                                          write0? write1?
                                                          write2? HeadMove.right
                                                          rfl rfl
                                                    | exact
                                                        SupportedSingleMoveRow3.move2
                                                          read0 read1 read2
                                                          write0? write1?
                                                          write2? HeadMove.left
                                                          rfl rfl
                                                    | exact
                                                        SupportedSingleMoveRow3.move2
                                                          read0 read1 read2
                                                          write0? write1?
                                                          write2? HeadMove.right
                                                          rfl rfl
                                              | cons _ _ =>
                                                  simp [supportsSingleMoveRow3] at h
                  | cons _ _ =>
                      simp [supportsSingleMoveRow3] at h

theorem supportsSingleMoveRow3_eq_true_iff
    (t : Transition) :
    supportsSingleMoveRow3 t = true ↔
      SupportedSingleMoveRow3 t :=
  ⟨supportedSingleMoveRow3_of_supports_eq_true,
    supportsSingleMoveRow3_eq_true_of_supported⟩

theorem readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_move0
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move0 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := move0 }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRow t) := by
  cases move0 with
  | stay =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteStayRow3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.stay }
                  , { write? := write1?, move := HeadMove.stay }
                  , { write? := write2?, move := HeadMove.stay } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              rfl rfl
  | left =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteMove0StayStayRow3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.left }
                  , { write? := write1?, move := HeadMove.stay }
                  , { write? := write2?, move := HeadMove.stay } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              HeadMove.left rfl rfl
  | right =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteMove0StayStayRow3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.right }
                  , { write? := write1?, move := HeadMove.stay }
                  , { write? := write2?, move := HeadMove.stay } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              HeadMove.right rfl rfl

theorem readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_move1
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move1 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := move1 }
        , { write? := write2?, move := HeadMove.stay } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRow t) := by
  cases move1 with
  | stay =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteStayRow3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.stay }
                  , { write? := write1?, move := HeadMove.stay }
                  , { write? := write2?, move := HeadMove.stay } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              rfl rfl
  | left =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteStayMove1StayRow3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.stay }
                  , { write? := write1?, move := HeadMove.left }
                  , { write? := write2?, move := HeadMove.stay } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              HeadMove.left rfl rfl
  | right =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteStayMove1StayRow3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.stay }
                  , { write? := write1?, move := HeadMove.right }
                  , { write? := write2?, move := HeadMove.stay } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              HeadMove.right rfl rfl

theorem readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_move2
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move2 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := HeadMove.stay }
        , { write? := write1?, move := HeadMove.stay }
        , { write? := write2?, move := move2 } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRow t) := by
  cases move2 with
  | stay =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteStayRow3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.stay }
                  , { write? := write1?, move := HeadMove.stay }
                  , { write? := write2?, move := HeadMove.stay } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              rfl rfl
  | left =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteStayStayMove2Row3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.stay }
                  , { write? := write1?, move := HeadMove.stay }
                  , { write? := write2?, move := HeadMove.left } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              HeadMove.left rfl rfl
  | right =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteSingleMoveRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteStayStayMove2Row3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := HeadMove.stay }
                  , { write? := write1?, move := HeadMove.stay }
                  , { write? := write2?, move := HeadMove.right } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              HeadMove.right rfl rfl

theorem readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : SupportedSingleMoveRow3 t) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRow t) := by
  cases hsupported with
  | move0 read0 read1 read2 write0? write1? write2? move0 hreads hactions =>
      exact
        readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_move0
          D t hD read0 read1 read2 write0? write1? write2?
          move0 hreads hactions
  | move1 read0 read1 read2 write0? write1? write2? move1 hreads hactions =>
      exact
        readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_move1
          D t hD read0 read1 read2 write0? write1? write2?
          move1 hreads hactions
  | move2 read0 read1 read2 write0? write1? write2? move2 hreads hactions =>
      exact
        readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_move2
          D t hD read0 read1 read2 write0? write1? write2?
          move2 hreads hactions

theorem readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_of_supports
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : supportsSingleMoveRow3 t = true) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRow t) :=
  readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
    D t hD (supportedSingleMoveRow3_of_supports_eq_true hsupported)

/--
Supported row selector followed by an explicit guard-refresh normalizer.

This is the canonical guarded row machine to use when later composition needs
the next row to start from the canonical guarded layout.
-/
def readWriteSingleMoveRow3DescriptionOfRowWithRefresh
    (t : Transition) (refresh : MachineDescription) :
    MachineDescription :=
  guardedLogicalEquivThenRefreshDescription
    (readWriteSingleMoveRow3DescriptionOfRow t)
    refresh

theorem readWriteSingleMoveRow3DescriptionOfRowWithRefresh_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : SupportedSingleMoveRow3 t)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRowWithRefresh t refresh) := by
  simpa [readWriteSingleMoveRow3DescriptionOfRowWithRefresh] using
    lowersGuardedTransitionLogicalEquiv_thenRefresh
      (readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
        D t hD hsupported)
      hrefresh

theorem readWriteSingleMoveRow3DescriptionOfRowWithRefresh_lowersGuardedTransitionEquiv_of_supports
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : supportsSingleMoveRow3 t = true)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRowWithRefresh t refresh) :=
  readWriteSingleMoveRow3DescriptionOfRowWithRefresh_lowersGuardedTransitionEquiv
    D t hD
    (supportedSingleMoveRow3_of_supports_eq_true hsupported)
    hrefresh

/--
Description-level support predicate for the current row compiler fragment.

This is the table-level hypothesis a later run lowerer can use before there is
a full compiler for arbitrary three-tape rows.
-/
structure SupportsSingleMoveRows3
    (D : Description) : Prop where
  tapeCount_eq : D.tapeCount = 3
  rows_supported :
    forall t : Transition,
      t ∈ D.transitions ->
        supportsSingleMoveRow3 t = true

/--
Boolean recognizer for descriptions covered by the current three-tape row
compiler.

This is the data-facing entry point for the guarded row-lowering path: once it
is true, every selected row has a guarded/equivalence machine through
{name}`readWriteSingleMoveRow3DescriptionOfRow`.
-/
def supportsSingleMoveRows3
    (D : Description) : Bool :=
  if D.tapeCount = 3 then
    D.transitions.all supportsSingleMoveRow3
  else
    false

theorem supportsSingleMoveRows3_eq_true_of_supported
    {D : Description}
  (hD : SupportsSingleMoveRows3 D) :
    supportsSingleMoveRows3 D = true := by
  simp [supportsSingleMoveRows3, hD.tapeCount_eq]
  exact hD.rows_supported

theorem supportedSingleMoveRows3_of_supports_eq_true
    {D : Description}
    (hD : supportsSingleMoveRows3 D = true) :
    SupportsSingleMoveRows3 D := by
  by_cases htapes : D.tapeCount = 3
  · have hrows :
        D.transitions.all supportsSingleMoveRow3 = true := by
      simpa [supportsSingleMoveRows3, htapes] using hD
    exact
      { tapeCount_eq := htapes
        rows_supported := by
          intro t ht
          exact List.all_eq_true.mp hrows t ht }
  · simp [supportsSingleMoveRows3, htapes] at hD

theorem supportsSingleMoveRows3_eq_true_iff
    (D : Description) :
    supportsSingleMoveRows3 D = true ↔
      SupportsSingleMoveRows3 D :=
  ⟨supportedSingleMoveRows3_of_supports_eq_true,
    supportsSingleMoveRows3_eq_true_of_supported⟩

theorem SupportsSingleMoveRows3.row_lowersGuardedTransitionLogicalEquiv
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    {t : Transition} (ht : t ∈ D.transitions) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRow t) :=
  readWriteSingleMoveRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_of_supports
    D t hD.tapeCount_eq (hD.rows_supported t ht)

theorem SupportsSingleMoveRows3.lookup_lowersGuardedTransitionLogicalEquiv
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRow t) :=
  hD.row_lowersGuardedTransitionLogicalEquiv
    (Description.lookupTransition_mem hlookup)

theorem SupportsSingleMoveRows3.row_lowersGuardedTransitionEquiv_withRefresh
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    {t : Transition} (ht : t ∈ D.transitions)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRowWithRefresh t refresh) :=
  readWriteSingleMoveRow3DescriptionOfRowWithRefresh_lowersGuardedTransitionEquiv_of_supports
    D t hD.tapeCount_eq (hD.rows_supported t ht) hrefresh

theorem SupportsSingleMoveRows3.lookup_lowersGuardedTransitionEquiv_withRefresh
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRowWithRefresh t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withRefresh
    (Description.lookupTransition_mem hlookup) hrefresh

theorem lookup_lowersGuardedTransitionLogicalEquiv_of_supportsSingleMoveRows3
    {D : Description}
    (hD : supportsSingleMoveRows3 D = true)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t) :
    LowersGuardedTransitionLogicalEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRow t) :=
  (supportedSingleMoveRows3_of_supports_eq_true hD)
    |>.lookup_lowersGuardedTransitionLogicalEquiv hlookup

theorem lookup_lowersGuardedTransitionEquiv_withRefresh_of_supportsSingleMoveRows3
    {D : Description}
    (hD : supportsSingleMoveRows3 D = true)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteSingleMoveRow3DescriptionOfRowWithRefresh t refresh) :=
  (supportedSingleMoveRows3_of_supports_eq_true hD)
    |>.lookup_lowersGuardedTransitionEquiv_withRefresh hlookup hrefresh

theorem SupportsSingleMoveRows3.lookup_realizes_structured_step_withRefresh
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    {c next : Configuration} {t : Transition}
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    D.stepConfig c = some next ∧
      (readWriteSingleMoveRow3DescriptionOfRowWithRefresh
        t refresh).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes next.tapes) :=
  lowersGuardedTransitionEquiv_realizes_structured_step
    (hD.lookup_lowersGuardedTransitionEquiv_withRefresh
      hlookup hrefresh)
    hc hlookup hnext

theorem SupportsSingleMoveRows3.stepConfig_realizes_structured_step_withRefresh
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readWriteSingleMoveRow3DescriptionOfRowWithRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) := by
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [Description.stepConfig, hlookup] at hstep
  | some t =>
      have hstepLookup :
          D.stepConfig c =
            some (structuredTransitionTarget D t c) :=
        stepConfig_eq_some_of_lookupTransition hlookup
      have hnext : next = structuredTransitionTarget D t c := by
        rw [hstep] at hstepLookup
        exact Option.some.inj hstepLookup
      have hreal :=
        hD.lookup_realizes_structured_step_withRefresh
          hc hlookup hnext hrefresh
      exact ⟨t, rfl, hnext, hreal.right⟩

theorem stepConfig_realizes_structured_step_withRefresh_of_supportsSingleMoveRows3
    {D : Description}
    (hD : supportsSingleMoveRows3 D = true)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readWriteSingleMoveRow3DescriptionOfRowWithRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) :=
  (supportedSingleMoveRows3_of_supports_eq_true hD)
    |>.stepConfig_realizes_structured_step_withRefresh
      hc hstep hrefresh

theorem SupportsSingleMoveRows3.lookup_realizes_structured_step
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    {c next : Configuration} {t : Transition}
    (hstate : next.state < D.stateCount)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      exists physical : Tape Bool,
        StructuredLogicalEquivEncodedConfig D next physical ∧
          (readWriteSingleMoveRow3DescriptionOfRow t).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            physical :=
  let hstep :=
    lowersGuardedTransitionLogicalEquiv_realizes_structured_step
      (hD.lookup_lowersGuardedTransitionLogicalEquiv hlookup)
      hc hlookup hnext
  ⟨hstep.left, by
    rcases hstep.right with
      ⟨physical, hphysical, hhalts⟩
    exact
      ⟨physical,
        ⟨hstate, Description.stepConfig_tape_count hstep.left, hphysical⟩,
        hhalts⟩⟩

theorem SupportsSingleMoveRows3.lookup_realizes_structured_step_of_wellFormed
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    (hwellFormed : D.WellFormed)
    {c next : Configuration} {t : Transition}
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      exists physical : Tape Bool,
        StructuredLogicalEquivEncodedConfig D next physical ∧
          (readWriteSingleMoveRow3DescriptionOfRow t).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            physical :=
  let hstep := stepConfig_eq_some_of_lookupTransition hlookup
  hD.lookup_realizes_structured_step
    (Description.stepConfig_state_bound hwellFormed (by
      rw [hnext]
      exact hstep))
    hc hlookup hnext

theorem SupportsSingleMoveRows3.stepConfig_realizes_structured_step
    {D : Description} (hD : SupportsSingleMoveRows3 D)
    (hwellFormed : D.WellFormed)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          exists physical : Tape Bool,
            StructuredLogicalEquivEncodedConfig D next physical ∧
              (readWriteSingleMoveRow3DescriptionOfRow t).HaltsFromTapeEquiv
                (encodedGuardedStructuredTapes c.tapes)
                physical := by
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [Description.stepConfig, hlookup] at hstep
  | some t =>
      have hstepLookup :
          D.stepConfig c =
            some (structuredTransitionTarget D t c) :=
        stepConfig_eq_some_of_lookupTransition hlookup
      have hnext : next = structuredTransitionTarget D t c := by
        rw [hstep] at hstepLookup
        exact Option.some.inj hstepLookup
      have hreal :=
        hD.lookup_realizes_structured_step_of_wellFormed
          hwellFormed hc hlookup hnext
      exact ⟨t, rfl, hnext, hreal.right⟩

theorem stepConfig_realizes_structured_step_of_supportsSingleMoveRows3
    {D : Description}
    (hD : supportsSingleMoveRows3 D = true)
    (hwellFormed : D.WellFormed)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          exists physical : Tape Bool,
            StructuredLogicalEquivEncodedConfig D next physical ∧
              (readWriteSingleMoveRow3DescriptionOfRow t).HaltsFromTapeEquiv
                (encodedGuardedStructuredTapes c.tapes)
                physical :=
  (supportedSingleMoveRows3_of_supports_eq_true hD)
    |>.stepConfig_realizes_structured_step hwellFormed hc hstep
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
