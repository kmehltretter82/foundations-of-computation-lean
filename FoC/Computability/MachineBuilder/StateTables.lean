import FoC.Computability.Encoding
import FoC.Computability.Program

set_option doc.verso true

/-!
# Machine-description construction tools

This module collects the low-level ingredients needed for the remaining
Chapter 5 Section 5.2 finite compiler constructions.  The definitions here are
still ordinary first-order data over {lit}`MachineDescription`: state offsets,
finite tape/configuration codes, and executable bounded searches over the
interpreter.

The bounded search layer is not yet a one-tape transition table.  It is the
checked executable specification that such a transition table must implement:
for fixed recognizer descriptions, it computes exactly the same finite-stage
answers as the staged dovetailer.
-/

namespace FoC
namespace Computability

open Languages

namespace TransitionDescription

/-!
## State offsets

State offsets are the basic operation behind disjoint unions and larger machine
builders.  They rename source and target states while preserving the read/write
action.
-/

def offsetStates (offset : Nat) (t : TransitionDescription) :
    TransitionDescription where
  source := offset + t.source
  read := t.read
  write := t.write
  move := t.move
  target := offset + t.target

theorem offsetStates_sameAction
    (offset : Nat) (t u : TransitionDescription)
    (h : SameAction t u) :
    SameAction (offsetStates offset t) (offsetStates offset u) := by
  rcases h with ⟨hwrite, hmove, htarget⟩
  simp [SameAction, offsetStates, hwrite, hmove, htarget]

theorem sameKey_of_offsetStates_sameKey
    {offset : Nat} {t u : TransitionDescription}
    (h : SameKey (offsetStates offset t) (offsetStates offset u)) :
    SameKey t u := by
  constructor
  · exact Nat.add_left_cancel h.left
  · exact h.right

theorem wellFormed_offsetStates
    {stateCount offset : Nat} {t : TransitionDescription}
    (h : WellFormed stateCount t) :
    WellFormed (offset + stateCount) (offsetStates offset t) := by
  constructor
  · exact Nat.add_lt_add_left h.left offset
  · exact Nat.add_lt_add_left h.right offset

end TransitionDescription

namespace MachineDescription

/-!
## Description-level state extension

The first builder keeps a transition table unchanged while reserving extra
states above it.  This is useful for adding controller states around an existing
machine without changing the old state numbers.
-/

def extendStates (extra : Nat) (D : MachineDescription) :
    MachineDescription where
  stateCount := D.stateCount + extra
  start := D.start
  halt := D.halt
  transitions := D.transitions

def HaltTransitionFree (D : MachineDescription) : Prop :=
  forall t : TransitionDescription, t ∈ D.transitions -> t.source ≠ D.halt

def SubroutineReady (D : MachineDescription) : Prop :=
  D.WellFormed ∧ D.HaltTransitionFree

theorem extendStates_wellFormed
    {extra : Nat} {D : MachineDescription}
    (hD : D.WellFormed) :
    (extendStates extra D).WellFormed := by
  constructor
  · have hpos : 0 < D.stateCount := hD.left
    change 0 < D.stateCount + extra
    omega
  constructor
  · exact Nat.lt_add_right extra hD.right.left
  constructor
  · exact Nat.lt_add_right extra hD.right.right.left
  constructor
  · intro t ht
    have htD := hD.right.right.right.left t ht
    constructor
    · exact Nat.lt_add_right extra htD.left
    · exact Nat.lt_add_right extra htD.right
  · intro t u ht hu hkey
    exact hD.right.right.right.right t u ht hu hkey

theorem extendStates_haltTransitionFree
    {extra : Nat} {D : MachineDescription}
    (hD : D.HaltTransitionFree) :
    (extendStates extra D).HaltTransitionFree :=
  hD

theorem extendStates_subroutineReady
    {extra : Nat} {D : MachineDescription}
    (hD : D.SubroutineReady) :
    (extendStates extra D).SubroutineReady :=
  ⟨extendStates_wellFormed hD.left,
    extendStates_haltTransitionFree hD.right⟩

theorem lookupTransition_halt_none
    {D : MachineDescription}
    (hD : D.HaltTransitionFree) (cell : Option Bool) :
    D.lookupTransition D.halt cell = none := by
  unfold lookupTransition
  apply (List.find?_eq_none).mpr
  intro t ht
  by_cases hs : t.source = D.halt
  · exact False.elim (hD t ht hs)
  · simp [Matches, hs]

theorem stepConfig_halt_none
    {D : MachineDescription}
    (hD : D.HaltTransitionFree) (T : Tape Bool) :
    D.stepConfig { state := D.halt, tape := T } = none := by
  simp [stepConfig, lookupTransition_halt_none hD]

theorem runConfig_halt
    {D : MachineDescription}
    (hD : D.HaltTransitionFree) (T : Tape Bool) :
    forall n : Nat,
      D.runConfig n { state := D.halt, tape := T } =
        { state := D.halt, tape := T }
  | 0 => rfl
  | n + 1 => by
      simp [runConfig, stepConfig_halt_none hD T]

/-!
## State-block offsets

The second builder moves a whole description into a higher state block.  The
proof preserves well-formedness and determinism, so later compiler code can
reuse a recognizer table inside a larger controller table.
-/

def offsetStates (offset : Nat) (D : MachineDescription) :
    MachineDescription where
  stateCount := offset + D.stateCount
  start := offset + D.start
  halt := offset + D.halt
  transitions := D.transitions.map
    (TransitionDescription.offsetStates offset)

theorem offsetStates_wellFormed
    {offset : Nat} {D : MachineDescription}
    (hD : D.WellFormed) :
    (offsetStates offset D).WellFormed := by
  constructor
  · have hpos : 0 < D.stateCount := hD.left
    change 0 < offset + D.stateCount
    omega
  constructor
  · exact Nat.add_lt_add_left hD.right.left offset
  constructor
  · exact Nat.add_lt_add_left hD.right.right.left offset
  constructor
  · intro t ht
    simp [offsetStates] at ht
    rcases ht with ⟨base, hbase, rfl⟩
    exact TransitionDescription.wellFormed_offsetStates
      (hD.right.right.right.left base hbase)
  · intro t u ht hu hkey
    simp [offsetStates] at ht hu
    rcases ht with ⟨baseT, hbaseT, rfl⟩
    rcases hu with ⟨baseU, hbaseU, rfl⟩
    exact TransitionDescription.offsetStates_sameAction offset baseT baseU
      (hD.right.right.right.right baseT baseU hbaseT hbaseU
        (TransitionDescription.sameKey_of_offsetStates_sameKey hkey))

theorem offsetStates_haltTransitionFree
    {offset : Nat} {D : MachineDescription}
    (hD : D.HaltTransitionFree) :
    (offsetStates offset D).HaltTransitionFree := by
  intro t ht
  simp [offsetStates] at ht
  rcases ht with ⟨base, hbase, rfl⟩
  intro hsource
  exact hD base hbase (Nat.add_left_cancel hsource)

theorem offsetStates_subroutineReady
    {offset : Nat} {D : MachineDescription}
    (hD : D.SubroutineReady) :
    (offsetStates offset D).SubroutineReady :=
  ⟨offsetStates_wellFormed hD.left,
    offsetStates_haltTransitionFree hD.right⟩

/-!
## Disjoint table unions

Disjoint union places a second transition table above the state range of the
first.  The constructor does not add controller edges; it is the checked
renaming/combination primitive that later sequencing and branching builders can
use.
-/

def disjointUnion (A B : MachineDescription) :
    MachineDescription where
  stateCount := A.stateCount + B.stateCount
  start := A.start
  halt := A.halt
  transitions :=
    A.transitions ++
      B.transitions.map
        (TransitionDescription.offsetStates A.stateCount)

theorem disjointUnion_wellFormed
    {A B : MachineDescription}
    (hA : A.WellFormed) (hB : B.WellFormed) :
    (disjointUnion A B).WellFormed := by
  constructor
  · have hpos : 0 < A.stateCount := hA.left
    change 0 < A.stateCount + B.stateCount
    omega
  constructor
  · exact Nat.lt_add_right B.stateCount hA.right.left
  constructor
  · exact Nat.lt_add_right B.stateCount hA.right.right.left
  constructor
  · intro t ht
    simp [disjointUnion] at ht
    cases ht with
    | inl hleft =>
        have htA := hA.right.right.right.left t hleft
        constructor
        · exact Nat.lt_add_right B.stateCount htA.left
        · exact Nat.lt_add_right B.stateCount htA.right
    | inr hright =>
        rcases hright with ⟨base, hbase, rfl⟩
        exact TransitionDescription.wellFormed_offsetStates
          (hB.right.right.right.left base hbase)
  · intro t u ht hu hkey
    simp [disjointUnion] at ht hu
    cases ht with
    | inl htA =>
        cases hu with
        | inl huA =>
            exact hA.right.right.right.right t u htA huA hkey
        | inr huB =>
            rcases huB with ⟨baseU, hbaseU, rfl⟩
            have htBound := (hA.right.right.right.left t htA).left
            have hsource : t.source = A.stateCount + baseU.source :=
              hkey.left
            omega
    | inr htB =>
        rcases htB with ⟨baseT, hbaseT, rfl⟩
        cases hu with
        | inl huA =>
            have huBound := (hA.right.right.right.left u huA).left
            have hsource : A.stateCount + baseT.source = u.source :=
              hkey.left
            omega
        | inr huB =>
            rcases huB with ⟨baseU, hbaseU, rfl⟩
            exact
              TransitionDescription.offsetStates_sameAction
                A.stateCount baseT baseU
                (hB.right.right.right.right baseT baseU
                  hbaseT hbaseU
                  (TransitionDescription.sameKey_of_offsetStates_sameKey
                    hkey))

theorem disjointUnion_haltTransitionFree
    {A B : MachineDescription}
    (hAFormed : A.WellFormed)
    (hA : A.HaltTransitionFree) :
    (disjointUnion A B).HaltTransitionFree := by
  intro t ht
  simp [disjointUnion] at ht
  cases ht with
  | inl htA =>
      exact hA t htA
  | inr htB =>
      rcases htB with ⟨base, _hbase, rfl⟩
      intro hsource
      have hhalt : A.halt < A.stateCount := hAFormed.right.right.left
      have hsourceEq : A.stateCount + base.source = A.halt := by
        simpa [TransitionDescription.offsetStates, disjointUnion] using
          hsource
      omega

theorem disjointUnion_subroutineReady
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.WellFormed) :
    (disjointUnion A B).SubroutineReady :=
  ⟨disjointUnion_wellFormed hA.left hB,
    disjointUnion_haltTransitionFree hA.left hA.right⟩

/-!
## Transition-fragment DSL

The simulator compiler will be assembled from small tables rather than raw
transition lists.  The primitives here are intentionally modest: single
read/write/move actions, cell-preserving branches, self-loops, and verified
finite fragments with an entry and exit state.
-/

def preserveCell (cell : Option Bool) : Option Bool :=
  cell

def transition (source : Nat) (read write : Option Bool)
    (move : Direction) (target : Nat) : TransitionDescription where
  source := source
  read := read
  write := write
  move := move
  target := target

def preserveTransition (source : Nat) (read : Option Bool)
    (move : Direction) (target : Nat) : TransitionDescription :=
  transition source read (preserveCell read) move target

def branchOnCell (source blankTarget falseTarget trueTarget : Nat)
    (move : Direction) : List TransitionDescription :=
  [ preserveTransition source none move blankTarget,
    preserveTransition source (some false) move falseTarget,
    preserveTransition source (some true) move trueTarget ]

def handoffTransitions (source target : Nat)
    (move : Direction) : List TransitionDescription :=
  branchOnCell source target target target move

def loopTransitions (state : Nat)
    (move : Direction) : List TransitionDescription :=
  branchOnCell state state state state move

def cellBranchTarget (cell : Option Bool)
    (blankTarget falseTarget trueTarget : Nat) : Nat :=
  match cell with
  | none => blankTarget
  | some false => falseTarget
  | some true => trueTarget

def cellBranchDescription
    (stateCount source halt blankTarget falseTarget trueTarget : Nat)
    (move : Direction) : MachineDescription where
  stateCount := stateCount
  start := source
  halt := halt
  transitions := branchOnCell source blankTarget falseTarget trueTarget move

theorem branchOnCell_wellFormed
    {stateCount source blankTarget falseTarget trueTarget : Nat}
    {move : Direction}
    (hsource : source < stateCount)
    (hblank : blankTarget < stateCount)
    (hfalse : falseTarget < stateCount)
    (htrue : trueTarget < stateCount) :
    forall t : TransitionDescription,
      t ∈ branchOnCell source blankTarget falseTarget trueTarget move ->
        TransitionDescription.WellFormed stateCount t := by
  intro t ht
  simp [branchOnCell, preserveTransition, transition,
    TransitionDescription.WellFormed] at ht ⊢
  rcases ht with rfl | rfl | rfl
  · exact ⟨hsource, hblank⟩
  · exact ⟨hsource, hfalse⟩
  · exact ⟨hsource, htrue⟩

theorem branchOnCell_deterministic
    (source blankTarget falseTarget trueTarget : Nat)
    (move : Direction) :
    forall t u : TransitionDescription,
      t ∈ branchOnCell source blankTarget falseTarget trueTarget move ->
      u ∈ branchOnCell source blankTarget falseTarget trueTarget move ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  simp [branchOnCell, preserveTransition, transition] at ht hu
  rcases ht with rfl | rfl | rfl <;>
    rcases hu with rfl | rfl | rfl <;>
      simp [TransitionDescription.SameKey,
        TransitionDescription.SameAction] at hkey ⊢

theorem branchOnCell_no_source
    {state source blankTarget falseTarget trueTarget : Nat}
    {move : Direction}
    (h : source ≠ state) :
    forall t : TransitionDescription,
      t ∈ branchOnCell source blankTarget falseTarget trueTarget move ->
        t.source ≠ state := by
  intro t ht
  simp [branchOnCell, preserveTransition, transition] at ht
  rcases ht with rfl | rfl | rfl <;> exact h

theorem handoffTransitions_wellFormed
    {stateCount source target : Nat} {move : Direction}
    (hsource : source < stateCount)
    (htarget : target < stateCount) :
    forall t : TransitionDescription,
      t ∈ handoffTransitions source target move ->
        TransitionDescription.WellFormed stateCount t :=
  branchOnCell_wellFormed hsource htarget htarget htarget

theorem handoffTransitions_deterministic
    (source target : Nat) (move : Direction) :
    forall t u : TransitionDescription,
      t ∈ handoffTransitions source target move ->
      u ∈ handoffTransitions source target move ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u :=
  branchOnCell_deterministic source target target target move

theorem loopTransitions_wellFormed
    {stateCount state : Nat} {move : Direction}
    (hstate : state < stateCount) :
    forall t : TransitionDescription,
      t ∈ loopTransitions state move ->
        TransitionDescription.WellFormed stateCount t :=
  branchOnCell_wellFormed hstate hstate hstate hstate

theorem loopTransitions_deterministic
    (state : Nat) (move : Direction) :
    forall t u : TransitionDescription,
      t ∈ loopTransitions state move ->
      u ∈ loopTransitions state move ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u :=
  branchOnCell_deterministic state state state state move

theorem cellBranchDescription_wellFormed
    {stateCount source halt blankTarget falseTarget trueTarget : Nat}
    {move : Direction}
    (hpos : 0 < stateCount)
    (hsource : source < stateCount)
    (hhalt : halt < stateCount)
    (hblank : blankTarget < stateCount)
    (hfalse : falseTarget < stateCount)
    (htrue : trueTarget < stateCount) :
    (cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).WellFormed := by
  constructor
  · exact hpos
  constructor
  · exact hsource
  constructor
  · exact hhalt
  constructor
  · exact branchOnCell_wellFormed
      hsource hblank hfalse htrue
  · exact branchOnCell_deterministic
      source blankTarget falseTarget trueTarget move

theorem cellBranchDescription_haltTransitionFree
    {stateCount source halt blankTarget falseTarget trueTarget : Nat}
    {move : Direction}
    (hsource : source ≠ halt) :
    (cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).HaltTransitionFree :=
  branchOnCell_no_source
    (state := halt) (source := source)
    (blankTarget := blankTarget) (falseTarget := falseTarget)
    (trueTarget := trueTarget) (move := move) hsource

theorem cellBranchDescription_subroutineReady
    {stateCount source halt blankTarget falseTarget trueTarget : Nat}
    {move : Direction}
    (hpos : 0 < stateCount)
    (hsource : source < stateCount)
    (hhalt : halt < stateCount)
    (hblank : blankTarget < stateCount)
    (hfalse : falseTarget < stateCount)
    (htrue : trueTarget < stateCount)
    (hsourceNe : source ≠ halt) :
    (cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).SubroutineReady :=
  ⟨cellBranchDescription_wellFormed
      hpos hsource hhalt hblank hfalse htrue,
    cellBranchDescription_haltTransitionFree hsourceNe⟩

theorem cellBranchDescription_stepConfig_start
    (stateCount source halt blankTarget falseTarget trueTarget : Nat)
    (move : Direction) (T : Tape Bool) :
    (cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).stepConfig
        { state := source, tape := T } =
      some
        { state :=
            cellBranchTarget (Tape.read T)
              blankTarget falseTarget trueTarget,
          tape := Tape.move move T } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          cases move <;>
            simp [cellBranchDescription, cellBranchTarget,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, branchOnCell,
              preserveTransition, transition, preserveCell,
              Tape.read, Tape.write]
      | some b =>
          cases b <;> cases move <;>
            simp [cellBranchDescription, cellBranchTarget,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, branchOnCell,
              preserveTransition, transition, preserveCell,
              Tape.read, Tape.write]

theorem cellBranchDescription_runConfig_one_start
    (stateCount source halt blankTarget falseTarget trueTarget : Nat)
    (move : Direction) (T : Tape Bool) :
    (cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).runConfig 1
        { state := source, tape := T } =
      { state :=
          cellBranchTarget (Tape.read T)
            blankTarget falseTarget trueTarget,
        tape := Tape.move move T } := by
  simp [MachineDescription.runConfig,
    cellBranchDescription_stepConfig_start]

structure Fragment where
  stateCount : Nat
  entry : Nat
  exit : Nat
  transitions : List TransitionDescription

namespace Fragment

def WellFormed (F : Fragment) : Prop :=
  0 < F.stateCount ∧
    F.entry < F.stateCount ∧
    F.exit < F.stateCount ∧
    (forall t : TransitionDescription,
      t ∈ F.transitions ->
        TransitionDescription.WellFormed F.stateCount t) ∧
    (forall t u : TransitionDescription,
      t ∈ F.transitions ->
      u ∈ F.transitions ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u) ∧
    (forall t : TransitionDescription,
      t ∈ F.transitions -> t.source ≠ F.exit)

def toDescription (F : Fragment) : MachineDescription where
  stateCount := F.stateCount
  start := F.entry
  halt := F.exit
  transitions := F.transitions

theorem toDescription_wellFormed
    {F : Fragment} (hF : F.WellFormed) :
    F.toDescription.WellFormed := by
  rcases hF with ⟨hpos, hentry, hexit, htrans, hdet, _hexitStops⟩
  exact ⟨hpos, hentry, hexit, htrans, hdet⟩

theorem toDescription_haltTransitionFree
    {F : Fragment} (hF : F.WellFormed) :
    F.toDescription.HaltTransitionFree := by
  rcases hF with
    ⟨_hpos, _hentry, _hexit, _htrans, _hdet, hexitStops⟩
  exact hexitStops

theorem toDescription_subroutineReady
    {F : Fragment} (hF : F.WellFormed) :
    F.toDescription.SubroutineReady :=
  ⟨toDescription_wellFormed hF,
    toDescription_haltTransitionFree hF⟩

def halt : Fragment where
  stateCount := 1
  entry := 0
  exit := 0
  transitions := []

theorem halt_wellFormed : halt.WellFormed := by
  simp [WellFormed, halt]

def singleAction (read write : Option Bool) (move : Direction) :
    Fragment where
  stateCount := 2
  entry := 0
  exit := 1
  transitions := [transition 0 read write move 1]

def writeThenMove (read write : Option Bool) (move : Direction) :
    Fragment :=
  singleAction read write move

theorem singleAction_wellFormed
    (read write : Option Bool) (move : Direction) :
    (singleAction read write move).WellFormed := by
  constructor
  · change 0 < 2
    omega
  constructor
  · change 0 < 2
    omega
  constructor
  · change 1 < 2
    omega
  constructor
  · intro t ht
    simp [singleAction, transition,
      TransitionDescription.WellFormed] at ht ⊢
    cases ht
    constructor
    · change 0 < 2
      omega
    · change 1 < 2
      omega
  constructor
  · intro t u ht hu hkey
    simp [singleAction, transition] at ht hu
    cases ht
    cases hu
    simp [TransitionDescription.SameAction]
  · intro t ht
    simp [singleAction, transition] at ht
    cases ht
    change 0 ≠ 1
    omega

theorem writeThenMove_wellFormed
    (read write : Option Bool) (move : Direction) :
    (writeThenMove read write move).WellFormed :=
  singleAction_wellFormed read write move

def handoff (move : Direction) : Fragment where
  stateCount := 2
  entry := 0
  exit := 1
  transitions := handoffTransitions 0 1 move

def preserveMove (move : Direction) : Fragment :=
  handoff move

theorem handoff_wellFormed (move : Direction) :
    (handoff move).WellFormed := by
  constructor
  · change 0 < 2
    omega
  constructor
  · change 0 < 2
    omega
  constructor
  · change 1 < 2
    omega
  constructor
  · intro t ht
    exact handoffTransitions_wellFormed
      (stateCount := 2) (source := 0) (target := 1)
      (move := move) (by omega) (by omega) t ht
  constructor
  · exact handoffTransitions_deterministic 0 1 move
  · exact branchOnCell_no_source (source := 0) (state := 1)
      (blankTarget := 1) (falseTarget := 1) (trueTarget := 1)
      (move := move) (by omega)

theorem preserveMove_wellFormed (move : Direction) :
    (preserveMove move).WellFormed :=
  handoff_wellFormed move

theorem handoff_runConfig_one
    (move : Direction) (T : Tape Bool) :
    (handoff move).toDescription.runConfig 1
        { state := (handoff move).entry, tape := T } =
      { state := (handoff move).exit, tape := Tape.move move T } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          cases move <;>
            rfl
      | some b =>
          cases b <;> cases move <;>
            rfl

theorem handoff_firstReaches
    (move : Direction) (T : Tape Bool) :
    exists n : Nat,
      (handoff move).toDescription.runConfig n
          { state := (handoff move).entry, tape := T } =
        { state := (handoff move).exit, tape := Tape.move move T } ∧
        forall k : Nat,
          k < n ->
            ((handoff move).toDescription.runConfig k
              { state := (handoff move).entry, tape := T }).state ≠
              (handoff move).exit := by
  exists 1
  constructor
  · exact handoff_runConfig_one move T
  · intro k hk
    have hk0 : k = 0 := by omega
    cases hk0
    change (handoff move).entry ≠ (handoff move).exit
    cases move <;> decide

def offsetStates (offset : Nat) (F : Fragment) : Fragment where
  stateCount := offset + F.stateCount
  entry := offset + F.entry
  exit := offset + F.exit
  transitions := F.transitions.map
    (TransitionDescription.offsetStates offset)

theorem offsetStates_wellFormed
    {offset : Nat} {F : Fragment} (hF : F.WellFormed) :
    (offsetStates offset F).WellFormed := by
  rcases hF with ⟨hpos, hentry, hexit, htrans, hdet, hexitStops⟩
  constructor
  · change 0 < offset + F.stateCount
    omega
  constructor
  · exact Nat.add_lt_add_left hentry offset
  constructor
  · exact Nat.add_lt_add_left hexit offset
  constructor
  · intro t ht
    simp [offsetStates] at ht
    rcases ht with ⟨base, hbase, rfl⟩
    exact TransitionDescription.wellFormed_offsetStates
      (htrans base hbase)
  constructor
  · intro t u ht hu hkey
    simp [offsetStates] at ht hu
    rcases ht with ⟨baseT, hbaseT, rfl⟩
    rcases hu with ⟨baseU, hbaseU, rfl⟩
    exact TransitionDescription.offsetStates_sameAction offset baseT baseU
      (hdet baseT baseU hbaseT hbaseU
        (TransitionDescription.sameKey_of_offsetStates_sameKey hkey))
  · intro t ht
    simp [offsetStates] at ht
    rcases ht with ⟨base, hbase, rfl⟩
    intro hsource
    exact hexitStops base hbase (Nat.add_left_cancel hsource)

def disjointUnion (A B : Fragment) : Fragment where
  stateCount := A.stateCount + B.stateCount
  entry := A.entry
  exit := A.exit
  transitions :=
    A.transitions ++
      B.transitions.map
        (TransitionDescription.offsetStates A.stateCount)

theorem disjointUnion_wellFormed
    {A B : Fragment}
    (hA : A.WellFormed) (hB : B.WellFormed) :
    (disjointUnion A B).WellFormed := by
  rcases hA with ⟨hApos, hAentry, hAexit, hAtrans, hAdet, hAexitStops⟩
  rcases hB with ⟨hBpos, _hBentry, _hBexit, hBtrans, hBdet, _hBexitStops⟩
  constructor
  · change 0 < A.stateCount + B.stateCount
    omega
  constructor
  · exact Nat.lt_add_right B.stateCount hAentry
  constructor
  · exact Nat.lt_add_right B.stateCount hAexit
  constructor
  · intro t ht
    simp [disjointUnion] at ht
    cases ht with
    | inl htA =>
        have htAFormed := hAtrans t htA
        constructor
        · exact Nat.lt_add_right B.stateCount htAFormed.left
        · exact Nat.lt_add_right B.stateCount htAFormed.right
    | inr htB =>
        rcases htB with ⟨base, hbase, rfl⟩
        exact TransitionDescription.wellFormed_offsetStates
          (hBtrans base hbase)
  constructor
  · intro t u ht hu hkey
    simp [disjointUnion] at ht hu
    cases ht with
    | inl htA =>
        cases hu with
        | inl huA =>
            exact hAdet t u htA huA hkey
        | inr huB =>
            rcases huB with ⟨baseU, hbaseU, rfl⟩
            have htBound := (hAtrans t htA).left
            have hsource : t.source = A.stateCount + baseU.source :=
              hkey.left
            omega
    | inr htB =>
        rcases htB with ⟨baseT, hbaseT, rfl⟩
        cases hu with
        | inl huA =>
            have huBound := (hAtrans u huA).left
            have hsource : A.stateCount + baseT.source = u.source :=
              hkey.left
            omega
        | inr huB =>
            rcases huB with ⟨baseU, hbaseU, rfl⟩
            exact TransitionDescription.offsetStates_sameAction
              A.stateCount baseT baseU
              (hBdet baseT baseU hbaseT hbaseU
                (TransitionDescription.sameKey_of_offsetStates_sameKey
                  hkey))
  · intro t ht
    simp [disjointUnion] at ht
    cases ht with
    | inl htA =>
        exact hAexitStops t htA
    | inr htB =>
        rcases htB with ⟨base, hbase, rfl⟩
        intro hsource
        have hbaseSource := (hBtrans base hbase).left
        have hEq : A.stateCount + base.source = A.exit := by
          simpa [TransitionDescription.offsetStates, disjointUnion]
            using hsource
        omega

def seq (A B : Fragment) (handoffMove : Direction) : Fragment where
  stateCount := A.stateCount + B.stateCount
  entry := A.entry
  exit := A.stateCount + B.exit
  transitions :=
    A.transitions ++
      handoffTransitions A.exit (A.stateCount + B.entry) handoffMove ++
        B.transitions.map
          (TransitionDescription.offsetStates A.stateCount)

theorem seq_wellFormed
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed) :
    (seq A B handoffMove).WellFormed := by
  rcases hA with
    ⟨hApos, hAentry, hAexit, hAtrans, hAdet, hAexitStops⟩
  rcases hB with
    ⟨hBpos, hBentry, hBexit, hBtrans, hBdet, hBexitStops⟩
  constructor
  · change 0 < A.stateCount + B.stateCount
    omega
  constructor
  · exact Nat.lt_add_right B.stateCount hAentry
  constructor
  · exact Nat.add_lt_add_left hBexit A.stateCount
  constructor
  · intro t ht
    simp [seq] at ht
    rcases ht with htA | htH | htB
    · have htFormed := hAtrans t htA
      constructor
      · exact Nat.lt_add_right B.stateCount htFormed.left
      · exact Nat.lt_add_right B.stateCount htFormed.right
    · exact handoffTransitions_wellFormed
        (stateCount := A.stateCount + B.stateCount)
        (source := A.exit)
        (target := A.stateCount + B.entry)
        (move := handoffMove)
        (by omega) (by omega) t htH
    · rcases htB with ⟨base, hbase, rfl⟩
      exact TransitionDescription.wellFormed_offsetStates
        (offset := A.stateCount) (hBtrans base hbase)
  constructor
  · intro t u ht hu hkey
    simp [seq] at ht hu
    rcases ht with htA | htH | htB
    · rcases hu with huA | huH | huB
      · exact hAdet t u htA huA hkey
      · simp [handoffTransitions, branchOnCell, preserveTransition,
          transition] at huH
        rcases huH with rfl | rfl | rfl
        · exfalso
          exact hAexitStops t htA hkey.left
        · exfalso
          exact hAexitStops t htA hkey.left
        · exfalso
          exact hAexitStops t htA hkey.left
      · rcases huB with ⟨baseU, hbaseU, rfl⟩
        have htBound := (hAtrans t htA).left
        have hsource :
            t.source = A.stateCount + baseU.source := hkey.left
        omega
    · rcases hu with huA | huH | huB
      · simp [handoffTransitions, branchOnCell, preserveTransition,
          transition] at htH
        rcases htH with rfl | rfl | rfl
        · exfalso
          exact hAexitStops u huA hkey.left.symm
        · exfalso
          exact hAexitStops u huA hkey.left.symm
        · exfalso
          exact hAexitStops u huA hkey.left.symm
      · exact handoffTransitions_deterministic
          A.exit (A.stateCount + B.entry) handoffMove
          t u htH huH hkey
      · rcases huB with ⟨baseU, hbaseU, rfl⟩
        simp [handoffTransitions, branchOnCell, preserveTransition,
          transition] at htH
        rcases htH with rfl | rfl | rfl
        · have hsource :
              A.exit = A.stateCount + baseU.source := hkey.left
          omega
        · have hsource :
              A.exit = A.stateCount + baseU.source := hkey.left
          omega
        · have hsource :
              A.exit = A.stateCount + baseU.source := hkey.left
          omega
    · rcases htB with ⟨baseT, hbaseT, rfl⟩
      rcases hu with huA | huH | huB
      · have huBound := (hAtrans u huA).left
        have hsource :
            A.stateCount + baseT.source = u.source := hkey.left
        omega
      · simp [handoffTransitions, branchOnCell, preserveTransition,
          transition] at huH
        rcases huH with rfl | rfl | rfl
        · have hsource :
              A.stateCount + baseT.source = A.exit := hkey.left
          omega
        · have hsource :
              A.stateCount + baseT.source = A.exit := hkey.left
          omega
        · have hsource :
              A.stateCount + baseT.source = A.exit := hkey.left
          omega
      · rcases huB with ⟨baseU, hbaseU, rfl⟩
        exact TransitionDescription.offsetStates_sameAction
          A.stateCount baseT baseU
          (hBdet baseT baseU hbaseT hbaseU
            (TransitionDescription.sameKey_of_offsetStates_sameKey hkey))
  · intro t ht
    simp [seq] at ht
    rcases ht with htA | htH | htB
    · intro hsource
      have htBound := (hAtrans t htA).left
      have hsource' : t.source = A.stateCount + B.exit := by
        simpa [seq] using hsource
      omega
    · exact branchOnCell_no_source (source := A.exit)
        (state := A.stateCount + B.exit)
        (blankTarget := A.stateCount + B.entry)
        (falseTarget := A.stateCount + B.entry)
        (trueTarget := A.stateCount + B.entry)
        (move := handoffMove) (by omega) t htH
    · rcases htB with ⟨base, hbase, rfl⟩
      intro hsource
      have hbaseSource : base.source = B.exit :=
        Nat.add_left_cancel hsource
      exact hBexitStops base hbase hbaseSource

end Fragment

/-!
## Description subroutines

A halt-transition-free description can be viewed as a fragment whose entry is
the start state and whose exit is the halt state.  This adapter lets later
finite-table constructions reuse the proved fragment sequencing semantics for
ordinary machine descriptions.
-/

def asFragment (D : MachineDescription) : Fragment where
  stateCount := D.stateCount
  entry := D.start
  exit := D.halt
  transitions := D.transitions

theorem asFragment_wellFormed
    {D : MachineDescription} (hD : D.SubroutineReady) :
    D.asFragment.WellFormed := by
  rcases hD with ⟨hWF, hhaltFree⟩
  rcases hWF with ⟨hpos, hstart, hhalt, htrans, hdet⟩
  exact ⟨hpos, hstart, hhalt, htrans, hdet, hhaltFree⟩

theorem asFragment_toDescription
    (D : MachineDescription) :
    D.asFragment.toDescription = D := by
  cases D
  rfl

def seqSubroutine
    (A B : MachineDescription) (handoffMove : Direction) :
    MachineDescription :=
  (Fragment.seq A.asFragment B.asFragment handoffMove).toDescription

theorem seqSubroutine_wellFormed
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (seqSubroutine A B handoffMove).WellFormed :=
  Fragment.toDescription_wellFormed
    (Fragment.seq_wellFormed
      (asFragment_wellFormed hA) (asFragment_wellFormed hB))

theorem seqSubroutine_haltTransitionFree
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (seqSubroutine A B handoffMove).HaltTransitionFree :=
  Fragment.toDescription_haltTransitionFree
    (Fragment.seq_wellFormed
      (asFragment_wellFormed hA) (asFragment_wellFormed hB))

theorem seqSubroutine_subroutineReady
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (seqSubroutine A B handoffMove).SubroutineReady :=
  ⟨seqSubroutine_wellFormed hA hB,
    seqSubroutine_haltTransitionFree hA hB⟩

/-!
## Fixed-simulator table skeletons

The bounded simulator realizer is ultimately a single finite transition table.
At this layer we name the reusable phase structure for such a table without
claiming that the phases already implement decoding, table lookup, or encoded
layout rewriting.  Each phase is a checked fragment, and the skeleton
composition is a checked finite description.
-/

structure FixedSimulatorTableSkeleton where
  decodeLayout : Fragment
  simulateStep : Fragment
  repeatControl : Fragment
  emitLayout : Fragment
  decodeLayout_wellFormed : decodeLayout.WellFormed
  simulateStep_wellFormed : simulateStep.WellFormed
  repeatControl_wellFormed : repeatControl.WellFormed
  emitLayout_wellFormed : emitLayout.WellFormed

namespace FixedSimulatorTableSkeleton

def toFragment (S : FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Fragment :=
  Fragment.seq
    (Fragment.seq
      (Fragment.seq S.decodeLayout S.simulateStep handoffMove)
      S.repeatControl handoffMove)
    S.emitLayout handoffMove

theorem toFragment_wellFormed
    (S : FixedSimulatorTableSkeleton) (handoffMove : Direction) :
    (S.toFragment handoffMove).WellFormed := by
  unfold toFragment
  apply Fragment.seq_wellFormed
  · apply Fragment.seq_wellFormed
    · apply Fragment.seq_wellFormed
      · exact S.decodeLayout_wellFormed
      · exact S.simulateStep_wellFormed
    · exact S.repeatControl_wellFormed
  · exact S.emitLayout_wellFormed

def toDescription (S : FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : MachineDescription :=
  (S.toFragment handoffMove).toDescription

theorem toDescription_wellFormed
    (S : FixedSimulatorTableSkeleton) (handoffMove : Direction) :
    (S.toDescription handoffMove).WellFormed :=
  Fragment.toDescription_wellFormed
    (S.toFragment_wellFormed handoffMove)

def linearPass (move : Direction) : FixedSimulatorTableSkeleton where
  decodeLayout := Fragment.preserveMove move
  simulateStep := Fragment.preserveMove move
  repeatControl := Fragment.preserveMove move
  emitLayout := Fragment.preserveMove move
  decodeLayout_wellFormed := Fragment.preserveMove_wellFormed move
  simulateStep_wellFormed := Fragment.preserveMove_wellFormed move
  repeatControl_wellFormed := Fragment.preserveMove_wellFormed move
  emitLayout_wellFormed := Fragment.preserveMove_wellFormed move

theorem linearPass_description_wellFormed
    (move handoffMove : Direction) :
    ((linearPass move).toDescription handoffMove).WellFormed :=
  toDescription_wellFormed (linearPass move) handoffMove

end FixedSimulatorTableSkeleton

end MachineDescription

end Computability
end FoC
