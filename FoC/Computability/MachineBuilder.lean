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
  · intro t ht
    exact branchOnCell_no_source (source := 0) (state := 1)
      (blankTarget := 1) (falseTarget := 1) (trueTarget := 1)
      (move := move) (by omega) t ht

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

/-!
## Tape and configuration codes

These encodings are over the existing {name}`MachineCodeSymbol` alphabet.  They
are not yet the tape layout used by a universal machine, but they give the
finite simulator target a precise, checked representation of configurations.
-/

def encodeCellsAppend (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  match cells with
  | [] => suffix
  | cell :: rest =>
      encodeCellAppend cell (encodeCellsAppend rest suffix)

def encodeCells (cells : List (Option Bool)) :
    Word MachineCodeSymbol :=
  encodeCellsAppend cells []

def decodeCells : Nat -> Word MachineCodeSymbol ->
    Option (List (Option Bool) × Word MachineCodeSymbol)
  | 0, tokens => some ([], tokens)
  | n + 1, tokens =>
      match decodeCell tokens with
      | none => none
      | some (cell, rest) =>
          match decodeCells n rest with
          | none => none
          | some (cells, suffix) => some (cell :: cells, suffix)

theorem decodeCells_encodeCellsAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    decodeCells cells.length (encodeCellsAppend cells suffix) =
      some (cells, suffix) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [encodeCellsAppend, decodeCells, decodeCell_encodeCellAppend, ih]

def encodeCellListAppend (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeNatAppend cells.length (encodeCellsAppend cells suffix)

def decodeCellList (tokens : Word MachineCodeSymbol) :
    Option (List (Option Bool) × Word MachineCodeSymbol) :=
  match decodeNat tokens with
  | none => none
  | some (len, rest) => decodeCells len rest

theorem decodeCellList_encodeCellListAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    decodeCellList (encodeCellListAppend cells suffix) =
      some (cells, suffix) := by
  simp [decodeCellList, encodeCellListAppend, decodeNat_encodeNatAppend,
    decodeCells_encodeCellsAppend]

def encodeTapeAppend (T : Tape Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeCellListAppend T.left
    (encodeCellAppend T.head
      (encodeCellListAppend T.right suffix))

def encodeTape (T : Tape Bool) : Word MachineCodeSymbol :=
  encodeTapeAppend T []

def decodeTape (tokens : Word MachineCodeSymbol) :
    Option (Tape Bool × Word MachineCodeSymbol) :=
  match decodeCellList tokens with
  | none => none
  | some (left, rest) =>
      match decodeCell rest with
      | none => none
      | some (head, rest) =>
          match decodeCellList rest with
          | none => none
          | some (right, suffix) =>
              some ({ left := left, head := head, right := right }, suffix)

theorem decodeTape_encodeTapeAppend
    (T : Tape Bool) (suffix : Word MachineCodeSymbol) :
    decodeTape (encodeTapeAppend T suffix) = some (T, suffix) := by
  cases T
  simp [encodeTapeAppend, decodeTape, decodeCellList_encodeCellListAppend,
    decodeCell_encodeCellAppend]

theorem decodeTape_encodeTape (T : Tape Bool) :
    decodeTape (encodeTape T) = some (T, []) :=
  decodeTape_encodeTapeAppend T []

def encodeConfigurationAppend (c : Configuration)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeNatAppend c.state (encodeTapeAppend c.tape suffix)

def encodeConfiguration (c : Configuration) :
    Word MachineCodeSymbol :=
  encodeConfigurationAppend c []

def decodeConfiguration (tokens : Word MachineCodeSymbol) :
    Option (Configuration × Word MachineCodeSymbol) :=
  match decodeNat tokens with
  | none => none
  | some (state, rest) =>
      match decodeTape rest with
      | none => none
      | some (tape, suffix) =>
          some ({ state := state, tape := tape }, suffix)

theorem decodeConfiguration_encodeConfigurationAppend
    (c : Configuration) (suffix : Word MachineCodeSymbol) :
    decodeConfiguration (encodeConfigurationAppend c suffix) =
      some (c, suffix) := by
  cases c
  simp [encodeConfigurationAppend, decodeConfiguration,
    decodeNat_encodeNatAppend, decodeTape_encodeTapeAppend]

theorem decodeConfiguration_encodeConfiguration (c : Configuration) :
    decodeConfiguration (encodeConfiguration c) = some (c, []) :=
  decodeConfiguration_encodeConfigurationAppend c []

def runEncodedConfiguration
    (D : MachineDescription) (steps : Nat)
    (tokens : Word MachineCodeSymbol) :
    Option (Configuration × Word MachineCodeSymbol) :=
  match decodeConfiguration tokens with
  | none => none
  | some (c, suffix) => some (D.runConfig steps c, suffix)

theorem runEncodedConfiguration_encodeConfigurationAppend
    (D : MachineDescription) (steps : Nat)
    (c : Configuration) (suffix : Word MachineCodeSymbol) :
    runEncodedConfiguration D steps
        (encodeConfigurationAppend c suffix) =
      some (D.runConfig steps c, suffix) := by
  simp [runEncodedConfiguration,
    decodeConfiguration_encodeConfigurationAppend]

theorem runEncodedConfiguration_encodeConfiguration
    (D : MachineDescription) (steps : Nat)
    (c : Configuration) :
    runEncodedConfiguration D steps (encodeConfiguration c) =
      some (D.runConfig steps c, []) :=
  runEncodedConfiguration_encodeConfigurationAppend D steps c []

def stepConfigurationCode
    (D : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeConfiguration tokens with
  | some (c, []) => some (encodeConfiguration (D.runConfig 1 c))
  | _ => none

theorem stepConfigurationCode_encodeConfiguration
    (D : MachineDescription) (c : Configuration) :
    stepConfigurationCode D (encodeConfiguration c) =
      some (encodeConfiguration (D.runConfig 1 c)) := by
  simp [stepConfigurationCode, decodeConfiguration_encodeConfiguration]

/-!
## Canonical simulator layouts

The transition-level simulator needs one fixed work-tape convention.  The
logical layout is first written as a word over {name}`MachineCodeSymbol`; the
actual Boolean machine tape then uses the existing fixed-width Boolean
expansion from {module}`FoC.Computability.Encoding`.

The single-simulator layout stores the original input, the current stage, the
simulated configuration, and a hit flag.  The paired dovetail layout stores the
same input and stage together with the two simulated configurations and their
accumulated hit flags.
-/

def encodeBoolAppend (b : Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeCellAppend (some b) suffix

def decodeBool (tokens : Word MachineCodeSymbol) :
    Option (Bool × Word MachineCodeSymbol) :=
  match decodeCell tokens with
  | some (some b, suffix) => some (b, suffix)
  | _ => none

theorem decodeBool_encodeBoolAppend
    (b : Bool) (suffix : Word MachineCodeSymbol) :
    decodeBool (encodeBoolAppend b suffix) = some (b, suffix) := by
  cases b <;> rfl

def cellsToWord? : List (Option Bool) -> Option (Word Bool)
  | [] => some []
  | none :: _ => none
  | some b :: rest =>
      match cellsToWord? rest with
      | none => none
      | some w => some (b :: w)

theorem cellsToWord?_map_some (w : Word Bool) :
    cellsToWord? (w.map some) = some w := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      simp [cellsToWord?, ih]

def encodeBoolWordAppend (w : Word Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeCellListAppend (w.map some) suffix

def encodeBoolWord (w : Word Bool) : Word MachineCodeSymbol :=
  encodeBoolWordAppend w []

def decodeBoolWord (tokens : Word MachineCodeSymbol) :
    Option (Word Bool × Word MachineCodeSymbol) :=
  match decodeCellList tokens with
  | none => none
  | some (cells, suffix) =>
      match cellsToWord? cells with
      | none => none
      | some w => some (w, suffix)

theorem decodeBoolWord_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    decodeBoolWord (encodeBoolWordAppend w suffix) =
      some (w, suffix) := by
  simp [decodeBoolWord, encodeBoolWordAppend,
    decodeCellList_encodeCellListAppend, cellsToWord?_map_some]

/-!
## Executable tape-code primitives

These primitives are executable transformations on the finite
{name}`MachineCodeSymbol` words that represent work-tape layouts.  They are
not transition tables yet; they are the precise code-level behavior that later
finite fragments must realize.
-/

structure TapeCodePrimitive where
  transform :
    Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)

namespace TapeCodePrimitive

def Realizes (P : TapeCodePrimitive)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)) :
    Prop :=
  forall w : Word MachineCodeSymbol, P.transform w = f w

def identity : TapeCodePrimitive where
  transform := fun w => some w

theorem identity_transform (w : Word MachineCodeSymbol) :
    identity.transform w = some w :=
  rfl

theorem identity_realizes :
    identity.Realizes (fun w => some w) := by
  intro w
  rfl

def erase : TapeCodePrimitive where
  transform := fun _ => some []

theorem erase_transform (w : Word MachineCodeSymbol) :
    erase.transform w = some [] :=
  rfl

def prepend (pre : Word MachineCodeSymbol) : TapeCodePrimitive where
  transform := fun w => some (List.append pre w)

theorem prepend_transform
    (pre w : Word MachineCodeSymbol) :
    (prepend pre).transform w = some (List.append pre w) :=
  rfl

def append (suffix : Word MachineCodeSymbol) : TapeCodePrimitive where
  transform := fun w => some (List.append w suffix)

theorem append_transform
    (suffix w : Word MachineCodeSymbol) :
    (append suffix).transform w = some (List.append w suffix) :=
  rfl

def compose (P Q : TapeCodePrimitive) : TapeCodePrimitive where
  transform := fun w =>
    match P.transform w with
    | none => none
    | some mid => Q.transform mid

theorem compose_transform_some
    {P Q : TapeCodePrimitive}
    {w mid out : Word MachineCodeSymbol}
    (hP : P.transform w = some mid)
    (hQ : Q.transform mid = some out) :
    (compose P Q).transform w = some out := by
  simp [compose, hP, hQ]

end TapeCodePrimitive

def stepConfigurationCodePrimitive
    (D : MachineDescription) : TapeCodePrimitive where
  transform := stepConfigurationCode D

theorem stepConfigurationCodePrimitive_encodeConfiguration
    (D : MachineDescription) (c : Configuration) :
    (stepConfigurationCodePrimitive D).transform
        (encodeConfiguration c) =
      some (encodeConfiguration (D.runConfig 1 c)) :=
  stepConfigurationCode_encodeConfiguration D c

structure SimulatorLayout where
  input : Word Bool
  stage : Nat
  config : Configuration
  hit : Bool

namespace SimulatorLayout

def encodeAppend (L : SimulatorLayout)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    encodeBoolWordAppend L.input
      (encodeNatAppend L.stage
        (encodeConfigurationAppend L.config
          (encodeBoolAppend L.hit suffix)))

def encode (L : SimulatorLayout) : Word MachineCodeSymbol :=
  encodeAppend L []

def decode (tokens : Word MachineCodeSymbol) :
    Option (SimulatorLayout × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match decodeBoolWord rest with
      | none => none
      | some (input, rest) =>
          match decodeNat rest with
          | none => none
          | some (stage, rest) =>
              match decodeConfiguration rest with
              | none => none
              | some (config, rest) =>
                  match decodeBool rest with
                  | none => none
                  | some (hit, suffix) =>
                      some ({ input := input
                              stage := stage
                              config := config
                              hit := hit }, suffix)
  | _ => none

theorem decode_encodeAppend
    (L : SimulatorLayout) (suffix : Word MachineCodeSymbol) :
    decode (encodeAppend L suffix) = some (L, suffix) := by
  cases L
  simp [encodeAppend, decode, decodeBoolWord_encodeBoolWordAppend,
    decodeNat_encodeNatAppend, decodeConfiguration_encodeConfigurationAppend,
    decodeBool_encodeBoolAppend]

theorem decode_encode (L : SimulatorLayout) :
    decode (encode L) = some (L, []) :=
  decode_encodeAppend L []

def decodeComplete (tokens : Word MachineCodeSymbol) :
    Option SimulatorLayout :=
  match decode tokens with
  | some (L, []) => some L
  | _ => none

theorem decodeComplete_encode (L : SimulatorLayout) :
    decodeComplete (encode L) = some L := by
  simp [decodeComplete, decode_encode]

def normalizeCode (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some L => some (encode L)

theorem normalizeCode_encode (L : SimulatorLayout) :
    normalizeCode (encode L) = some (encode L) := by
  simp [normalizeCode, decodeComplete_encode]

def normalizeCodePrimitive : TapeCodePrimitive where
  transform := normalizeCode

theorem normalizeCodePrimitive_encode (L : SimulatorLayout) :
    normalizeCodePrimitive.transform (encode L) =
      some (encode L) :=
  normalizeCode_encode L

def asBoolInput (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput (encode L)

def tape (L : SimulatorLayout) : Tape Bool :=
  Tape.input (asBoolInput L)

theorem tape_normalizedOutput (L : SimulatorLayout) :
    Tape.normalizedOutput (tape L) = asBoolInput L := by
  simpa [tape, asBoolInput] using
    (Tape.normalizedOutput_output (encodeCodeWordAsInput (encode L)))

def initial (D : MachineDescription) (w : Word Bool)
    (stage : Nat) : SimulatorLayout where
  input := w
  stage := stage
  config := D.initial w
  hit := false

def nextConfig (D : MachineDescription)
    (c : Configuration) : Configuration :=
  match D.stepConfig c with
  | none => c
  | some next => next

theorem nextConfig_eq_runConfig_one
    (D : MachineDescription) (c : Configuration) :
    nextConfig D c = D.runConfig 1 c := by
  cases hstep : D.stepConfig c <;>
    simp [nextConfig, runConfig, hstep]

def haltedConfigBool (D : MachineDescription)
    (c : Configuration) : Bool :=
  c.state == D.halt

theorem haltedConfigBool_eq_true_iff
    (D : MachineDescription) (c : Configuration) :
    haltedConfigBool D c = true <-> c.state = D.halt := by
  simp [haltedConfigBool]

def step (D : MachineDescription)
    (L : SimulatorLayout) : SimulatorLayout :=
  let next := nextConfig D L.config
  { L with
    config := next
    hit := L.hit || haltedConfigBool D next }

theorem step_config
    (D : MachineDescription) (L : SimulatorLayout) :
    (step D L).config = D.runConfig 1 L.config := by
  simp [step, nextConfig_eq_runConfig_one]

theorem step_input
    (D : MachineDescription) (L : SimulatorLayout) :
    (step D L).input = L.input :=
  rfl

theorem step_stage
    (D : MachineDescription) (L : SimulatorLayout) :
    (step D L).stage = L.stage :=
  rfl

theorem step_hit_eq_true_iff
    (D : MachineDescription) (L : SimulatorLayout) :
    (step D L).hit = true <->
      L.hit = true ∨ (D.runConfig 1 L.config).state = D.halt := by
  simp [step, nextConfig_eq_runConfig_one, haltedConfigBool_eq_true_iff]

def haltedFromConfigInBool (D : MachineDescription)
    (c : Configuration) (n : Nat) : Bool :=
  (D.runConfig n c).state == D.halt

theorem haltedFromConfigInBool_eq_true_iff
    (D : MachineDescription) (c : Configuration) (n : Nat) :
    haltedFromConfigInBool D c n = true <->
      (D.runConfig n c).state = D.halt := by
  simp [haltedFromConfigInBool]

def hitsFromConfigByBool (D : MachineDescription)
    (c : Configuration) : Nat -> Bool
  | 0 => haltedFromConfigInBool D c 0
  | limit + 1 =>
      hitsFromConfigByBool D c limit ||
        haltedFromConfigInBool D c (limit + 1)

theorem hitsFromConfigByBool_eq_true_iff
    (D : MachineDescription) (c : Configuration) (limit : Nat) :
    hitsFromConfigByBool D c limit = true <->
      exists n : Nat, n ≤ limit ∧
        (D.runConfig n c).state = D.halt := by
  induction limit with
  | zero =>
      constructor
      · intro h
        exact ⟨0, Nat.le_refl 0,
          (haltedFromConfigInBool_eq_true_iff D c 0).mp h⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        have hn : n = 0 := by omega
        cases hn
        exact (haltedFromConfigInBool_eq_true_iff D c 0).mpr hhalt
  | succ limit ih =>
      constructor
      · intro h
        have hcases :
            hitsFromConfigByBool D c limit = true ∨
              haltedFromConfigInBool D c (limit + 1) = true := by
          simpa [hitsFromConfigByBool] using h
        cases hcases with
        | inl hprev =>
            rcases ih.mp hprev with ⟨n, hnle, hhalt⟩
            exact ⟨n, Nat.le_trans hnle (Nat.le_succ limit), hhalt⟩
        | inr hnow =>
            exact ⟨limit + 1, Nat.le_refl (limit + 1),
              (haltedFromConfigInBool_eq_true_iff
                D c (limit + 1)).mp hnow⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        by_cases hn : n ≤ limit
        · have hprev : hitsFromConfigByBool D c limit = true :=
            ih.mpr ⟨n, hn, hhalt⟩
          simp [hitsFromConfigByBool, hprev]
        · have hnEq : n = limit + 1 := by omega
          cases hnEq
          have hnow :
              haltedFromConfigInBool D c (limit + 1) = true :=
            (haltedFromConfigInBool_eq_true_iff
              D c (limit + 1)).mpr hhalt
          simp [hitsFromConfigByBool, hnow]

def run (D : MachineDescription)
    (steps : Nat) (L : SimulatorLayout) : SimulatorLayout :=
  { L with
    config := D.runConfig steps L.config
    hit := L.hit || hitsFromConfigByBool D L.config steps }

theorem run_config
    (D : MachineDescription) (steps : Nat) (L : SimulatorLayout) :
    (run D steps L).config = D.runConfig steps L.config :=
  rfl

theorem run_input
    (D : MachineDescription) (steps : Nat) (L : SimulatorLayout) :
    (run D steps L).input = L.input :=
  rfl

theorem run_stage
    (D : MachineDescription) (steps : Nat) (L : SimulatorLayout) :
    (run D steps L).stage = L.stage :=
  rfl

theorem run_hit_eq_true_iff
    (D : MachineDescription) (steps : Nat) (L : SimulatorLayout) :
    (run D steps L).hit = true <->
      L.hit = true ∨
        exists n : Nat, n ≤ steps ∧
          (D.runConfig n L.config).state = D.halt := by
  simp [run, hitsFromConfigByBool_eq_true_iff]

theorem run_initial_hit_eq_true_iff
    (D : MachineDescription) (w : Word Bool) (steps : Nat) :
    (run D steps (initial D w steps)).hit = true <->
      exists n : Nat, n ≤ steps ∧ D.HaltsIn n w := by
  simp [run_hit_eq_true_iff, initial, HaltsIn]

def runCode (D : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some L => some (encode (run D L.stage L))

theorem runCode_encode
    (D : MachineDescription) (L : SimulatorLayout) :
    runCode D (encode L) = some (encode (run D L.stage L)) := by
  simp [runCode, decodeComplete_encode]

def runCodePrimitive (D : MachineDescription) : TapeCodePrimitive where
  transform := runCode D

theorem runCodePrimitive_encode
    (D : MachineDescription) (L : SimulatorLayout) :
    (runCodePrimitive D).transform (encode L) =
      some (encode (run D L.stage L)) :=
  runCode_encode D L

def afterRun (D : MachineDescription)
    (L : SimulatorLayout) (steps : Nat) : SimulatorLayout :=
  { L with
    config := D.runConfig steps L.config
    hit := L.hit ||
      ((D.runConfig steps L.config).state == D.halt) }

theorem afterRun_config
    (D : MachineDescription) (L : SimulatorLayout) (steps : Nat) :
    (afterRun D L steps).config = D.runConfig steps L.config :=
  rfl

end SimulatorLayout

structure DovetailLayout where
  input : Word Bool
  stage : Nat
  acceptConfig : Configuration
  rejectConfig : Configuration
  acceptHit : Bool
  rejectHit : Bool

namespace DovetailLayout

def encodeAppend (L : DovetailLayout)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.transition ::
    encodeBoolWordAppend L.input
      (encodeNatAppend L.stage
        (encodeConfigurationAppend L.acceptConfig
          (encodeConfigurationAppend L.rejectConfig
            (encodeBoolAppend L.acceptHit
              (encodeBoolAppend L.rejectHit suffix)))))

def encode (L : DovetailLayout) : Word MachineCodeSymbol :=
  encodeAppend L []

def decode (tokens : Word MachineCodeSymbol) :
    Option (DovetailLayout × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.transition :: rest =>
      match decodeBoolWord rest with
      | none => none
      | some (input, rest) =>
          match decodeNat rest with
          | none => none
          | some (stage, rest) =>
              match decodeConfiguration rest with
              | none => none
              | some (acceptConfig, rest) =>
                  match decodeConfiguration rest with
                  | none => none
                  | some (rejectConfig, rest) =>
                      match decodeBool rest with
                      | none => none
                      | some (acceptHit, rest) =>
                          match decodeBool rest with
                          | none => none
                          | some (rejectHit, suffix) =>
                              some ({ input := input
                                      stage := stage
                                      acceptConfig := acceptConfig
                                      rejectConfig := rejectConfig
                                      acceptHit := acceptHit
                                      rejectHit := rejectHit }, suffix)
  | _ => none

theorem decode_encodeAppend
    (L : DovetailLayout) (suffix : Word MachineCodeSymbol) :
    decode (encodeAppend L suffix) = some (L, suffix) := by
  cases L
  simp [encodeAppend, decode, decodeBoolWord_encodeBoolWordAppend,
    decodeNat_encodeNatAppend, decodeConfiguration_encodeConfigurationAppend,
    decodeBool_encodeBoolAppend]

theorem decode_encode (L : DovetailLayout) :
    decode (encode L) = some (L, []) :=
  decode_encodeAppend L []

def decodeComplete (tokens : Word MachineCodeSymbol) :
    Option DovetailLayout :=
  match decode tokens with
  | some (L, []) => some L
  | _ => none

theorem decodeComplete_encode (L : DovetailLayout) :
    decodeComplete (encode L) = some L := by
  simp [decodeComplete, decode_encode]

def asBoolInput (L : DovetailLayout) : Word Bool :=
  encodeCodeWordAsInput (encode L)

def tape (L : DovetailLayout) : Tape Bool :=
  Tape.input (asBoolInput L)

theorem tape_normalizedOutput (L : DovetailLayout) :
    Tape.normalizedOutput (tape L) = asBoolInput L := by
  simpa [tape, asBoolInput] using
    (Tape.normalizedOutput_output (encodeCodeWordAsInput (encode L)))

def initial (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : DovetailLayout where
  input := w
  stage := stage
  acceptConfig := accept.initial w
  rejectConfig := reject.initial w
  acceptHit := false
  rejectHit := false

def advance (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) : DovetailLayout :=
  let acceptConfig := accept.runConfig steps L.acceptConfig
  let rejectConfig := reject.runConfig steps L.rejectConfig
  { L with
    acceptConfig := acceptConfig
    rejectConfig := rejectConfig
    acceptHit := L.acceptHit || (acceptConfig.state == accept.halt)
    rejectHit := L.rejectHit || (rejectConfig.state == reject.halt) }

theorem advance_acceptConfig
    (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) :
    (advance accept reject L steps).acceptConfig =
      accept.runConfig steps L.acceptConfig := by
  simp [advance]

theorem advance_rejectConfig
    (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) :
    (advance accept reject L steps).rejectConfig =
      reject.runConfig steps L.rejectConfig := by
  simp [advance]

def run (accept reject : MachineDescription)
    (steps : Nat) (L : DovetailLayout) : DovetailLayout :=
  let acceptConfig := accept.runConfig steps L.acceptConfig
  let rejectConfig := reject.runConfig steps L.rejectConfig
  { L with
    acceptConfig := acceptConfig
    rejectConfig := rejectConfig
    acceptHit :=
      L.acceptHit ||
        SimulatorLayout.hitsFromConfigByBool
          accept L.acceptConfig steps
    rejectHit :=
      L.rejectHit ||
        SimulatorLayout.hitsFromConfigByBool
          reject L.rejectConfig steps }

theorem run_acceptConfig
    (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) :
    (run accept reject steps L).acceptConfig =
      accept.runConfig steps L.acceptConfig := by
  simp [run]

theorem run_rejectConfig
    (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) :
    (run accept reject steps L).rejectConfig =
      reject.runConfig steps L.rejectConfig := by
  simp [run]

def outputFromHits (L : DovetailLayout) : Option (Word Bool) :=
  if L.acceptHit = true then
    some [true]
  else if L.rejectHit = true then
    some [false]
  else
    none

def runCode (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some L => some (encode (run accept reject L.stage L))

theorem runCode_encode
    (accept reject : MachineDescription) (L : DovetailLayout) :
    runCode accept reject (encode L) =
      some (encode (run accept reject L.stage L)) := by
  simp [runCode, decodeComplete_encode]

def runCodePrimitive
    (accept reject : MachineDescription) : TapeCodePrimitive where
  transform := runCode accept reject

theorem runCodePrimitive_encode
    (accept reject : MachineDescription) (L : DovetailLayout) :
    (runCodePrimitive accept reject).transform (encode L) =
      some (encode (run accept reject L.stage L)) :=
  runCode_encode accept reject L

end DovetailLayout

/-!
## Executable bounded simulation

The following Boolean search is the executable core of the textbook dovetailing
argument.  It searches the concrete interpreter up to a stage bound and is
proved equivalent to the trace-level search used by {name}`DovetailProgram`.
-/

def haltsInBool (D : MachineDescription) (n : Nat)
    (w : Word Bool) : Bool :=
  (D.runConfig n (D.initial w)).state == D.halt

theorem haltsInBool_eq_true_iff
    (D : MachineDescription) (n : Nat) (w : Word Bool) :
    haltsInBool D n w = true <-> D.HaltsIn n w := by
  simp [haltsInBool, HaltsIn]

def hitsByBool (D : MachineDescription) (w : Word Bool) :
    Nat -> Bool
  | 0 => haltsInBool D 0 w
  | limit + 1 =>
      hitsByBool D w limit || haltsInBool D (limit + 1) w

theorem hitsByBool_eq_true_iff
    (D : MachineDescription) (w : Word Bool) (limit : Nat) :
    hitsByBool D w limit = true <->
      exists n : Nat, n ≤ limit ∧ D.HaltsIn n w := by
  induction limit with
  | zero =>
      constructor
      · intro h
        exact ⟨0, Nat.le_refl 0,
          (haltsInBool_eq_true_iff D 0 w).mp h⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        have hn : n = 0 := by omega
        cases hn
        exact (haltsInBool_eq_true_iff D 0 w).mpr hhalt
  | succ limit ih =>
      constructor
      · intro h
        have hcases :
            hitsByBool D w limit = true ∨
              haltsInBool D (limit + 1) w = true := by
          simpa [hitsByBool] using h
        cases hcases with
        | inl hprev =>
            rcases ih.mp hprev with ⟨n, hnle, hhalt⟩
            exact ⟨n, Nat.le_trans hnle (Nat.le_succ limit), hhalt⟩
        | inr hnow =>
            exact ⟨limit + 1, Nat.le_refl (limit + 1),
              (haltsInBool_eq_true_iff D (limit + 1) w).mp hnow⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        by_cases hn : n ≤ limit
        · have hprev : hitsByBool D w limit = true :=
            ih.mpr ⟨n, hn, hhalt⟩
          simp [hitsByBool, hprev]
        · have hnEq : n = limit + 1 := by omega
          cases hnEq
          have hnow : haltsInBool D (limit + 1) w = true :=
            (haltsInBool_eq_true_iff D (limit + 1) w).mpr hhalt
          simp [hitsByBool, hnow]

def boundedDovetailOutput
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) : Option (Word Bool) :=
  if hitsByBool accept w limit = true then
    some [true]
  else if hitsByBool reject w limit = true then
    some [false]
  else
    none

namespace DovetailLayout

theorem simulator_hitsFromInitial_eq_hitsByBool
    (D : MachineDescription) (w : Word Bool) (limit : Nat) :
    SimulatorLayout.hitsFromConfigByBool D (D.initial w) limit =
      hitsByBool D w limit := by
  induction limit with
  | zero =>
      simp [SimulatorLayout.hitsFromConfigByBool, hitsByBool,
        SimulatorLayout.haltedFromConfigInBool, haltsInBool]
  | succ limit ih =>
      simp [SimulatorLayout.hitsFromConfigByBool, hitsByBool,
        SimulatorLayout.haltedFromConfigInBool, haltsInBool, ih]

theorem run_initial_acceptHit
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    (run accept reject limit
      (initial accept reject w limit)).acceptHit =
      hitsByBool accept w limit := by
  simp [run, initial, simulator_hitsFromInitial_eq_hitsByBool]

theorem run_initial_rejectHit
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    (run accept reject limit
      (initial accept reject w limit)).rejectHit =
      hitsByBool reject w limit := by
  simp [run, initial, simulator_hitsFromInitial_eq_hitsByBool]

theorem outputFromHits_run_initial_eq_boundedDovetailOutput
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    outputFromHits
        (run accept reject limit
          (initial accept reject w limit)) =
      boundedDovetailOutput accept reject w limit := by
  simp [outputFromHits, boundedDovetailOutput,
    run_initial_acceptHit, run_initial_rejectHit]

end DovetailLayout

theorem boundedDovetailOutput_eq_dovetailProgram_run
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    boundedDovetailOutput accept reject w limit =
      (DovetailProgram
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w)).run w limit := by
  classical
  by_cases haccept : hitsByBool accept w limit = true
  · have hacceptTrace :
      TraceHitsBy (fun w n => accept.HaltsIn n w) w limit :=
        (hitsByBool_eq_true_iff accept w limit).mp haccept
    simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace]
  · have hacceptTrace :
      ¬ TraceHitsBy (fun w n => accept.HaltsIn n w) w limit := by
        intro h
        exact haccept ((hitsByBool_eq_true_iff accept w limit).mpr h)
    by_cases hreject : hitsByBool reject w limit = true
    · have hrejectTrace :
        TraceHitsBy (fun w n => reject.HaltsIn n w) w limit :=
          (hitsByBool_eq_true_iff reject w limit).mp hreject
      simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace,
        hreject, hrejectTrace]
    · have hrejectTrace :
        ¬ TraceHitsBy (fun w n => reject.HaltsIn n w) w limit := by
          intro h
          exact hreject ((hitsByBool_eq_true_iff reject w limit).mpr h)
      simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace,
        hreject, hrejectTrace]

end MachineDescription

end Computability
end FoC
