import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Dispatcher

set_option doc.verso true

/-!
# Static dispatcher reader assembly

This module starts the finite-table assembly layer for the static dispatcher.
It keeps the compact dispatcher read states from the dispatcher scaffolding, but uses
an entry-aware copied-reader layout with an explicit no-stay bounce from
{lit}`ready state` into the tape-0 reader block.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace StaticDispatcherReaderAssembly

def TransitionListDeterministic
    (transitions : List TransitionDescription) : Prop :=
  forall t u : TransitionDescription,
    t ∈ transitions -> u ∈ transitions ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u

def TransitionSourceDisjoint
    (left right : List TransitionDescription) : Prop :=
  forall t u : TransitionDescription,
    t ∈ left -> u ∈ right -> t.source ≠ u.source

def TransitionSourcesBelow
    (bound : Nat) (transitions : List TransitionDescription) : Prop :=
  forall t : TransitionDescription, t ∈ transitions -> t.source < bound

def TransitionSourcesAtLeast
    (bound : Nat) (transitions : List TransitionDescription) : Prop :=
  forall t : TransitionDescription, t ∈ transitions -> bound ≤ t.source

def TransitionSourcesNe
    (state : Nat) (transitions : List TransitionDescription) : Prop :=
  forall t : TransitionDescription, t ∈ transitions -> t.source ≠ state

def TransitionListWellFormed
    (stateCount : Nat) (transitions : List TransitionDescription) : Prop :=
  forall t : TransitionDescription,
    t ∈ transitions -> TransitionDescription.WellFormed stateCount t

theorem transitionListDeterministic_of_wellFormed
    {M : MachineDescription} (hM : M.WellFormed) :
    TransitionListDeterministic M.transitions :=
  hM.right.right.right.right

theorem transitionListWellFormed_of_wellFormed_mono
    {M : MachineDescription} {stateCount : Nat}
    (hM : M.WellFormed) (hle : M.stateCount ≤ stateCount) :
    TransitionListWellFormed stateCount M.transitions := by
  intro t ht
  have hformed := hM.right.right.right.left t ht
  exact
    ⟨Nat.lt_of_lt_of_le hformed.left hle,
      Nat.lt_of_lt_of_le hformed.right hle⟩

theorem transitionListDeterministic_append_of_sourceDisjoint
    {left right : List TransitionDescription}
    (hleft : TransitionListDeterministic left)
    (hright : TransitionListDeterministic right)
    (hdisjoint : TransitionSourceDisjoint left right) :
    TransitionListDeterministic (left ++ right) := by
  intro t u ht hu hkey
  simp at ht hu
  rcases ht with ht | ht <;> rcases hu with hu | hu
  · exact hleft t u ht hu hkey
  · exact False.elim ((hdisjoint t u ht hu) hkey.left)
  · exact False.elim ((hdisjoint u t hu ht) hkey.left.symm)
  · exact hright t u ht hu hkey

theorem transitionListDeterministic_flatMap
    {α : Type} {items : List α}
    {transitions : α -> List TransitionDescription}
    (hdet :
      forall item : α,
        item ∈ items -> TransitionListDeterministic (transitions item))
    (hdisjoint :
      forall item₀ : α,
        item₀ ∈ items ->
          forall item₁ : α,
            item₁ ∈ items ->
              item₀ ≠ item₁ ->
                TransitionSourceDisjoint
                  (transitions item₀) (transitions item₁)) :
    TransitionListDeterministic (List.flatMap transitions items) := by
  intro t u ht hu hkey
  rw [List.mem_flatMap] at ht hu
  rcases ht with ⟨item₀, hitem₀, ht⟩
  rcases hu with ⟨item₁, hitem₁, hu⟩
  by_cases hsame : item₀ = item₁
  · subst item₁
    exact hdet item₀ hitem₀ t u ht hu hkey
  · exact False.elim
      ((hdisjoint item₀ hitem₀ item₁ hitem₁ hsame) t u ht hu
        hkey.left)

theorem transitionSourceDisjoint_of_below_atLeast
    {bound : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesBelow bound left)
    (hright : TransitionSourcesAtLeast bound right) :
    TransitionSourceDisjoint left right := by
  intro t u ht hu hsource
  have htBound := hleft t ht
  have huBound := hright u hu
  lia

theorem transitionSourceDisjoint_flatMap_left
    {α : Type} {items : List α}
    {left : α -> List TransitionDescription}
    {right : List TransitionDescription}
    (h :
      forall item : α,
        item ∈ items -> TransitionSourceDisjoint (left item) right) :
    TransitionSourceDisjoint (List.flatMap left items) right := by
  intro t u ht hu hsource
  rw [List.mem_flatMap] at ht
  rcases ht with ⟨item, hitem, ht⟩
  exact h item hitem t u ht hu hsource

theorem transitionSourceDisjoint_flatMap_right
    {α : Type} {items : List α}
    {left : List TransitionDescription}
    {right : α -> List TransitionDescription}
    (h :
      forall item : α,
        item ∈ items -> TransitionSourceDisjoint left (right item)) :
    TransitionSourceDisjoint left (List.flatMap right items) := by
  intro t u ht hu hsource
  rw [List.mem_flatMap] at hu
  rcases hu with ⟨item, hitem, hu⟩
  exact h item hitem t u ht hu hsource

theorem transitionSourceDisjoint_append_left
    {left₀ left₁ right : List TransitionDescription}
    (h₀ : TransitionSourceDisjoint left₀ right)
    (h₁ : TransitionSourceDisjoint left₁ right) :
    TransitionSourceDisjoint (left₀ ++ left₁) right := by
  intro t u ht hu hsource
  simp at ht
  rcases ht with ht | ht
  · exact h₀ t u ht hu hsource
  · exact h₁ t u ht hu hsource

theorem transitionSourcesBelow_mono
    {lower upper : Nat} {transitions : List TransitionDescription}
    (hle : lower ≤ upper)
    (h : TransitionSourcesBelow lower transitions) :
    TransitionSourcesBelow upper transitions := by
  intro t ht
  exact Nat.lt_of_lt_of_le (h t ht) hle

theorem transitionSourcesBelow_append
    {bound : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesBelow bound left)
    (hright : TransitionSourcesBelow bound right) :
    TransitionSourcesBelow bound (left ++ right) := by
  intro t ht
  simp at ht
  rcases ht with ht | ht
  · exact hleft t ht
  · exact hright t ht

theorem transitionSourcesBelow_bind
    {α : Type} {bound : Nat} {items : List α}
    {transitions : α -> List TransitionDescription}
    (h :
      forall item : α,
        item ∈ items -> TransitionSourcesBelow bound (transitions item)) :
    TransitionSourcesBelow bound (List.flatMap transitions items) := by
  intro t ht
  rw [List.mem_flatMap] at ht
  rcases ht with ⟨item, hitem, ht⟩
  exact h item hitem t ht

theorem transitionListWellFormed_append
    {stateCount : Nat} {left right : List TransitionDescription}
    (hleft : TransitionListWellFormed stateCount left)
    (hright : TransitionListWellFormed stateCount right) :
    TransitionListWellFormed stateCount (left ++ right) := by
  intro t ht
  simp at ht
  rcases ht with ht | ht
  · exact hleft t ht
  · exact hright t ht

theorem transitionListWellFormed_bind
    {α : Type} {stateCount : Nat} {items : List α}
    {transitions : α -> List TransitionDescription}
    (h :
      forall item : α,
        item ∈ items ->
          TransitionListWellFormed stateCount (transitions item)) :
    TransitionListWellFormed stateCount (List.flatMap transitions items) := by
  intro t ht
  rw [List.mem_flatMap] at ht
  rcases ht with ⟨item, hitem, ht⟩
  exact h item hitem t ht

theorem transitionSourcesNe_append
    {state : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesNe state left)
    (hright : TransitionSourcesNe state right) :
    TransitionSourcesNe state (left ++ right) := by
  intro t ht
  simp at ht
  rcases ht with ht | ht
  · exact hleft t ht
  · exact hright t ht

theorem transitionSourcesNe_bind
    {α : Type} {state : Nat} {items : List α}
    {transitions : α -> List TransitionDescription}
    (h :
      forall item : α,
        item ∈ items -> TransitionSourcesNe state (transitions item)) :
    TransitionSourcesNe state (List.flatMap transitions items) := by
  intro t ht
  rw [List.mem_flatMap] at ht
  rcases ht with ⟨item, hitem, ht⟩
  exact h item hitem t ht

theorem offsetReadExitRetargetDescription_sources_in_offset_block
    {offset : Nat} {localTarget target : Option Bool -> Nat}
    {M : MachineDescription}
    (hM : M.WellFormed) :
    forall t : TransitionDescription,
      t ∈ (MachineDescription.offsetReadExitRetargetDescription
            offset localTarget target M).transitions ->
        offset ≤ t.source ∧ t.source < offset + M.stateCount := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
  have hsource := (hM.right.right.right.left base hbase).left
  simp [MachineDescription.readExitRetargetStates]
  lia

theorem offsetRetargetDescription_sources_in_offset_block
    {offset target : Nat} {M : MachineDescription}
    (hM : M.WellFormed) :
    forall t : TransitionDescription,
      t ∈ (MachineDescription.offsetRetargetDescription
            offset target M).transitions ->
        offset ≤ t.source ∧ t.source < offset + M.stateCount := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
  have hsource := (hM.right.right.right.left base hbase).left
  simp [TransitionDescription.sharedExitRetargetStates]
  lia

theorem blankHeadBounceJumpDescription_transition_source_cases
    {stateCount source scratch target : Nat}
    {t : TransitionDescription}
    (ht :
      t ∈ (blankHeadBounceJumpDescription
        stateCount source scratch target).transitions) :
    t.source = source ∨ t.source = scratch := by
  simp [blankHeadBounceJumpDescription] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> simp

theorem blankHeadBounceJumpDescription_sources_below
    {stateCount source scratch target bound : Nat}
    (hsource : source < bound) (hscratch : scratch < bound) :
    TransitionSourcesBelow bound
      (blankHeadBounceJumpDescription
        stateCount source scratch target).transitions := by
  intro t ht
  rcases
      blankHeadBounceJumpDescription_transition_source_cases ht with
    h | h
  · rw [h]
    exact hsource
  · rw [h]
    exact hscratch

theorem blankHeadBounceJumpDescription_transitionListDeterministic
    {stateCount source scratch target : Nat}
    (hsourceScratch : source ≠ scratch) :
    TransitionListDeterministic
      (blankHeadBounceJumpDescription
        stateCount source scratch target).transitions := by
  intro t u ht hu hkey
  simp [blankHeadBounceJumpDescription] at ht hu
  rcases ht with rfl | rfl | rfl | rfl <;>
    rcases hu with rfl | rfl | rfl | rfl <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction, hsourceScratch] at hkey ⊢
  · exact False.elim (hsourceScratch hkey.symm)

/--
Scratch states for the no-stay handoff from a structured ready state to the
copied tape-0 reader block.
-/
def readyJumpScratchBase (D : Description) : Nat :=
  StaticDispatcherState.readerStateLimit D

def readyJumpScratch (D : Description) (state : Nat) : Nat :=
  readyJumpScratchBase D + state

def readyJumpLimit (D : Description) : Nat :=
  readyJumpScratchBase D + D.stateCount

def tape0ReaderBlockBase (D : Description) : Nat :=
  readyJumpLimit D

def tape0ReaderOffset (D : Description) (state : Nat) : Nat :=
  tape0ReaderBlockBase D +
    state * branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount

def tape0ReaderDescription (D : Description) (state : Nat) :
    MachineDescription :=
  retargetedBranchingTape0ReadHeadCellAllExitsDescription
    (tape0ReaderOffset D state)
    (StaticDispatcherState.tape0ReaderTargets D state)

def tape0ReaderStart (D : Description) (state : Nat) : Nat :=
  (tape0ReaderDescription D state).start

def tape0ReaderLimit (D : Description) : Nat :=
  tape0ReaderBlockBase D +
    D.stateCount *
      branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount

def afterRead0JumpScratchBase (D : Description) : Nat :=
  tape0ReaderLimit D

def afterRead0JumpScratch (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  afterRead0JumpScratchBase D + 3 * state + ReadTuple3.readCode read0

def afterRead0JumpLimit (D : Description) : Nat :=
  afterRead0JumpScratchBase D + 3 * D.stateCount

def tape1ReaderBlockBase (D : Description) : Nat :=
  afterRead0JumpLimit D

def tape1ReaderOffset (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  tape1ReaderBlockBase D +
    (ReadTuple3.readCode read0 * D.stateCount + state) *
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount

def tape1ReaderDescription (D : Description) (state : Nat)
    (read0 : Option Bool) : MachineDescription :=
  retargetedBranchingTape1ReadHeadCellAllExitsDescription
    (tape1ReaderOffset D state read0)
    (StaticDispatcherState.tape1ReaderTargets D state read0)

def tape1ReaderStart (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  (tape1ReaderDescription D state read0).start

def tape1ReaderLimit (D : Description) : Nat :=
  tape1ReaderBlockBase D +
    3 * D.stateCount *
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount

def afterRead1JumpScratchBase (D : Description) : Nat :=
  tape1ReaderLimit D

def afterRead1JumpScratch (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Nat :=
  afterRead1JumpScratchBase D + 9 * state +
    ReadTuple3.code01 read0 read1

def afterRead1JumpLimit (D : Description) : Nat :=
  afterRead1JumpScratchBase D + 9 * D.stateCount

def tape2ReaderBlockBase (D : Description) : Nat :=
  afterRead1JumpLimit D

def tape2ReaderOffset (D : Description)
    (state : Nat) (read0 read1 : Option Bool) : Nat :=
  tape2ReaderBlockBase D +
    (ReadTuple3.code01 read0 read1 * D.stateCount + state) *
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount

def tape2ReaderDescription (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : MachineDescription :=
  retargetedBranchingTape1ReadHeadCellAllExitsDescription
    (tape2ReaderOffset D state read0 read1)
    (StaticDispatcherState.tape2ReaderTargets D state read0 read1)

def tape2ReaderStart (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Nat :=
  (tape2ReaderDescription D state read0 read1).start

def tape2ReaderLimit (D : Description) : Nat :=
  tape2ReaderBlockBase D +
    9 * D.stateCount *
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount

def threeHeadReaderStateLimit (D : Description) : Nat :=
  tape2ReaderLimit D

def readyJumpDescription (D : Description) (state : Nat) :
    MachineDescription :=
  blankHeadBounceJumpDescription (threeHeadReaderStateLimit D)
    (StaticDispatcherState.ready state)
    (readyJumpScratch D state)
    (tape0ReaderStart D state)

def afterRead0JumpDescription (D : Description) (state : Nat)
    (read0 : Option Bool) : MachineDescription :=
  blankHeadBounceJumpDescription (threeHeadReaderStateLimit D)
    (StaticDispatcherState.afterRead0 D state read0)
    (afterRead0JumpScratch D state read0)
    (tape1ReaderStart D state read0)

def afterRead1JumpDescription (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : MachineDescription :=
  blankHeadBounceJumpDescription (threeHeadReaderStateLimit D)
    (StaticDispatcherState.afterRead1 D state read0 read1)
    (afterRead1JumpScratch D state read0 read1)
    (tape2ReaderStart D state read0 read1)

theorem ready_lt_readyJumpScratch
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    StaticDispatcherState.ready state < readyJumpScratch D state := by
  unfold StaticDispatcherState.ready readyJumpScratch readyJumpScratchBase
  unfold StaticDispatcherState.readerStateLimit StaticDispatcherState.afterRead1Base StaticDispatcherState.afterRead0Base
  lia

theorem readyJumpScratch_lt_readyJumpLimit
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    readyJumpScratch D state < readyJumpLimit D := by
  unfold readyJumpScratch readyJumpLimit
  lia

theorem ready_ne_readyJumpScratch
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    StaticDispatcherState.ready state ≠ readyJumpScratch D state :=
  Nat.ne_of_lt (ready_lt_readyJumpScratch D hstate)

theorem readerStateLimit_le_tape0ReaderOffset
    (D : Description) (state : Nat) :
    StaticDispatcherState.readerStateLimit D ≤ tape0ReaderOffset D state := by
  unfold tape0ReaderOffset tape0ReaderBlockBase readyJumpLimit
    readyJumpScratchBase
  lia

theorem readerStateLimit_le_tape1ReaderOffset
    (D : Description) (state : Nat) (read0 : Option Bool) :
    StaticDispatcherState.readerStateLimit D ≤
      tape1ReaderOffset D state read0 := by
  unfold tape1ReaderOffset tape1ReaderBlockBase afterRead0JumpLimit
    afterRead0JumpScratchBase
    tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
    readyJumpScratchBase
  lia

theorem readerStateLimit_le_tape2ReaderOffset
    (D : Description) (state : Nat) (read0 read1 : Option Bool) :
    StaticDispatcherState.readerStateLimit D ≤
      tape2ReaderOffset D state read0 read1 := by
  unfold tape2ReaderOffset tape2ReaderBlockBase afterRead1JumpLimit
    afterRead1JumpScratchBase tape1ReaderLimit tape1ReaderBlockBase
    afterRead0JumpLimit
    afterRead0JumpScratchBase tape0ReaderLimit tape0ReaderBlockBase
    readyJumpLimit readyJumpScratchBase
  lia

theorem tape0ReaderTargets_lt_tape0ReaderOffset
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    forall read0 : Option Bool,
      StaticDispatcherState.tape0ReaderTargets D state read0 <
        tape0ReaderOffset D state := by
  intro read0
  exact
    Nat.lt_of_lt_of_le
      (StaticDispatcherState.tape0ReaderTargets_lt_readerStateLimit D hstate read0)
      (readerStateLimit_le_tape0ReaderOffset D state)

theorem tape1ReaderTargets_lt_tape1ReaderOffset
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    forall read1 : Option Bool,
      StaticDispatcherState.tape1ReaderTargets D state read0 read1 <
        tape1ReaderOffset D state read0 := by
  intro read1
  exact
    Nat.lt_of_lt_of_le
      (StaticDispatcherState.tape1ReaderTargets_lt_readerStateLimit D read0 hstate read1)
      (readerStateLimit_le_tape1ReaderOffset D state read0)

theorem tape2ReaderTargets_lt_tape2ReaderOffset
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    forall read2 : Option Bool,
      StaticDispatcherState.tape2ReaderTargets D state read0 read1 read2 <
        tape2ReaderOffset D state read0 read1 := by
  intro read2
  exact
    Nat.lt_of_lt_of_le
      (StaticDispatcherState.tape2ReaderTargets_lt_readerStateLimit D read0 read1 hstate read2)
      (readerStateLimit_le_tape2ReaderOffset D state read0 read1)

theorem tape0ReaderDescription_subroutineReady
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    (tape0ReaderDescription D state).SubroutineReady := by
  exact
    retargetedBranchingTape0ReadHeadCellAllExitsDescription_subroutineReady
      (tape0ReaderTargets_lt_tape0ReaderOffset D hstate)

theorem tape1ReaderDescription_subroutineReady
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    (tape1ReaderDescription D state read0).SubroutineReady := by
  exact
    retargetedBranchingTape1ReadHeadCellAllExitsDescription_subroutineReady
      (tape1ReaderTargets_lt_tape1ReaderOffset D read0 hstate)

theorem tape2ReaderDescription_subroutineReady
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    (tape2ReaderDescription D state read0 read1).SubroutineReady := by
  exact
    retargetedBranchingTape1ReadHeadCellAllExitsDescription_subroutineReady
      (tape2ReaderTargets_lt_tape2ReaderOffset D read0 read1 hstate)

theorem tape0ReaderDescription_sources_in_block
    (D : Description) (state : Nat) :
    forall t : TransitionDescription,
      t ∈ (tape0ReaderDescription D state).transitions ->
        tape0ReaderOffset D state ≤ t.source ∧
          t.source <
            tape0ReaderOffset D state +
              branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount := by
  simpa [tape0ReaderDescription,
    retargetedBranchingTape0ReadHeadCellAllExitsDescription] using
    offsetReadExitRetargetDescription_sources_in_offset_block
      (offset := tape0ReaderOffset D state)
      (localTarget :=
        branchingTape0ReadHeadCellAndReturnToSeparatorTarget)
      (target := StaticDispatcherState.tape0ReaderTargets D state)
      (M := branchingTape0ReadHeadCellAndReturnToSeparatorDescription)
      branchingTape0ReadHeadCellAndReturnToSeparatorDescription_subroutineReady.left

theorem tape1ReaderDescription_sources_in_block
    (D : Description) (state : Nat) (read0 : Option Bool) :
    forall t : TransitionDescription,
      t ∈ (tape1ReaderDescription D state read0).transitions ->
        tape1ReaderOffset D state read0 ≤ t.source ∧
          t.source <
            tape1ReaderOffset D state read0 +
              branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount := by
  simpa [tape1ReaderDescription,
    retargetedBranchingTape1ReadHeadCellAllExitsDescription] using
    offsetReadExitRetargetDescription_sources_in_offset_block
      (offset := tape1ReaderOffset D state read0)
      (localTarget :=
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget)
      (target := StaticDispatcherState.tape1ReaderTargets D state read0)
      (M := branchingTape1ReadHeadCellAndReturnToSeparatorDescription)
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_subroutineReady.left

theorem tape2ReaderDescription_sources_in_block
    (D : Description) (state : Nat)
    (read0 read1 : Option Bool) :
    forall t : TransitionDescription,
      t ∈ (tape2ReaderDescription D state read0 read1).transitions ->
        tape2ReaderOffset D state read0 read1 ≤ t.source ∧
          t.source <
            tape2ReaderOffset D state read0 read1 +
              branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount := by
  simpa [tape2ReaderDescription,
    retargetedBranchingTape1ReadHeadCellAllExitsDescription] using
    offsetReadExitRetargetDescription_sources_in_offset_block
      (offset := tape2ReaderOffset D state read0 read1)
      (localTarget :=
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget)
      (target :=
        StaticDispatcherState.tape2ReaderTargets D state read0 read1)
      (M := branchingTape1ReadHeadCellAndReturnToSeparatorDescription)
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_subroutineReady.left

theorem indexedReaderBlockEnd_le_limit
    (base stateCount blockCount slots code state : Nat)
    (hcode : code < slots) (hstate : state < stateCount) :
    base + (code * stateCount + state) * blockCount + blockCount ≤
      base + slots * stateCount * blockCount := by
  have hstate' :
      code * stateCount + state + 1 ≤ (code + 1) * stateCount := by
    have hstep :
        code * stateCount + (state + 1) ≤
          code * stateCount + stateCount :=
      Nat.add_le_add_left (Nat.succ_le_of_lt hstate)
        (code * stateCount)
    have hstep' :
        code * stateCount + state + 1 ≤
          code * stateCount + stateCount := by
      simpa [Nat.add_assoc] using hstep
    have hmul :
        (code + 1) * stateCount =
          code * stateCount + stateCount := by
      simp [Nat.add_mul]
    simpa [hmul] using hstep'
  have hcode' :
      (code + 1) * stateCount ≤ slots * stateCount :=
    Nat.mul_le_mul_right stateCount (Nat.succ_le_of_lt hcode)
  have hidx :
      (code * stateCount + state + 1) * blockCount ≤
        slots * stateCount * blockCount :=
    Nat.mul_le_mul_right blockCount
      (Nat.le_trans hstate' hcode')
  have hidx' :
      (code * stateCount + state) * blockCount + blockCount ≤
        slots * stateCount * blockCount := by
    simpa [Nat.succ_mul] using hidx
  exact
    (by
      simpa [Nat.add_assoc] using
        Nat.add_le_add_left hidx' base)

theorem indexedReaderBlocks_source_ne_of_state_ne
    {base blockCount state₀ state₁ source : Nat}
    (hne : state₀ ≠ state₁)
    (h₀ :
      base + state₀ * blockCount ≤ source ∧
        source < base + state₀ * blockCount + blockCount)
    (h₁ :
      base + state₁ * blockCount ≤ source ∧
        source < base + state₁ * blockCount + blockCount) :
    False := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hidx :
        (state₀ + 1) * blockCount ≤ state₁ * blockCount :=
      Nat.mul_le_mul_right blockCount (Nat.succ_le_of_lt hlt)
    have hupper :
        base + state₀ * blockCount + blockCount ≤
          base + state₁ * blockCount := by
      simpa [Nat.succ_mul, Nat.add_assoc] using
        Nat.add_le_add_left hidx base
    exact (Nat.not_lt_of_ge (Nat.le_trans hupper h₁.left)) h₀.right
  · have hidx :
        (state₁ + 1) * blockCount ≤ state₀ * blockCount :=
      Nat.mul_le_mul_right blockCount (Nat.succ_le_of_lt hgt)
    have hupper :
        base + state₁ * blockCount + blockCount ≤
          base + state₀ * blockCount := by
      simpa [Nat.succ_mul, Nat.add_assoc] using
        Nat.add_le_add_left hidx base
    exact (Nat.not_lt_of_ge (Nat.le_trans hupper h₀.left)) h₁.right

theorem tape0ReaderOffset_blockEnd_le_tape0ReaderLimit
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    tape0ReaderOffset D state +
      branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount ≤
        tape0ReaderLimit D := by
  have h :=
    indexedReaderBlockEnd_le_limit
      (base := tape0ReaderBlockBase D)
      (stateCount := D.stateCount)
      (blockCount :=
        branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount)
      (slots := 1)
      (code := 0)
      (state := state)
      (by decide)
      hstate
  simpa [tape0ReaderOffset, tape0ReaderLimit] using h

theorem tape1ReaderOffset_blockEnd_le_tape1ReaderLimit
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    tape1ReaderOffset D state read0 +
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount ≤
        tape1ReaderLimit D := by
  have h :=
    indexedReaderBlockEnd_le_limit
      (base := tape1ReaderBlockBase D)
      (stateCount := D.stateCount)
      (blockCount :=
        branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount)
      (slots := 3)
      (code := ReadTuple3.readCode read0)
      (state := state)
      (ReadTuple3.readCode_lt_three read0)
      hstate
  simpa [tape1ReaderOffset, tape1ReaderLimit] using h

theorem tape2ReaderOffset_blockEnd_le_tape2ReaderLimit
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    tape2ReaderOffset D state read0 read1 +
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount ≤
        tape2ReaderLimit D := by
  have h :=
    indexedReaderBlockEnd_le_limit
      (base := tape2ReaderBlockBase D)
      (stateCount := D.stateCount)
      (blockCount :=
        branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount)
      (slots := 9)
      (code := ReadTuple3.code01 read0 read1)
      (state := state)
      (ReadTuple3.code01_lt_nine read0 read1)
      hstate
  simpa [tape2ReaderOffset, tape2ReaderLimit] using h

theorem tape0ReaderDescription_stateCount_le_threeHeadReaderStateLimit
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    (tape0ReaderDescription D state).stateCount ≤
      threeHeadReaderStateLimit D := by
  have hblock :=
    tape0ReaderOffset_blockEnd_le_tape0ReaderLimit D hstate
  have hlimit : tape0ReaderLimit D ≤ threeHeadReaderStateLimit D := by
    unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
      afterRead1JumpLimit afterRead1JumpScratchBase tape1ReaderLimit
      tape1ReaderBlockBase afterRead0JumpLimit afterRead0JumpScratchBase
    lia
  simpa [tape0ReaderDescription,
    retargetedBranchingTape0ReadHeadCellAllExitsDescription,
    MachineDescription.offsetReadExitRetargetDescription] using
    Nat.le_trans hblock hlimit

theorem tape1ReaderDescription_stateCount_le_threeHeadReaderStateLimit
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    (tape1ReaderDescription D state read0).stateCount ≤
      threeHeadReaderStateLimit D := by
  have hblock :=
    tape1ReaderOffset_blockEnd_le_tape1ReaderLimit
      D read0 hstate
  have hlimit : tape1ReaderLimit D ≤ threeHeadReaderStateLimit D := by
    unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
      afterRead1JumpLimit afterRead1JumpScratchBase
    lia
  simpa [tape1ReaderDescription,
    retargetedBranchingTape1ReadHeadCellAllExitsDescription,
    MachineDescription.offsetReadExitRetargetDescription] using
    Nat.le_trans hblock hlimit

theorem tape2ReaderDescription_stateCount_le_threeHeadReaderStateLimit
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    (tape2ReaderDescription D state read0 read1).stateCount ≤
      threeHeadReaderStateLimit D := by
  have hblock :=
    tape2ReaderOffset_blockEnd_le_tape2ReaderLimit
      D read0 read1 hstate
  simpa [threeHeadReaderStateLimit, tape2ReaderDescription,
    retargetedBranchingTape1ReadHeadCellAllExitsDescription,
    MachineDescription.offsetReadExitRetargetDescription] using hblock

theorem tape0ReaderDescription_sources_atLeast
    (D : Description) (state : Nat) :
    TransitionSourcesAtLeast (tape0ReaderOffset D state)
      (tape0ReaderDescription D state).transitions := by
  intro t ht
  exact (tape0ReaderDescription_sources_in_block D state t ht).left

theorem tape1ReaderDescription_sources_atLeast
    (D : Description) (state : Nat) (read0 : Option Bool) :
    TransitionSourcesAtLeast (tape1ReaderOffset D state read0)
      (tape1ReaderDescription D state read0).transitions := by
  intro t ht
  exact
    (tape1ReaderDescription_sources_in_block D state read0 t ht).left

theorem tape2ReaderDescription_sources_atLeast
    (D : Description) (state : Nat)
    (read0 read1 : Option Bool) :
    TransitionSourcesAtLeast (tape2ReaderOffset D state read0 read1)
      (tape2ReaderDescription D state read0 read1).transitions := by
  intro t ht
  exact
    (tape2ReaderDescription_sources_in_block
      D state read0 read1 t ht).left

theorem afterRead0JumpScratch_lt_afterRead0JumpLimit
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead0JumpScratch D state read0 <
      afterRead0JumpLimit D := by
  have hcode := ReadTuple3.readCode_lt_three read0
  unfold afterRead0JumpScratch afterRead0JumpLimit
  lia

theorem afterRead1JumpScratch_lt_afterRead1JumpLimit
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    afterRead1JumpScratch D state read0 read1 <
      afterRead1JumpLimit D := by
  have hcode := ReadTuple3.code01_lt_nine read0 read1
  unfold afterRead1JumpScratch afterRead1JumpLimit
  lia

theorem afterRead0_lt_afterRead0JumpScratch
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    StaticDispatcherState.afterRead0 D state read0 <
      afterRead0JumpScratch D state read0 := by
  have hlow :=
    Nat.lt_of_lt_of_le
      (StaticDispatcherState.afterRead0_lt_afterRead1Base D read0 hstate)
      (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
  have hle :
      StaticDispatcherState.readerStateLimit D ≤
        afterRead0JumpScratch D state read0 := by
    unfold afterRead0JumpScratch afterRead0JumpScratchBase
      tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit readyJumpScratchBase
    lia
  exact Nat.lt_of_lt_of_le hlow hle

theorem afterRead1_lt_afterRead1JumpScratch
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    StaticDispatcherState.afterRead1 D state read0 read1 <
      afterRead1JumpScratch D state read0 read1 := by
  have hlow :=
    StaticDispatcherState.afterRead1_lt_readerStateLimit D read0 read1
      hstate
  have hle :
      StaticDispatcherState.readerStateLimit D ≤
        afterRead1JumpScratch D state read0 read1 := by
    unfold afterRead1JumpScratch afterRead1JumpScratchBase
      tape1ReaderLimit tape1ReaderBlockBase afterRead0JumpLimit
      afterRead0JumpScratchBase tape0ReaderLimit tape0ReaderBlockBase
      readyJumpLimit readyJumpScratchBase
    lia
  exact Nat.lt_of_lt_of_le hlow hle

theorem afterRead0_ne_afterRead0JumpScratch
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    StaticDispatcherState.afterRead0 D state read0 ≠
      afterRead0JumpScratch D state read0 :=
  Nat.ne_of_lt (afterRead0_lt_afterRead0JumpScratch D read0 hstate)

theorem afterRead1_ne_afterRead1JumpScratch
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    StaticDispatcherState.afterRead1 D state read0 read1 ≠
      afterRead1JumpScratch D state read0 read1 :=
  Nat.ne_of_lt
    (afterRead1_lt_afterRead1JumpScratch D read0 read1 hstate)

def readyJumpTape0ReaderTransitions
    (D : Description) (state : Nat) : List TransitionDescription :=
  (readyJumpDescription D state).transitions ++
    (tape0ReaderDescription D state).transitions

def afterRead0JumpTape1ReaderTransitions
    (D : Description) (state : Nat) (read0 : Option Bool) :
    List TransitionDescription :=
  (afterRead0JumpDescription D state read0).transitions ++
    (tape1ReaderDescription D state read0).transitions

def afterRead1JumpTape2ReaderTransitions
    (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : List TransitionDescription :=
  (afterRead1JumpDescription D state read0 read1).transitions ++
    (tape2ReaderDescription D state read0 read1).transitions

def readOptionValues : List (Option Bool) :=
  [none, some false, some true]

def activeStateValues (D : Description) : List Nat :=
  (List.range D.stateCount).filter (fun state => decide (state ≠ D.halt))

theorem activeStateValues_mem_lt
    {D : Description} {state : Nat}
    (hstate : state ∈ activeStateValues D) :
    state < D.stateCount := by
  rcases List.mem_filter.mp hstate with ⟨hstate, _hne⟩
  exact List.mem_range.mp hstate

theorem activeStateValues_mem_ne_halt
    {D : Description} {state : Nat}
    (hstate : state ∈ activeStateValues D) :
    state ≠ D.halt := by
  rcases List.mem_filter.mp hstate with ⟨_hstate, hne⟩
  exact of_decide_eq_true hne

def readyJumpTape0ReaderAllTransitions
    (D : Description) : List TransitionDescription :=
  List.flatMap
    (fun state => readyJumpTape0ReaderTransitions D state)
    (activeStateValues D)

def afterRead0JumpTape1ReaderAllTransitions
    (D : Description) : List TransitionDescription :=
  List.flatMap
    (fun read0 =>
      List.flatMap
        (fun state =>
          afterRead0JumpTape1ReaderTransitions D state read0)
        (activeStateValues D))
    readOptionValues

def afterRead1JumpTape2ReaderAllTransitions
    (D : Description) : List TransitionDescription :=
  List.flatMap
    (fun read0 =>
      List.flatMap
        (fun read1 =>
          List.flatMap
            (fun state =>
              afterRead1JumpTape2ReaderTransitions D state read0 read1)
            (activeStateValues D))
        readOptionValues)
    readOptionValues

def threeHeadReaderTransitions
    (D : Description) : List TransitionDescription :=
  readyJumpTape0ReaderAllTransitions D ++
    afterRead0JumpTape1ReaderAllTransitions D ++
      afterRead1JumpTape2ReaderAllTransitions D

def threeHeadReaderDescription (D : Description) : MachineDescription where
  stateCount := threeHeadReaderStateLimit D
  start := StaticDispatcherState.ready D.start
  halt := StaticDispatcherState.ready D.halt
  transitions := threeHeadReaderTransitions D

theorem readyJumpDescription_sources_below_tape0ReaderOffset
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    TransitionSourcesBelow (tape0ReaderOffset D state)
      (readyJumpDescription D state).transitions := by
  apply blankHeadBounceJumpDescription_sources_below
  · exact
      Nat.lt_of_lt_of_le
        (Nat.lt_trans
          (ready_lt_readyJumpScratch D hstate)
          (readyJumpScratch_lt_readyJumpLimit D hstate))
        (by
          unfold tape0ReaderOffset tape0ReaderBlockBase
          exact Nat.le_add_right _ _)
  · have hlt := readyJumpScratch_lt_readyJumpLimit D hstate
    unfold tape0ReaderOffset tape0ReaderBlockBase
    lia

theorem afterRead0JumpDescription_sources_below_tape1ReaderOffset
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourcesBelow (tape1ReaderOffset D state read0)
      (afterRead0JumpDescription D state read0).transitions := by
  apply blankHeadBounceJumpDescription_sources_below
  · have hlow :=
      Nat.lt_of_lt_of_le
        (StaticDispatcherState.afterRead0_lt_afterRead1Base
          D read0 hstate)
        (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
    exact Nat.lt_of_lt_of_le hlow
      (readerStateLimit_le_tape1ReaderOffset D state read0)
  · have hscratch :=
      afterRead0JumpScratch_lt_afterRead0JumpLimit D read0 hstate
    have hbase :
        afterRead0JumpLimit D ≤ tape1ReaderOffset D state read0 := by
      unfold tape1ReaderOffset tape1ReaderBlockBase
      lia
    exact Nat.lt_of_lt_of_le hscratch hbase

theorem afterRead1JumpDescription_sources_below_tape2ReaderOffset
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourcesBelow (tape2ReaderOffset D state read0 read1)
      (afterRead1JumpDescription D state read0 read1).transitions := by
  apply blankHeadBounceJumpDescription_sources_below
  · have hlow :=
      StaticDispatcherState.afterRead1_lt_readerStateLimit
        D read0 read1 hstate
    exact Nat.lt_of_lt_of_le hlow
      (readerStateLimit_le_tape2ReaderOffset D state read0 read1)
  · have hscratch :=
      afterRead1JumpScratch_lt_afterRead1JumpLimit
        D read0 read1 hstate
    have hbase :
        afterRead1JumpLimit D ≤
          tape2ReaderOffset D state read0 read1 := by
      unfold tape2ReaderOffset tape2ReaderBlockBase
      lia
    exact Nat.lt_of_lt_of_le hscratch hbase

theorem readyJump_tape0Reader_sourceDisjoint
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    TransitionSourceDisjoint
      (readyJumpDescription D state).transitions
      (tape0ReaderDescription D state).transitions :=
  transitionSourceDisjoint_of_below_atLeast
    (readyJumpDescription_sources_below_tape0ReaderOffset D hstate)
    (tape0ReaderDescription_sources_atLeast D state)

theorem afterRead0Jump_tape1Reader_sourceDisjoint
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourceDisjoint
      (afterRead0JumpDescription D state read0).transitions
      (tape1ReaderDescription D state read0).transitions :=
  transitionSourceDisjoint_of_below_atLeast
    (afterRead0JumpDescription_sources_below_tape1ReaderOffset
      D read0 hstate)
    (tape1ReaderDescription_sources_atLeast D state read0)

theorem afterRead1Jump_tape2Reader_sourceDisjoint
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourceDisjoint
      (afterRead1JumpDescription D state read0 read1).transitions
      (tape2ReaderDescription D state read0 read1).transitions :=
  transitionSourceDisjoint_of_below_atLeast
    (afterRead1JumpDescription_sources_below_tape2ReaderOffset
      D read0 read1 hstate)
    (tape2ReaderDescription_sources_atLeast D state read0 read1)

theorem readyJumpTape0ReaderTransitions_deterministic
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    TransitionListDeterministic
      (readyJumpTape0ReaderTransitions D state) := by
  unfold readyJumpTape0ReaderTransitions
  exact
    transitionListDeterministic_append_of_sourceDisjoint
      (blankHeadBounceJumpDescription_transitionListDeterministic
        (ready_ne_readyJumpScratch D hstate))
      (transitionListDeterministic_of_wellFormed
        (tape0ReaderDescription_subroutineReady D hstate).left)
      (readyJump_tape0Reader_sourceDisjoint D hstate)

theorem afterRead0JumpTape1ReaderTransitions_deterministic
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionListDeterministic
      (afterRead0JumpTape1ReaderTransitions D state read0) := by
  unfold afterRead0JumpTape1ReaderTransitions
  exact
    transitionListDeterministic_append_of_sourceDisjoint
      (blankHeadBounceJumpDescription_transitionListDeterministic
        (afterRead0_ne_afterRead0JumpScratch D read0 hstate))
      (transitionListDeterministic_of_wellFormed
        (tape1ReaderDescription_subroutineReady D read0 hstate).left)
      (afterRead0Jump_tape1Reader_sourceDisjoint D read0 hstate)

theorem afterRead1JumpTape2ReaderTransitions_deterministic
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionListDeterministic
      (afterRead1JumpTape2ReaderTransitions D state read0 read1) := by
  unfold afterRead1JumpTape2ReaderTransitions
  exact
    transitionListDeterministic_append_of_sourceDisjoint
      (blankHeadBounceJumpDescription_transitionListDeterministic
        (afterRead1_ne_afterRead1JumpScratch D read0 read1 hstate))
      (transitionListDeterministic_of_wellFormed
        (tape2ReaderDescription_subroutineReady
          D read0 read1 hstate).left)
      (afterRead1Jump_tape2Reader_sourceDisjoint
        D read0 read1 hstate)

theorem readyJumpDescription_wellFormed
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    (readyJumpDescription D state).WellFormed := by
  have hsource :
      StaticDispatcherState.ready state < threeHeadReaderStateLimit D := by
    have hready := ready_lt_readyJumpScratch D hstate
    have hscratch := readyJumpScratch_lt_readyJumpLimit D hstate
    have hlimit : readyJumpLimit D ≤ threeHeadReaderStateLimit D := by
      unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
        afterRead1JumpLimit afterRead1JumpScratchBase tape1ReaderLimit
        tape1ReaderBlockBase afterRead0JumpLimit afterRead0JumpScratchBase
        tape0ReaderLimit tape0ReaderBlockBase
      lia
    exact Nat.lt_of_lt_of_le (Nat.lt_trans hready hscratch) hlimit
  have hscratch :
      readyJumpScratch D state < threeHeadReaderStateLimit D := by
    have hscratch := readyJumpScratch_lt_readyJumpLimit D hstate
    have hlimit : readyJumpLimit D ≤ threeHeadReaderStateLimit D := by
      unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
        afterRead1JumpLimit afterRead1JumpScratchBase tape1ReaderLimit
        tape1ReaderBlockBase afterRead0JumpLimit afterRead0JumpScratchBase
        tape0ReaderLimit tape0ReaderBlockBase
      lia
    exact Nat.lt_of_lt_of_le hscratch hlimit
  have htarget :
      tape0ReaderStart D state < threeHeadReaderStateLimit D := by
    have hstart :=
      (tape0ReaderDescription_subroutineReady D hstate).left.right.left
    exact Nat.lt_of_lt_of_le hstart
      (tape0ReaderDescription_stateCount_le_threeHeadReaderStateLimit
        D hstate)
  simpa [readyJumpDescription] using
    blankHeadBounceJumpDescription_wellFormed
      hsource hscratch htarget (ready_ne_readyJumpScratch D hstate)

theorem afterRead0JumpDescription_wellFormed
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    (afterRead0JumpDescription D state read0).WellFormed := by
  have hlimit : afterRead0JumpLimit D ≤ threeHeadReaderStateLimit D := by
    unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
      afterRead1JumpLimit afterRead1JumpScratchBase tape1ReaderLimit
      tape1ReaderBlockBase
    lia
  have hscratch0 :=
    afterRead0JumpScratch_lt_afterRead0JumpLimit D read0 hstate
  have hsource :
      StaticDispatcherState.afterRead0 D state read0 <
        threeHeadReaderStateLimit D := by
    have hsource0 := afterRead0_lt_afterRead0JumpScratch D read0 hstate
    exact Nat.lt_of_lt_of_le (Nat.lt_trans hsource0 hscratch0) hlimit
  have hscratch :
      afterRead0JumpScratch D state read0 <
        threeHeadReaderStateLimit D :=
    Nat.lt_of_lt_of_le hscratch0 hlimit
  have htarget :
      tape1ReaderStart D state read0 < threeHeadReaderStateLimit D := by
    have hstart :=
      (tape1ReaderDescription_subroutineReady D read0 hstate).left.right.left
    exact Nat.lt_of_lt_of_le hstart
      (tape1ReaderDescription_stateCount_le_threeHeadReaderStateLimit
        D read0 hstate)
  simpa [afterRead0JumpDescription] using
    blankHeadBounceJumpDescription_wellFormed
      hsource hscratch htarget
      (afterRead0_ne_afterRead0JumpScratch D read0 hstate)

theorem afterRead1JumpDescription_wellFormed
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    (afterRead1JumpDescription D state read0 read1).WellFormed := by
  have hlimit : afterRead1JumpLimit D ≤ threeHeadReaderStateLimit D := by
    unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
    lia
  have hscratch0 :=
    afterRead1JumpScratch_lt_afterRead1JumpLimit
      D read0 read1 hstate
  have hsource :
      StaticDispatcherState.afterRead1 D state read0 read1 <
        threeHeadReaderStateLimit D := by
    have hsource0 :=
      afterRead1_lt_afterRead1JumpScratch D read0 read1 hstate
    exact Nat.lt_of_lt_of_le (Nat.lt_trans hsource0 hscratch0) hlimit
  have hscratch :
      afterRead1JumpScratch D state read0 read1 <
        threeHeadReaderStateLimit D :=
    Nat.lt_of_lt_of_le hscratch0 hlimit
  have htarget :
      tape2ReaderStart D state read0 read1 <
        threeHeadReaderStateLimit D := by
    have hstart :=
      (tape2ReaderDescription_subroutineReady
        D read0 read1 hstate).left.right.left
    exact Nat.lt_of_lt_of_le hstart
      (tape2ReaderDescription_stateCount_le_threeHeadReaderStateLimit
        D read0 read1 hstate)
  simpa [afterRead1JumpDescription] using
    blankHeadBounceJumpDescription_wellFormed
      hsource hscratch htarget
      (afterRead1_ne_afterRead1JumpScratch D read0 read1 hstate)

theorem readyJumpTape0ReaderTransitions_wellFormed
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    TransitionListWellFormed (threeHeadReaderStateLimit D)
      (readyJumpTape0ReaderTransitions D state) := by
  unfold readyJumpTape0ReaderTransitions
  apply transitionListWellFormed_append
  · exact
      transitionListWellFormed_of_wellFormed_mono
        (readyJumpDescription_wellFormed D hstate)
        (by simp [readyJumpDescription, blankHeadBounceJumpDescription])
  · exact
      transitionListWellFormed_of_wellFormed_mono
        (tape0ReaderDescription_subroutineReady D hstate).left
        (tape0ReaderDescription_stateCount_le_threeHeadReaderStateLimit
          D hstate)

theorem afterRead0JumpTape1ReaderTransitions_wellFormed
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionListWellFormed (threeHeadReaderStateLimit D)
      (afterRead0JumpTape1ReaderTransitions D state read0) := by
  unfold afterRead0JumpTape1ReaderTransitions
  apply transitionListWellFormed_append
  · exact
      transitionListWellFormed_of_wellFormed_mono
        (afterRead0JumpDescription_wellFormed D read0 hstate)
        (by
          simp [afterRead0JumpDescription, blankHeadBounceJumpDescription])
  · exact
      transitionListWellFormed_of_wellFormed_mono
        (tape1ReaderDescription_subroutineReady D read0 hstate).left
        (tape1ReaderDescription_stateCount_le_threeHeadReaderStateLimit
          D read0 hstate)

theorem afterRead1JumpTape2ReaderTransitions_wellFormed
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionListWellFormed (threeHeadReaderStateLimit D)
      (afterRead1JumpTape2ReaderTransitions D state read0 read1) := by
  unfold afterRead1JumpTape2ReaderTransitions
  apply transitionListWellFormed_append
  · exact
      transitionListWellFormed_of_wellFormed_mono
        (afterRead1JumpDescription_wellFormed D read0 read1 hstate)
        (by
          simp [afterRead1JumpDescription, blankHeadBounceJumpDescription])
  · exact
      transitionListWellFormed_of_wellFormed_mono
        (tape2ReaderDescription_subroutineReady
          D read0 read1 hstate).left
        (tape2ReaderDescription_stateCount_le_threeHeadReaderStateLimit
          D read0 read1 hstate)

theorem readyJumpTape0ReaderTransitions_source_cases
    (D : Description) {state : Nat}
    {t : TransitionDescription}
    (ht : t ∈ readyJumpTape0ReaderTransitions D state) :
    t.source = StaticDispatcherState.ready state ∨
      t.source = readyJumpScratch D state ∨
        tape0ReaderOffset D state ≤ t.source ∧
          t.source <
            tape0ReaderOffset D state +
              branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount := by
  unfold readyJumpTape0ReaderTransitions at ht
  simp at ht
  rcases ht with ht | ht
  · rcases
      blankHeadBounceJumpDescription_transition_source_cases ht with
      hsource | hscratch
    · exact Or.inl hsource
    · exact Or.inr (Or.inl hscratch)
  · exact Or.inr (Or.inr
      (tape0ReaderDescription_sources_in_block D state t ht))

theorem afterRead0JumpTape1ReaderTransitions_source_cases
    (D : Description) {state : Nat} (read0 : Option Bool)
    {t : TransitionDescription}
    (ht : t ∈ afterRead0JumpTape1ReaderTransitions D state read0) :
    t.source = StaticDispatcherState.afterRead0 D state read0 ∨
      t.source = afterRead0JumpScratch D state read0 ∨
        tape1ReaderOffset D state read0 ≤ t.source ∧
          t.source <
            tape1ReaderOffset D state read0 +
              branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount := by
  unfold afterRead0JumpTape1ReaderTransitions at ht
  simp at ht
  rcases ht with ht | ht
  · rcases
      blankHeadBounceJumpDescription_transition_source_cases ht with
      hsource | hscratch
    · exact Or.inl hsource
    · exact Or.inr (Or.inl hscratch)
  · exact Or.inr (Or.inr
      (tape1ReaderDescription_sources_in_block D state read0 t ht))

theorem afterRead1JumpTape2ReaderTransitions_source_cases
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    {t : TransitionDescription}
    (ht : t ∈ afterRead1JumpTape2ReaderTransitions D state read0 read1) :
    t.source = StaticDispatcherState.afterRead1 D state read0 read1 ∨
      t.source = afterRead1JumpScratch D state read0 read1 ∨
        tape2ReaderOffset D state read0 read1 ≤ t.source ∧
          t.source <
            tape2ReaderOffset D state read0 read1 +
              branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount := by
  unfold afterRead1JumpTape2ReaderTransitions at ht
  simp at ht
  rcases ht with ht | ht
  · rcases
      blankHeadBounceJumpDescription_transition_source_cases ht with
      hsource | hscratch
    · exact Or.inl hsource
    · exact Or.inr (Or.inl hscratch)
  · exact Or.inr (Or.inr
      (tape2ReaderDescription_sources_in_block D state read0 read1 t ht))

theorem readyJumpTape0ReaderTransitions_sourceDisjoint_of_ne
    (D : Description) {state₀ state₁ : Nat}
    (hstate₀ : state₀ < D.stateCount)
    (hstate₁ : state₁ < D.stateCount)
    (hne : state₀ ≠ state₁) :
    TransitionSourceDisjoint
      (readyJumpTape0ReaderTransitions D state₀)
      (readyJumpTape0ReaderTransitions D state₁) := by
  intro t u ht hu hsource
  have hleftCases :=
    readyJumpTape0ReaderTransitions_source_cases D ht
  have hrightCases :=
    readyJumpTape0ReaderTransitions_source_cases D hu
  rcases hleftCases with hleftReady | hleftCases
  · rcases hrightCases with hrightReady | hrightCases
    · have heq : state₀ = state₁ := by
        rw [hleftReady, hrightReady] at hsource
        simpa [StaticDispatcherState.ready] using hsource
      exact hne heq
    · rcases hrightCases with hrightScratch | hrightReader
      · have hreadyLt :
            StaticDispatcherState.ready state₀ <
              StaticDispatcherState.readerStateLimit D := by
          unfold StaticDispatcherState.ready
            StaticDispatcherState.readerStateLimit
            StaticDispatcherState.afterRead1Base
            StaticDispatcherState.afterRead0Base
          lia
        have hscratchGe :
            StaticDispatcherState.readerStateLimit D ≤
              readyJumpScratch D state₁ := by
          unfold readyJumpScratch readyJumpScratchBase
          lia
        rw [hleftReady, hrightScratch] at hsource
        lia
      · have hreadyLt :=
          Nat.lt_trans (ready_lt_readyJumpScratch D hstate₀)
            (readyJumpScratch_lt_readyJumpLimit D hstate₀)
        have hreaderGe : readyJumpLimit D ≤ u.source := by
          exact Nat.le_trans
            (by
              unfold tape0ReaderOffset tape0ReaderBlockBase
              exact Nat.le_add_right _ _)
            hrightReader.left
        rw [hleftReady] at hsource
        lia
  · rcases hleftCases with hleftScratch | hleftReader
    · rcases hrightCases with hrightReady | hrightCases
      · have hreadyLt :
            StaticDispatcherState.ready state₁ <
              StaticDispatcherState.readerStateLimit D := by
          unfold StaticDispatcherState.ready
            StaticDispatcherState.readerStateLimit
            StaticDispatcherState.afterRead1Base
            StaticDispatcherState.afterRead0Base
          lia
        have hscratchGe :
            StaticDispatcherState.readerStateLimit D ≤
              readyJumpScratch D state₀ := by
          unfold readyJumpScratch readyJumpScratchBase
          lia
        rw [hleftScratch, hrightReady] at hsource
        lia
      · rcases hrightCases with hrightScratch | hrightReader
        · have heq : state₀ = state₁ := by
            rw [hleftScratch, hrightScratch] at hsource
            unfold readyJumpScratch at hsource
            lia
          exact hne heq
        · have hscratchLt :=
            readyJumpScratch_lt_readyJumpLimit D hstate₀
          have hreaderGe : readyJumpLimit D ≤ u.source := by
            exact Nat.le_trans
              (by
                unfold tape0ReaderOffset tape0ReaderBlockBase
                exact Nat.le_add_right _ _)
              hrightReader.left
          rw [hleftScratch] at hsource
          lia
    · rcases hrightCases with hrightReady | hrightCases
      · have hreadyLt :=
          Nat.lt_trans (ready_lt_readyJumpScratch D hstate₁)
            (readyJumpScratch_lt_readyJumpLimit D hstate₁)
        have hreaderGe : readyJumpLimit D ≤ t.source := by
          exact Nat.le_trans
            (by
              unfold tape0ReaderOffset tape0ReaderBlockBase
              exact Nat.le_add_right _ _)
            hleftReader.left
        rw [hrightReady] at hsource
        lia
      · rcases hrightCases with hrightScratch | hrightReader
        · have hscratchLt :=
            readyJumpScratch_lt_readyJumpLimit D hstate₁
          have hreaderGe : readyJumpLimit D ≤ t.source := by
            exact Nat.le_trans
              (by
                unfold tape0ReaderOffset tape0ReaderBlockBase
                exact Nat.le_add_right _ _)
              hleftReader.left
          rw [hrightScratch] at hsource
          lia
        · have hrightReader' := hrightReader
          rw [← hsource] at hrightReader'
          unfold tape0ReaderOffset tape0ReaderBlockBase at hleftReader hrightReader'
          exact
            indexedReaderBlocks_source_ne_of_state_ne
              (base := readyJumpLimit D)
              (blockCount :=
                branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount)
              (source := t.source)
              hne hleftReader hrightReader'

theorem readyJumpTape0ReaderTransitions_sources_ne_halt
    (D : Description) {state : Nat}
    (hhalt : D.halt < D.stateCount)
    (hstate : state < D.stateCount) (hne : state ≠ D.halt) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (readyJumpTape0ReaderTransitions D state) := by
  intro t ht
  rcases readyJumpTape0ReaderTransitions_source_cases D ht with
    hsource | hcases
  · rw [hsource]
    simpa [StaticDispatcherState.ready] using hne
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      unfold StaticDispatcherState.ready readyJumpScratch
        readyJumpScratchBase StaticDispatcherState.readerStateLimit
        StaticDispatcherState.afterRead1Base
        StaticDispatcherState.afterRead0Base
      lia
    · have hlow := hreader.left
      unfold tape0ReaderOffset tape0ReaderBlockBase
        readyJumpLimit readyJumpScratchBase
        StaticDispatcherState.readerStateLimit
        StaticDispatcherState.afterRead1Base
        StaticDispatcherState.afterRead0Base at hlow
      unfold StaticDispatcherState.ready
      lia

theorem afterRead0JumpTape1ReaderTransitions_sources_ne_halt
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hhalt : D.halt < D.stateCount)
    (_hstate : state < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (afterRead0JumpTape1ReaderTransitions D state read0) := by
  intro t ht
  rcases afterRead0JumpTape1ReaderTransitions_source_cases D read0 ht with
    hsource | hcases
  · rw [hsource]
    unfold StaticDispatcherState.ready StaticDispatcherState.afterRead0
      StaticDispatcherState.afterRead0Base
    lia
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      unfold StaticDispatcherState.ready afterRead0JumpScratch
        afterRead0JumpScratchBase tape0ReaderLimit tape0ReaderBlockBase
        readyJumpLimit readyJumpScratchBase
        StaticDispatcherState.readerStateLimit
        StaticDispatcherState.afterRead1Base
        StaticDispatcherState.afterRead0Base
      lia
    · have hlow := hreader.left
      unfold tape1ReaderOffset tape1ReaderBlockBase
        afterRead0JumpLimit afterRead0JumpScratchBase
        tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
        readyJumpScratchBase StaticDispatcherState.readerStateLimit
        StaticDispatcherState.afterRead1Base
        StaticDispatcherState.afterRead0Base at hlow
      unfold StaticDispatcherState.ready
      lia

theorem afterRead1JumpTape2ReaderTransitions_sources_ne_halt
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hhalt : D.halt < D.stateCount)
    (_hstate : state < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (afterRead1JumpTape2ReaderTransitions D state read0 read1) := by
  intro t ht
  rcases afterRead1JumpTape2ReaderTransitions_source_cases
      D read0 read1 ht with
    hsource | hcases
  · rw [hsource]
    unfold StaticDispatcherState.ready StaticDispatcherState.afterRead1
      StaticDispatcherState.afterRead1Base
      StaticDispatcherState.afterRead0Base
    lia
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      unfold StaticDispatcherState.ready afterRead1JumpScratch
        afterRead1JumpScratchBase tape1ReaderLimit tape1ReaderBlockBase
        afterRead0JumpLimit afterRead0JumpScratchBase
        tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
        readyJumpScratchBase StaticDispatcherState.readerStateLimit
        StaticDispatcherState.afterRead1Base
        StaticDispatcherState.afterRead0Base
      lia
    · have hlow := hreader.left
      unfold tape2ReaderOffset tape2ReaderBlockBase
        afterRead1JumpLimit afterRead1JumpScratchBase
        tape1ReaderLimit tape1ReaderBlockBase
        afterRead0JumpLimit afterRead0JumpScratchBase
        tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
        readyJumpScratchBase StaticDispatcherState.readerStateLimit
        StaticDispatcherState.afterRead1Base
        StaticDispatcherState.afterRead0Base at hlow
      unfold StaticDispatcherState.ready
      lia

theorem readyJumpTape0Reader_afterRead0JumpTape1Reader_sourceDisjoint
    (D : Description) {readyState afterState : Nat}
    (read0 : Option Bool)
    (hready : readyState < D.stateCount)
    (hafter : afterState < D.stateCount) :
    TransitionSourceDisjoint
      (readyJumpTape0ReaderTransitions D readyState)
      (afterRead0JumpTape1ReaderTransitions D afterState read0) := by
  intro t u ht hu hsource
  have hreadyCases :=
    readyJumpTape0ReaderTransitions_source_cases D ht
  have hafterCases :=
    afterRead0JumpTape1ReaderTransitions_source_cases D read0 hu
  rcases hreadyCases with hreadySource | hreadyCases
  · rcases hafterCases with hafterSource | hafterCases
    · have hEq :
          StaticDispatcherState.ready readyState =
            StaticDispatcherState.afterRead0 D afterState read0 := by
        rw [← hreadySource, hsource, hafterSource]
      have hcode := ReadTuple3.readCode_lt_three read0
      unfold StaticDispatcherState.ready StaticDispatcherState.afterRead0
        StaticDispatcherState.afterRead0Base at hEq
      lia
    · rcases hafterCases with hafterScratch | hafterReader
      · have hEq :
            StaticDispatcherState.ready readyState =
              afterRead0JumpScratch D afterState read0 := by
          rw [← hreadySource, hsource, hafterScratch]
        have hcode := ReadTuple3.readCode_lt_three read0
        unfold StaticDispatcherState.ready afterRead0JumpScratch
          afterRead0JumpScratchBase tape0ReaderLimit tape0ReaderBlockBase
          readyJumpLimit readyJumpScratchBase
          StaticDispatcherState.readerStateLimit
          StaticDispatcherState.afterRead1Base
          StaticDispatcherState.afterRead0Base at hEq
        lia
      · have hEq :
            StaticDispatcherState.ready readyState = u.source := by
          rw [← hreadySource, hsource]
        have huLower : D.stateCount ≤ u.source := by
          have hblock := hafterReader.left
          unfold tape1ReaderOffset tape1ReaderBlockBase
            afterRead0JumpLimit afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase StaticDispatcherState.readerStateLimit
            StaticDispatcherState.afterRead1Base
            StaticDispatcherState.afterRead0Base at hblock
          lia
        unfold StaticDispatcherState.ready at hEq
        lia
  · rcases hreadyCases with hreadyScratch | hreadyReader
    · rcases hafterCases with hafterSource | hafterCases
      · have hEq :
            readyJumpScratch D readyState =
              StaticDispatcherState.afterRead0 D afterState read0 := by
          rw [← hreadyScratch, hsource, hafterSource]
        have hcode := ReadTuple3.readCode_lt_three read0
        simp [readyJumpScratch, readyJumpScratchBase,
          StaticDispatcherState.readerStateLimit,
          StaticDispatcherState.afterRead1Base,
          StaticDispatcherState.afterRead0Base,
          StaticDispatcherState.afterRead0] at hEq
        lia
      · rcases hafterCases with hafterScratch | hafterReader
        · have hEq :
              readyJumpScratch D readyState =
                afterRead0JumpScratch D afterState read0 := by
            rw [← hreadyScratch, hsource, hafterScratch]
          have hcode := ReadTuple3.readCode_lt_three read0
          simp [readyJumpScratch, readyJumpScratchBase,
            afterRead0JumpScratch, afterRead0JumpScratchBase,
            tape0ReaderLimit, tape0ReaderBlockBase, readyJumpLimit] at hEq
          lia
        · have hEq : readyJumpScratch D readyState = u.source := by
            rw [← hreadyScratch, hsource]
          have huLower : readyJumpLimit D ≤ u.source := by
            have hblock := hafterReader.left
            unfold tape1ReaderOffset tape1ReaderBlockBase
              afterRead0JumpLimit afterRead0JumpScratchBase
              tape0ReaderLimit tape0ReaderBlockBase at hblock
            lia
          have hscratchLt :
              readyJumpScratch D readyState < readyJumpLimit D :=
            readyJumpScratch_lt_readyJumpLimit D hready
          lia
    · rcases hafterCases with hafterSource | hafterCases
      · have hEq :
            t.source =
              StaticDispatcherState.afterRead0 D afterState read0 := by
          rw [hsource, hafterSource]
        have hafterLt :
            StaticDispatcherState.afterRead0 D afterState read0 <
              tape0ReaderOffset D readyState := by
          have hlow :=
            Nat.lt_of_lt_of_le
              (StaticDispatcherState.afterRead0_lt_afterRead1Base
                D read0 hafter)
              (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
          exact Nat.lt_of_lt_of_le hlow
            (readerStateLimit_le_tape0ReaderOffset D readyState)
        lia
      · rcases hafterCases with hafterScratch | hafterReader
        · have hEq :
              t.source = afterRead0JumpScratch D afterState read0 := by
            rw [hsource, hafterScratch]
          have hreadyLt : t.source < tape0ReaderLimit D :=
            Nat.lt_of_lt_of_le hreadyReader.right
              (tape0ReaderOffset_blockEnd_le_tape0ReaderLimit D hready)
          have hscratchLower :
              tape0ReaderLimit D ≤
                afterRead0JumpScratch D afterState read0 := by
            unfold afterRead0JumpScratch afterRead0JumpScratchBase
            lia
          lia
        · have hEq : t.source = u.source := hsource
          have hreadyLt : t.source < tape0ReaderLimit D :=
            Nat.lt_of_lt_of_le hreadyReader.right
              (tape0ReaderOffset_blockEnd_le_tape0ReaderLimit D hready)
          have huLower : tape0ReaderLimit D ≤ u.source := by
            have hblock := hafterReader.left
            unfold tape1ReaderOffset tape1ReaderBlockBase
              afterRead0JumpLimit afterRead0JumpScratchBase at hblock
            lia
          lia

theorem afterRead0JumpTape1Reader_afterRead1JumpTape2Reader_sourceDisjoint
    (D : Description) {state0 state1 : Nat}
    (read0 read0' read1 : Option Bool)
    (hstate0 : state0 < D.stateCount)
    (hstate1 : state1 < D.stateCount) :
    TransitionSourceDisjoint
      (afterRead0JumpTape1ReaderTransitions D state0 read0)
      (afterRead1JumpTape2ReaderTransitions D state1 read0' read1) := by
  intro t u ht hu hsource
  have hleftCases :=
    afterRead0JumpTape1ReaderTransitions_source_cases D read0 ht
  have hrightCases :=
    afterRead1JumpTape2ReaderTransitions_source_cases D read0' read1 hu
  rcases hleftCases with hleftSource | hleftCases
  · rcases hrightCases with hrightSource | hrightCases
    · have hEq :
          StaticDispatcherState.afterRead0 D state0 read0 =
            StaticDispatcherState.afterRead1 D state1 read0' read1 := by
        rw [← hleftSource, hsource, hrightSource]
      have hleftLt :=
        StaticDispatcherState.afterRead0_lt_afterRead1Base
          D read0 hstate0
      have hrightGe :=
        StaticDispatcherState.afterRead1Base_le_afterRead1
          D state1 read0' read1
      lia
    · rcases hrightCases with hrightScratch | hrightReader
      · have hEq :
            StaticDispatcherState.afterRead0 D state0 read0 =
              afterRead1JumpScratch D state1 read0' read1 := by
          rw [← hleftSource, hsource, hrightScratch]
        have hleftLt :=
          Nat.lt_of_lt_of_le
            (StaticDispatcherState.afterRead0_lt_afterRead1Base
              D read0 hstate0)
            (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
        have hrightGe :
            StaticDispatcherState.readerStateLimit D ≤
              afterRead1JumpScratch D state1 read0' read1 := by
          unfold afterRead1JumpScratch afterRead1JumpScratchBase
            tape1ReaderLimit tape1ReaderBlockBase
            afterRead0JumpLimit afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase
          lia
        lia
      · have hEq :
            StaticDispatcherState.afterRead0 D state0 read0 = u.source := by
          rw [← hleftSource, hsource]
        have hleftLt :
            StaticDispatcherState.afterRead0 D state0 read0 <
              StaticDispatcherState.readerStateLimit D :=
          Nat.lt_of_lt_of_le
            (StaticDispatcherState.afterRead0_lt_afterRead1Base
              D read0 hstate0)
            (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
        have hrightGe :
            StaticDispatcherState.readerStateLimit D ≤ u.source := by
          have hblock := hrightReader.left
          unfold tape2ReaderOffset tape2ReaderBlockBase
            afterRead1JumpLimit afterRead1JumpScratchBase
            tape1ReaderLimit tape1ReaderBlockBase
            afterRead0JumpLimit afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase at hblock
          lia
        lia
  · rcases hleftCases with hleftScratch | hleftReader
    · rcases hrightCases with hrightSource | hrightCases
      · have hEq :
            afterRead0JumpScratch D state0 read0 =
              StaticDispatcherState.afterRead1 D state1 read0' read1 := by
          rw [← hleftScratch, hsource, hrightSource]
        have hleftGe :
            StaticDispatcherState.readerStateLimit D ≤
              afterRead0JumpScratch D state0 read0 := by
          unfold afterRead0JumpScratch afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase
          lia
        have hrightLt :=
          StaticDispatcherState.afterRead1_lt_readerStateLimit
            D read0' read1 hstate1
        lia
      · rcases hrightCases with hrightScratch | hrightReader
        · have hEq :
              afterRead0JumpScratch D state0 read0 =
                afterRead1JumpScratch D state1 read0' read1 := by
            rw [← hleftScratch, hsource, hrightScratch]
          have hleftLt :=
            afterRead0JumpScratch_lt_afterRead0JumpLimit
              D read0 hstate0
          have hrightGe :
              afterRead0JumpLimit D ≤
                afterRead1JumpScratch D state1 read0' read1 := by
            unfold afterRead1JumpScratch afterRead1JumpScratchBase
              tape1ReaderLimit tape1ReaderBlockBase
            lia
          lia
        · have hEq : afterRead0JumpScratch D state0 read0 = u.source := by
            rw [← hleftScratch, hsource]
          have hleftLt :=
            afterRead0JumpScratch_lt_afterRead0JumpLimit
              D read0 hstate0
          have hrightGe : afterRead0JumpLimit D ≤ u.source := by
            have hblock := hrightReader.left
            unfold tape2ReaderOffset tape2ReaderBlockBase
              afterRead1JumpLimit afterRead1JumpScratchBase
              tape1ReaderLimit tape1ReaderBlockBase at hblock
            lia
          lia
    · rcases hrightCases with hrightSource | hrightCases
      · have hEq :
            t.source =
              StaticDispatcherState.afterRead1 D state1 read0' read1 := by
          rw [hsource, hrightSource]
        have hleftGe :
            StaticDispatcherState.readerStateLimit D ≤ t.source := by
          have hblock := hleftReader.left
          unfold tape1ReaderOffset tape1ReaderBlockBase
            afterRead0JumpLimit afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase at hblock
          lia
        have hrightLt :=
          StaticDispatcherState.afterRead1_lt_readerStateLimit
            D read0' read1 hstate1
        lia
      · rcases hrightCases with hrightScratch | hrightReader
        · have hEq :
              t.source = afterRead1JumpScratch D state1 read0' read1 := by
            rw [hsource, hrightScratch]
          have hleftLt : t.source < tape1ReaderLimit D := by
            exact
              Nat.lt_of_lt_of_le hleftReader.right
                (tape1ReaderOffset_blockEnd_le_tape1ReaderLimit
                  D read0 hstate0)
          have hrightGe :
              tape1ReaderLimit D ≤
                afterRead1JumpScratch D state1 read0' read1 := by
            unfold afterRead1JumpScratch afterRead1JumpScratchBase
            lia
          lia
        · have hEq : t.source = u.source := hsource
          have hleftLt : t.source < tape1ReaderLimit D := by
            exact
              Nat.lt_of_lt_of_le hleftReader.right
                (tape1ReaderOffset_blockEnd_le_tape1ReaderLimit
                  D read0 hstate0)
          have hrightGe : tape1ReaderLimit D ≤ u.source := by
            have hblock := hrightReader.left
            unfold tape2ReaderOffset tape2ReaderBlockBase
              afterRead1JumpLimit afterRead1JumpScratchBase at hblock
            lia
          lia

theorem readyJumpTape0Reader_afterRead1JumpTape2Reader_sourceDisjoint
    (D : Description) {readyState afterState : Nat}
    (read0 read1 : Option Bool)
    (hready : readyState < D.stateCount)
    (hafter : afterState < D.stateCount) :
    TransitionSourceDisjoint
      (readyJumpTape0ReaderTransitions D readyState)
      (afterRead1JumpTape2ReaderTransitions D afterState read0 read1) := by
  intro t u ht hu hsource
  have hreadyCases :=
    readyJumpTape0ReaderTransitions_source_cases D ht
  have hafterCases :=
    afterRead1JumpTape2ReaderTransitions_source_cases D read0 read1 hu
  rcases hreadyCases with hreadySource | hreadyCases
  · rcases hafterCases with hafterSource | hafterCases
    · have hEq :
          StaticDispatcherState.ready readyState =
            StaticDispatcherState.afterRead1 D afterState read0 read1 := by
        rw [← hreadySource, hsource, hafterSource]
      have hreadyLt : StaticDispatcherState.ready readyState < D.stateCount := by
        simpa [StaticDispatcherState.ready] using hready
      have hafterGe : D.stateCount ≤
          StaticDispatcherState.afterRead1 D afterState read0 read1 := by
        have hbase :=
          StaticDispatcherState.afterRead1Base_le_afterRead1
            D afterState read0 read1
        unfold StaticDispatcherState.afterRead1Base
          StaticDispatcherState.afterRead0Base at hbase
        lia
      lia
    · rcases hafterCases with hafterScratch | hafterReader
      · have hEq :
            StaticDispatcherState.ready readyState =
              afterRead1JumpScratch D afterState read0 read1 := by
          rw [← hreadySource, hsource, hafterScratch]
        have hreadyLt : StaticDispatcherState.ready readyState < D.stateCount := by
          simpa [StaticDispatcherState.ready] using hready
        have hafterGe : D.stateCount ≤
            afterRead1JumpScratch D afterState read0 read1 := by
          unfold afterRead1JumpScratch afterRead1JumpScratchBase
            tape1ReaderLimit tape1ReaderBlockBase
            afterRead0JumpLimit afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase StaticDispatcherState.readerStateLimit
            StaticDispatcherState.afterRead1Base
            StaticDispatcherState.afterRead0Base
          lia
        lia
      · have hEq : StaticDispatcherState.ready readyState = u.source := by
          rw [← hreadySource, hsource]
        have hreadyLt : StaticDispatcherState.ready readyState < D.stateCount := by
          simpa [StaticDispatcherState.ready] using hready
        have hafterGe : D.stateCount ≤ u.source := by
          have hblock := hafterReader.left
          unfold tape2ReaderOffset tape2ReaderBlockBase
            afterRead1JumpLimit afterRead1JumpScratchBase
            tape1ReaderLimit tape1ReaderBlockBase
            afterRead0JumpLimit afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase StaticDispatcherState.readerStateLimit
            StaticDispatcherState.afterRead1Base
            StaticDispatcherState.afterRead0Base at hblock
          lia
        lia
  · rcases hreadyCases with hreadyScratch | hreadyReader
    · rcases hafterCases with hafterSource | hafterCases
      · have hEq :
            readyJumpScratch D readyState =
              StaticDispatcherState.afterRead1 D afterState read0 read1 := by
          rw [← hreadyScratch, hsource, hafterSource]
        have hreadyGe :
            StaticDispatcherState.readerStateLimit D ≤
              readyJumpScratch D readyState := by
          unfold readyJumpScratch readyJumpScratchBase
          lia
        have hafterLt :=
          StaticDispatcherState.afterRead1_lt_readerStateLimit
            D read0 read1 hafter
        lia
      · rcases hafterCases with hafterScratch | hafterReader
        · have hEq :
              readyJumpScratch D readyState =
                afterRead1JumpScratch D afterState read0 read1 := by
            rw [← hreadyScratch, hsource, hafterScratch]
          have hreadyLt :=
            readyJumpScratch_lt_readyJumpLimit D hready
          have hafterGe :
              readyJumpLimit D ≤
                afterRead1JumpScratch D afterState read0 read1 := by
            unfold afterRead1JumpScratch afterRead1JumpScratchBase
              tape1ReaderLimit tape1ReaderBlockBase
              afterRead0JumpLimit afterRead0JumpScratchBase
              tape0ReaderLimit tape0ReaderBlockBase
            lia
          lia
        · have hEq : readyJumpScratch D readyState = u.source := by
            rw [← hreadyScratch, hsource]
          have hreadyLt :=
            readyJumpScratch_lt_readyJumpLimit D hready
          have hafterGe : readyJumpLimit D ≤ u.source := by
            have hblock := hafterReader.left
            unfold tape2ReaderOffset tape2ReaderBlockBase
              afterRead1JumpLimit afterRead1JumpScratchBase
              tape1ReaderLimit tape1ReaderBlockBase
              afterRead0JumpLimit afterRead0JumpScratchBase
              tape0ReaderLimit tape0ReaderBlockBase at hblock
            lia
          lia
    · rcases hafterCases with hafterSource | hafterCases
      · have hEq :
            t.source =
              StaticDispatcherState.afterRead1 D afterState read0 read1 := by
          rw [hsource, hafterSource]
        have hreadyGe :
            StaticDispatcherState.readerStateLimit D ≤ t.source := by
          have hblock := hreadyReader.left
          unfold tape0ReaderOffset tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase at hblock
          lia
        have hafterLt :=
          StaticDispatcherState.afterRead1_lt_readerStateLimit
            D read0 read1 hafter
        lia
      · rcases hafterCases with hafterScratch | hafterReader
        · have hEq :
              t.source = afterRead1JumpScratch D afterState read0 read1 := by
            rw [hsource, hafterScratch]
          have hreadyLt : t.source < tape0ReaderLimit D :=
            Nat.lt_of_lt_of_le hreadyReader.right
              (tape0ReaderOffset_blockEnd_le_tape0ReaderLimit D hready)
          have hafterGe :
              tape0ReaderLimit D ≤
                afterRead1JumpScratch D afterState read0 read1 := by
            unfold afterRead1JumpScratch afterRead1JumpScratchBase
              tape1ReaderLimit tape1ReaderBlockBase
              afterRead0JumpLimit afterRead0JumpScratchBase
            lia
          lia
        · have hEq : t.source = u.source := hsource
          have hreadyLt : t.source < tape0ReaderLimit D :=
            Nat.lt_of_lt_of_le hreadyReader.right
              (tape0ReaderOffset_blockEnd_le_tape0ReaderLimit D hready)
          have hafterGe : tape0ReaderLimit D ≤ u.source := by
            have hblock := hafterReader.left
            unfold tape2ReaderOffset tape2ReaderBlockBase
              afterRead1JumpLimit afterRead1JumpScratchBase
              tape1ReaderLimit tape1ReaderBlockBase
              afterRead0JumpLimit afterRead0JumpScratchBase at hblock
            lia
          lia

theorem readyJumpTape0ReaderAll_afterRead0JumpTape1ReaderAll_sourceDisjoint
    (D : Description) :
    TransitionSourceDisjoint
      (readyJumpTape0ReaderAllTransitions D)
      (afterRead0JumpTape1ReaderAllTransitions D) := by
  unfold readyJumpTape0ReaderAllTransitions
    afterRead0JumpTape1ReaderAllTransitions
  apply transitionSourceDisjoint_flatMap_left
  intro readyState hreadyState
  apply transitionSourceDisjoint_flatMap_right
  intro read0 _hread0
  apply transitionSourceDisjoint_flatMap_right
  intro afterState hafterState
  exact
    readyJumpTape0Reader_afterRead0JumpTape1Reader_sourceDisjoint
      D read0
      (activeStateValues_mem_lt hreadyState)
      (activeStateValues_mem_lt hafterState)

theorem readyJumpTape0ReaderAllTransitions_deterministic
    (D : Description) :
    TransitionListDeterministic
      (readyJumpTape0ReaderAllTransitions D) := by
  unfold readyJumpTape0ReaderAllTransitions
  apply transitionListDeterministic_flatMap
  · intro state hstate
    exact
      readyJumpTape0ReaderTransitions_deterministic
        D (activeStateValues_mem_lt hstate)
  · intro state₀ hstate₀ state₁ hstate₁ hne
    exact
      readyJumpTape0ReaderTransitions_sourceDisjoint_of_ne
        D
        (activeStateValues_mem_lt hstate₀)
        (activeStateValues_mem_lt hstate₁)
        hne

theorem afterRead0JumpTape1ReaderAll_afterRead1JumpTape2ReaderAll_sourceDisjoint
    (D : Description) :
    TransitionSourceDisjoint
      (afterRead0JumpTape1ReaderAllTransitions D)
      (afterRead1JumpTape2ReaderAllTransitions D) := by
  unfold afterRead0JumpTape1ReaderAllTransitions
    afterRead1JumpTape2ReaderAllTransitions
  apply transitionSourceDisjoint_flatMap_left
  intro read0 _hread0
  apply transitionSourceDisjoint_flatMap_left
  intro state0 hstate0
  apply transitionSourceDisjoint_flatMap_right
  intro read0' _hread0'
  apply transitionSourceDisjoint_flatMap_right
  intro read1 _hread1
  apply transitionSourceDisjoint_flatMap_right
  intro state1 hstate1
  exact
    afterRead0JumpTape1Reader_afterRead1JumpTape2Reader_sourceDisjoint
      D read0 read0' read1
      (activeStateValues_mem_lt hstate0)
      (activeStateValues_mem_lt hstate1)

theorem readyJumpTape0ReaderAll_afterRead1JumpTape2ReaderAll_sourceDisjoint
    (D : Description) :
    TransitionSourceDisjoint
      (readyJumpTape0ReaderAllTransitions D)
      (afterRead1JumpTape2ReaderAllTransitions D) := by
  unfold readyJumpTape0ReaderAllTransitions
    afterRead1JumpTape2ReaderAllTransitions
  apply transitionSourceDisjoint_flatMap_left
  intro readyState hreadyState
  apply transitionSourceDisjoint_flatMap_right
  intro read0 _hread0
  apply transitionSourceDisjoint_flatMap_right
  intro read1 _hread1
  apply transitionSourceDisjoint_flatMap_right
  intro afterState hafterState
  exact
    readyJumpTape0Reader_afterRead1JumpTape2Reader_sourceDisjoint
      D read0 read1
      (activeStateValues_mem_lt hreadyState)
      (activeStateValues_mem_lt hafterState)

theorem readyAndAfterRead0All_afterRead1JumpTape2ReaderAll_sourceDisjoint
    (D : Description) :
    TransitionSourceDisjoint
      (readyJumpTape0ReaderAllTransitions D ++
        afterRead0JumpTape1ReaderAllTransitions D)
      (afterRead1JumpTape2ReaderAllTransitions D) :=
  transitionSourceDisjoint_append_left
    (readyJumpTape0ReaderAll_afterRead1JumpTape2ReaderAll_sourceDisjoint D)
    (afterRead0JumpTape1ReaderAll_afterRead1JumpTape2ReaderAll_sourceDisjoint D)

theorem readyJumpTape0ReaderTransitions_sources_below_afterRead0JumpLimit
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    TransitionSourcesBelow (afterRead0JumpLimit D)
      (readyJumpTape0ReaderTransitions D state) := by
  unfold readyJumpTape0ReaderTransitions
  apply transitionSourcesBelow_append
  · have hle :
        tape0ReaderOffset D state ≤ afterRead0JumpLimit D := by
      have hblock :=
        tape0ReaderOffset_blockEnd_le_tape0ReaderLimit D hstate
      have hlimit :
          tape0ReaderLimit D ≤ afterRead0JumpLimit D := by
        unfold afterRead0JumpLimit afterRead0JumpScratchBase
        lia
      exact
        Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) hblock)
          hlimit
    exact
      transitionSourcesBelow_mono hle
        (readyJumpDescription_sources_below_tape0ReaderOffset D hstate)
  · intro t ht
    have hblock := tape0ReaderDescription_sources_in_block D state t ht
    have hlimit :=
      tape0ReaderOffset_blockEnd_le_tape0ReaderLimit D hstate
    unfold afterRead0JumpLimit afterRead0JumpScratchBase
    lia

theorem afterRead0JumpTape1ReaderTransitions_sources_below_afterRead1JumpLimit
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourcesBelow (afterRead1JumpLimit D)
      (afterRead0JumpTape1ReaderTransitions D state read0) := by
  unfold afterRead0JumpTape1ReaderTransitions
  apply transitionSourcesBelow_append
  · have hle :
        tape1ReaderOffset D state read0 ≤ afterRead1JumpLimit D := by
      have hblock :=
        tape1ReaderOffset_blockEnd_le_tape1ReaderLimit
          D read0 hstate
      have hlimit :
          tape1ReaderLimit D ≤ afterRead1JumpLimit D := by
        unfold afterRead1JumpLimit afterRead1JumpScratchBase
        lia
      exact
        Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) hblock)
          hlimit
    exact
      transitionSourcesBelow_mono hle
        (afterRead0JumpDescription_sources_below_tape1ReaderOffset
          D read0 hstate)
  · intro t ht
    have hblock :=
      tape1ReaderDescription_sources_in_block D state read0 t ht
    have hlimit :=
      tape1ReaderOffset_blockEnd_le_tape1ReaderLimit
        D read0 hstate
    unfold afterRead1JumpLimit afterRead1JumpScratchBase
    lia

theorem afterRead1JumpTape2ReaderTransitions_sources_below_stateLimit
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourcesBelow (threeHeadReaderStateLimit D)
      (afterRead1JumpTape2ReaderTransitions D state read0 read1) := by
  unfold afterRead1JumpTape2ReaderTransitions
  apply transitionSourcesBelow_append
  · have hle :
        tape2ReaderOffset D state read0 read1 ≤
          threeHeadReaderStateLimit D := by
      have hblock :=
        tape2ReaderOffset_blockEnd_le_tape2ReaderLimit
          D read0 read1 hstate
      exact
        Nat.le_trans (Nat.le_add_right _ _) hblock
    exact
      transitionSourcesBelow_mono hle
        (afterRead1JumpDescription_sources_below_tape2ReaderOffset
          D read0 read1 hstate)
  · intro t ht
    have hblock :=
      tape2ReaderDescription_sources_in_block
        D state read0 read1 t ht
    exact
      Nat.lt_of_lt_of_le hblock.right
        (by
          simpa [threeHeadReaderStateLimit] using
            tape2ReaderOffset_blockEnd_le_tape2ReaderLimit
              D read0 read1 hstate)

theorem readyJumpTape0ReaderAllTransitions_sources_below_afterRead0JumpLimit
    (D : Description) :
    TransitionSourcesBelow (afterRead0JumpLimit D)
      (readyJumpTape0ReaderAllTransitions D) := by
  unfold readyJumpTape0ReaderAllTransitions
  apply transitionSourcesBelow_bind
  intro state hstate
  exact
    readyJumpTape0ReaderTransitions_sources_below_afterRead0JumpLimit
      D (activeStateValues_mem_lt hstate)

theorem afterRead0JumpTape1ReaderAllTransitions_sources_below_afterRead1JumpLimit
    (D : Description) :
    TransitionSourcesBelow (afterRead1JumpLimit D)
      (afterRead0JumpTape1ReaderAllTransitions D) := by
  unfold afterRead0JumpTape1ReaderAllTransitions
  apply transitionSourcesBelow_bind
  intro read0 _hread0
  apply transitionSourcesBelow_bind
  intro state hstate
  exact
    afterRead0JumpTape1ReaderTransitions_sources_below_afterRead1JumpLimit
      D read0 (activeStateValues_mem_lt hstate)

theorem afterRead1JumpTape2ReaderAllTransitions_sources_below_stateLimit
    (D : Description) :
    TransitionSourcesBelow (threeHeadReaderStateLimit D)
      (afterRead1JumpTape2ReaderAllTransitions D) := by
  unfold afterRead1JumpTape2ReaderAllTransitions
  apply transitionSourcesBelow_bind
  intro read0 _hread0
  apply transitionSourcesBelow_bind
  intro read1 _hread1
  apply transitionSourcesBelow_bind
  intro state hstate
  exact
    afterRead1JumpTape2ReaderTransitions_sources_below_stateLimit
      D read0 read1 (activeStateValues_mem_lt hstate)

theorem readyJumpTape0ReaderAllTransitions_sources_below_stateLimit
    (D : Description) :
    TransitionSourcesBelow (threeHeadReaderStateLimit D)
      (readyJumpTape0ReaderAllTransitions D) := by
  apply transitionSourcesBelow_mono
    (h := readyJumpTape0ReaderAllTransitions_sources_below_afterRead0JumpLimit D)
  unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
    afterRead1JumpLimit afterRead1JumpScratchBase tape1ReaderLimit
    tape1ReaderBlockBase
  lia

theorem afterRead0JumpTape1ReaderAllTransitions_sources_below_stateLimit
    (D : Description) :
    TransitionSourcesBelow (threeHeadReaderStateLimit D)
      (afterRead0JumpTape1ReaderAllTransitions D) := by
  apply transitionSourcesBelow_mono
    (h :=
      afterRead0JumpTape1ReaderAllTransitions_sources_below_afterRead1JumpLimit
        D)
  unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
  lia

theorem threeHeadReaderTransitions_sources_below_stateLimit
    (D : Description) :
    TransitionSourcesBelow (threeHeadReaderStateLimit D)
      (threeHeadReaderTransitions D) := by
  simpa [threeHeadReaderTransitions] using
    transitionSourcesBelow_append
      (transitionSourcesBelow_append
        (readyJumpTape0ReaderAllTransitions_sources_below_stateLimit D)
        (afterRead0JumpTape1ReaderAllTransitions_sources_below_stateLimit D))
      (afterRead1JumpTape2ReaderAllTransitions_sources_below_stateLimit D)

theorem readyJumpTape0ReaderAllTransitions_wellFormed
    (D : Description) :
    TransitionListWellFormed (threeHeadReaderStateLimit D)
      (readyJumpTape0ReaderAllTransitions D) := by
  unfold readyJumpTape0ReaderAllTransitions
  apply transitionListWellFormed_bind
  intro state hstate
  exact
    readyJumpTape0ReaderTransitions_wellFormed
      D (activeStateValues_mem_lt hstate)

theorem afterRead0JumpTape1ReaderAllTransitions_wellFormed
    (D : Description) :
    TransitionListWellFormed (threeHeadReaderStateLimit D)
      (afterRead0JumpTape1ReaderAllTransitions D) := by
  unfold afterRead0JumpTape1ReaderAllTransitions
  apply transitionListWellFormed_bind
  intro read0 _hread0
  apply transitionListWellFormed_bind
  intro state hstate
  exact
    afterRead0JumpTape1ReaderTransitions_wellFormed
      D read0 (activeStateValues_mem_lt hstate)

theorem afterRead1JumpTape2ReaderAllTransitions_wellFormed
    (D : Description) :
    TransitionListWellFormed (threeHeadReaderStateLimit D)
      (afterRead1JumpTape2ReaderAllTransitions D) := by
  unfold afterRead1JumpTape2ReaderAllTransitions
  apply transitionListWellFormed_bind
  intro read0 _hread0
  apply transitionListWellFormed_bind
  intro read1 _hread1
  apply transitionListWellFormed_bind
  intro state hstate
  exact
    afterRead1JumpTape2ReaderTransitions_wellFormed
      D read0 read1 (activeStateValues_mem_lt hstate)

theorem threeHeadReaderTransitions_wellFormed
    (D : Description) :
    TransitionListWellFormed (threeHeadReaderStateLimit D)
      (threeHeadReaderTransitions D) := by
  simpa [threeHeadReaderTransitions] using
    transitionListWellFormed_append
      (transitionListWellFormed_append
        (readyJumpTape0ReaderAllTransitions_wellFormed D)
        (afterRead0JumpTape1ReaderAllTransitions_wellFormed D))
      (afterRead1JumpTape2ReaderAllTransitions_wellFormed D)

theorem threeHeadReaderDescription_transitions_wellFormed
    (D : Description) :
    forall t : TransitionDescription,
      t ∈ (threeHeadReaderDescription D).transitions ->
        TransitionDescription.WellFormed
          (threeHeadReaderDescription D).stateCount t := by
  simpa [threeHeadReaderDescription] using
    threeHeadReaderTransitions_wellFormed D

theorem structuredStateCount_le_threeHeadReaderStateLimit
    (D : Description) :
    D.stateCount ≤ threeHeadReaderStateLimit D := by
  unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
    afterRead1JumpLimit afterRead1JumpScratchBase tape1ReaderLimit
    tape1ReaderBlockBase afterRead0JumpLimit afterRead0JumpScratchBase
    tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
    readyJumpScratchBase StaticDispatcherState.readerStateLimit
    StaticDispatcherState.afterRead1Base StaticDispatcherState.afterRead0Base
  lia

theorem threeHeadReaderDescription_stateCount_pos
    (D : Description) (hD : D.WellFormed) :
    0 < (threeHeadReaderDescription D).stateCount := by
  exact
    Nat.lt_of_lt_of_le hD.right.left
      (by
        simpa [threeHeadReaderDescription] using
          structuredStateCount_le_threeHeadReaderStateLimit D)

theorem threeHeadReaderDescription_start_lt
    (D : Description) (hD : D.WellFormed) :
    (threeHeadReaderDescription D).start <
      (threeHeadReaderDescription D).stateCount := by
  exact
    Nat.lt_of_lt_of_le hD.right.right.left
      (by
        simpa [threeHeadReaderDescription,
          StaticDispatcherState.ready] using
          structuredStateCount_le_threeHeadReaderStateLimit D)

theorem threeHeadReaderDescription_halt_lt
    (D : Description) (hD : D.WellFormed) :
    (threeHeadReaderDescription D).halt <
      (threeHeadReaderDescription D).stateCount := by
  exact
    Nat.lt_of_lt_of_le hD.right.right.right.left
      (by
        simpa [threeHeadReaderDescription,
          StaticDispatcherState.ready] using
          structuredStateCount_le_threeHeadReaderStateLimit D)

theorem readyJumpTape0ReaderAllTransitions_sources_ne_halt
    (D : Description) (hhalt : D.halt < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (readyJumpTape0ReaderAllTransitions D) := by
  unfold readyJumpTape0ReaderAllTransitions
  apply transitionSourcesNe_bind
  intro state hstate
  exact
    readyJumpTape0ReaderTransitions_sources_ne_halt
      D hhalt (activeStateValues_mem_lt hstate)
      (activeStateValues_mem_ne_halt hstate)

theorem afterRead0JumpTape1ReaderAllTransitions_sources_ne_halt
    (D : Description) (hhalt : D.halt < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (afterRead0JumpTape1ReaderAllTransitions D) := by
  unfold afterRead0JumpTape1ReaderAllTransitions
  apply transitionSourcesNe_bind
  intro read0 _hread0
  apply transitionSourcesNe_bind
  intro state hstate
  exact
    afterRead0JumpTape1ReaderTransitions_sources_ne_halt
      D read0 hhalt (activeStateValues_mem_lt hstate)

theorem afterRead1JumpTape2ReaderAllTransitions_sources_ne_halt
    (D : Description) (hhalt : D.halt < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (afterRead1JumpTape2ReaderAllTransitions D) := by
  unfold afterRead1JumpTape2ReaderAllTransitions
  apply transitionSourcesNe_bind
  intro read0 _hread0
  apply transitionSourcesNe_bind
  intro read1 _hread1
  apply transitionSourcesNe_bind
  intro state hstate
  exact
    afterRead1JumpTape2ReaderTransitions_sources_ne_halt
      D read0 read1 hhalt (activeStateValues_mem_lt hstate)

theorem threeHeadReaderTransitions_sources_ne_halt
    (D : Description) (hhalt : D.halt < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (threeHeadReaderTransitions D) := by
  simpa [threeHeadReaderTransitions] using
    transitionSourcesNe_append
      (transitionSourcesNe_append
        (readyJumpTape0ReaderAllTransitions_sources_ne_halt D hhalt)
        (afterRead0JumpTape1ReaderAllTransitions_sources_ne_halt
          D hhalt))
      (afterRead1JumpTape2ReaderAllTransitions_sources_ne_halt D hhalt)

theorem threeHeadReaderDescription_haltTransitionFree
    (D : Description) (hhalt : D.halt < D.stateCount) :
    (threeHeadReaderDescription D).HaltTransitionFree := by
  simpa [threeHeadReaderDescription] using
    threeHeadReaderTransitions_sources_ne_halt D hhalt

theorem readyJumpDescription_runsFromTapeSeparator
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical 0 physical) :
    RunsFromStateTapeEquiv
      (readyJumpDescription D state)
      (StaticDispatcherState.ready state)
      (tape0ReaderStart D state)
      physical physical := by
  simpa [readyJumpDescription] using
    blankHeadBounceJumpDescription_runsFromTapeSeparator
      (stateCount := threeHeadReaderStateLimit D)
      (source := StaticDispatcherState.ready state)
      (scratch := readyJumpScratch D state)
      (target := tape0ReaderStart D state)
      (ready_ne_readyJumpScratch D hstate)
      hseparator

theorem afterRead0JumpDescription_runsFromTapeSeparator
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical tapeIndex physical) :
    RunsFromStateTapeEquiv
      (afterRead0JumpDescription D state read0)
      (StaticDispatcherState.afterRead0 D state read0)
      (tape1ReaderStart D state read0)
      physical physical := by
  simpa [afterRead0JumpDescription] using
    blankHeadBounceJumpDescription_runsFromTapeSeparator
      (stateCount := threeHeadReaderStateLimit D)
      (source := StaticDispatcherState.afterRead0 D state read0)
      (scratch := afterRead0JumpScratch D state read0)
      (target := tape1ReaderStart D state read0)
      (afterRead0_ne_afterRead0JumpScratch D read0 hstate)
      hseparator

theorem afterRead1JumpDescription_runsFromTapeSeparator
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical tapeIndex physical) :
    RunsFromStateTapeEquiv
      (afterRead1JumpDescription D state read0 read1)
      (StaticDispatcherState.afterRead1 D state read0 read1)
      (tape2ReaderStart D state read0 read1)
      physical physical := by
  simpa [afterRead1JumpDescription] using
    blankHeadBounceJumpDescription_runsFromTapeSeparator
      (stateCount := threeHeadReaderStateLimit D)
      (source := StaticDispatcherState.afterRead1 D state read0 read1)
      (scratch := afterRead1JumpScratch D state read0 read1)
      (target := tape2ReaderStart D state read0 read1)
      (afterRead1_ne_afterRead1JumpScratch D read0 read1 hstate)
      hseparator

theorem tape0ReaderDescription_runsFromGuardedBlockStart
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 0
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tape0ReaderDescription D state)
          (tape0ReaderStart D state)
          (StaticDispatcherState.afterRead0 D state
            (Tape.read (Description.tapeAt logical 0)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  simpa [tape0ReaderDescription, tape0ReaderStart,
    StaticDispatcherState.tape0ReaderTargets, StaticDispatcherState.tape0ReaderTarget] using
      retargetedBranchingTape0ReadHeadCellAllExitsDescription_runsFromGuardedBlockStart
        (offset := tape0ReaderOffset D state)
        (target := StaticDispatcherState.tape0ReaderTargets D state)
        (tape0ReaderTargets_lt_tape0ReaderOffset D hstate)
        hlength

theorem tape1ReaderDescription_runsFromGuardedBlockStart
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 1
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tape1ReaderDescription D state read0)
          (tape1ReaderStart D state read0)
          (StaticDispatcherState.afterRead1 D state read0
            (Tape.read (Description.tapeAt logical 1)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  simpa [tape1ReaderDescription, tape1ReaderStart,
    StaticDispatcherState.tape1ReaderTargets, StaticDispatcherState.tape1ReaderTarget] using
      retargetedBranchingTape1ReadHeadCellAllExitsDescription_runsFromGuardedBlockStart
        (offset := tape1ReaderOffset D state read0)
        (target := StaticDispatcherState.tape1ReaderTargets D state read0)
        (tape1ReaderTargets_lt_tape1ReaderOffset D read0 hstate)
        hlength

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
