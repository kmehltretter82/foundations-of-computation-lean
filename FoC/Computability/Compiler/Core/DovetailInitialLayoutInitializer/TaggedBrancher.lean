import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.InputTape

set_option doc.verso true

/-!
# TaggedBrancher

Shared-halt tagged branching for the append-input initializer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace DovetailInitialLayoutInitializer

def sharedExitRetargetTransition
    (offset oldHalt commonHalt : Nat)
    (t : TransitionDescription) : TransitionDescription where
  source := offset + t.source
  read := t.read
  write := t.write
  move := t.move
  target := if t.target = oldHalt then commonHalt else offset + t.target

def taggedBranchBlankOffset : Nat := 2

def taggedBranchFalseOffset
    (blankBranch : MachineDescription) : Nat :=
  taggedBranchBlankOffset + blankBranch.stateCount

def taggedBranchTrueOffset
    (blankBranch falseBranch : MachineDescription) : Nat :=
  taggedBranchFalseOffset blankBranch + falseBranch.stateCount

def taggedBranchStateCount
    (blankBranch falseBranch trueBranch : MachineDescription) : Nat :=
  taggedBranchTrueOffset blankBranch falseBranch +
    trueBranch.stateCount

def RestoreFirstBitTaggedBrancherDescription
    (blankBranch falseBranch trueBranch : MachineDescription) :
    MachineDescription where
  stateCount :=
    taggedBranchStateCount blankBranch falseBranch trueBranch
  start := 0
  halt := 1
  transitions :=
    [ transition
        0 none (some false) Direction.right
        (if blankBranch.start = blankBranch.halt then 1
          else taggedBranchBlankOffset + blankBranch.start)
    , transition
        0 (some false) (some false) Direction.right
        (if falseBranch.start = falseBranch.halt then 1
          else taggedBranchFalseOffset blankBranch +
            falseBranch.start)
    , transition
        0 (some true) (some false) Direction.right
        (if trueBranch.start = trueBranch.halt then 1
          else taggedBranchTrueOffset blankBranch falseBranch +
            trueBranch.start)
    ] ++
    blankBranch.transitions.map
      (sharedExitRetargetTransition
        taggedBranchBlankOffset blankBranch.halt 1) ++
    falseBranch.transitions.map
      (sharedExitRetargetTransition
        (taggedBranchFalseOffset blankBranch)
        falseBranch.halt 1) ++
    trueBranch.transitions.map
      (sharedExitRetargetTransition
        (taggedBranchTrueOffset blankBranch falseBranch)
        trueBranch.halt 1)

def sharedExitBranchConfiguration
    (offset oldHalt commonHalt : Nat)
    (c : Configuration) :
    Configuration where
  state := if c.state = oldHalt then commonHalt else offset + c.state
  tape := c.tape

theorem sharedExitRetargetTransition_sameAction
    (offset oldHalt commonHalt : Nat)
    {t u : TransitionDescription}
    (h : TransitionDescription.SameAction t u) :
    TransitionDescription.SameAction
      (sharedExitRetargetTransition
        offset oldHalt commonHalt t)
      (sharedExitRetargetTransition
        offset oldHalt commonHalt u) := by
  rcases h with ⟨hwrite, hmove, htarget⟩
  simp [TransitionDescription.SameAction,
    sharedExitRetargetTransition, hwrite, hmove, htarget]

theorem sharedExitRetargetTransition_sameKey_source
    {offset oldHalt commonHalt : Nat}
    {t u : TransitionDescription}
    (h :
      TransitionDescription.SameKey
        (sharedExitRetargetTransition
          offset oldHalt commonHalt t)
        (sharedExitRetargetTransition
          offset oldHalt commonHalt u)) :
    TransitionDescription.SameKey t u := by
  constructor
  · exact Nat.add_left_cancel h.left
  · exact h.right

theorem
    restoreFirstBitTaggedBrancherDescription_subroutineReady
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).SubroutineReady := by
  constructor
  · constructor
    · simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset]
      omega
    constructor
    · simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset]
      omega
    constructor
    · simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset]
      omega
    constructor
    · intro t ht
      simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset,
        sharedExitRetargetTransition,
        transition,
        TransitionDescription.WellFormed] at ht ⊢
      have hblankStart : blankBranch.start < blankBranch.stateCount :=
        hblank.left.right.left
      have hfalseStart : falseBranch.start < falseBranch.stateCount :=
        hfalse.left.right.left
      have htrueStart : trueBranch.start < trueBranch.stateCount :=
        htrue.left.right.left
      rcases ht with rfl | rfl | rfl |
          ⟨base, hbase, rfl⟩ |
          ⟨base, hbase, rfl⟩ |
          ⟨base, hbase, rfl⟩
      · constructor
        · simp
          omega
        · by_cases hstart : blankBranch.start = blankBranch.halt
          · simp [hstart]
            omega
          · simp [hstart]
            omega
      · constructor
        · simp
          omega
        · by_cases hstart : falseBranch.start = falseBranch.halt
          · simp [hstart]
            omega
          · simp [hstart]
            omega
      · constructor
        · simp
          omega
        · by_cases hstart : trueBranch.start = trueBranch.halt
          · simp [hstart]
            omega
          · simp [hstart]
            omega
      · have hbaseWF :=
          hblank.left.right.right.right.left base hbase
        have hbaseSource : base.source < blankBranch.stateCount :=
          hbaseWF.left
        have hbaseTarget : base.target < blankBranch.stateCount :=
          hbaseWF.right
        constructor
        · change
            2 + base.source <
              2 + blankBranch.stateCount +
                falseBranch.stateCount + trueBranch.stateCount
          omega
        · by_cases htarget : base.target = blankBranch.halt
          · simpa [htarget] using
              (show
                1 <
                  2 + blankBranch.stateCount +
                    falseBranch.stateCount + trueBranch.stateCount by
                omega)
          · change
              (if base.target = blankBranch.halt then 1
                else 2 + base.target) <
                2 + blankBranch.stateCount +
                  falseBranch.stateCount + trueBranch.stateCount
            simp [htarget]
            omega
      · have hbaseWF :=
          hfalse.left.right.right.right.left base hbase
        have hbaseSource : base.source < falseBranch.stateCount :=
          hbaseWF.left
        have hbaseTarget : base.target < falseBranch.stateCount :=
          hbaseWF.right
        constructor
        · change
            2 + blankBranch.stateCount + base.source <
              2 + blankBranch.stateCount +
                falseBranch.stateCount + trueBranch.stateCount
          omega
        · by_cases htarget : base.target = falseBranch.halt
          · simpa [htarget] using
              (show
                1 <
                  2 + blankBranch.stateCount +
                    falseBranch.stateCount + trueBranch.stateCount by
                omega)
          · change
              (if base.target = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + base.target) <
                2 + blankBranch.stateCount +
                  falseBranch.stateCount + trueBranch.stateCount
            simp [htarget]
            omega
      · have hbaseWF :=
          htrue.left.right.right.right.left base hbase
        have hbaseSource : base.source < trueBranch.stateCount :=
          hbaseWF.left
        have hbaseTarget : base.target < trueBranch.stateCount :=
          hbaseWF.right
        constructor
        · change
            2 + blankBranch.stateCount + falseBranch.stateCount +
                base.source <
              2 + blankBranch.stateCount +
                falseBranch.stateCount + trueBranch.stateCount
          omega
        · by_cases htarget : base.target = trueBranch.halt
          · simpa [htarget] using
              (show
                1 <
                  2 + blankBranch.stateCount +
                    falseBranch.stateCount + trueBranch.stateCount by
                omega)
          · change
              (if base.target = trueBranch.halt then 1
                else 2 + blankBranch.stateCount +
                  falseBranch.stateCount + base.target) <
                2 + blankBranch.stateCount +
                  falseBranch.stateCount + trueBranch.stateCount
            simp [htarget]
            omega
    · intro t u ht hu hkey
      simp [RestoreFirstBitTaggedBrancherDescription,
        taggedBranchStateCount,
        taggedBranchTrueOffset,
        taggedBranchFalseOffset,
        taggedBranchBlankOffset,
        sharedExitRetargetTransition,
        transition] at ht hu ⊢
      rcases ht with rfl | rfl | rfl |
          ⟨baseT, hbaseT, rfl⟩ |
          ⟨baseT, hbaseT, rfl⟩ |
          ⟨baseT, hbaseT, rfl⟩
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ <;>
          simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢ <;>
          try omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ <;>
          simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢ <;>
          try omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ <;>
          simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢ <;>
          try omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hsame :=
            hblank.left.right.right.right.right
              baseT baseU hbaseT hbaseU hkey
          rcases hsame with ⟨hwrite, hmove, htarget⟩
          simp [hwrite, hmove, htarget]
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseTSource :
              baseT.source < blankBranch.stateCount :=
            (hblank.left.right.right.right.left baseT hbaseT).left
          omega
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseTSource :
              baseT.source < blankBranch.stateCount :=
            (hblank.left.right.right.right.left baseT hbaseT).left
          omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseUSource :
              baseU.source < blankBranch.stateCount :=
            (hblank.left.right.right.right.left baseU hbaseU).left
          omega
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hsame :=
            hfalse.left.right.right.right.right
              baseT baseU hbaseT hbaseU hkey
          rcases hsame with ⟨hwrite, hmove, htarget⟩
          simp [hwrite, hmove, htarget]
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseTSource :
              baseT.source < falseBranch.stateCount :=
            (hfalse.left.right.right.right.left baseT hbaseT).left
          omega
      · rcases hu with rfl | rfl | rfl |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩ |
            ⟨baseU, hbaseU, rfl⟩
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey] at hkey
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseUSource :
              baseU.source < blankBranch.stateCount :=
            (hblank.left.right.right.right.left baseU hbaseU).left
          omega
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hbaseUSource :
              baseU.source < falseBranch.stateCount :=
            (hfalse.left.right.right.right.left baseU hbaseU).left
          omega
        · simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
          have hsame :=
            htrue.left.right.right.right.right
              baseT baseU hbaseT hbaseU hkey
          rcases hsame with ⟨hwrite, hmove, htarget⟩
          simp [hwrite, hmove, htarget]
  · intro t ht
    simp [RestoreFirstBitTaggedBrancherDescription,
      taggedBranchStateCount,
      taggedBranchTrueOffset,
      taggedBranchFalseOffset,
      taggedBranchBlankOffset,
      sharedExitRetargetTransition,
      transition] at ht ⊢
    rcases ht with rfl | rfl | rfl |
        ⟨base, _hbase, rfl⟩ |
        ⟨base, _hbase, rfl⟩ |
        ⟨base, _hbase, rfl⟩ <;> simp <;> omega

theorem
    restoreFirstBitTaggedBrancherDescription_lookup_blank
    {blankBranch falseBranch trueBranch : MachineDescription}
    (_hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {state : Nat} {cell : Option Bool}
    (hstate : state < blankBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).lookupTransition
        (taggedBranchBlankOffset + state) cell =
      Option.map
        (sharedExitRetargetTransition
          taggedBranchBlankOffset blankBranch.halt 1)
        (blankBranch.lookupTransition state cell) := by
  unfold lookupTransition
  have hfindControl :
      List.find?
          (Matches
            (taggedBranchBlankOffset + state) cell)
          [ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else taggedBranchBlankOffset + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else taggedBranchFalseOffset blankBranch +
                  falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else taggedBranchTrueOffset blankBranch falseBranch +
                  trueBranch.start)
          ] = none := by
    simp [Matches, transition,
      taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset]
    omega
  have hfindFalse :
      List.find?
          (Matches
            (taggedBranchBlankOffset + state) cell)
          (falseBranch.transitions.map
            (sharedExitRetargetTransition
              (taggedBranchFalseOffset blankBranch)
              falseBranch.halt 1)) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < falseBranch.stateCount :=
      (hfalse.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchFalseOffset blankBranch + base.source =
          taggedBranchBlankOffset + state := by
      have hpair :
          taggedBranchFalseOffset blankBranch + base.source =
              taggedBranchBlankOffset + state ∧
            base.read = cell := by
        simpa [Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset] at hsource
    omega
  have hfindTrue :
      List.find?
          (Matches
            (taggedBranchBlankOffset + state) cell)
          (trueBranch.transitions.map
            (sharedExitRetargetTransition
              (taggedBranchTrueOffset blankBranch falseBranch)
              trueBranch.halt 1)) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < trueBranch.stateCount :=
      (htrue.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchTrueOffset blankBranch falseBranch +
            base.source =
          taggedBranchBlankOffset + state := by
      have hpair :
          taggedBranchTrueOffset blankBranch falseBranch +
                base.source =
              taggedBranchBlankOffset + state ∧
            base.read = cell := by
        simpa [Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] at hsource
    omega
  have hpredicate :
      (Matches
          (taggedBranchBlankOffset + state) cell ∘
        sharedExitRetargetTransition
          taggedBranchBlankOffset blankBranch.halt 1) =
        Matches state cell := by
    funext t
    have hsourceBeq :
        (taggedBranchBlankOffset + t.source ==
            taggedBranchBlankOffset + state) =
          (t.source == state) := by
      by_cases hsource : t.source = state
      · have hoffset :
          taggedBranchBlankOffset + t.source =
            taggedBranchBlankOffset + state := by
          omega
        have hleft :
            (taggedBranchBlankOffset + t.source ==
                taggedBranchBlankOffset + state) = true := by
          rw [beq_iff_eq]
          exact hoffset
        have hright : (t.source == state) = true := by
          rw [beq_iff_eq]
          exact hsource
        rw [hleft, hright]
      · have hoffset :
          taggedBranchBlankOffset + t.source ≠
            taggedBranchBlankOffset + state := by
          omega
        have hleft :
            (taggedBranchBlankOffset + t.source ==
                taggedBranchBlankOffset + state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hoffset
        have hright : (t.source == state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hsource
        rw [hleft, hright]
    simp [Function.comp, Matches,
      sharedExitRetargetTransition, hsourceBeq]
  have hfindControl' :
      List.find?
          (Matches (2 + state) cell)
          [ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindControl
  have hfindFalse' :
      List.find?
          (Matches (2 + state) cell)
          (falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount) falseBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset] using hfindFalse
  have hfindTrue' :
      List.find?
          (Matches (2 + state) cell)
          (trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindTrue
  change
    List.find?
        (Matches (2 + state) cell)
        ([ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] ++
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2 blankBranch.halt 1) ++
          falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount) falseBranch.halt 1) ++
          trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1))) =
      Option.map
        (sharedExitRetargetTransition 2 blankBranch.halt 1)
        (List.find? (Matches state cell)
          blankBranch.transitions)
  have hpredicate' :
      (Matches (2 + state) cell ∘
        sharedExitRetargetTransition
          2 blankBranch.halt 1) =
        Matches state cell := by
    simpa [taggedBranchBlankOffset] using hpredicate
  have hfalseMapNone :
      Option.map
          (sharedExitRetargetTransition
            (2 + blankBranch.stateCount) falseBranch.halt 1)
          (List.find?
            (Matches (2 + state) cell ∘
              sharedExitRetargetTransition
                (2 + blankBranch.stateCount) falseBranch.halt 1)
            falseBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindFalse'
  have htrueMapNone :
      Option.map
          (sharedExitRetargetTransition
            (2 + blankBranch.stateCount + falseBranch.stateCount)
            trueBranch.halt 1)
          (List.find?
            (Matches (2 + state) cell ∘
              sharedExitRetargetTransition
                (2 + blankBranch.stateCount + falseBranch.stateCount)
                trueBranch.halt 1)
            trueBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindTrue'
  rw [List.find?_append, hfindControl']
  simp
  rw [hpredicate', hfalseMapNone, htrueMapNone]
  cases hlocal :
      List.find? (Matches state cell)
        blankBranch.transitions <;>
    simp

theorem
    restoreFirstBitTaggedBrancherDescription_step_blank
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {c : Configuration}
    (hstate : c.state < blankBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).stepConfig
        (sharedExitBranchConfiguration
          taggedBranchBlankOffset blankBranch.halt 1 c) =
      Option.map
        (sharedExitBranchConfiguration
          taggedBranchBlankOffset blankBranch.halt 1)
        (blankBranch.stepConfig c) := by
  cases c with
  | mk state tape =>
      by_cases hhalt : state = blankBranch.halt
      · subst state
        have hblankStep :
            blankBranch.stepConfig
                { state := blankBranch.halt, tape := tape } = none :=
          stepConfig_halt_none hblank.right tape
        have hbrancherStep :
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).stepConfig
                { state := 1, tape := tape } = none :=
          stepConfig_halt_none
            (restoreFirstBitTaggedBrancherDescription_subroutineReady
              hblank hfalse htrue).right tape
        simp [sharedExitBranchConfiguration, hblankStep,
          hbrancherStep]
      · have hlookup :=
          restoreFirstBitTaggedBrancherDescription_lookup_blank
            hblank hfalse htrue (state := state)
            (cell := Tape.read tape) hstate
        simp [stepConfig,
          sharedExitBranchConfiguration, hhalt, hlookup]
        cases hlocal :
            blankBranch.lookupTransition state (Tape.read tape) with
        | none =>
            simp
        | some t =>
            simp [sharedExitRetargetTransition,
              sharedExitBranchConfiguration]
theorem restoreFirstBitTaggedBrancherDescription_run_blank
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    (n : Nat) (c : Configuration)
    (hstate : c.state < blankBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).runConfig n
        (sharedExitBranchConfiguration
          taggedBranchBlankOffset blankBranch.halt 1 c) =
      sharedExitBranchConfiguration
        taggedBranchBlankOffset blankBranch.halt 1
        (blankBranch.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      rw [runConfig]
      rw [restoreFirstBitTaggedBrancherDescription_step_blank
        hblank hfalse htrue hstate]
      cases hstep : blankBranch.stepConfig c with
      | none =>
          simp [runConfig, hstep]
      | some next =>
          have hnextState : next.state < blankBranch.stateCount :=
            stepConfig_state_bound hblank.left hstep
          simp [runConfig, hstep, ih next hnextState]
theorem restoreFirstBitTaggedBrancherDescription_run_none
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {T Tout : Tape Bool}
    (hread : Tape.read T = none)
    (hbranch :
      exists steps : Nat,
        blankBranch.runConfig steps
            { state := blankBranch.start
              tape := Tape.move Direction.right
                (Tape.write (some false) T) } =
          { state := blankBranch.halt, tape := Tout }) :
    exists steps : Nat,
      (RestoreFirstBitTaggedBrancherDescription
        blankBranch falseBranch trueBranch).runConfig steps
          { state :=
              (RestoreFirstBitTaggedBrancherDescription
                blankBranch falseBranch trueBranch).start
            tape := T } =
        { state :=
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).halt
          tape := Tout } := by
  rcases hbranch with ⟨n, hn⟩
  let D :=
    RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch
  let branchStart : Configuration :=
    { state := blankBranch.start
      tape := Tape.move Direction.right (Tape.write (some false) T) }
  have hfirst :
      D.runConfig 1 { state := D.start, tape := T } =
        sharedExitBranchConfiguration
          taggedBranchBlankOffset blankBranch.halt 1
          branchStart := by
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [D, branchStart,
              RestoreFirstBitTaggedBrancherDescription,
              sharedExitBranchConfiguration,
              taggedBranchBlankOffset,
              taggedBranchFalseOffset,
              taggedBranchTrueOffset,
              runConfig, stepConfig,
              lookupTransition, Matches,
              transition, Tape.read, Tape.write,
              Tape.move, Tape.moveRight]
        | some b =>
            cases b <;> simp [Tape.read] at hread
  refine ⟨1 + n, ?_⟩
  rw [runConfig_add]
  rw [hfirst]
  have hstartBound : branchStart.state < blankBranch.stateCount := by
    exact hblank.left.right.left
  rw [restoreFirstBitTaggedBrancherDescription_run_blank
    hblank hfalse htrue n branchStart hstartBound]
  rw [hn]
  simp [RestoreFirstBitTaggedBrancherDescription,
    sharedExitBranchConfiguration]

theorem
    restoreFirstBitTaggedBrancherDescription_lookup_false
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (_hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {state : Nat} {cell : Option Bool}
    (hstate : state < falseBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).lookupTransition
        (taggedBranchFalseOffset blankBranch + state) cell =
      Option.map
        (sharedExitRetargetTransition
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1)
        (falseBranch.lookupTransition state cell) := by
  unfold lookupTransition
  have hfindControl :
      List.find?
          (Matches
            (taggedBranchFalseOffset blankBranch + state) cell)
          [ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else taggedBranchBlankOffset + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else taggedBranchFalseOffset blankBranch +
                  falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else taggedBranchTrueOffset blankBranch falseBranch +
                  trueBranch.start)
          ] = none := by
    simp [Matches, transition,
      taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset]
    omega
  have hfindBlank :
      List.find?
          (Matches
            (taggedBranchFalseOffset blankBranch + state) cell)
          (blankBranch.transitions.map
            (sharedExitRetargetTransition
              taggedBranchBlankOffset blankBranch.halt 1)) =
        none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < blankBranch.stateCount :=
      (hblank.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchBlankOffset + base.source =
          taggedBranchFalseOffset blankBranch + state := by
      have hpair :
          taggedBranchBlankOffset + base.source =
              taggedBranchFalseOffset blankBranch + state ∧
            base.read = cell := by
        simpa [Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset] at hsource
    omega
  have hfindTrue :
      List.find?
          (Matches
            (taggedBranchFalseOffset blankBranch + state) cell)
          (trueBranch.transitions.map
            (sharedExitRetargetTransition
              (taggedBranchTrueOffset blankBranch falseBranch)
              trueBranch.halt 1)) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < trueBranch.stateCount :=
      (htrue.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchTrueOffset blankBranch falseBranch +
            base.source =
          taggedBranchFalseOffset blankBranch + state := by
      have hpair :
          taggedBranchTrueOffset blankBranch falseBranch +
                base.source =
              taggedBranchFalseOffset blankBranch + state ∧
            base.read = cell := by
        simpa [Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] at hsource
    omega
  have hpredicate :
      (Matches
          (taggedBranchFalseOffset blankBranch + state) cell ∘
        sharedExitRetargetTransition
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1) =
        Matches state cell := by
    funext t
    have hsourceBeq :
        (taggedBranchFalseOffset blankBranch + t.source ==
            taggedBranchFalseOffset blankBranch + state) =
          (t.source == state) := by
      by_cases hsource : t.source = state
      · have hoffset :
          taggedBranchFalseOffset blankBranch + t.source =
            taggedBranchFalseOffset blankBranch + state := by
          omega
        have hleft :
            (taggedBranchFalseOffset blankBranch + t.source ==
                taggedBranchFalseOffset blankBranch + state) =
              true := by
          rw [beq_iff_eq]
          exact hoffset
        have hright : (t.source == state) = true := by
          rw [beq_iff_eq]
          exact hsource
        rw [hleft, hright]
      · have hoffset :
          taggedBranchFalseOffset blankBranch + t.source ≠
            taggedBranchFalseOffset blankBranch + state := by
          omega
        have hleft :
            (taggedBranchFalseOffset blankBranch + t.source ==
                taggedBranchFalseOffset blankBranch + state) =
              false := by
          rw [beq_eq_false_iff_ne]
          exact hoffset
        have hright : (t.source == state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hsource
        rw [hleft, hright]
    simp [Function.comp, Matches,
      sharedExitRetargetTransition, hsourceBeq]
  have hfindControl' :
      List.find?
          (Matches
            (2 + blankBranch.stateCount + state) cell)
          [ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindControl
  have hfindBlank' :
      List.find?
          (Matches
            (2 + blankBranch.stateCount + state) cell)
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2
              blankBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset] using hfindBlank
  have hfindTrue' :
      List.find?
          (Matches
            (2 + blankBranch.stateCount + state) cell)
          (trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindTrue
  change
    List.find?
        (Matches
          (2 + blankBranch.stateCount + state) cell)
        ([ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] ++
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2 blankBranch.halt 1) ++
          falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount) falseBranch.halt 1) ++
          trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1))) =
      Option.map
        (sharedExitRetargetTransition
          (2 + blankBranch.stateCount) falseBranch.halt 1)
        (List.find? (Matches state cell)
          falseBranch.transitions)
  have hpredicate' :
      (Matches
          (2 + blankBranch.stateCount + state) cell ∘
        sharedExitRetargetTransition
          (2 + blankBranch.stateCount) falseBranch.halt 1) =
        Matches state cell := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset] using hpredicate
  have hblankMapNone :
      Option.map
          (sharedExitRetargetTransition 2 blankBranch.halt 1)
          (List.find?
            (Matches
                (2 + blankBranch.stateCount + state) cell ∘
              sharedExitRetargetTransition 2
                blankBranch.halt 1)
            blankBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindBlank'
  have htrueMapNone :
      Option.map
          (sharedExitRetargetTransition
            (2 + blankBranch.stateCount + falseBranch.stateCount)
            trueBranch.halt 1)
          (List.find?
            (Matches
                (2 + blankBranch.stateCount + state) cell ∘
              sharedExitRetargetTransition
                (2 + blankBranch.stateCount + falseBranch.stateCount)
                trueBranch.halt 1)
            trueBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindTrue'
  rw [List.find?_append, hfindControl']
  simp
  rw [hblankMapNone, hpredicate', htrueMapNone]
  cases hlocal :
      List.find? (Matches state cell)
        falseBranch.transitions <;>
    simp

theorem
    restoreFirstBitTaggedBrancherDescription_step_false
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {c : Configuration}
    (hstate : c.state < falseBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).stepConfig
        (sharedExitBranchConfiguration
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1 c) =
      Option.map
        (sharedExitBranchConfiguration
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1)
        (falseBranch.stepConfig c) := by
  cases c with
  | mk state tape =>
      by_cases hhalt : state = falseBranch.halt
      · subst state
        have hfalseStep :
            falseBranch.stepConfig
                { state := falseBranch.halt, tape := tape } = none :=
          stepConfig_halt_none hfalse.right tape
        have hbrancherStep :
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).stepConfig
                { state := 1, tape := tape } = none :=
          stepConfig_halt_none
            (restoreFirstBitTaggedBrancherDescription_subroutineReady
              hblank hfalse htrue).right tape
        simp [sharedExitBranchConfiguration, hfalseStep,
          hbrancherStep]
      · have hlookup :=
          restoreFirstBitTaggedBrancherDescription_lookup_false
            hblank hfalse htrue (state := state)
            (cell := Tape.read tape) hstate
        simp [stepConfig,
          sharedExitBranchConfiguration, hhalt, hlookup]
        cases hlocal :
            falseBranch.lookupTransition state (Tape.read tape) with
        | none =>
            simp
        | some t =>
            simp [sharedExitRetargetTransition,
              sharedExitBranchConfiguration]
theorem restoreFirstBitTaggedBrancherDescription_run_false_branch
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    (n : Nat) (c : Configuration)
    (hstate : c.state < falseBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).runConfig n
        (sharedExitBranchConfiguration
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1 c) =
      sharedExitBranchConfiguration
        (taggedBranchFalseOffset blankBranch)
        falseBranch.halt 1
        (falseBranch.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      rw [runConfig]
      rw [restoreFirstBitTaggedBrancherDescription_step_false
        hblank hfalse htrue hstate]
      cases hstep : falseBranch.stepConfig c with
      | none =>
          simp [runConfig, hstep]
      | some next =>
          have hnextState : next.state < falseBranch.stateCount :=
            stepConfig_state_bound hfalse.left hstep
          simp [runConfig, hstep, ih next hnextState]

theorem
    restoreFirstBitTaggedBrancherDescription_run_false
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {T Tout : Tape Bool}
    (hread : Tape.read T = some false)
    (hbranch :
      exists steps : Nat,
        falseBranch.runConfig steps
            { state := falseBranch.start
              tape := Tape.move Direction.right
                (Tape.write (some false) T) } =
          { state := falseBranch.halt, tape := Tout }) :
    exists steps : Nat,
      (RestoreFirstBitTaggedBrancherDescription
        blankBranch falseBranch trueBranch).runConfig steps
          { state :=
              (RestoreFirstBitTaggedBrancherDescription
                blankBranch falseBranch trueBranch).start
            tape := T } =
        { state :=
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).halt
          tape := Tout } := by
  rcases hbranch with ⟨n, hn⟩
  let D :=
    RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch
  let branchStart : Configuration :=
    { state := falseBranch.start
      tape := Tape.move Direction.right (Tape.write (some false) T) }
  have hfirst :
      D.runConfig 1 { state := D.start, tape := T } =
        sharedExitBranchConfiguration
          (taggedBranchFalseOffset blankBranch)
          falseBranch.halt 1
          branchStart := by
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [Tape.read] at hread
        | some b =>
            cases b
            · simp [D, branchStart,
                RestoreFirstBitTaggedBrancherDescription,
                sharedExitBranchConfiguration,
                taggedBranchBlankOffset,
                taggedBranchFalseOffset,
                taggedBranchTrueOffset,
                runConfig, stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            · simp [Tape.read] at hread
  refine ⟨1 + n, ?_⟩
  rw [runConfig_add]
  rw [hfirst]
  have hstartBound : branchStart.state < falseBranch.stateCount := by
    exact hfalse.left.right.left
  rw [restoreFirstBitTaggedBrancherDescription_run_false_branch
    hblank hfalse htrue n branchStart hstartBound]
  rw [hn]
  simp [RestoreFirstBitTaggedBrancherDescription,
    sharedExitBranchConfiguration]

theorem
    restoreFirstBitTaggedBrancherDescription_lookup_true
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (_htrue : trueBranch.SubroutineReady)
    {state : Nat} {cell : Option Bool}
    (_hstate : state < trueBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).lookupTransition
        (taggedBranchTrueOffset blankBranch falseBranch + state)
        cell =
      Option.map
        (sharedExitRetargetTransition
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1)
        (trueBranch.lookupTransition state cell) := by
  unfold lookupTransition
  have hfindControl :
      List.find?
          (Matches
            (taggedBranchTrueOffset blankBranch falseBranch +
              state) cell)
          [ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else taggedBranchBlankOffset + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else taggedBranchFalseOffset blankBranch +
                  falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else taggedBranchTrueOffset blankBranch falseBranch +
                  trueBranch.start)
          ] = none := by
    simp [Matches, transition,
      taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset]
    omega
  have hfindBlank :
      List.find?
          (Matches
            (taggedBranchTrueOffset blankBranch falseBranch +
              state) cell)
          (blankBranch.transitions.map
            (sharedExitRetargetTransition
              taggedBranchBlankOffset blankBranch.halt 1)) =
        none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < blankBranch.stateCount :=
      (hblank.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchBlankOffset + base.source =
          taggedBranchTrueOffset blankBranch falseBranch +
            state := by
      have hpair :
          taggedBranchBlankOffset + base.source =
              taggedBranchTrueOffset blankBranch falseBranch +
                state ∧
            base.read = cell := by
        simpa [Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] at hsource
    omega
  have hfindFalse :
      List.find?
          (Matches
            (taggedBranchTrueOffset blankBranch falseBranch +
              state) cell)
          (falseBranch.transitions.map
            (sharedExitRetargetTransition
              (taggedBranchFalseOffset blankBranch)
              falseBranch.halt 1)) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    have hbaseSource : base.source < falseBranch.stateCount :=
      (hfalse.left.right.right.right.left base hbase).left
    have hsource :
        taggedBranchFalseOffset blankBranch + base.source =
          taggedBranchTrueOffset blankBranch falseBranch +
            state := by
      have hpair :
          taggedBranchFalseOffset blankBranch + base.source =
              taggedBranchTrueOffset blankBranch falseBranch +
                state ∧
            base.read = cell := by
        simpa [Matches,
          sharedExitRetargetTransition] using hmatch
      exact hpair.left
    simp [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] at hsource
    omega
  have hpredicate :
      (Matches
          (taggedBranchTrueOffset blankBranch falseBranch +
            state) cell ∘
        sharedExitRetargetTransition
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1) =
        Matches state cell := by
    funext t
    have hsourceBeq :
        (taggedBranchTrueOffset blankBranch falseBranch +
              t.source ==
            taggedBranchTrueOffset blankBranch falseBranch +
              state) =
          (t.source == state) := by
      by_cases hsource : t.source = state
      · have hoffset :
          taggedBranchTrueOffset blankBranch falseBranch +
                t.source =
            taggedBranchTrueOffset blankBranch falseBranch +
                state := by
          omega
        have hleft :
            (taggedBranchTrueOffset blankBranch falseBranch +
                  t.source ==
                taggedBranchTrueOffset blankBranch falseBranch +
                  state) = true := by
          rw [beq_iff_eq]
          exact hoffset
        have hright : (t.source == state) = true := by
          rw [beq_iff_eq]
          exact hsource
        rw [hleft, hright]
      · have hoffset :
          taggedBranchTrueOffset blankBranch falseBranch +
                t.source ≠
            taggedBranchTrueOffset blankBranch falseBranch +
                state := by
          omega
        have hleft :
            (taggedBranchTrueOffset blankBranch falseBranch +
                  t.source ==
                taggedBranchTrueOffset blankBranch falseBranch +
                  state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hoffset
        have hright : (t.source == state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hsource
        rw [hleft, hright]
    simp [Function.comp, Matches,
      sharedExitRetargetTransition, hsourceBeq]
  have hfindControl' :
      List.find?
          (Matches
            (2 + blankBranch.stateCount + falseBranch.stateCount + state)
            cell)
          [ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindControl
  have hfindBlank' :
      List.find?
          (Matches
            (2 + blankBranch.stateCount + falseBranch.stateCount + state)
            cell)
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2
              blankBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindBlank
  have hfindFalse' :
      List.find?
          (Matches
            (2 + blankBranch.stateCount + falseBranch.stateCount + state)
            cell)
          (falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount)
              falseBranch.halt 1)) = none := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hfindFalse
  change
    List.find?
        (Matches
          (2 + blankBranch.stateCount + falseBranch.stateCount + state)
          cell)
        ([ transition
              0 none (some false) Direction.right
              (if blankBranch.start = blankBranch.halt then 1
                else 2 + blankBranch.start)
          , transition
              0 (some false) (some false) Direction.right
              (if falseBranch.start = falseBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.start)
          , transition
              0 (some true) (some false) Direction.right
              (if trueBranch.start = trueBranch.halt then 1
                else 2 + blankBranch.stateCount + falseBranch.stateCount +
                  trueBranch.start)
          ] ++
          (blankBranch.transitions.map
            (sharedExitRetargetTransition 2 blankBranch.halt 1) ++
          falseBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount) falseBranch.halt 1) ++
          trueBranch.transitions.map
            (sharedExitRetargetTransition
              (2 + blankBranch.stateCount + falseBranch.stateCount)
              trueBranch.halt 1))) =
      Option.map
        (sharedExitRetargetTransition
          (2 + blankBranch.stateCount + falseBranch.stateCount)
          trueBranch.halt 1)
        (List.find? (Matches state cell)
          trueBranch.transitions)
  have hpredicate' :
      (Matches
          (2 + blankBranch.stateCount + falseBranch.stateCount + state)
          cell ∘
        sharedExitRetargetTransition
          (2 + blankBranch.stateCount + falseBranch.stateCount)
          trueBranch.halt 1) =
        Matches state cell := by
    simpa [taggedBranchBlankOffset,
      taggedBranchFalseOffset,
      taggedBranchTrueOffset] using hpredicate
  have hblankMapNone :
      Option.map
          (sharedExitRetargetTransition 2 blankBranch.halt 1)
          (List.find?
            (Matches
                (2 + blankBranch.stateCount + falseBranch.stateCount +
                  state) cell ∘
              sharedExitRetargetTransition 2
                blankBranch.halt 1)
            blankBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindBlank'
  have hfalseMapNone :
      Option.map
          (sharedExitRetargetTransition
            (2 + blankBranch.stateCount) falseBranch.halt 1)
          (List.find?
            (Matches
                (2 + blankBranch.stateCount + falseBranch.stateCount +
                  state) cell ∘
              sharedExitRetargetTransition
                (2 + blankBranch.stateCount) falseBranch.halt 1)
            falseBranch.transitions) = none := by
    rw [← List.find?_map]
    exact hfindFalse'
  rw [List.find?_append, hfindControl']
  simp
  rw [hblankMapNone, hfalseMapNone, hpredicate']
  cases hlocal :
      List.find? (Matches state cell)
        trueBranch.transitions <;>
    simp

theorem
    restoreFirstBitTaggedBrancherDescription_step_true
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {c : Configuration}
    (hstate : c.state < trueBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).stepConfig
        (sharedExitBranchConfiguration
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1 c) =
      Option.map
        (sharedExitBranchConfiguration
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1)
        (trueBranch.stepConfig c) := by
  cases c with
  | mk state tape =>
      by_cases hhalt : state = trueBranch.halt
      · subst state
        have htrueStep :
            trueBranch.stepConfig
                { state := trueBranch.halt, tape := tape } = none :=
          stepConfig_halt_none htrue.right tape
        have hbrancherStep :
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).stepConfig
                { state := 1, tape := tape } = none :=
          stepConfig_halt_none
            (restoreFirstBitTaggedBrancherDescription_subroutineReady
              hblank hfalse htrue).right tape
        simp [sharedExitBranchConfiguration, htrueStep,
          hbrancherStep]
      · have hlookup :=
          restoreFirstBitTaggedBrancherDescription_lookup_true
            hblank hfalse htrue (state := state)
            (cell := Tape.read tape) hstate
        simp [stepConfig,
          sharedExitBranchConfiguration, hhalt, hlookup]
        cases hlocal :
            trueBranch.lookupTransition state (Tape.read tape) with
        | none =>
            simp
        | some t =>
            simp [sharedExitRetargetTransition,
              sharedExitBranchConfiguration]
theorem restoreFirstBitTaggedBrancherDescription_run_true_branch
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    (n : Nat) (c : Configuration)
    (hstate : c.state < trueBranch.stateCount) :
    (RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch).runConfig n
        (sharedExitBranchConfiguration
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1 c) =
      sharedExitBranchConfiguration
        (taggedBranchTrueOffset blankBranch falseBranch)
        trueBranch.halt 1
        (trueBranch.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      rw [runConfig]
      rw [restoreFirstBitTaggedBrancherDescription_step_true
        hblank hfalse htrue hstate]
      cases hstep : trueBranch.stepConfig c with
      | none =>
          simp [runConfig, hstep]
      | some next =>
          have hnextState : next.state < trueBranch.stateCount :=
            stepConfig_state_bound htrue.left hstep
          simp [runConfig, hstep, ih next hnextState]
theorem restoreFirstBitTaggedBrancherDescription_run_true
    {blankBranch falseBranch trueBranch : MachineDescription}
    (hblank : blankBranch.SubroutineReady)
    (hfalse : falseBranch.SubroutineReady)
    (htrue : trueBranch.SubroutineReady)
    {T Tout : Tape Bool}
    (hread : Tape.read T = some true)
    (hbranch :
      exists steps : Nat,
        trueBranch.runConfig steps
            { state := trueBranch.start
              tape := Tape.move Direction.right
                (Tape.write (some false) T) } =
          { state := trueBranch.halt, tape := Tout }) :
    exists steps : Nat,
      (RestoreFirstBitTaggedBrancherDescription
        blankBranch falseBranch trueBranch).runConfig steps
          { state :=
              (RestoreFirstBitTaggedBrancherDescription
                blankBranch falseBranch trueBranch).start
            tape := T } =
        { state :=
            (RestoreFirstBitTaggedBrancherDescription
              blankBranch falseBranch trueBranch).halt
          tape := Tout } := by
  rcases hbranch with ⟨n, hn⟩
  let D :=
    RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch
  let branchStart : Configuration :=
    { state := trueBranch.start
      tape := Tape.move Direction.right (Tape.write (some false) T) }
  have hfirst :
      D.runConfig 1 { state := D.start, tape := T } =
        sharedExitBranchConfiguration
          (taggedBranchTrueOffset blankBranch falseBranch)
          trueBranch.halt 1
          branchStart := by
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [Tape.read] at hread
        | some b =>
            cases b
            · simp [Tape.read] at hread
            · simp [D, branchStart,
                RestoreFirstBitTaggedBrancherDescription,
                sharedExitBranchConfiguration,
                taggedBranchBlankOffset,
                taggedBranchFalseOffset,
                taggedBranchTrueOffset,
                runConfig, stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
  refine ⟨1 + n, ?_⟩
  rw [runConfig_add]
  rw [hfirst]
  have hstartBound : branchStart.state < trueBranch.stateCount := by
    exact htrue.left.right.left
  rw [restoreFirstBitTaggedBrancherDescription_run_true_branch
    hblank hfalse htrue n branchStart hstartBound]
  rw [hn]
  simp [RestoreFirstBitTaggedBrancherDescription,
    sharedExitBranchConfiguration]


end DovetailInitialLayoutInitializer
end Computability
end FoC
