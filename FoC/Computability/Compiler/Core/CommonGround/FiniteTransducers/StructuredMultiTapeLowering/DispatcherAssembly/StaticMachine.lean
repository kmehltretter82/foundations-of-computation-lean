import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.DispatcherAssembly.SelectedRuns

set_option doc.verso true

/-!
# Concrete static dispatcher machine

This module packages the aggregate three-head reader plus row-selection table
as an ordinary machine description.  The no-row branch still exposes its
current tape-2-separator endpoint separately; the full static step-lowering
wrapper will use the returned no-row branch once that endpoint is incorporated
into the table.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace StaticDispatcherReaderAssembly

theorem transitionListWellFormed_mono
    {small big : Nat} {transitions : List TransitionDescription}
    (h : TransitionListWellFormed small transitions)
    (hle : small ≤ big) :
    TransitionListWellFormed big transitions := by
  intro t ht
  have hformed := h t ht
  exact
    ⟨Nat.lt_of_lt_of_le hformed.left hle,
      Nat.lt_of_lt_of_le hformed.right hle⟩

theorem noRowJumpLimit_le_selectedRowBranchLimit
    (D : Description) (rowBlockSize : Nat) :
    noRowJumpLimit D ≤ selectedRowBranchLimit D rowBlockSize := by
  unfold selectedRowBranchLimit selectedRowBranchRowBase
    selectedRowBranchScratchBase
  lia

theorem threeHeadReaderStateLimit_le_selectedRowBranchLimit
    (D : Description) (rowBlockSize : Nat) :
    threeHeadReaderStateLimit D ≤
      selectedRowBranchLimit D rowBlockSize := by
  have hle : threeHeadReaderStateLimit D ≤ noRowJumpLimit D := by
    unfold noRowJumpLimit noRowJumpScratchBase
    exact Nat.le_add_right _ _
  exact Nat.le_trans hle
    (noRowJumpLimit_le_selectedRowBranchLimit D rowBlockSize)

theorem noRowJumpItemTransitions_wellFormed
    (D : Description) (rowBlockSize : Nat)
    {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D) :
    TransitionListWellFormed
      (selectedRowBranchLimit D rowBlockSize)
      (noRowJumpItemTransitions D item) := by
  cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 with
  | some t =>
      simp [noRowJumpItemTransitions, hlookup, TransitionListWellFormed]
  | none =>
      have hstate := noRowJumpItems_mem_state_lt hitem
      have hmono :
          (noRowJumpDescription D item.1 item.2).stateCount ≤
            selectedRowBranchLimit D rowBlockSize := by
        simpa [noRowJumpDescription, blankHeadBounceJumpDescription] using
          noRowJumpLimit_le_selectedRowBranchLimit D rowBlockSize
      simpa [noRowJumpItemTransitions, hlookup] using
        transitionListWellFormed_of_wellFormed_mono
          (noRowJumpDescription_wellFormed D item.2 hstate) hmono

theorem noRowJumpAllTransitions_wellFormed
    (D : Description) (rowBlockSize : Nat) :
    TransitionListWellFormed
      (selectedRowBranchLimit D rowBlockSize)
      (noRowJumpAllTransitions D) := by
  unfold noRowJumpAllTransitions
  apply transitionListWellFormed_bind
  intro item hitem
  exact noRowJumpItemTransitions_wellFormed D rowBlockSize hitem

theorem threeHeadReaderNoRowTransitions_wellFormed
    (D : Description) (rowBlockSize : Nat) :
    TransitionListWellFormed
      (selectedRowBranchLimit D rowBlockSize)
      (threeHeadReaderNoRowTransitions D) := by
  simpa [threeHeadReaderNoRowTransitions] using
    transitionListWellFormed_append
      (transitionListWellFormed_mono
        (threeHeadReaderTransitions_wellFormed D)
        (threeHeadReaderStateLimit_le_selectedRowBranchLimit
          D rowBlockSize))
      (noRowJumpAllTransitions_wellFormed D rowBlockSize)

theorem retargetedSelectedRowSeparatorDescription_stateCount_le_offset_add_blockSize
    {offset target rowBlockSize : Nat} {t : Transition}
    {refresh : MachineDescription}
    (htargetBelow : target < offset)
    (hrowFits :
      (selectedRowSeparatorDescription t refresh).stateCount ≤
        rowBlockSize) :
    (retargetedSelectedRowSeparatorDescription
      offset target t refresh).stateCount ≤ offset + rowBlockSize := by
  simpa [retargetedSelectedRowSeparatorDescription,
    MachineDescription.offsetRetargetDescription] using
    (Nat.max_le.mpr
      ⟨Nat.add_le_add_left hrowFits offset,
        Nat.le_trans (Nat.succ_le_of_lt htargetBelow)
          (Nat.le_add_right offset rowBlockSize)⟩)

theorem retargetedSelectedRowSeparatorDescription_stateCount_le_limit
    {D : Description} (hDwf : D.WellFormed)
    {rowBlockSize : Nat} {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D)
    {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 = some t)
    {refresh : MachineDescription}
    (hrowFits :
      (selectedRowSeparatorDescription t refresh).stateCount ≤
        rowBlockSize) :
    (retargetedSelectedRowSeparatorDescription
      (selectedRowBranchRowOffset D rowBlockSize item.1 item.2)
      (StaticDispatcherState.ready t.target) t refresh).stateCount ≤
        selectedRowBranchLimit D rowBlockSize := by
  have htargetBelow :
      StaticDispatcherState.ready t.target <
        selectedRowBranchRowOffset D rowBlockSize item.1 item.2 :=
    ready_target_lt_selectedRowBranchRowOffset hDwf hlookup rowBlockSize
  have hblock :
      selectedRowBranchRowOffset D rowBlockSize item.1 item.2 +
          rowBlockSize ≤
        selectedRowBranchLimit D rowBlockSize :=
    selectedRowBranchRowOffset_add_blockSize_le_limit
      D item.2 (noRowJumpItems_mem_state_lt hitem)
  exact Nat.le_trans
    (retargetedSelectedRowSeparatorDescription_stateCount_le_offset_add_blockSize
      htargetBelow hrowFits)
    hblock

theorem selectedRowBranchTransitions_wellFormed
    {D : Description} (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {rowBlockSize : Nat} {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D)
    {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 = some t)
    (hrowFits :
      (selectedRowSeparatorDescription t refresh).stateCount ≤
        rowBlockSize) :
    TransitionListWellFormed
      (selectedRowBranchLimit D rowBlockSize)
      (selectedRowBranchTransitions
        (selectedRowBranchLimit D rowBlockSize)
        (selectedRowBranchRowOffset D rowBlockSize item.1 item.2)
        D item.1 item.2
        (selectedRowBranchScratch D item.1 item.2)
        t refresh) := by
  let rowMachine :=
    retargetedSelectedRowSeparatorDescription
      (selectedRowBranchRowOffset D rowBlockSize item.1 item.2)
      (StaticDispatcherState.ready t.target) t refresh
  let jumpMachine :=
    selectedRowBranchJumpDescription
      (selectedRowBranchLimit D rowBlockSize)
      D item.1 item.2
      (selectedRowBranchScratch D item.1 item.2)
      rowMachine.start
  have hstate := noRowJumpItems_mem_state_lt hitem
  have hsourceLimit :
      StaticDispatcherState.afterRead D item.1 item.2 <
        selectedRowBranchLimit D rowBlockSize :=
    afterRead_lt_selectedRowBranchLimit D item.2 rowBlockSize hstate
  have hscratchLimit :
      selectedRowBranchScratch D item.1 item.2 <
        selectedRowBranchLimit D rowBlockSize :=
    selectedRowBranchScratch_lt_selectedRowBranchLimit
      D item.2 rowBlockSize hstate
  have hstartLimit : rowMachine.start <
      selectedRowBranchLimit D rowBlockSize := by
    simpa [rowMachine] using
      selectedRowBranchRetargetedStart_lt_limit
        hrows hitem hlookup hrefresh rowBlockSize hrowFits
  have hsourceScratch :
      StaticDispatcherState.afterRead D item.1 item.2 ≠
        selectedRowBranchScratch D item.1 item.2 :=
    Nat.ne_of_lt (afterRead_lt_selectedRowBranchScratch D item.2 hstate)
  have hjumpWellFormed :
      TransitionListWellFormed
        (selectedRowBranchLimit D rowBlockSize)
        jumpMachine.transitions := by
    exact
      transitionListWellFormed_of_wellFormed_mono
        (by
          simpa [jumpMachine, selectedRowBranchJumpDescription] using
            blankHeadBounceJumpDescription_wellFormed
              hsourceLimit hscratchLimit hstartLimit hsourceScratch)
        (Nat.le_refl _)
  have htargetBelow :
      StaticDispatcherState.ready t.target <
        selectedRowBranchRowOffset D rowBlockSize item.1 item.2 :=
    ready_target_lt_selectedRowBranchRowOffset hDwf hlookup rowBlockSize
  have hrowReady :
      rowMachine.SubroutineReady := by
    simpa [rowMachine] using
      retargetedSelectedRowSeparatorDescription_subroutineReady
        htargetBelow hrows hlookup hrefresh
  have hrowCount :
      rowMachine.stateCount ≤ selectedRowBranchLimit D rowBlockSize := by
    simpa [rowMachine] using
      retargetedSelectedRowSeparatorDescription_stateCount_le_limit
        hDwf hitem hlookup hrowFits
  have hrowWellFormed :
      TransitionListWellFormed
        (selectedRowBranchLimit D rowBlockSize)
        rowMachine.transitions :=
    transitionListWellFormed_of_wellFormed_mono
      hrowReady.left hrowCount
  simpa [selectedRowBranchTransitions, jumpMachine, rowMachine] using
    transitionListWellFormed_append hjumpWellFormed hrowWellFormed

theorem selectedRowItemTransitions_wellFormed
    {D : Description} (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (rowBlockSize : Nat)
    (hrowFits :
      forall item : Nat × ReadTuple3,
        item ∈ noRowJumpItems D ->
          forall t : Transition,
            lookupTransitionFromReadTuple3 D item.1 item.2 = some t ->
              (selectedRowSeparatorDescription t refresh).stateCount ≤
                rowBlockSize)
    {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D) :
    TransitionListWellFormed
      (selectedRowBranchLimit D rowBlockSize)
      (selectedRowItemTransitions D refresh rowBlockSize item) := by
  cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 with
  | none =>
      simp [selectedRowItemTransitions, hlookup, TransitionListWellFormed]
  | some t =>
      simpa [selectedRowItemTransitions, hlookup] using
        selectedRowBranchTransitions_wellFormed
          hDwf hrows hrefresh hitem hlookup
          (hrowFits item hitem t hlookup)

theorem selectedRowAllTransitions_wellFormed
    {D : Description} (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (rowBlockSize : Nat)
    (hrowFits :
      forall item : Nat × ReadTuple3,
        item ∈ noRowJumpItems D ->
          forall t : Transition,
            lookupTransitionFromReadTuple3 D item.1 item.2 = some t ->
              (selectedRowSeparatorDescription t refresh).stateCount ≤
                rowBlockSize) :
    TransitionListWellFormed
      (selectedRowBranchLimit D rowBlockSize)
      (selectedRowAllTransitions D refresh rowBlockSize) := by
  unfold selectedRowAllTransitions
  apply transitionListWellFormed_bind
  intro item hitem
  exact selectedRowItemTransitions_wellFormed
    hDwf hrows hrefresh rowBlockSize hrowFits hitem

theorem threeHeadReaderNoRowSelectedTransitions_wellFormed
    {D : Description} (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (rowBlockSize : Nat)
    (hrowFits :
      forall item : Nat × ReadTuple3,
        item ∈ noRowJumpItems D ->
          forall t : Transition,
            lookupTransitionFromReadTuple3 D item.1 item.2 = some t ->
              (selectedRowSeparatorDescription t refresh).stateCount ≤
                rowBlockSize) :
    TransitionListWellFormed
      (selectedRowBranchLimit D rowBlockSize)
      (threeHeadReaderNoRowSelectedTransitions
        D refresh rowBlockSize) := by
  simpa [threeHeadReaderNoRowSelectedTransitions] using
    transitionListWellFormed_append
      (threeHeadReaderNoRowTransitions_wellFormed D rowBlockSize)
      (selectedRowAllTransitions_wellFormed
        hDwf hrows hrefresh rowBlockSize hrowFits)

/-- Concrete aggregate static dispatcher table for a supplied row refresh. -/
def staticLoweredDescription
    (D : Description) (refresh : MachineDescription) :
    MachineDescription :=
  tableMachine
    (selectedRowBranchLimit D (selectedRowBlockSize D refresh))
    (StaticDispatcherState.ready D.start)
    (StaticDispatcherState.ready D.halt)
    (threeHeadReaderNoRowSelectedTransitions
      D refresh (selectedRowBlockSize D refresh))

theorem selectedRowBranchLimit_pos
    (D : Description) (hDwf : D.WellFormed)
    (rowBlockSize : Nat) :
    0 < selectedRowBranchLimit D rowBlockSize := by
  have hstate :
      0 < D.stateCount := hDwf.right.left
  have hle :
      D.stateCount ≤ selectedRowBranchLimit D rowBlockSize :=
    Nat.le_trans (stateCount_le_noRowJumpLimit D)
      (noRowJumpLimit_le_selectedRowBranchLimit D rowBlockSize)
  exact Nat.lt_of_lt_of_le hstate hle

theorem ready_lt_selectedRowBranchLimit
    {D : Description} {state rowBlockSize : Nat}
    (hstate : state < D.stateCount) :
    StaticDispatcherState.ready state <
      selectedRowBranchLimit D rowBlockSize := by
  have hle :
      D.stateCount ≤ selectedRowBranchLimit D rowBlockSize :=
    Nat.le_trans (stateCount_le_noRowJumpLimit D)
      (noRowJumpLimit_le_selectedRowBranchLimit D rowBlockSize)
  exact Nat.lt_of_lt_of_le
    (by simpa [StaticDispatcherState.ready] using hstate) hle

theorem staticLoweredDescription_wellFormed
    (D : Description) (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    (staticLoweredDescription D refresh).WellFormed := by
  let rowBlockSize := selectedRowBlockSize D refresh
  refine ⟨?stateCount, ?start, ?halt, ?transitions, ?deterministic⟩
  · exact selectedRowBranchLimit_pos D hDwf rowBlockSize
  · simpa [staticLoweredDescription, rowBlockSize] using
      ready_lt_selectedRowBranchLimit
        (D := D) (state := D.start) (rowBlockSize := rowBlockSize)
        hDwf.right.right.left
  · simpa [staticLoweredDescription, rowBlockSize] using
      ready_lt_selectedRowBranchLimit
        (D := D) (state := D.halt) (rowBlockSize := rowBlockSize)
        hDwf.right.right.right.left
  · simpa [staticLoweredDescription, rowBlockSize] using
      threeHeadReaderNoRowSelectedTransitions_wellFormed
        hDwf hrows hrefresh rowBlockSize
        (by
          intro item hitem t hlookup
          exact selectedRowBlockSize_fits D refresh hitem hlookup)
  · simpa [staticLoweredDescription, rowBlockSize,
      MachineDescription.Deterministic] using
      threeHeadReaderNoRowSelectedTransitions_deterministic
        hDwf hrows hrefresh rowBlockSize
        (by
          intro item hitem t hlookup
          exact selectedRowBlockSize_fits D refresh hitem hlookup)

theorem staticLoweredDescription_noRow_runs
    (D : Description) (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {state : Nat}
    (hstate : state ∈ activeStateValues D)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3)
    (hlookup :
      lookupTransitionFromReadTuple3 D state (ReadTuple3.ofTapes logical) =
        none) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (staticLoweredDescription D refresh)
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.ready state)
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  simpa [staticLoweredDescription] using
    staticDispatcher_noRow_runs
      D hDwf hrows hrefresh hstate hlength hlookup

theorem staticLoweredDescription_selectedRow_runs
    (D : Description) (hD : D.tapeCount = 3)
    (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {state : Nat} (hstate : state ∈ activeStateValues D)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3)
    {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state (ReadTuple3.ofTapes logical) =
        some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        (oneStepOrSelf D { state := state, tapes := logical }).state =
          t.target ∧
        RunsFromStateTapeEquiv
          (staticLoweredDescription D refresh)
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.ready t.target)
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes
            (oneStepOrSelf D { state := state, tapes := logical }).tapes) := by
  simpa [staticLoweredDescription] using
    staticDispatcher_selectedRow_runs
      D hD hDwf hrows hstate hlength hlookup hrefresh

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
