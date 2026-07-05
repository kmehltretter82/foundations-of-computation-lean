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

def noRowReturnBlockSize : Nat :=
  returnFromTape2SeparatorToBlockStartDescription.stateCount

def noRowReturnRowBase (D : Description) (rowBlockSize : Nat) : Nat :=
  selectedRowBranchLimit D rowBlockSize

def noRowReturnOffset (D : Description) (rowBlockSize : Nat)
    (state : Nat) (reads : ReadTuple3) : Nat :=
  noRowReturnRowBase D rowBlockSize +
    rowSelectionIndex state reads * noRowReturnBlockSize

def noRowReturnLimit (D : Description) (rowBlockSize : Nat) : Nat :=
  noRowReturnRowBase D rowBlockSize +
    27 * D.stateCount * noRowReturnBlockSize

def retargetedNoRowReturnDescription
    (offset target : Nat) : MachineDescription :=
  MachineDescription.offsetRetargetDescription offset target
    returnFromTape2SeparatorToBlockStartDescription

def returnedNoRowJumpDescription
    (D : Description) (rowBlockSize : Nat)
    (state : Nat) (reads : ReadTuple3) : MachineDescription :=
  blankHeadBounceJumpDescription (noRowReturnLimit D rowBlockSize)
    (StaticDispatcherState.afterRead D state reads)
    (noRowJumpScratch D state reads)
    (retargetedNoRowReturnDescription
      (noRowReturnOffset D rowBlockSize state reads)
      (StaticDispatcherState.ready state)).start

def returnedNoRowBranchTransitions
    (D : Description) (rowBlockSize : Nat)
    (state : Nat) (reads : ReadTuple3) : List TransitionDescription :=
  (returnedNoRowJumpDescription D rowBlockSize state reads).transitions ++
    (retargetedNoRowReturnDescription
      (noRowReturnOffset D rowBlockSize state reads)
      (StaticDispatcherState.ready state)).transitions

def returnedNoRowItemTransitions
    (D : Description) (rowBlockSize : Nat)
    (item : Nat × ReadTuple3) : List TransitionDescription :=
  match lookupTransitionFromReadTuple3 D item.1 item.2 with
  | some _ => []
  | none => returnedNoRowBranchTransitions D rowBlockSize item.1 item.2

def returnedNoRowAllTransitions
    (D : Description) (rowBlockSize : Nat) : List TransitionDescription :=
  List.flatMap
    (fun item => returnedNoRowItemTransitions D rowBlockSize item)
    (noRowJumpItems D)

def threeHeadReaderReturnedNoRowSelectedTransitions
    (D : Description) (refresh : MachineDescription)
    (rowBlockSize : Nat) : List TransitionDescription :=
  threeHeadReaderTransitions D ++
    returnedNoRowAllTransitions D rowBlockSize ++
      selectedRowAllTransitions D refresh rowBlockSize

theorem selectedRowBranchLimit_le_noRowReturnRowBase
    (D : Description) (rowBlockSize : Nat) :
    selectedRowBranchLimit D rowBlockSize ≤
      noRowReturnRowBase D rowBlockSize := by
  exact Nat.le_refl _

theorem selectedRowBranchLimit_le_noRowReturnOffset
    (D : Description) (rowBlockSize state : Nat)
    (reads : ReadTuple3) :
    selectedRowBranchLimit D rowBlockSize ≤
      noRowReturnOffset D rowBlockSize state reads := by
  unfold noRowReturnOffset noRowReturnRowBase
  exact Nat.le_add_right _ _

theorem noRowReturnOffset_add_blockSize_le_limit
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    noRowReturnOffset D rowBlockSize state reads +
        noRowReturnBlockSize ≤
      noRowReturnLimit D rowBlockSize := by
  have hsucc :
      rowSelectionIndex state reads + 1 ≤ 27 * D.stateCount :=
    Nat.succ_le_of_lt
      (rowSelectionIndex_lt_stateCountBlock D reads hstate)
  have hmul := Nat.mul_le_mul_right noRowReturnBlockSize hsucc
  have hmain :
      noRowReturnRowBase D rowBlockSize +
          ((rowSelectionIndex state reads + 1) *
            noRowReturnBlockSize) ≤
        noRowReturnLimit D rowBlockSize := by
    simpa [noRowReturnLimit, Nat.add_assoc] using
      Nat.add_le_add_left hmul (noRowReturnRowBase D rowBlockSize)
  simpa [noRowReturnOffset, Nat.add_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hmain

theorem ready_lt_noRowReturnOffset
    {D : Description} {rowBlockSize state : Nat} {reads : ReadTuple3}
    (hstate : state < D.stateCount) :
    StaticDispatcherState.ready state <
      noRowReturnOffset D rowBlockSize state reads := by
  have hready :
      StaticDispatcherState.ready state < D.stateCount := by
    simpa [StaticDispatcherState.ready] using hstate
  have hlimit :
      D.stateCount ≤ selectedRowBranchLimit D rowBlockSize :=
    Nat.le_trans (stateCount_le_noRowJumpLimit D)
      (noRowJumpLimit_le_selectedRowBranchLimit D rowBlockSize)
  exact Nat.lt_of_lt_of_le hready
    (Nat.le_trans hlimit
      (selectedRowBranchLimit_le_noRowReturnOffset
        D rowBlockSize state reads))

theorem retargetedNoRowReturnDescription_subroutineReady
    {D : Description} {rowBlockSize state : Nat} {reads : ReadTuple3}
    (hstate : state < D.stateCount) :
    (retargetedNoRowReturnDescription
      (noRowReturnOffset D rowBlockSize state reads)
      (StaticDispatcherState.ready state)).SubroutineReady := by
  exact
    MachineDescription.offsetRetargetDescription_subroutineReady
      (ready_lt_noRowReturnOffset
        (D := D) (rowBlockSize := rowBlockSize)
        (state := state) (reads := reads) hstate)
      returnFromTape2SeparatorToBlockStartDescription_subroutineReady.left

theorem retargetedNoRowReturnDescription_sources_in_offset_block
    (offset target : Nat) :
    forall u : TransitionDescription,
      u ∈ (retargetedNoRowReturnDescription
            offset target).transitions ->
        offset ≤ u.source ∧
          u.source <
            offset + noRowReturnBlockSize := by
  simpa [retargetedNoRowReturnDescription, noRowReturnBlockSize] using
    offsetRetargetDescription_sources_in_offset_block
      returnFromTape2SeparatorToBlockStartDescription_subroutineReady.left

theorem retargetedNoRowReturnDescription_stateCount_le_offset_add_blockSize
    {offset target : Nat}
    (htargetBelow : target < offset) :
    (retargetedNoRowReturnDescription offset target).stateCount ≤
      offset + noRowReturnBlockSize := by
  simpa [retargetedNoRowReturnDescription,
    MachineDescription.offsetRetargetDescription, noRowReturnBlockSize] using
    (Nat.max_le.mpr
      ⟨Nat.le_refl (offset + noRowReturnBlockSize),
        Nat.le_trans (Nat.succ_le_of_lt htargetBelow)
          (Nat.le_add_right offset noRowReturnBlockSize)⟩)

theorem returnFromTape2SeparatorToBlockStartDescription_start_lt_halt :
    returnFromTape2SeparatorToBlockStartDescription.start <
      returnFromTape2SeparatorToBlockStartDescription.halt := by
  have hfirstStart :
      returnFromNextSeparatorToCurrentSeparatorDescription.start <
        returnFromNextSeparatorToCurrentSeparatorDescription.stateCount :=
    (returnFromNextSeparatorToCurrentSeparatorDescription_contract 1)
      |>.subroutineReady |>.left |>.right |>.left
  have hsecondCount :
      0 < returnFromTape1SeparatorToBlockStartDescription.stateCount :=
    returnFromTape1SeparatorToBlockStartDescription_contract
      |>.subroutineReady |>.left |>.left
  unfold returnFromTape2SeparatorToBlockStartDescription
    canonicalPrimitiveSeqDescription
    MachineDescription.seqSubroutine
    MachineDescription.Fragment.seq
    MachineDescription.Fragment.toDescription
    MachineDescription.asFragment
  simp
  lia

theorem returnFromTape2SeparatorToBlockStartDescription_start_ne_halt :
    returnFromTape2SeparatorToBlockStartDescription.start ≠
      returnFromTape2SeparatorToBlockStartDescription.halt :=
  Nat.ne_of_lt
    returnFromTape2SeparatorToBlockStartDescription_start_lt_halt

theorem retargetedNoRowReturnDescription_start_eq
    (offset target : Nat) :
    (retargetedNoRowReturnDescription offset target).start =
      offset + returnFromTape2SeparatorToBlockStartDescription.start := by
  simp [retargetedNoRowReturnDescription,
    MachineDescription.offsetRetargetDescription,
    returnFromTape2SeparatorToBlockStartDescription_start_ne_halt]

theorem retargetedNoRowReturnDescription_start_atLeast_offset
    (offset target : Nat) :
    offset ≤ (retargetedNoRowReturnDescription offset target).start := by
  rw [retargetedNoRowReturnDescription_start_eq]
  exact Nat.le_add_right _ _

theorem retargetedNoRowReturnDescription_start_lt_offset_add_blockSize
    (offset target : Nat) :
    (retargetedNoRowReturnDescription offset target).start <
      offset + noRowReturnBlockSize := by
  have hlocalStart :
      returnFromTape2SeparatorToBlockStartDescription.start <
        noRowReturnBlockSize := by
    simpa [noRowReturnBlockSize] using
      returnFromTape2SeparatorToBlockStartDescription_subroutineReady
        |>.left |>.right |>.left
  rw [retargetedNoRowReturnDescription_start_eq]
  exact Nat.add_lt_add_left hlocalStart offset

theorem retargetedNoRowReturnDescription_start_lt_limit
    {D : Description} {rowBlockSize state : Nat} {reads : ReadTuple3}
    (hstate : state < D.stateCount) :
    (retargetedNoRowReturnDescription
      (noRowReturnOffset D rowBlockSize state reads)
      (StaticDispatcherState.ready state)).start <
        noRowReturnLimit D rowBlockSize := by
  exact Nat.lt_of_lt_of_le
    (retargetedNoRowReturnDescription_start_lt_offset_add_blockSize
      (noRowReturnOffset D rowBlockSize state reads)
      (StaticDispatcherState.ready state))
    (noRowReturnOffset_add_blockSize_le_limit
      D reads hstate)

theorem selectedRowBranchLimit_le_noRowReturnLimit
    (D : Description) (rowBlockSize : Nat) :
    selectedRowBranchLimit D rowBlockSize ≤
      noRowReturnLimit D rowBlockSize := by
  unfold noRowReturnLimit noRowReturnRowBase
  exact Nat.le_add_right _ _

theorem noRowJumpLimit_le_noRowReturnLimit
    (D : Description) (rowBlockSize : Nat) :
    noRowJumpLimit D ≤ noRowReturnLimit D rowBlockSize :=
  Nat.le_trans
    (noRowJumpLimit_le_selectedRowBranchLimit D rowBlockSize)
    (selectedRowBranchLimit_le_noRowReturnLimit D rowBlockSize)

theorem returnedNoRowJumpDescription_subroutineReady
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    (returnedNoRowJumpDescription D rowBlockSize state reads).SubroutineReady := by
  have hsource :
      StaticDispatcherState.afterRead D state reads <
        noRowReturnLimit D rowBlockSize :=
    Nat.lt_of_lt_of_le
      (afterRead_lt_noRowJumpLimit D reads hstate)
      (noRowJumpLimit_le_noRowReturnLimit D rowBlockSize)
  have hscratch :
      noRowJumpScratch D state reads <
        noRowReturnLimit D rowBlockSize :=
    Nat.lt_of_lt_of_le
      (noRowJumpScratch_lt_noRowJumpLimit D reads hstate)
      (noRowJumpLimit_le_noRowReturnLimit D rowBlockSize)
  have htarget :
      (retargetedNoRowReturnDescription
        (noRowReturnOffset D rowBlockSize state reads)
        (StaticDispatcherState.ready state)).start <
          noRowReturnLimit D rowBlockSize :=
    retargetedNoRowReturnDescription_start_lt_limit
      (D := D) (rowBlockSize := rowBlockSize)
      (state := state) (reads := reads) hstate
  have hsourceScratch :
      StaticDispatcherState.afterRead D state reads ≠
        noRowJumpScratch D state reads :=
    Nat.ne_of_lt (afterRead_lt_noRowJumpScratch D reads hstate)
  have hsourceTargetLt :
      StaticDispatcherState.afterRead D state reads <
        (retargetedNoRowReturnDescription
          (noRowReturnOffset D rowBlockSize state reads)
          (StaticDispatcherState.ready state)).start := by
    exact Nat.lt_of_lt_of_le
      (afterRead_lt_selectedRowBranchLimit
        D reads rowBlockSize hstate)
      (Nat.le_trans
        (selectedRowBranchLimit_le_noRowReturnOffset
          D rowBlockSize state reads)
        (retargetedNoRowReturnDescription_start_atLeast_offset
          (noRowReturnOffset D rowBlockSize state reads)
          (StaticDispatcherState.ready state)))
  have hscratchTargetLt :
      noRowJumpScratch D state reads <
        (retargetedNoRowReturnDescription
          (noRowReturnOffset D rowBlockSize state reads)
          (StaticDispatcherState.ready state)).start := by
    have hscratchSelected :
        noRowJumpScratch D state reads <
          selectedRowBranchLimit D rowBlockSize :=
      Nat.lt_of_lt_of_le
        (noRowJumpScratch_lt_noRowJumpLimit D reads hstate)
        (noRowJumpLimit_le_selectedRowBranchLimit D rowBlockSize)
    exact Nat.lt_of_lt_of_le hscratchSelected
      (Nat.le_trans
        (selectedRowBranchLimit_le_noRowReturnOffset
          D rowBlockSize state reads)
        (retargetedNoRowReturnDescription_start_atLeast_offset
          (noRowReturnOffset D rowBlockSize state reads)
          (StaticDispatcherState.ready state)))
  simpa [returnedNoRowJumpDescription] using
    blankHeadBounceJumpDescription_subroutineReady
      hsource hscratch htarget hsourceScratch
      (Nat.ne_of_lt hsourceTargetLt).symm
      (Nat.ne_of_lt hscratchTargetLt).symm

theorem returnedNoRowBranchTransitions_wellFormed
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    TransitionListWellFormed
      (noRowReturnLimit D rowBlockSize)
      (returnedNoRowBranchTransitions D rowBlockSize state reads) := by
  have hjump :
      TransitionListWellFormed
        (noRowReturnLimit D rowBlockSize)
        (returnedNoRowJumpDescription D rowBlockSize state reads).transitions :=
    transitionListWellFormed_of_wellFormed_mono
      (returnedNoRowJumpDescription_subroutineReady
        D reads hstate).left
      (Nat.le_refl _)
  have htargetBelow :
      StaticDispatcherState.ready state <
        noRowReturnOffset D rowBlockSize state reads :=
    ready_lt_noRowReturnOffset
      (D := D) (rowBlockSize := rowBlockSize)
      (state := state) (reads := reads) hstate
  have hreturnCount :
      (retargetedNoRowReturnDescription
        (noRowReturnOffset D rowBlockSize state reads)
        (StaticDispatcherState.ready state)).stateCount ≤
          noRowReturnLimit D rowBlockSize :=
    Nat.le_trans
      (retargetedNoRowReturnDescription_stateCount_le_offset_add_blockSize
        htargetBelow)
      (noRowReturnOffset_add_blockSize_le_limit D reads hstate)
  have hreturn :
      TransitionListWellFormed
        (noRowReturnLimit D rowBlockSize)
        (retargetedNoRowReturnDescription
          (noRowReturnOffset D rowBlockSize state reads)
          (StaticDispatcherState.ready state)).transitions :=
    transitionListWellFormed_of_wellFormed_mono
      (retargetedNoRowReturnDescription_subroutineReady
        (D := D) (rowBlockSize := rowBlockSize)
        (state := state) (reads := reads) hstate).left
      hreturnCount
  simpa [returnedNoRowBranchTransitions] using
    transitionListWellFormed_append hjump hreturn

theorem returnedNoRowItemTransitions_wellFormed
    (D : Description) (rowBlockSize : Nat)
    {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D) :
    TransitionListWellFormed
      (noRowReturnLimit D rowBlockSize)
      (returnedNoRowItemTransitions D rowBlockSize item) := by
  cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 with
  | some t =>
      simp [returnedNoRowItemTransitions, hlookup,
        TransitionListWellFormed]
  | none =>
      simpa [returnedNoRowItemTransitions, hlookup] using
        returnedNoRowBranchTransitions_wellFormed
          D item.2 (noRowJumpItems_mem_state_lt hitem)

theorem returnedNoRowAllTransitions_wellFormed
    (D : Description) (rowBlockSize : Nat) :
    TransitionListWellFormed
      (noRowReturnLimit D rowBlockSize)
      (returnedNoRowAllTransitions D rowBlockSize) := by
  unfold returnedNoRowAllTransitions
  apply transitionListWellFormed_bind
  intro item hitem
  exact returnedNoRowItemTransitions_wellFormed
    D rowBlockSize hitem

theorem retargetedNoRowReturnDescription_runsFromTape2Separator
    {D : Description} {rowBlockSize state : Nat} {reads : ReadTuple3}
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3)
    {physical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2 physical) :
    RunsFromStateTapeEquiv
      (retargetedNoRowReturnDescription
        (noRowReturnOffset D rowBlockSize state reads)
        (StaticDispatcherState.ready state))
      (retargetedNoRowReturnDescription
        (noRowReturnOffset D rowBlockSize state reads)
        (StaticDispatcherState.ready state)).start
      (StaticDispatcherState.ready state)
      physical
      (encodedGuardedStructuredTapes logical) := by
  have htargetBelow :
      StaticDispatcherState.ready state <
        noRowReturnOffset D rowBlockSize state reads :=
    ready_lt_noRowReturnOffset
      (D := D) (rowBlockSize := rowBlockSize)
      (state := state) (reads := reads) hstate
  have hrun :=
    returnFromTape2SeparatorToCanonicalBlockStart_runs
      hlength hseparator
  simpa [retargetedNoRowReturnDescription] using
    runsFromStateTapeEquiv_offsetRetargetDescription
      (offset := noRowReturnOffset D rowBlockSize state reads)
      (target := StaticDispatcherState.ready state)
      htargetBelow
      returnFromTape2SeparatorToBlockStartDescription_subroutineReady.right
      hrun

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
