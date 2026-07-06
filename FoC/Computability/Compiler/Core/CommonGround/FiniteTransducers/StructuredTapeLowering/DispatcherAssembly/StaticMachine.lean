import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.DispatcherAssembly.SelectedRuns
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Runs

set_option doc.verso true

/-!
# Concrete static dispatcher machine

This module packages the aggregate three-head reader plus row-selection table
as an ordinary machine description.  The no-row branch returns from the
tape-2-separator endpoint to the canonical encoded structured tape.
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

def threeHeadReaderReturnedNoRowTransitions
    (D : Description) (rowBlockSize : Nat) :
    List TransitionDescription :=
  threeHeadReaderTransitions D ++
    returnedNoRowAllTransitions D rowBlockSize

def threeHeadReaderReturnedNoRowSelectedTransitions
    (D : Description) (refresh : MachineDescription)
    (rowBlockSize : Nat) : List TransitionDescription :=
  threeHeadReaderReturnedNoRowTransitions D rowBlockSize ++
      selectedRowAllTransitions D refresh rowBlockSize

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

theorem returnedNoRowJumpDescription_sources_below_returnOffset
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    TransitionSourcesBelow
      (noRowReturnOffset D rowBlockSize state reads)
      (returnedNoRowJumpDescription D rowBlockSize state reads).transitions := by
  intro u hu
  rcases
      blankHeadBounceJumpDescription_transition_source_cases
        (by
          simpa [returnedNoRowJumpDescription] using hu) with
    hsource | hscratch
  · rw [hsource]
    exact Nat.lt_of_lt_of_le
      (afterRead_lt_selectedRowBranchLimit D reads rowBlockSize hstate)
      (selectedRowBranchLimit_le_noRowReturnOffset
        D rowBlockSize state reads)
  · rw [hscratch]
    have hscratchSelected :
        noRowJumpScratch D state reads <
          selectedRowBranchLimit D rowBlockSize :=
      Nat.lt_of_lt_of_le
        (noRowJumpScratch_lt_noRowJumpLimit D reads hstate)
        (noRowJumpLimit_le_selectedRowBranchLimit D rowBlockSize)
    exact Nat.lt_of_lt_of_le hscratchSelected
      (selectedRowBranchLimit_le_noRowReturnOffset
        D rowBlockSize state reads)

theorem retargetedNoRowReturnDescription_sources_atLeast_offset
    (offset target : Nat) :
    TransitionSourcesAtLeast offset
      (retargetedNoRowReturnDescription offset target).transitions := by
  intro u hu
  exact
    (retargetedNoRowReturnDescription_sources_in_offset_block
      offset target u hu).left

theorem returnedNoRowJump_return_sourceDisjoint
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    TransitionSourceDisjoint
      (returnedNoRowJumpDescription D rowBlockSize state reads).transitions
      (retargetedNoRowReturnDescription
        (noRowReturnOffset D rowBlockSize state reads)
        (StaticDispatcherState.ready state)).transitions :=
  transitionSourceDisjoint_of_below_atLeast
    (returnedNoRowJumpDescription_sources_below_returnOffset
      D reads hstate)
    (retargetedNoRowReturnDescription_sources_atLeast_offset
      (noRowReturnOffset D rowBlockSize state reads)
      (StaticDispatcherState.ready state))

theorem returnedNoRowBranchTransitions_source_region
    {D : Description} {rowBlockSize state : Nat} {reads : ReadTuple3}
    {u : TransitionDescription}
    (hu :
      u ∈ returnedNoRowBranchTransitions D rowBlockSize state reads) :
    u.source = StaticDispatcherState.afterRead D state reads ∨
      u.source = noRowJumpScratch D state reads ∨
        (noRowReturnOffset D rowBlockSize state reads ≤ u.source ∧
          u.source <
            noRowReturnOffset D rowBlockSize state reads +
              noRowReturnBlockSize) := by
  simp [returnedNoRowBranchTransitions] at hu
  rcases hu with huJump | huReturn
  · rcases
      blankHeadBounceJumpDescription_transition_source_cases
        (by
          simpa [returnedNoRowJumpDescription] using huJump) with
      hsource | hscratch
    · exact Or.inl hsource
    · exact Or.inr (Or.inl hscratch)
  · exact Or.inr (Or.inr
      (retargetedNoRowReturnDescription_sources_in_offset_block
        (noRowReturnOffset D rowBlockSize state reads)
        (StaticDispatcherState.ready state) u huReturn))

theorem returnedNoRowBranchTransitions_deterministic
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    TransitionListDeterministic
      (returnedNoRowBranchTransitions D rowBlockSize state reads) := by
  have hjumpDet :
      TransitionListDeterministic
        (returnedNoRowJumpDescription D rowBlockSize state reads).transitions :=
    transitionListDeterministic_of_wellFormed
      (returnedNoRowJumpDescription_subroutineReady
        D reads hstate).left
  have hreturnDet :
      TransitionListDeterministic
        (retargetedNoRowReturnDescription
          (noRowReturnOffset D rowBlockSize state reads)
          (StaticDispatcherState.ready state)).transitions :=
    transitionListDeterministic_of_wellFormed
      (retargetedNoRowReturnDescription_subroutineReady
        (D := D) (rowBlockSize := rowBlockSize)
        (state := state) (reads := reads) hstate).left
  simpa [returnedNoRowBranchTransitions] using
    transitionListDeterministic_append_of_sourceDisjoint
      hjumpDet hreturnDet
      (returnedNoRowJump_return_sourceDisjoint
        D reads hstate)

theorem returnedNoRowItemTransitions_deterministic
    (D : Description) (rowBlockSize : Nat)
    {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D) :
    TransitionListDeterministic
      (returnedNoRowItemTransitions D rowBlockSize item) := by
  cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 with
  | some t =>
      simp [returnedNoRowItemTransitions, hlookup,
        TransitionListDeterministic]
  | none =>
      simpa [returnedNoRowItemTransitions, hlookup] using
        returnedNoRowBranchTransitions_deterministic
          D item.2 (noRowJumpItems_mem_state_lt hitem)

theorem noRowJumpScratch_eq_pair
    (D : Description) {state₀ state₁ : Nat}
    {reads₀ reads₁ : ReadTuple3}
    (hscratch :
      noRowJumpScratch D state₀ reads₀ =
        noRowJumpScratch D state₁ reads₁) :
    (state₀, reads₀) = (state₁, reads₁) := by
  apply rowSelectionIndex_eq_pair
  unfold rowSelectionIndex
  unfold noRowJumpScratch at hscratch
  exact Nat.add_left_cancel (n := noRowJumpScratchBase D) (by
    simpa [Nat.add_assoc] using hscratch)

theorem noRowReturnOffset_add_blockSize_le_of_index_lt
    (D : Description) {rowBlockSize state₀ state₁ : Nat}
    {reads₀ reads₁ : ReadTuple3}
    (hindex :
      rowSelectionIndex state₀ reads₀ <
        rowSelectionIndex state₁ reads₁) :
    noRowReturnOffset D rowBlockSize state₀ reads₀ +
        noRowReturnBlockSize ≤
      noRowReturnOffset D rowBlockSize state₁ reads₁ := by
  have hsucc :
      rowSelectionIndex state₀ reads₀ + 1 ≤
        rowSelectionIndex state₁ reads₁ :=
    Nat.succ_le_of_lt hindex
  have hmul :=
    Nat.mul_le_mul_right noRowReturnBlockSize hsucc
  have hmain :
      noRowReturnRowBase D rowBlockSize +
          ((rowSelectionIndex state₀ reads₀ + 1) *
            noRowReturnBlockSize) ≤
        noRowReturnRowBase D rowBlockSize +
          rowSelectionIndex state₁ reads₁ *
            noRowReturnBlockSize :=
    Nat.add_le_add_left hmul (noRowReturnRowBase D rowBlockSize)
  simpa [noRowReturnOffset, Nat.add_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hmain

theorem returnedNoRowItemTransitions_sourceDisjoint_of_ne
    (D : Description) (rowBlockSize : Nat)
    {item₀ item₁ : Nat × ReadTuple3}
    (hitem₀ : item₀ ∈ noRowJumpItems D)
    (hitem₁ : item₁ ∈ noRowJumpItems D)
    (hne : item₀ ≠ item₁) :
    TransitionSourceDisjoint
      (returnedNoRowItemTransitions D rowBlockSize item₀)
      (returnedNoRowItemTransitions D rowBlockSize item₁) := by
  cases hlookup₀ :
      lookupTransitionFromReadTuple3 D item₀.1 item₀.2 with
  | some t =>
      simp [returnedNoRowItemTransitions, hlookup₀,
        TransitionSourceDisjoint]
  | none =>
      cases hlookup₁ :
          lookupTransitionFromReadTuple3 D item₁.1 item₁.2 with
      | some t =>
          simp [returnedNoRowItemTransitions, hlookup₀, hlookup₁,
            TransitionSourceDisjoint]
      | none =>
          intro left right hleft hright hsource
          have hstate₀ := noRowJumpItems_mem_state_lt hitem₀
          have hstate₁ := noRowJumpItems_mem_state_lt hitem₁
          have hleft' :
              left ∈ returnedNoRowBranchTransitions
                D rowBlockSize item₀.1 item₀.2 := by
            simpa [returnedNoRowItemTransitions, hlookup₀] using hleft
          have hright' :
              right ∈ returnedNoRowBranchTransitions
                D rowBlockSize item₁.1 item₁.2 := by
            simpa [returnedNoRowItemTransitions, hlookup₁] using hright
          rcases returnedNoRowBranchTransitions_source_region
              (D := D) (rowBlockSize := rowBlockSize)
              (state := item₀.1) (reads := item₀.2)
              hleft' with
            hleftAfter | hleftCases
          · rcases returnedNoRowBranchTransitions_source_region
                (D := D) (rowBlockSize := rowBlockSize)
                (state := item₁.1) (reads := item₁.2)
                hright' with
              hrightAfter | hrightCases
            · rw [hleftAfter, hrightAfter] at hsource
              exact hne (afterRead_eq_pair D hsource)
            · rcases hrightCases with hrightScratch | hrightReturn
              · rw [hleftAfter, hrightScratch] at hsource
                have hlt :=
                  afterRead_lt_noRowJumpScratch_of_states
                    (D := D) (afterState := item₀.1)
                    (scratchState := item₁.1)
                    item₀.2 item₁.2 hstate₀
                exact Nat.ne_of_lt hlt hsource
              · rw [hleftAfter] at hsource
                have hlt :
                    StaticDispatcherState.afterRead D item₀.1 item₀.2 <
                      noRowReturnOffset D rowBlockSize
                        item₁.1 item₁.2 :=
                  Nat.lt_of_lt_of_le
                    (afterRead_lt_selectedRowBranchLimit
                      D item₀.2 rowBlockSize hstate₀)
                    (selectedRowBranchLimit_le_noRowReturnOffset
                      D rowBlockSize item₁.1 item₁.2)
                exact Nat.ne_of_lt
                  (Nat.lt_of_lt_of_le hlt hrightReturn.left)
                  hsource
          · rcases hleftCases with hleftScratch | hleftReturn
            · rcases returnedNoRowBranchTransitions_source_region
                  (D := D) (rowBlockSize := rowBlockSize)
                  (state := item₁.1) (reads := item₁.2)
                  hright' with
                hrightAfter | hrightCases
              · rw [hleftScratch, hrightAfter] at hsource
                have hlt :=
                  afterRead_lt_noRowJumpScratch_of_states
                    (D := D) (afterState := item₁.1)
                    (scratchState := item₀.1)
                    item₁.2 item₀.2 hstate₁
                exact (Nat.ne_of_lt hlt).symm hsource
              · rcases hrightCases with hrightScratch | hrightReturn
                · rw [hleftScratch, hrightScratch] at hsource
                  exact hne (noRowJumpScratch_eq_pair D hsource)
                · rw [hleftScratch] at hsource
                  have hscratchSelected :
                      noRowJumpScratch D item₀.1 item₀.2 <
                        selectedRowBranchLimit D rowBlockSize :=
                    Nat.lt_of_lt_of_le
                      (noRowJumpScratch_lt_noRowJumpLimit
                        D item₀.2 hstate₀)
                      (noRowJumpLimit_le_selectedRowBranchLimit
                        D rowBlockSize)
                  have hlt :
                      noRowJumpScratch D item₀.1 item₀.2 <
                        noRowReturnOffset D rowBlockSize
                          item₁.1 item₁.2 :=
                    Nat.lt_of_lt_of_le hscratchSelected
                      (selectedRowBranchLimit_le_noRowReturnOffset
                        D rowBlockSize item₁.1 item₁.2)
                  exact Nat.ne_of_lt
                    (Nat.lt_of_lt_of_le hlt hrightReturn.left)
                    hsource
            · rcases returnedNoRowBranchTransitions_source_region
                  (D := D) (rowBlockSize := rowBlockSize)
                  (state := item₁.1) (reads := item₁.2)
                  hright' with
                hrightAfter | hrightCases
              · rw [hrightAfter] at hsource
                have hlt :
                    StaticDispatcherState.afterRead D item₁.1 item₁.2 <
                      noRowReturnOffset D rowBlockSize
                        item₀.1 item₀.2 :=
                  Nat.lt_of_lt_of_le
                    (afterRead_lt_selectedRowBranchLimit
                      D item₁.2 rowBlockSize hstate₁)
                    (selectedRowBranchLimit_le_noRowReturnOffset
                      D rowBlockSize item₀.1 item₀.2)
                exact (Nat.ne_of_lt
                  (Nat.lt_of_lt_of_le hlt hleftReturn.left)).symm
                  hsource
              · rcases hrightCases with hrightScratch | hrightReturn
                · rw [hrightScratch] at hsource
                  have hscratchSelected :
                      noRowJumpScratch D item₁.1 item₁.2 <
                        selectedRowBranchLimit D rowBlockSize :=
                    Nat.lt_of_lt_of_le
                      (noRowJumpScratch_lt_noRowJumpLimit
                        D item₁.2 hstate₁)
                      (noRowJumpLimit_le_selectedRowBranchLimit
                        D rowBlockSize)
                  have hlt :
                      noRowJumpScratch D item₁.1 item₁.2 <
                        noRowReturnOffset D rowBlockSize
                          item₀.1 item₀.2 :=
                    Nat.lt_of_lt_of_le hscratchSelected
                      (selectedRowBranchLimit_le_noRowReturnOffset
                        D rowBlockSize item₀.1 item₀.2)
                  exact (Nat.ne_of_lt
                    (Nat.lt_of_lt_of_le hlt hleftReturn.left)).symm
                    hsource
                · have hindexNe :
                    rowSelectionIndex item₀.1 item₀.2 ≠
                      rowSelectionIndex item₁.1 item₁.2 := by
                    intro hindex
                    exact hne (rowSelectionIndex_eq_pair hindex)
                  rcases Nat.lt_or_gt_of_ne hindexNe with
                    hindexLt | hindexGt
                  · have hblock :
                        noRowReturnOffset D rowBlockSize
                            item₀.1 item₀.2 +
                          noRowReturnBlockSize ≤
                        noRowReturnOffset D rowBlockSize
                            item₁.1 item₁.2 :=
                      noRowReturnOffset_add_blockSize_le_of_index_lt
                        D hindexLt
                    have hltRight :
                        left.source < right.source :=
                      Nat.lt_of_lt_of_le hleftReturn.right
                        (Nat.le_trans hblock hrightReturn.left)
                    exact Nat.ne_of_lt hltRight hsource
                  · have hblock :
                        noRowReturnOffset D rowBlockSize
                            item₁.1 item₁.2 +
                          noRowReturnBlockSize ≤
                        noRowReturnOffset D rowBlockSize
                            item₀.1 item₀.2 :=
                      noRowReturnOffset_add_blockSize_le_of_index_lt
                        D hindexGt
                    have hltLeft :
                        right.source < left.source :=
                      Nat.lt_of_lt_of_le hrightReturn.right
                        (Nat.le_trans hblock hleftReturn.left)
                    exact (Nat.ne_of_lt hltLeft).symm hsource

theorem returnedNoRowAllTransitions_deterministic
    (D : Description) (rowBlockSize : Nat) :
    TransitionListDeterministic
      (returnedNoRowAllTransitions D rowBlockSize) := by
  unfold returnedNoRowAllTransitions
  apply transitionListDeterministic_flatMap
  · intro item hitem
    exact returnedNoRowItemTransitions_deterministic
      D rowBlockSize hitem
  · intro item₀ hitem₀ item₁ hitem₁ hne
    exact returnedNoRowItemTransitions_sourceDisjoint_of_ne
      D rowBlockSize hitem₀ hitem₁ hne

theorem threeHeadReaderStateLimit_le_noRowReturnLimit
    (D : Description) (rowBlockSize : Nat) :
    threeHeadReaderStateLimit D ≤
      noRowReturnLimit D rowBlockSize :=
  Nat.le_trans
    (threeHeadReaderStateLimit_le_selectedRowBranchLimit
      D rowBlockSize)
    (selectedRowBranchLimit_le_noRowReturnLimit D rowBlockSize)

theorem threeHeadReaderTransitions_returnedNoRowItemTransitions_sourceDisjoint
    (D : Description) (rowBlockSize : Nat)
    {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D) :
    TransitionSourceDisjoint
      (threeHeadReaderTransitions D)
      (returnedNoRowItemTransitions D rowBlockSize item) := by
  cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 with
  | some t =>
      simp [returnedNoRowItemTransitions, hlookup,
        TransitionSourceDisjoint]
  | none =>
      intro left right hleft hright hsource
      have hstate := noRowJumpItems_mem_state_lt hitem
      have hright' :
          right ∈ returnedNoRowBranchTransitions
            D rowBlockSize item.1 item.2 := by
        simpa [returnedNoRowItemTransitions, hlookup] using hright
      rcases returnedNoRowBranchTransitions_source_region
          (D := D) (rowBlockSize := rowBlockSize)
          (state := item.1) (reads := item.2)
          hright' with
        hrightAfter | hrightCases
      · rw [hrightAfter] at hsource
        exact
          (threeHeadReaderTransitions_sources_ne_afterRead
            D item.2 hstate left hleft) hsource
      · rcases hrightCases with hrightScratch | hrightReturn
        · have hleftLt :=
            threeHeadReaderTransitions_sources_below_stateLimit
              D left hleft
          have hrightGe :
              threeHeadReaderStateLimit D ≤ right.source := by
            rw [hrightScratch]
            exact threeHeadReaderStateLimit_le_noRowJumpScratch
              D item.1 item.2
          lia
        · have hleftLt :=
            threeHeadReaderTransitions_sources_below_stateLimit
              D left hleft
          have hrightGe :
              threeHeadReaderStateLimit D ≤ right.source :=
            Nat.le_trans
              (threeHeadReaderStateLimit_le_selectedRowBranchLimit
                D rowBlockSize)
              (Nat.le_trans
                (selectedRowBranchLimit_le_noRowReturnOffset
                  D rowBlockSize item.1 item.2)
                hrightReturn.left)
          lia

theorem threeHeadReaderTransitions_returnedNoRowAllTransitions_sourceDisjoint
    (D : Description) (rowBlockSize : Nat) :
    TransitionSourceDisjoint
      (threeHeadReaderTransitions D)
      (returnedNoRowAllTransitions D rowBlockSize) := by
  unfold returnedNoRowAllTransitions
  apply transitionSourceDisjoint_flatMap_right
  intro item hitem
  exact
    threeHeadReaderTransitions_returnedNoRowItemTransitions_sourceDisjoint
      D rowBlockSize hitem

theorem threeHeadReaderReturnedNoRowTransitions_deterministic
    (D : Description) (rowBlockSize : Nat) :
    TransitionListDeterministic
      (threeHeadReaderReturnedNoRowTransitions D rowBlockSize) := by
  simpa [threeHeadReaderReturnedNoRowTransitions] using
    transitionListDeterministic_append_of_sourceDisjoint
      (threeHeadReaderTransitions_deterministic D)
      (returnedNoRowAllTransitions_deterministic D rowBlockSize)
      (threeHeadReaderTransitions_returnedNoRowAllTransitions_sourceDisjoint
        D rowBlockSize)

theorem threeHeadReaderReturnedNoRowTransitions_wellFormed
    (D : Description) (rowBlockSize : Nat) :
    TransitionListWellFormed
      (noRowReturnLimit D rowBlockSize)
      (threeHeadReaderReturnedNoRowTransitions D rowBlockSize) := by
  simpa [threeHeadReaderReturnedNoRowTransitions] using
    transitionListWellFormed_append
      (transitionListWellFormed_mono
        (threeHeadReaderTransitions_wellFormed D)
        (threeHeadReaderStateLimit_le_noRowReturnLimit
          D rowBlockSize))
      (returnedNoRowAllTransitions_wellFormed D rowBlockSize)

theorem selectedRowItemTransitions_sources_below_branchLimit
    {D : Description}
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
    TransitionSourcesBelow
      (selectedRowBranchLimit D rowBlockSize)
      (selectedRowItemTransitions D refresh rowBlockSize item) := by
  cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 with
  | none =>
      simp [selectedRowItemTransitions, hlookup,
        TransitionSourcesBelow]
  | some t =>
      intro u hu
      have hu' :
          u ∈ selectedRowBranchTransitions
            (selectedRowBranchLimit D rowBlockSize)
            (selectedRowBranchRowOffset D rowBlockSize item.1 item.2)
            D item.1 item.2
            (selectedRowBranchScratch D item.1 item.2)
            t refresh := by
        simpa [selectedRowItemTransitions, hlookup] using hu
      rcases selectedRowBranchTransitions_source_region
          (branchStateCount := selectedRowBranchLimit D rowBlockSize)
          (offset :=
            selectedRowBranchRowOffset D rowBlockSize item.1 item.2)
          (D := D) (state := item.1) (reads := item.2)
          (scratch := selectedRowBranchScratch D item.1 item.2)
          (t := t) (refresh := refresh)
          hrows hlookup hrefresh hu' with
        hafter | hcases
      · rw [hafter]
        exact afterRead_lt_selectedRowBranchLimit
          D item.2 rowBlockSize (noRowJumpItems_mem_state_lt hitem)
      · rcases hcases with hscratch | hrow
        · rw [hscratch]
          exact selectedRowBranchScratch_lt_selectedRowBranchLimit
            D item.2 rowBlockSize (noRowJumpItems_mem_state_lt hitem)
        · have hrowLtBlock :
              u.source <
                selectedRowBranchRowOffset D rowBlockSize
                    item.1 item.2 +
                  rowBlockSize :=
            Nat.lt_of_lt_of_le hrow.right
              (Nat.add_le_add_left
                (hrowFits item hitem t hlookup)
                (selectedRowBranchRowOffset D rowBlockSize
                  item.1 item.2))
          exact Nat.lt_of_lt_of_le hrowLtBlock
            (selectedRowBranchRowOffset_add_blockSize_le_limit
              D item.2 (noRowJumpItems_mem_state_lt hitem))

theorem selectedRowAllTransitions_sources_below_branchLimit
    {D : Description}
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
    TransitionSourcesBelow
      (selectedRowBranchLimit D rowBlockSize)
      (selectedRowAllTransitions D refresh rowBlockSize) := by
  unfold selectedRowAllTransitions
  apply transitionSourcesBelow_bind
  intro item hitem
  exact selectedRowItemTransitions_sources_below_branchLimit
    hrows hrefresh rowBlockSize hrowFits hitem

theorem returnedNoRowItemTransitions_selectedRowItemTransitions_sourceDisjoint
    {D : Description}
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
    {noItem selectedItem : Nat × ReadTuple3}
    (hnoItem : noItem ∈ noRowJumpItems D)
    (hselectedItem : selectedItem ∈ noRowJumpItems D) :
    TransitionSourceDisjoint
      (returnedNoRowItemTransitions D rowBlockSize noItem)
      (selectedRowItemTransitions D refresh rowBlockSize selectedItem) := by
  cases hnoLookup :
      lookupTransitionFromReadTuple3 D noItem.1 noItem.2 with
  | some t =>
      simp [returnedNoRowItemTransitions, hnoLookup,
        TransitionSourceDisjoint]
  | none =>
      cases hselectedLookup :
          lookupTransitionFromReadTuple3 D selectedItem.1
            selectedItem.2 with
      | none =>
          simp [selectedRowItemTransitions, hselectedLookup,
            TransitionSourceDisjoint]
      | some t =>
          intro left right hleft hright hsource
          have hnoState := noRowJumpItems_mem_state_lt hnoItem
          have hright' :
              right ∈ selectedRowBranchTransitions
                (selectedRowBranchLimit D rowBlockSize)
                (selectedRowBranchRowOffset D rowBlockSize
                  selectedItem.1 selectedItem.2)
                D selectedItem.1 selectedItem.2
                (selectedRowBranchScratch D selectedItem.1
                  selectedItem.2)
                t refresh := by
            simpa [selectedRowItemTransitions, hselectedLookup] using
              hright
          have hleft' :
              left ∈ returnedNoRowBranchTransitions
                D rowBlockSize noItem.1 noItem.2 := by
            simpa [returnedNoRowItemTransitions, hnoLookup] using hleft
          rcases returnedNoRowBranchTransitions_source_region
              (D := D) (rowBlockSize := rowBlockSize)
              (state := noItem.1) (reads := noItem.2)
              hleft' with
            hleftAfter | hleftCases
          · rcases
              selectedRowBranchTransitions_source_cases
                (branchStateCount := selectedRowBranchLimit D rowBlockSize)
                (offset :=
                  selectedRowBranchRowOffset D rowBlockSize
                    selectedItem.1 selectedItem.2)
                (D := D) (state := selectedItem.1)
                (reads := selectedItem.2)
                (scratch :=
                  selectedRowBranchScratch D selectedItem.1
                    selectedItem.2)
                (t := t) (refresh := refresh)
                hrows hselectedLookup hrefresh hright' with
              hrightAfter | hrightCases
            · rw [hleftAfter, hrightAfter] at hsource
              have hpair := afterRead_eq_pair D hsource
              have hfst : noItem.1 = selectedItem.1 :=
                congrArg Prod.fst hpair
              have hsnd : noItem.2 = selectedItem.2 :=
                congrArg Prod.snd hpair
              have hselectedLookup' :
                  lookupTransitionFromReadTuple3 D noItem.1 noItem.2 =
                    some t := by
                rw [hfst, hsnd]
                exact hselectedLookup
              rw [hselectedLookup'] at hnoLookup
              contradiction
            · rcases hrightCases with hrightScratch | hrightRow
              · rw [hleftAfter, hrightScratch] at hsource
                have hlt :=
                  afterRead_lt_selectedRowBranchScratch_of_states
                    (D := D) (afterState := noItem.1)
                    (scratchState := selectedItem.1)
                    noItem.2 selectedItem.2 hnoState
                exact Nat.ne_of_lt hlt hsource
              · rw [hleftAfter] at hsource
                have hlt :=
                  afterRead_lt_selectedRowBranchRowOffset
                    (D := D) (state := selectedItem.1)
                    (afterState := noItem.1)
                    selectedItem.2 noItem.2 rowBlockSize hnoState
                have hge : selectedRowBranchRowOffset D rowBlockSize
                    selectedItem.1 selectedItem.2 ≤ right.source :=
                  hrightRow
                exact Nat.ne_of_lt
                  (Nat.lt_of_lt_of_le hlt hge) hsource
          · rcases hleftCases with hleftScratch | hleftReturn
            · rcases
                selectedRowBranchTransitions_source_cases
                  (branchStateCount := selectedRowBranchLimit D rowBlockSize)
                  (offset :=
                    selectedRowBranchRowOffset D rowBlockSize
                      selectedItem.1 selectedItem.2)
                  (D := D) (state := selectedItem.1)
                  (reads := selectedItem.2)
                  (scratch :=
                    selectedRowBranchScratch D selectedItem.1
                      selectedItem.2)
                  (t := t) (refresh := refresh)
                  hrows hselectedLookup hrefresh hright' with
                hrightAfter | hrightCases
              · rw [hleftScratch, hrightAfter] at hsource
                have hselectedState :
                    selectedItem.1 < D.stateCount :=
                  noRowJumpItems_mem_state_lt hselectedItem
                have hlt :=
                  afterRead_lt_noRowJumpScratch_of_states
                    (D := D) (afterState := selectedItem.1)
                    (scratchState := noItem.1)
                    selectedItem.2 noItem.2 hselectedState
                exact (Nat.ne_of_lt hlt).symm hsource
              · rcases hrightCases with hrightScratch | hrightRow
                · rw [hleftScratch, hrightScratch] at hsource
                  have hleftLt :
                      noRowJumpScratch D noItem.1 noItem.2 <
                        noRowJumpLimit D :=
                    noRowJumpScratch_lt_noRowJumpLimit
                      D noItem.2 hnoState
                  have hrightGe :
                      noRowJumpLimit D ≤
                        selectedRowBranchScratch D selectedItem.1
                          selectedItem.2 :=
                    noRowJumpLimit_le_selectedRowBranchScratch
                      D selectedItem.1 selectedItem.2
                  exact Nat.ne_of_lt
                    (Nat.lt_of_lt_of_le hleftLt hrightGe) hsource
                · rw [hleftScratch] at hsource
                  have hleftLt :
                      noRowJumpScratch D noItem.1 noItem.2 <
                        noRowJumpLimit D :=
                    noRowJumpScratch_lt_noRowJumpLimit
                      D noItem.2 hnoState
                  have hrowGe :
                      noRowJumpLimit D ≤
                        selectedRowBranchRowOffset D rowBlockSize
                          selectedItem.1 selectedItem.2 := by
                    exact Nat.le_trans
                      (by
                        unfold selectedRowBranchRowBase
                          selectedRowBranchScratchBase
                        exact Nat.le_add_right _ _)
                      (selectedRowBranchRowBase_le_selectedRowBranchRowOffset
                        D rowBlockSize selectedItem.1 selectedItem.2)
                  have hge : selectedRowBranchRowOffset D rowBlockSize
                      selectedItem.1 selectedItem.2 ≤ right.source :=
                    hrightRow
                  exact Nat.ne_of_lt
                    (Nat.lt_of_lt_of_le hleftLt
                      (Nat.le_trans hrowGe hge)) hsource
            · have hrightBelow :
                  right.source < selectedRowBranchLimit D rowBlockSize :=
                selectedRowItemTransitions_sources_below_branchLimit
                  hrows hrefresh rowBlockSize hrowFits
                  hselectedItem right hright
              have hleftGe :
                  selectedRowBranchLimit D rowBlockSize ≤ left.source :=
                Nat.le_trans
                  (selectedRowBranchLimit_le_noRowReturnOffset
                    D rowBlockSize noItem.1 noItem.2)
                  hleftReturn.left
              exact
                (Nat.ne_of_lt
                  (Nat.lt_of_lt_of_le hrightBelow hleftGe)).symm
                  hsource

theorem returnedNoRowAllTransitions_selectedRowAllTransitions_sourceDisjoint
    {D : Description}
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
    TransitionSourceDisjoint
      (returnedNoRowAllTransitions D rowBlockSize)
      (selectedRowAllTransitions D refresh rowBlockSize) := by
  unfold returnedNoRowAllTransitions selectedRowAllTransitions
  apply transitionSourceDisjoint_flatMap_left
  intro noItem hnoItem
  apply transitionSourceDisjoint_flatMap_right
  intro selectedItem hselectedItem
  exact
    returnedNoRowItemTransitions_selectedRowItemTransitions_sourceDisjoint
      hrows hrefresh rowBlockSize hrowFits hnoItem hselectedItem

theorem threeHeadReaderReturnedNoRowTransitions_selectedRowAllTransitions_sourceDisjoint
    {D : Description} (hrows : SupportsReadWriteRows3 D)
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
    TransitionSourceDisjoint
      (threeHeadReaderReturnedNoRowTransitions D rowBlockSize)
      (selectedRowAllTransitions D refresh rowBlockSize) := by
  simpa [threeHeadReaderReturnedNoRowTransitions] using
    transitionSourceDisjoint_append_left
      (threeHeadReaderTransitions_selectedRowAllTransitions_sourceDisjoint
        hrows hrefresh rowBlockSize)
      (returnedNoRowAllTransitions_selectedRowAllTransitions_sourceDisjoint
        hrows hrefresh rowBlockSize hrowFits)

theorem threeHeadReaderReturnedNoRowSelectedTransitions_deterministic
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
    TransitionListDeterministic
      (threeHeadReaderReturnedNoRowSelectedTransitions
        D refresh rowBlockSize) := by
  simpa [threeHeadReaderReturnedNoRowSelectedTransitions] using
    transitionListDeterministic_append_of_sourceDisjoint
      (threeHeadReaderReturnedNoRowTransitions_deterministic
        D rowBlockSize)
      (selectedRowAllTransitions_deterministic
        hDwf hrows hrefresh rowBlockSize hrowFits)
      (threeHeadReaderReturnedNoRowTransitions_selectedRowAllTransitions_sourceDisjoint
        hrows hrefresh rowBlockSize hrowFits)

theorem threeHeadReaderReturnedNoRowSelectedTransitions_wellFormed
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
      (noRowReturnLimit D rowBlockSize)
      (threeHeadReaderReturnedNoRowSelectedTransitions
        D refresh rowBlockSize) := by
  simpa [threeHeadReaderReturnedNoRowSelectedTransitions] using
    transitionListWellFormed_append
      (threeHeadReaderReturnedNoRowTransitions_wellFormed
        D rowBlockSize)
      (transitionListWellFormed_mono
        (selectedRowAllTransitions_wellFormed
          hDwf hrows hrefresh rowBlockSize hrowFits)
        (selectedRowBranchLimit_le_noRowReturnLimit
          D rowBlockSize))

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

theorem returnedNoRowBranchTransitions_sources_ne_ready
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.ready state)
      (returnedNoRowBranchTransitions D rowBlockSize state reads) := by
  intro u hu
  rcases returnedNoRowBranchTransitions_source_region
      (D := D) (rowBlockSize := rowBlockSize)
      (state := state) (reads := reads) hu with
    hafter | hcases
  · rw [hafter]
    exact (Nat.ne_of_lt (ready_lt_afterRead D reads hstate)).symm
  · rcases hcases with hscratch | hreturn
    · rw [hscratch]
      exact (Nat.ne_of_lt (ready_lt_noRowJumpScratch D reads hstate)).symm
    · have hreadyReturn :
          StaticDispatcherState.ready state < u.source :=
        Nat.lt_of_lt_of_le
          (ready_lt_noRowReturnOffset
            (D := D) (rowBlockSize := rowBlockSize)
            (state := state) (reads := reads) hstate)
          hreturn.left
      exact (Nat.ne_of_lt hreadyReturn).symm

theorem returnedNoRowAllTransitions_sources_ne_ready
    (D : Description) (rowBlockSize : Nat) {state : Nat}
    (hstate : state < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.ready state)
      (returnedNoRowAllTransitions D rowBlockSize) := by
  unfold returnedNoRowAllTransitions
  apply transitionSourcesNe_bind
  intro item _hitem
  cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 with
  | some _ =>
      simp [returnedNoRowItemTransitions, hlookup,
        TransitionSourcesNe]
  | none =>
      intro u hu
      have hreadyLt :
          StaticDispatcherState.ready state < D.stateCount := by
        simpa [StaticDispatcherState.ready] using hstate
      have hbranch :
          u ∈ returnedNoRowBranchTransitions
            D rowBlockSize item.1 item.2 := by
        simpa [returnedNoRowItemTransitions, hlookup] using hu
      rcases returnedNoRowBranchTransitions_source_region
          (D := D) (rowBlockSize := rowBlockSize)
          (state := item.1) (reads := item.2) hbranch with
        hafter | hcases
      · rw [hafter]
        have hafterGe :
            D.stateCount ≤ StaticDispatcherState.afterRead D item.1 item.2 := by
          unfold StaticDispatcherState.afterRead
          lia
        exact
          (Nat.ne_of_lt
            (Nat.lt_of_lt_of_le hreadyLt hafterGe)).symm
      · rcases hcases with hscratch | hreturn
        · rw [hscratch]
          have hscratchGe :
              D.stateCount ≤ noRowJumpScratch D item.1 item.2 := by
            exact
              Nat.le_trans (structuredStateCount_le_threeHeadReaderStateLimit D)
                (threeHeadReaderStateLimit_le_noRowJumpScratch
                  D item.1 item.2)
          exact
            (Nat.ne_of_lt
              (Nat.lt_of_lt_of_le hreadyLt hscratchGe)).symm
        · have hoffsetGe :
              D.stateCount ≤ u.source :=
            Nat.le_trans
              (Nat.le_trans (stateCount_le_noRowJumpLimit D)
                (noRowJumpLimit_le_selectedRowBranchLimit
                  D rowBlockSize))
              (Nat.le_trans
                (selectedRowBranchLimit_le_noRowReturnOffset
                  D rowBlockSize item.1 item.2)
                hreturn.left)
          exact
            (Nat.ne_of_lt
              (Nat.lt_of_lt_of_le hreadyLt hoffsetGe)).symm

theorem threeHeadReaderReturnedNoRowTransitions_sources_ne_halt
    (D : Description) (rowBlockSize : Nat)
    (hhalt : D.halt < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (threeHeadReaderReturnedNoRowTransitions D rowBlockSize) := by
  simpa [threeHeadReaderReturnedNoRowTransitions] using
    transitionSourcesNe_append
      (threeHeadReaderTransitions_sources_ne_halt D hhalt)
      (returnedNoRowAllTransitions_sources_ne_ready
        D rowBlockSize hhalt)

theorem selectedRowItemTransitions_sources_ne_ready_halt
    {D : Description}
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (rowBlockSize : Nat) (hhalt : D.halt < D.stateCount)
    {item : Nat × ReadTuple3} :
    TransitionSourcesNe
      (StaticDispatcherState.ready D.halt)
      (selectedRowItemTransitions D refresh rowBlockSize item) := by
  intro u hu
  have hreadyLt :
      StaticDispatcherState.ready D.halt < D.stateCount := by
    simpa [StaticDispatcherState.ready] using hhalt
  rcases
      selectedRowItemTransitions_source_cases
        hrows hrefresh rowBlockSize hu with
    hafter | hcases
  · rw [hafter]
    have hafterGe :
        D.stateCount ≤ StaticDispatcherState.afterRead D item.1 item.2 := by
      unfold StaticDispatcherState.afterRead
      lia
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le hreadyLt hafterGe)).symm
  · rcases hcases with hscratch | hoffset
    · rw [hscratch]
      have hscratchGe :
          D.stateCount ≤ selectedRowBranchScratch D item.1 item.2 :=
        Nat.le_trans (stateCount_le_noRowJumpLimit D)
          (noRowJumpLimit_le_selectedRowBranchScratch
            D item.1 item.2)
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le hreadyLt hscratchGe)).symm
    · have hoffsetGe :
          D.stateCount ≤ u.source :=
        Nat.le_trans
          (stateCount_le_selectedRowBranchRowOffset
            D rowBlockSize item.1 item.2)
          hoffset
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le hreadyLt hoffsetGe)).symm

theorem selectedRowAllTransitions_sources_ne_ready_halt
    {D : Description}
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (rowBlockSize : Nat) (hhalt : D.halt < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.ready D.halt)
      (selectedRowAllTransitions D refresh rowBlockSize) := by
  unfold selectedRowAllTransitions
  apply transitionSourcesNe_bind
  intro item _hitem
  exact
    selectedRowItemTransitions_sources_ne_ready_halt
      hrows hrefresh rowBlockSize hhalt

theorem threeHeadReaderReturnedNoRowSelectedTransitions_sources_ne_halt
    {D : Description}
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (rowBlockSize : Nat) (hhalt : D.halt < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.ready D.halt)
      (threeHeadReaderReturnedNoRowSelectedTransitions
        D refresh rowBlockSize) := by
  simpa [threeHeadReaderReturnedNoRowSelectedTransitions] using
    transitionSourcesNe_append
      (threeHeadReaderReturnedNoRowTransitions_sources_ne_halt
        D rowBlockSize hhalt)
      (selectedRowAllTransitions_sources_ne_ready_halt
        hrows hrefresh rowBlockSize hhalt)

theorem returnedNoRowBranchTransitions_subset_returnedNoRowAllTransitions
    (D : Description) (rowBlockSize : Nat)
    {state : Nat} (hstate : state ∈ activeStateValues D)
    {reads : ReadTuple3}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = none) :
    forall u : TransitionDescription,
      u ∈ returnedNoRowBranchTransitions D rowBlockSize state reads ->
        u ∈ returnedNoRowAllTransitions D rowBlockSize := by
  intro u hu
  unfold returnedNoRowAllTransitions
  rw [List.mem_flatMap]
  refine ⟨(state, reads), ?_, ?_⟩
  · exact noRowJumpItems_mem_of_state_mem hstate reads
  · simpa [returnedNoRowItemTransitions, hlookup] using hu

theorem returnedNoRowJumpDescription_runsFromExistingTapeSeparator
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical 2 physical) :
    RunsFromStateTapeEquiv
      (returnedNoRowJumpDescription D rowBlockSize state reads)
      (StaticDispatcherState.afterRead D state reads)
      (retargetedNoRowReturnDescription
        (noRowReturnOffset D rowBlockSize state reads)
        (StaticDispatcherState.ready state)).start
      physical
      physical := by
  have hsourceScratch :
      StaticDispatcherState.afterRead D state reads ≠
        noRowJumpScratch D state reads :=
    Nat.ne_of_lt (afterRead_lt_noRowJumpScratch D reads hstate)
  simpa [returnedNoRowJumpDescription] using
    blankHeadBounceJumpDescription_runsFromTapeSeparator
      hsourceScratch hseparator.left

theorem returnedNoRowBranchTransitions_runsFromExistingTapeSeparator
    (D : Description) {rowBlockSize state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3)
    {physical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2 physical) :
    RunsFromStateTapeEquiv
      (tableMachine (noRowReturnLimit D rowBlockSize)
        (StaticDispatcherState.afterRead D state reads)
        (StaticDispatcherState.ready state)
        (returnedNoRowBranchTransitions D rowBlockSize state reads))
      (StaticDispatcherState.afterRead D state reads)
      (StaticDispatcherState.ready state)
      physical
      (encodedGuardedStructuredTapes logical) := by
  let returnMachine :=
    retargetedNoRowReturnDescription
      (noRowReturnOffset D rowBlockSize state reads)
      (StaticDispatcherState.ready state)
  let jumpMachine :=
    returnedNoRowJumpDescription D rowBlockSize state reads
  let branchMachine :=
    tableMachine (noRowReturnLimit D rowBlockSize)
      (StaticDispatcherState.afterRead D state reads)
      (StaticDispatcherState.ready state)
      (returnedNoRowBranchTransitions D rowBlockSize state reads)
  have hdet : branchMachine.Deterministic := by
    exact
      tableMachine_deterministic_of_transitionListDeterministic
        (returnedNoRowBranchTransitions_deterministic
          D reads hstate)
  have hjumpRaw :
      RunsFromStateTapeEquiv
        jumpMachine
        (StaticDispatcherState.afterRead D state reads)
        returnMachine.start
        physical
        physical := by
    simpa [jumpMachine, returnMachine] using
      returnedNoRowJumpDescription_runsFromExistingTapeSeparator
        D reads hstate hseparator
  have hjumpBranch :
      RunsFromStateTapeEquiv branchMachine
        (StaticDispatcherState.afterRead D state reads)
        returnMachine.start
        physical
        physical := by
    exact
      runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
        (small := jumpMachine)
        (big := branchMachine)
        (hsubset := by
          intro u hu
          simpa [branchMachine, tableMachine,
            returnedNoRowBranchTransitions, jumpMachine] using Or.inl hu)
        hdet
        (by
          simpa [jumpMachine, returnMachine] using
            (returnedNoRowJumpDescription_subroutineReady
              D reads hstate).right)
        hjumpRaw
  have hreturnRaw :
      RunsFromStateTapeEquiv
        returnMachine
        returnMachine.start
        (StaticDispatcherState.ready state)
        physical
        (encodedGuardedStructuredTapes logical) := by
    simpa [returnMachine] using
      retargetedNoRowReturnDescription_runsFromTape2Separator
        (D := D) (rowBlockSize := rowBlockSize)
        (state := state) (reads := reads) hstate hlength hseparator
  have hreturnBranch :
      RunsFromStateTapeEquiv branchMachine
        returnMachine.start
        (StaticDispatcherState.ready state)
        physical
        (encodedGuardedStructuredTapes logical) := by
    exact
      runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
        (small := returnMachine)
        (big := branchMachine)
        (hsubset := by
          intro u hu
          simpa [branchMachine, tableMachine,
            returnedNoRowBranchTransitions, returnMachine] using Or.inr hu)
        hdet
        (by
          simpa [returnMachine] using
            (retargetedNoRowReturnDescription_subroutineReady
              (D := D) (rowBlockSize := rowBlockSize)
              (state := state) (reads := reads) hstate).right)
        hreturnRaw
  simpa [branchMachine] using
    runsFromStateTapeEquiv_trans hjumpBranch hreturnBranch

theorem threeHeadReaderReturnedNoRowSelectedTransitions_runsReader
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
    {state : Nat}
    (hstate : state ∈ activeStateValues D)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tableMachine (noRowReturnLimit D rowBlockSize)
            (StaticDispatcherState.ready D.start)
            (StaticDispatcherState.ready D.halt)
            (threeHeadReaderReturnedNoRowSelectedTransitions
              D refresh rowBlockSize))
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.afterRead D state
            { read0 := Tape.read (Description.tapeAt logical 0),
              read1 := Tape.read (Description.tapeAt logical 1),
              read2 := Tape.read (Description.tapeAt logical 2) })
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases threeHeadReaderDescription_runs D hstate hlength with
    ⟨separatorPhysical, hseparator, hrun⟩
  refine ⟨separatorPhysical, hseparator, ?_⟩
  exact
    runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      (small := threeHeadReaderDescription D)
      (big :=
        tableMachine (noRowReturnLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderReturnedNoRowSelectedTransitions
            D refresh rowBlockSize))
      (hsubset := by
        intro u hu
        simpa [tableMachine, threeHeadReaderDescription,
          threeHeadReaderReturnedNoRowSelectedTransitions,
          threeHeadReaderReturnedNoRowTransitions] using
          Or.inl hu)
      (hdet :=
        tableMachine_deterministic_of_transitionListDeterministic
          (threeHeadReaderReturnedNoRowSelectedTransitions_deterministic
            hDwf hrows hrefresh rowBlockSize hrowFits))
      (hfree := by
        intro u hu
        simpa [threeHeadReaderDescription] using
          threeHeadReaderTransitions_sources_ne_afterRead
            D
            { read0 := Tape.read (Description.tapeAt logical 0),
              read1 := Tape.read (Description.tapeAt logical 1),
              read2 := Tape.read (Description.tapeAt logical 2) }
            (activeStateValues_mem_lt hstate) u hu)
      hrun

theorem threeHeadReaderReturnedNoRowSelectedTransitions_runsNoRowFromExistingTapeSeparator
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
    {state : Nat} (reads : ReadTuple3)
    (hstate : state ∈ activeStateValues D)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = none)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3)
    {physical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2 physical) :
    RunsFromStateTapeEquiv
      (tableMachine (noRowReturnLimit D rowBlockSize)
        (StaticDispatcherState.ready D.start)
        (StaticDispatcherState.ready D.halt)
        (threeHeadReaderReturnedNoRowSelectedTransitions
          D refresh rowBlockSize))
      (StaticDispatcherState.afterRead D state reads)
      (StaticDispatcherState.ready state)
      physical
      (encodedGuardedStructuredTapes logical) := by
  exact
    runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      (small :=
        tableMachine (noRowReturnLimit D rowBlockSize)
          (StaticDispatcherState.afterRead D state reads)
          (StaticDispatcherState.ready state)
          (returnedNoRowBranchTransitions D rowBlockSize state reads))
      (big :=
        tableMachine (noRowReturnLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderReturnedNoRowSelectedTransitions
            D refresh rowBlockSize))
      (hsubset := by
        intro u hu
        have hbranch :
            u ∈ returnedNoRowAllTransitions D rowBlockSize :=
          returnedNoRowBranchTransitions_subset_returnedNoRowAllTransitions
            D rowBlockSize hstate hlookup u (by simpa [tableMachine] using hu)
        simpa [tableMachine,
          threeHeadReaderReturnedNoRowSelectedTransitions,
          threeHeadReaderReturnedNoRowTransitions] using
          Or.inr (Or.inl hbranch))
      (hdet :=
        tableMachine_deterministic_of_transitionListDeterministic
          (threeHeadReaderReturnedNoRowSelectedTransitions_deterministic
            hDwf hrows hrefresh rowBlockSize hrowFits))
      (hfree :=
        tableMachine_transitionFreeAt_of_sourcesNe
          (returnedNoRowBranchTransitions_sources_ne_ready
            D reads (activeStateValues_mem_lt hstate)))
      (returnedNoRowBranchTransitions_runsFromExistingTapeSeparator
        D reads (activeStateValues_mem_lt hstate) hlength hseparator)

theorem threeHeadReaderReturnedNoRowSelectedTransitions_runsSelectedFromExistingTapeSeparator
    (D : Description) (hD : D.tapeCount = 3)
    (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {state : Nat} (hstate : state ∈ activeStateValues D)
    {logical : List (Tape Bool)} {t : Transition}
    (hlength : logical.length = 3)
    (hlookup :
      lookupTransitionFromReadTuple3 D state
        (ReadTuple3.ofTapes logical) = some t)
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
    (hrowStartAtLeast :
      forall item : Nat × ReadTuple3,
        item ∈ noRowJumpItems D ->
          forall t : Transition,
            lookupTransitionFromReadTuple3 D item.1 item.2 = some t ->
              selectedRowBranchRowOffset D rowBlockSize item.1 item.2 ≤
                (retargetedSelectedRowSeparatorDescription
                  (selectedRowBranchRowOffset D rowBlockSize item.1 item.2)
                  (StaticDispatcherState.ready t.target) t refresh).start)
    (hrowStartLimit :
      forall item : Nat × ReadTuple3,
        item ∈ noRowJumpItems D ->
          forall t : Transition,
            lookupTransitionFromReadTuple3 D item.1 item.2 = some t ->
              (retargetedSelectedRowSeparatorDescription
                (selectedRowBranchRowOffset D rowBlockSize item.1 item.2)
                (StaticDispatcherState.ready t.target) t refresh).start <
                  selectedRowBranchLimit D rowBlockSize)
    {separatorPhysical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical) :
    let reads := ReadTuple3.ofTapes logical
    let c : Configuration := { state := state, tapes := logical }
    (oneStepOrSelf D c).state = t.target ∧
      RunsFromStateTapeEquiv
        (tableMachine (noRowReturnLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderReturnedNoRowSelectedTransitions
            D refresh rowBlockSize))
        (StaticDispatcherState.afterRead D state reads)
        (StaticDispatcherState.ready t.target)
        separatorPhysical
        (encodedGuardedStructuredTapes (oneStepOrSelf D c).tapes) := by
  intro reads c
  have hstateLt := activeStateValues_mem_lt hstate
  have hitem :
      (state, reads) ∈ noRowJumpItems D := by
    exact noRowJumpItems_mem_of_state_mem hstate reads
  have hlookupReads :
      lookupTransitionFromReadTuple3 D state reads = some t := by
    simpa [reads] using hlookup
  have hsourceScratch :
      StaticDispatcherState.afterRead D state reads ≠
        selectedRowBranchScratch D state reads :=
    Nat.ne_of_lt
      (afterRead_lt_selectedRowBranchScratch D reads hstateLt)
  have hsourceBelow :
      StaticDispatcherState.afterRead D state reads <
        selectedRowBranchRowOffset D rowBlockSize state reads :=
    afterRead_lt_selectedRowBranchRowOffset
      (D := D) (state := state) (afterState := state)
      reads reads rowBlockSize hstateLt
  have hscratchBelow :
      selectedRowBranchScratch D state reads <
        selectedRowBranchRowOffset D rowBlockSize state reads :=
    selectedRowBranchScratch_lt_selectedRowBranchRowOffset
      (D := D) (scratchState := state)
      reads rowBlockSize state reads hstateLt
  have hsourceLimit :
      StaticDispatcherState.afterRead D state reads <
        selectedRowBranchLimit D rowBlockSize :=
    afterRead_lt_selectedRowBranchLimit
      D reads rowBlockSize hstateLt
  have hscratchLimit :
      selectedRowBranchScratch D state reads <
        selectedRowBranchLimit D rowBlockSize :=
    selectedRowBranchScratch_lt_selectedRowBranchLimit
      D reads rowBlockSize hstateLt
  have htargetBelow :
      StaticDispatcherState.ready t.target <
        selectedRowBranchRowOffset D rowBlockSize state reads :=
    ready_target_lt_selectedRowBranchRowOffset
      hDwf hlookupReads rowBlockSize
  have hbranch :=
    selectedRowBranchTransitions_runsFromTape2Separator
      D hD hrows hlength hlookup hrefresh
      hsourceScratch
      (by simpa [reads] using hsourceBelow)
      hscratchBelow hsourceLimit hscratchLimit
      (by
        simpa [reads] using
          hrowStartAtLeast (state, reads) hitem t hlookupReads)
      (by
        simpa [reads] using
          hrowStartLimit (state, reads) hitem t hlookupReads)
      htargetBelow hseparator
  rcases hbranch with ⟨honeState, hrun⟩
  have hdet :
      (tableMachine (noRowReturnLimit D rowBlockSize)
        (StaticDispatcherState.ready D.start)
        (StaticDispatcherState.ready D.halt)
        (threeHeadReaderReturnedNoRowSelectedTransitions
          D refresh rowBlockSize)).Deterministic := by
    exact
      tableMachine_deterministic_of_transitionListDeterministic
        (threeHeadReaderReturnedNoRowSelectedTransitions_deterministic
          hDwf hrows hrefresh rowBlockSize hrowFits)
  have hfree :
      (tableMachine (selectedRowBranchLimit D rowBlockSize)
        (StaticDispatcherState.afterRead D state reads)
        (StaticDispatcherState.ready t.target)
        (selectedRowBranchTransitions
          (selectedRowBranchLimit D rowBlockSize)
          (selectedRowBranchRowOffset D rowBlockSize state reads)
          D state reads
          (selectedRowBranchScratch D state reads)
          t refresh)).TransitionFreeAt
          (StaticDispatcherState.ready t.target) := by
    exact
      tableMachine_transitionFreeAt_of_sourcesNe
        (selectedRowBranchTransitions_sources_ne_ready
          hDwf hrows hlookupReads hrefresh rowBlockSize)
  have hsubset :
      forall u : TransitionDescription,
        u ∈
          (tableMachine (selectedRowBranchLimit D rowBlockSize)
            (StaticDispatcherState.afterRead D state reads)
            (StaticDispatcherState.ready t.target)
            (selectedRowBranchTransitions
              (selectedRowBranchLimit D rowBlockSize)
              (selectedRowBranchRowOffset D rowBlockSize state reads)
              D state reads
              (selectedRowBranchScratch D state reads)
              t refresh)).transitions ->
          u ∈
            (tableMachine (noRowReturnLimit D rowBlockSize)
              (StaticDispatcherState.ready D.start)
              (StaticDispatcherState.ready D.halt)
              (threeHeadReaderReturnedNoRowSelectedTransitions
                D refresh rowBlockSize)).transitions := by
    intro u hu
    have hselected :
        u ∈ selectedRowAllTransitions D refresh rowBlockSize :=
      selectedRowBranchTransitions_subset_selectedRowAllTransitions
        D rowBlockSize hstate hlookupReads u (by simpa using hu)
    simpa [tableMachine,
      threeHeadReaderReturnedNoRowSelectedTransitions,
      threeHeadReaderReturnedNoRowTransitions] using
      Or.inr (Or.inr hselected)
  exact ⟨honeState,
    runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hfree hrun⟩

theorem staticReturnedDispatcher_noRow_runs_of_rowBlockSize
    (D : Description) (hDwf : D.WellFormed)
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
    {state : Nat}
    (hstate : state ∈ activeStateValues D)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3)
    (hlookup :
      lookupTransitionFromReadTuple3 D state (ReadTuple3.ofTapes logical) =
        none) :
    RunsFromStateTapeEquiv
      (tableMachine (noRowReturnLimit D rowBlockSize)
        (StaticDispatcherState.ready D.start)
        (StaticDispatcherState.ready D.halt)
        (threeHeadReaderReturnedNoRowSelectedTransitions
          D refresh rowBlockSize))
      (StaticDispatcherState.ready state)
      (StaticDispatcherState.ready state)
      (encodedGuardedStructuredTapes logical)
      (encodedGuardedStructuredTapes logical) := by
  rcases
      threeHeadReaderReturnedNoRowSelectedTransitions_runsReader
        hDwf hrows hrefresh rowBlockSize hrowFits hstate hlength with
    ⟨separatorPhysical, hseparator, hreader⟩
  let reads := ReadTuple3.ofTapes logical
  have hbranch :
      RunsFromStateTapeEquiv
        (tableMachine (noRowReturnLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderReturnedNoRowSelectedTransitions
            D refresh rowBlockSize))
        (StaticDispatcherState.afterRead D state reads)
        (StaticDispatcherState.ready state)
        separatorPhysical
        (encodedGuardedStructuredTapes logical) := by
    exact
      threeHeadReaderReturnedNoRowSelectedTransitions_runsNoRowFromExistingTapeSeparator
        hDwf hrows hrefresh rowBlockSize hrowFits reads hstate
        (by simpa [reads] using hlookup) hlength hseparator
  have hreader' :
      RunsFromStateTapeEquiv
        (tableMachine (noRowReturnLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderReturnedNoRowSelectedTransitions
            D refresh rowBlockSize))
        (StaticDispatcherState.ready state)
        (StaticDispatcherState.afterRead D state reads)
        (encodedGuardedStructuredTapes logical)
        separatorPhysical := by
    simpa [reads, ReadTuple3.ofTapes] using hreader
  exact runsFromStateTapeEquiv_trans hreader' hbranch

theorem staticReturnedDispatcher_noRow_runs
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
    RunsFromStateTapeEquiv
      (tableMachine
        (noRowReturnLimit D (selectedRowBlockSize D refresh))
        (StaticDispatcherState.ready D.start)
        (StaticDispatcherState.ready D.halt)
        (threeHeadReaderReturnedNoRowSelectedTransitions
          D refresh (selectedRowBlockSize D refresh)))
      (StaticDispatcherState.ready state)
      (StaticDispatcherState.ready state)
      (encodedGuardedStructuredTapes logical)
      (encodedGuardedStructuredTapes logical) := by
  exact
    staticReturnedDispatcher_noRow_runs_of_rowBlockSize
      D hDwf hrows hrefresh (selectedRowBlockSize D refresh)
      (by
        intro item hitem t hlookup
        exact selectedRowBlockSize_fits D refresh hitem hlookup)
      hstate hlength hlookup

theorem staticReturnedDispatcher_selectedRow_runs_of_rowBlockSize
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
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (rowBlockSize : Nat)
    (hrowFits :
      forall item : Nat × ReadTuple3,
        item ∈ noRowJumpItems D ->
          forall t : Transition,
            lookupTransitionFromReadTuple3 D item.1 item.2 = some t ->
              (selectedRowSeparatorDescription t refresh).stateCount ≤
                rowBlockSize) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        (oneStepOrSelf D { state := state, tapes := logical }).state =
          t.target ∧
        RunsFromStateTapeEquiv
          (tableMachine (noRowReturnLimit D rowBlockSize)
            (StaticDispatcherState.ready D.start)
            (StaticDispatcherState.ready D.halt)
            (threeHeadReaderReturnedNoRowSelectedTransitions
              D refresh rowBlockSize))
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.ready t.target)
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes
            (oneStepOrSelf D { state := state, tapes := logical }).tapes) := by
  rcases
      threeHeadReaderReturnedNoRowSelectedTransitions_runsReader
        hDwf hrows hrefresh rowBlockSize hrowFits hstate hlength with
    ⟨separatorPhysical, hseparator, hreader⟩
  let reads := ReadTuple3.ofTapes logical
  let c : Configuration := { state := state, tapes := logical }
  have hbranch :=
    threeHeadReaderReturnedNoRowSelectedTransitions_runsSelectedFromExistingTapeSeparator
      D hD hDwf hrows hstate hlength hlookup hrefresh rowBlockSize
      hrowFits
      (by
        intro item _hitem t _hlookup
        exact
          retargetedSelectedRowSeparatorDescription_start_atLeast_offset
            (selectedRowBranchRowOffset D rowBlockSize item.1 item.2)
            (StaticDispatcherState.ready t.target) t refresh)
      (by
        intro item hitem t hlookup
        exact
          selectedRowBranchRetargetedStart_lt_limit
            hrows hitem hlookup hrefresh rowBlockSize
            (hrowFits item hitem t hlookup))
      hseparator
  rcases hbranch with ⟨honeState, hbranchRun⟩
  have hreader' :
      RunsFromStateTapeEquiv
        (tableMachine (noRowReturnLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderReturnedNoRowSelectedTransitions
            D refresh rowBlockSize))
        (StaticDispatcherState.ready state)
        (StaticDispatcherState.afterRead D state reads)
        (encodedGuardedStructuredTapes logical)
        separatorPhysical := by
    simpa [reads, ReadTuple3.ofTapes] using hreader
  exact
    ⟨separatorPhysical, hseparator, by simpa [c] using honeState,
      by
        simpa [c] using
          runsFromStateTapeEquiv_trans hreader' hbranchRun⟩

theorem staticReturnedDispatcher_selectedRow_runs
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
          (tableMachine
            (noRowReturnLimit D (selectedRowBlockSize D refresh))
            (StaticDispatcherState.ready D.start)
            (StaticDispatcherState.ready D.halt)
            (threeHeadReaderReturnedNoRowSelectedTransitions
              D refresh (selectedRowBlockSize D refresh)))
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.ready t.target)
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes
            (oneStepOrSelf D { state := state, tapes := logical }).tapes) := by
  exact
    staticReturnedDispatcher_selectedRow_runs_of_rowBlockSize
      D hD hDwf hrows hstate hlength hlookup hrefresh
      (selectedRowBlockSize D refresh)
      (by
        intro item hitem t hlookup
        exact selectedRowBlockSize_fits D refresh hitem hlookup)

/-- Concrete aggregate static dispatcher table for a supplied row refresh. -/
def staticLoweredDescription
    (D : Description) (refresh : MachineDescription) :
    MachineDescription :=
  tableMachine
    (noRowReturnLimit D (selectedRowBlockSize D refresh))
    (StaticDispatcherState.ready D.start)
    (StaticDispatcherState.ready D.halt)
    (threeHeadReaderReturnedNoRowSelectedTransitions
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

theorem activeStateValues_mem_of_lt_ne_halt
    {D : Description} {state : Nat}
    (hstate : state < D.stateCount)
    (hne : state ≠ D.halt) :
    state ∈ activeStateValues D := by
  unfold activeStateValues
  rw [List.mem_filter]
  exact ⟨List.mem_range.mpr hstate, by simp [hne]⟩

theorem staticLoweredDescription_wellFormed
    (D : Description) (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    (staticLoweredDescription D refresh).WellFormed := by
  let rowBlockSize := selectedRowBlockSize D refresh
  refine ⟨?stateCount, ?start, ?halt, ?transitions, ?deterministic⟩
  · exact Nat.lt_of_lt_of_le
      (selectedRowBranchLimit_pos D hDwf rowBlockSize)
      (selectedRowBranchLimit_le_noRowReturnLimit D rowBlockSize)
  · have hready :
        StaticDispatcherState.ready D.start <
          selectedRowBranchLimit D rowBlockSize :=
      ready_lt_selectedRowBranchLimit
        (D := D) (state := D.start) (rowBlockSize := rowBlockSize)
        hDwf.right.right.left
    exact Nat.lt_of_lt_of_le hready
      (selectedRowBranchLimit_le_noRowReturnLimit D rowBlockSize)
  · have hready :
        StaticDispatcherState.ready D.halt <
          selectedRowBranchLimit D rowBlockSize :=
      ready_lt_selectedRowBranchLimit
        (D := D) (state := D.halt) (rowBlockSize := rowBlockSize)
        hDwf.right.right.right.left
    exact Nat.lt_of_lt_of_le hready
      (selectedRowBranchLimit_le_noRowReturnLimit D rowBlockSize)
  · simpa [staticLoweredDescription, rowBlockSize] using
      threeHeadReaderReturnedNoRowSelectedTransitions_wellFormed
        hDwf hrows hrefresh rowBlockSize
        (by
          intro item hitem t hlookup
          exact selectedRowBlockSize_fits D refresh hitem hlookup)
  · simpa [staticLoweredDescription, rowBlockSize,
      MachineDescription.Deterministic] using
      threeHeadReaderReturnedNoRowSelectedTransitions_deterministic
        hDwf hrows hrefresh rowBlockSize
        (by
          intro item hitem t hlookup
          exact selectedRowBlockSize_fits D refresh hitem hlookup)

theorem staticLoweredDescription_haltTransitionFree
    (D : Description) (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    (staticLoweredDescription D refresh).HaltTransitionFree := by
  let rowBlockSize := selectedRowBlockSize D refresh
  simpa [staticLoweredDescription, rowBlockSize] using
    threeHeadReaderReturnedNoRowSelectedTransitions_sources_ne_halt
      hrows hrefresh rowBlockSize hDwf.right.right.right.left

theorem staticLoweredDescription_subroutineReady
    (D : Description) (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    (staticLoweredDescription D refresh).SubroutineReady :=
  ⟨staticLoweredDescription_wellFormed D hDwf hrows hrefresh,
    staticLoweredDescription_haltTransitionFree D hDwf hrows hrefresh⟩

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
    RunsFromStateTapeEquiv
      (staticLoweredDescription D refresh)
      (StaticDispatcherState.ready state)
      (StaticDispatcherState.ready state)
      (encodedGuardedStructuredTapes logical)
      (encodedGuardedStructuredTapes logical) := by
  simpa [staticLoweredDescription] using
    staticReturnedDispatcher_noRow_runs
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
    staticReturnedDispatcher_selectedRow_runs
      D hD hDwf hrows hstate hlength hlookup hrefresh

theorem staticLoweredDescription_stepLowering
    (D : Description) (hD : D.tapeCount = 3)
    (hDwf : D.WellFormed)
    (hhaltFree : D.HaltTransitionFree)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    StaticStepLoweringWithRefresh D
      (staticLoweredDescription D refresh)
      StaticDispatcherState.ready := by
  refine ⟨staticLoweredDescription_wellFormed D hDwf hrows hrefresh, ?_⟩
  intro c hstate htapes
  cases c with
  | mk state tapes =>
      by_cases hhalt : state = D.halt
      · have hone :
            oneStepOrSelf D { state := state, tapes := tapes } =
              { state := state, tapes := tapes } := by
          exact
            oneStepOrSelf_of_stepConfig_none
              (Description.stepConfig_halt_none hhaltFree
                { state := state, tapes := tapes } hhalt)
        simpa [hone] using
          runsFromStateTapeEquiv_refl
            (staticLoweredDescription D refresh)
            (StaticDispatcherState.ready state)
            (encodedGuardedStructuredTapes tapes)
      · have hactive :
            state ∈ activeStateValues D :=
          activeStateValues_mem_of_lt_ne_halt hstate hhalt
        have hlength : tapes.length = 3 := by
          simpa [hD] using htapes
        cases hlookup :
            lookupTransitionFromReadTuple3 D state
              (ReadTuple3.ofTapes tapes) with
        | none =>
            have hone :
                oneStepOrSelf D { state := state, tapes := tapes } =
                  { state := state, tapes := tapes } :=
              oneStepOrSelf_eq_self_of_lookupTransitionFromReadTuple3_eq_none
                D hD (state := state) (logical := tapes)
                (reads := ReadTuple3.ofTapes tapes) rfl hlookup
            simpa [hone] using
              staticLoweredDescription_noRow_runs
                D hDwf hrows hrefresh hactive hlength hlookup
        | some t =>
            rcases
                staticLoweredDescription_selectedRow_runs
                  D hD hDwf hrows hactive hlength hlookup hrefresh with
              ⟨_separatorPhysical, _hseparator, honeState, hrun⟩
            simpa [honeState] using hrun

def StaticLoweredDescription
    (D : Description) (hD : D.tapeCount = 3)
    (hDwf : D.WellFormed)
    (hhaltFree : D.HaltTransitionFree)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    StaticLoweredDescriptionWithRefresh D where
  machine := staticLoweredDescription D refresh
  stateMap := StaticDispatcherState.ready
  start_eq := rfl
  halt_eq := rfl
  stepLowering :=
    staticLoweredDescription_stepLowering
      D hD hDwf hhaltFree hrows hrefresh

theorem loweredRun_simulates_structured_run
    (D : Description) (hD : D.tapeCount = 3)
    (hDwf : D.WellFormed)
    (hhaltFree : D.HaltTransitionFree)
    (hrows : SupportsReadWriteRows3 D)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      D.runConfig n (D.initial inputs) =
          { state := D.halt, tapes := tapes } ∧
        (staticLoweredDescription D refresh).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes tapes) :=
  (StaticLoweredDescription
      D hD hDwf hhaltFree hrows hrefresh).simulates_initial_haltsWithTapes
    hDwf hhalts

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
