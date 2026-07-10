import FoC.Computability.Compiler.Structured.Dispatcher.StaticMachine.NoRowReturn

set_option doc.verso true

/-!
# Static dispatcher runs

Execution proofs and final lowered static dispatcher construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace StaticDispatcherReaderAssembly

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
  simpa [retargetedNoRowReturnDescription] using!
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
          simpa [jumpMachine, returnMachine] using!
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
          simpa [returnMachine] using!
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
        D rowBlockSize hstate hlookupReads u (by simpa using! hu)
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
  · simpa [staticLoweredDescription, rowBlockSize] using!
      threeHeadReaderReturnedNoRowSelectedTransitions_wellFormed
        hDwf hrows hrefresh rowBlockSize
        (by
          intro item hitem t hlookup
          exact selectedRowBlockSize_fits D refresh hitem hlookup)
  · simpa [staticLoweredDescription, rowBlockSize,
      MachineDescription.Deterministic] using!
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
  simpa [staticLoweredDescription, rowBlockSize] using!
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
