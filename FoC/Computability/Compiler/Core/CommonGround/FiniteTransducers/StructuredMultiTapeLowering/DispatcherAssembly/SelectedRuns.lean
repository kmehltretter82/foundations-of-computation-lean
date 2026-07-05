import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.DispatcherAssembly.Selection

set_option doc.verso true

/-!
# Static dispatcher selected-row aggregate runs

This module lifts the selected-row branch execution from a single concrete
branch table into the aggregate reader/no-row/selected-row table.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace StaticDispatcherReaderAssembly

theorem readTuple3Values_mem (reads : ReadTuple3) :
    reads ∈ readTuple3Values := by
  cases reads with
  | mk read0 read1 read2 =>
      cases read0 with
      | none =>
          cases read1 with
          | none =>
              cases read2 with
              | none => simp [readTuple3Values, readOptionValues]
              | some bit => cases bit <;> simp [readTuple3Values, readOptionValues]
          | some bit1 =>
              cases bit1 <;>
                cases read2 with
                | none => simp [readTuple3Values, readOptionValues]
                | some bit2 =>
                    cases bit2 <;> simp [readTuple3Values, readOptionValues]
      | some bit0 =>
          cases bit0 <;>
            cases read1 with
            | none =>
                cases read2 with
                | none => simp [readTuple3Values, readOptionValues]
                | some bit2 =>
                    cases bit2 <;> simp [readTuple3Values, readOptionValues]
            | some bit1 =>
                cases bit1 <;>
                  cases read2 with
                  | none => simp [readTuple3Values, readOptionValues]
                  | some bit2 =>
                      cases bit2 <;> simp [readTuple3Values, readOptionValues]

theorem noRowJumpItems_mem_of_state_mem
    {D : Description} {state : Nat} (hstate : state ∈ activeStateValues D)
    (reads : ReadTuple3) :
    (state, reads) ∈ noRowJumpItems D := by
  unfold noRowJumpItems
  rw [List.mem_flatMap]
  refine ⟨state, hstate, ?_⟩
  rw [List.mem_map]
  exact ⟨reads, readTuple3Values_mem reads, rfl⟩

theorem selectedRowBranchTransitions_subset_selectedRowAllTransitions
    (D : Description) {state : Nat} {reads : ReadTuple3}
    {t : Transition} {refresh : MachineDescription}
    (rowBlockSize : Nat)
    (hstate : state ∈ activeStateValues D)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t) :
    forall u : TransitionDescription,
      u ∈
        selectedRowBranchTransitions
          (selectedRowBranchLimit D rowBlockSize)
          (selectedRowBranchRowOffset D rowBlockSize state reads)
          D state reads
          (selectedRowBranchScratch D state reads)
          t refresh ->
        u ∈ selectedRowAllTransitions D refresh rowBlockSize := by
  intro u hu
  unfold selectedRowAllTransitions
  rw [List.mem_flatMap]
  refine ⟨(state, reads), ?_, ?_⟩
  · exact noRowJumpItems_mem_of_state_mem hstate reads
  · simpa [selectedRowItemTransitions, hlookup] using hu

theorem selectedRowBranchTransitions_sources_ne_ready
    {D : Description} (hDwf : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (rowBlockSize : Nat) :
    TransitionSourcesNe
      (StaticDispatcherState.ready t.target)
      (selectedRowBranchTransitions
        (selectedRowBranchLimit D rowBlockSize)
        (selectedRowBranchRowOffset D rowBlockSize state reads)
        D state reads
        (selectedRowBranchScratch D state reads)
        t refresh) := by
  intro u hu
  have htargetBelow :
      StaticDispatcherState.ready t.target <
        selectedRowBranchRowOffset D rowBlockSize state reads :=
    ready_target_lt_selectedRowBranchRowOffset
      hDwf hlookup rowBlockSize
  have htargetState :
      StaticDispatcherState.ready t.target < D.stateCount := by
    have htarget :=
      lookupTransitionFromReadTuple3_target_lt_stateCount
        hDwf hlookup
    simpa [StaticDispatcherState.ready] using htarget
  rcases
      selectedRowBranchTransitions_source_cases
        (branchStateCount := selectedRowBranchLimit D rowBlockSize)
        (offset := selectedRowBranchRowOffset D rowBlockSize state reads)
        (D := D) (state := state) (reads := reads)
        (scratch := selectedRowBranchScratch D state reads)
        (t := t) (refresh := refresh)
        hrows hlookup hrefresh hu with
    hsource | hcases
  · rw [hsource]
    have hafterGe :
        D.stateCount ≤ StaticDispatcherState.afterRead D state reads := by
      unfold StaticDispatcherState.afterRead
      lia
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le htargetState hafterGe)).symm
  · rcases hcases with hscratch | hoffset
    · rw [hscratch]
      have hscratchGe :
          D.stateCount ≤ selectedRowBranchScratch D state reads :=
        Nat.le_trans (stateCount_le_noRowJumpLimit D)
          (noRowJumpLimit_le_selectedRowBranchScratch D state reads)
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetState hscratchGe)).symm
    · exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetBelow hoffset)).symm

theorem afterRead_lt_selectedRowBranchLimit
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (rowBlockSize : Nat) (hstate : state < D.stateCount) :
    StaticDispatcherState.afterRead D state reads <
      selectedRowBranchLimit D rowBlockSize := by
  exact Nat.lt_of_lt_of_le
    (afterRead_lt_selectedRowBranchRowBase D reads hstate)
    (by
      unfold selectedRowBranchLimit
      exact Nat.le_add_right _ _)

theorem selectedRowBranchScratch_lt_selectedRowBranchLimit
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (rowBlockSize : Nat) (hstate : state < D.stateCount) :
    selectedRowBranchScratch D state reads <
      selectedRowBranchLimit D rowBlockSize := by
  exact Nat.lt_of_lt_of_le
    (selectedRowBranchScratch_lt_selectedRowBranchRowBase
      D reads hstate)
    (by
      unfold selectedRowBranchLimit
      exact Nat.le_add_right _ _)

theorem threeHeadReaderNoRowSelectedTransitions_runsSelectedFromExistingTapeSeparator
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
        (tableMachine (selectedRowBranchLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderNoRowSelectedTransitions
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
      (tableMachine (selectedRowBranchLimit D rowBlockSize)
        (StaticDispatcherState.ready D.start)
        (StaticDispatcherState.ready D.halt)
        (threeHeadReaderNoRowSelectedTransitions
          D refresh rowBlockSize)).Deterministic := by
    exact
      tableMachine_deterministic_of_transitionListDeterministic
        (threeHeadReaderNoRowSelectedTransitions_deterministic
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
            (tableMachine (selectedRowBranchLimit D rowBlockSize)
              (StaticDispatcherState.ready D.start)
              (StaticDispatcherState.ready D.halt)
              (threeHeadReaderNoRowSelectedTransitions
                D refresh rowBlockSize)).transitions := by
    intro u hu
    simpa [tableMachine, threeHeadReaderNoRowSelectedTransitions] using
      Or.inr
        (selectedRowBranchTransitions_subset_selectedRowAllTransitions
          D rowBlockSize hstate hlookupReads u (by simpa using hu))
  exact ⟨honeState,
    runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hfree hrun⟩

theorem threeHeadReaderNoRowSelectedTransitions_runsReader
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
          (tableMachine (selectedRowBranchLimit D rowBlockSize)
            (StaticDispatcherState.ready D.start)
            (StaticDispatcherState.ready D.halt)
            (threeHeadReaderNoRowSelectedTransitions
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
        tableMachine (selectedRowBranchLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderNoRowSelectedTransitions
            D refresh rowBlockSize))
      (hsubset := by
        intro u hu
        simpa [tableMachine, threeHeadReaderDescription,
          threeHeadReaderNoRowSelectedTransitions,
          threeHeadReaderNoRowTransitions] using Or.inl hu)
      (hdet :=
        tableMachine_deterministic_of_transitionListDeterministic
          (threeHeadReaderNoRowSelectedTransitions_deterministic
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

theorem staticDispatcher_selectedRow_runs
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
                  selectedRowBranchLimit D rowBlockSize) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        (oneStepOrSelf D { state := state, tapes := logical }).state =
          t.target ∧
        RunsFromStateTapeEquiv
          (tableMachine (selectedRowBranchLimit D rowBlockSize)
            (StaticDispatcherState.ready D.start)
            (StaticDispatcherState.ready D.halt)
            (threeHeadReaderNoRowSelectedTransitions
              D refresh rowBlockSize))
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.ready t.target)
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes
            (oneStepOrSelf D { state := state, tapes := logical }).tapes) := by
  rcases
      threeHeadReaderNoRowSelectedTransitions_runsReader
        hDwf hrows hrefresh rowBlockSize hrowFits hstate hlength with
    ⟨separatorPhysical, hseparator, hreader⟩
  let reads := ReadTuple3.ofTapes logical
  let c : Configuration := { state := state, tapes := logical }
  have hbranch :=
    threeHeadReaderNoRowSelectedTransitions_runsSelectedFromExistingTapeSeparator
      D hD hDwf hrows hstate hlength hlookup hrefresh rowBlockSize
      hrowFits hrowStartAtLeast hrowStartLimit hseparator
  rcases hbranch with ⟨honeState, hbranchRun⟩
  have hreader' :
      RunsFromStateTapeEquiv
        (tableMachine (selectedRowBranchLimit D rowBlockSize)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderNoRowSelectedTransitions
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

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
