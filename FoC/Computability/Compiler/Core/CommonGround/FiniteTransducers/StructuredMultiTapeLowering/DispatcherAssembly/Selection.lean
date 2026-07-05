import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.DispatcherAssembly.Runs

set_option doc.verso true

/-!
# Static dispatcher row selection assembly

This module starts the finite-control row-selection branch that runs after the
three-head reader has reached an {lit}`afterRead` state.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace StaticDispatcherReaderAssembly

def noRowJumpScratchBase (D : Description) : Nat :=
  threeHeadReaderStateLimit D

def noRowJumpScratch (D : Description) (state : Nat)
    (reads : ReadTuple3) : Nat :=
  noRowJumpScratchBase D + 27 * state + reads.code

def noRowJumpLimit (D : Description) : Nat :=
  noRowJumpScratchBase D + 27 * D.stateCount

def noRowJumpDescription (D : Description) (state : Nat)
    (reads : ReadTuple3) : MachineDescription :=
  blankHeadBounceJumpDescription (noRowJumpLimit D)
    (StaticDispatcherState.afterRead D state reads)
    (noRowJumpScratch D state reads)
    (StaticDispatcherState.ready state)

theorem readerStateLimit_le_threeHeadReaderStateLimit
    (D : Description) :
    StaticDispatcherState.readerStateLimit D ≤
      threeHeadReaderStateLimit D := by
  unfold threeHeadReaderStateLimit tape2ReaderLimit tape2ReaderBlockBase
    afterRead1JumpLimit afterRead1JumpScratchBase tape1ReaderLimit
    tape1ReaderBlockBase afterRead0JumpLimit afterRead0JumpScratchBase
    tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
    readyJumpScratchBase
  lia

theorem noRowJumpScratch_lt_noRowJumpLimit
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    noRowJumpScratch D state reads < noRowJumpLimit D := by
  have hcode := ReadTuple3.code_lt_twentySeven reads
  unfold noRowJumpScratch noRowJumpLimit
  lia

theorem afterRead_lt_noRowJumpScratch
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    StaticDispatcherState.afterRead D state reads <
      noRowJumpScratch D state reads := by
  have hafter :=
    StaticDispatcherState.afterRead_lt_afterRead0Base
      D reads hstate
  have hbase :
      StaticDispatcherState.afterRead0Base D ≤
        noRowJumpScratch D state reads := by
    have h0 := StaticDispatcherState.afterRead0Base_le_readerStateLimit D
    have h1 := readerStateLimit_le_threeHeadReaderStateLimit D
    have h2 :
        threeHeadReaderStateLimit D ≤
          noRowJumpScratch D state reads := by
      unfold noRowJumpScratch noRowJumpScratchBase
      lia
    exact Nat.le_trans h0 (Nat.le_trans h1 h2)
  exact Nat.lt_of_lt_of_le hafter hbase

theorem afterRead_lt_noRowJumpLimit
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    StaticDispatcherState.afterRead D state reads <
      noRowJumpLimit D :=
  Nat.lt_trans
    (afterRead_lt_noRowJumpScratch D reads hstate)
    (noRowJumpScratch_lt_noRowJumpLimit D reads hstate)

theorem ready_lt_afterRead
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    StaticDispatcherState.ready state <
      StaticDispatcherState.afterRead D state reads := by
  have hready :
      StaticDispatcherState.ready state < D.stateCount := by
    simpa [StaticDispatcherState.ready] using hstate
  have hafter :
      D.stateCount ≤
        StaticDispatcherState.afterRead D state reads := by
    unfold StaticDispatcherState.afterRead
    lia
  exact Nat.lt_of_lt_of_le hready hafter

theorem ready_lt_noRowJumpScratch
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    StaticDispatcherState.ready state <
      noRowJumpScratch D state reads :=
  Nat.lt_trans
    (ready_lt_afterRead D reads hstate)
    (afterRead_lt_noRowJumpScratch D reads hstate)

theorem ready_lt_noRowJumpLimit
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    StaticDispatcherState.ready state < noRowJumpLimit D := by
  have hlimit : D.stateCount ≤ noRowJumpLimit D := by
    unfold noRowJumpLimit noRowJumpScratchBase
    have hreader := readerStateLimit_le_threeHeadReaderStateLimit D
    have hbase :
        D.stateCount ≤ StaticDispatcherState.readerStateLimit D := by
      unfold StaticDispatcherState.readerStateLimit
        StaticDispatcherState.afterRead1Base
        StaticDispatcherState.afterRead0Base
      lia
    exact Nat.le_trans hbase (Nat.le_trans hreader (Nat.le_add_right _ _))
  exact Nat.lt_of_lt_of_le hstate hlimit

theorem noRowJumpDescription_wellFormed
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    (noRowJumpDescription D state reads).WellFormed := by
  have hsource :=
    afterRead_lt_noRowJumpLimit D reads hstate
  have hscratch :=
    noRowJumpScratch_lt_noRowJumpLimit D reads hstate
  have htarget :=
    ready_lt_noRowJumpLimit D hstate
  have hsourceScratch :
      StaticDispatcherState.afterRead D state reads ≠
        noRowJumpScratch D state reads :=
    Nat.ne_of_lt (afterRead_lt_noRowJumpScratch D reads hstate)
  simpa [noRowJumpDescription] using
    blankHeadBounceJumpDescription_wellFormed
      hsource hscratch htarget hsourceScratch

theorem noRowJumpDescription_subroutineReady
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    (noRowJumpDescription D state reads).SubroutineReady := by
  have hsource :=
    afterRead_lt_noRowJumpLimit D reads hstate
  have hscratch :=
    noRowJumpScratch_lt_noRowJumpLimit D reads hstate
  have htarget :=
    ready_lt_noRowJumpLimit D hstate
  have hsourceScratch :
      StaticDispatcherState.afterRead D state reads ≠
        noRowJumpScratch D state reads :=
    Nat.ne_of_lt (afterRead_lt_noRowJumpScratch D reads hstate)
  have htargetSource :
      StaticDispatcherState.ready state ≠
        StaticDispatcherState.afterRead D state reads :=
    Nat.ne_of_lt (ready_lt_afterRead D reads hstate)
  have htargetScratch :
      StaticDispatcherState.ready state ≠
        noRowJumpScratch D state reads :=
    Nat.ne_of_lt (ready_lt_noRowJumpScratch D reads hstate)
  simpa [noRowJumpDescription] using
    blankHeadBounceJumpDescription_subroutineReady
      hsource hscratch htarget hsourceScratch
      htargetSource htargetScratch

theorem noRowJumpDescription_runsFromTapeSeparator
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical 2 physical) :
    RunsFromStateTapeEquiv
      (noRowJumpDescription D state reads)
      (StaticDispatcherState.afterRead D state reads)
      (StaticDispatcherState.ready state)
      physical
      physical := by
  have hsourceScratch :
      StaticDispatcherState.afterRead D state reads ≠
        noRowJumpScratch D state reads :=
    Nat.ne_of_lt (afterRead_lt_noRowJumpScratch D reads hstate)
  simpa [noRowJumpDescription] using
    blankHeadBounceJumpDescription_runsFromTapeSeparator
      hsourceScratch hseparator

theorem noRowJumpDescription_runsFromExistingTapeSeparator
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical 2 physical) :
    RunsFromStateTapeEquiv
      (noRowJumpDescription D state reads)
      (StaticDispatcherState.afterRead D state reads)
      (StaticDispatcherState.ready state)
      physical
      physical :=
  noRowJumpDescription_runsFromTapeSeparator
    D reads hstate hseparator.left

theorem stepConfig_eq_none_of_lookupTransitionFromReadTuple3_eq_none
    (D : Description) (hD : D.tapeCount = 3)
    {state : Nat} {logical : List (Tape Bool)} {reads : ReadTuple3}
    (hreads : ReadTuple3.ofTapes logical = reads)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = none) :
    D.stepConfig { state := state, tapes := logical } = none := by
  let c : Configuration := { state := state, tapes := logical }
  have hlookupConfig :
      lookupTransitionFromReadTuple3 D c.state (ReadTuple3.ofConfig c) =
        none := by
    simpa [c, ReadTuple3.ofConfig, hreads] using hlookup
  have hlookupStructured :
      D.lookupTransition c = none := by
    rw [← lookupTransitionFromReadTuple3_eq_lookupTransition D hD c]
    exact hlookupConfig
  simp [Description.stepConfig, c, hlookupStructured]

theorem oneStepOrSelf_eq_self_of_lookupTransitionFromReadTuple3_eq_none
    (D : Description) (hD : D.tapeCount = 3)
    {state : Nat} {logical : List (Tape Bool)} {reads : ReadTuple3}
    (hreads : ReadTuple3.ofTapes logical = reads)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = none) :
    oneStepOrSelf D { state := state, tapes := logical } =
      { state := state, tapes := logical } := by
  exact
    oneStepOrSelf_of_stepConfig_none
      (stepConfig_eq_none_of_lookupTransitionFromReadTuple3_eq_none
        D hD hreads hlookup)

theorem readTuple3Code_injective :
    Function.Injective ReadTuple3.code := by
  intro reads₀ reads₁ hcode
  cases reads₀ with
  | mk read0₀ read1₀ read2₀ =>
      cases reads₁ with
      | mk read0₁ read1₁ read2₁ =>
          have hidx :=
            boundedRemainderIndex_eq_of_eq
              (slots := 9)
              (state₀ := ReadTuple3.readCode read2₀)
              (state₁ := ReadTuple3.readCode read2₁)
              (code₀ := ReadTuple3.code01 read0₀ read1₀)
              (code₁ := ReadTuple3.code01 read0₁ read1₁)
              (ReadTuple3.code01_lt_nine read0₀ read1₀)
              (ReadTuple3.code01_lt_nine read0₁ read1₁)
              (by
                unfold ReadTuple3.code01
                unfold ReadTuple3.code at hcode
                lia)
          have h01 := code01_injective hidx.right
          have h2 := readCode_injective hidx.left
          cases h01.left
          cases h01.right
          cases h2
          rfl

def readTuple3Values : List ReadTuple3 :=
  List.flatMap
    (fun read0 =>
      List.flatMap
        (fun read1 =>
          readOptionValues.map
            (fun read2 : Option Bool =>
              { read0 := read0, read1 := read1, read2 := read2 }))
        readOptionValues)
    readOptionValues

def noRowJumpTransitions (D : Description) (state : Nat)
    (reads : ReadTuple3) : List TransitionDescription :=
  (noRowJumpDescription D state reads).transitions

def noRowJumpItems (D : Description) : List (Nat × ReadTuple3) :=
  List.flatMap
    (fun state =>
      readTuple3Values.map (fun reads => (state, reads)))
    (activeStateValues D)

def noRowJumpItemTransitions
    (D : Description) (item : Nat × ReadTuple3) :
    List TransitionDescription :=
  if lookupTransitionFromReadTuple3 D item.1 item.2 = none then
    noRowJumpTransitions D item.1 item.2
  else
    []

def noRowJumpAllTransitions (D : Description) :
    List TransitionDescription :=
  List.flatMap (fun item => noRowJumpItemTransitions D item)
    (noRowJumpItems D)

theorem noRowJumpItems_mem_state_lt
    {D : Description} {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D) :
    item.1 < D.stateCount := by
  unfold noRowJumpItems at hitem
  rw [List.mem_flatMap] at hitem
  rcases hitem with ⟨state, hstate, hitem⟩
  rw [List.mem_map] at hitem
  rcases hitem with ⟨reads, _hreads, hitem⟩
  cases hitem
  exact activeStateValues_mem_lt hstate

theorem noRowJumpTransitions_source_cases
    (D : Description) {state : Nat} (reads : ReadTuple3)
    {t : TransitionDescription}
    (ht : t ∈ noRowJumpTransitions D state reads) :
    t.source = StaticDispatcherState.afterRead D state reads ∨
      t.source = noRowJumpScratch D state reads := by
  unfold noRowJumpTransitions noRowJumpDescription at ht
  exact blankHeadBounceJumpDescription_transition_source_cases ht

theorem noRowJumpTransitions_deterministic
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    TransitionListDeterministic
      (noRowJumpTransitions D state reads) := by
  have hsourceScratch :
      StaticDispatcherState.afterRead D state reads ≠
        noRowJumpScratch D state reads :=
    Nat.ne_of_lt (afterRead_lt_noRowJumpScratch D reads hstate)
  simpa [noRowJumpTransitions, noRowJumpDescription] using
    blankHeadBounceJumpDescription_transitionListDeterministic
      hsourceScratch

theorem afterRead_lt_noRowJumpScratch_of_states
    (D : Description) {afterState scratchState : Nat}
    (afterReads scratchReads : ReadTuple3)
    (hafterState : afterState < D.stateCount) :
    StaticDispatcherState.afterRead D afterState afterReads <
      noRowJumpScratch D scratchState scratchReads := by
  have hafter :=
    StaticDispatcherState.afterRead_lt_afterRead0Base
      D afterReads hafterState
  have hbase :
      StaticDispatcherState.afterRead0Base D ≤
        noRowJumpScratch D scratchState scratchReads := by
    have h0 := StaticDispatcherState.afterRead0Base_le_readerStateLimit D
    have h1 := readerStateLimit_le_threeHeadReaderStateLimit D
    have h2 :
        threeHeadReaderStateLimit D ≤
          noRowJumpScratch D scratchState scratchReads := by
      unfold noRowJumpScratch noRowJumpScratchBase
      lia
    exact Nat.le_trans h0 (Nat.le_trans h1 h2)
  exact Nat.lt_of_lt_of_le hafter hbase

theorem noRowJumpTransitions_sourceDisjoint_of_ne
    (D : Description) {state₀ state₁ : Nat}
    (reads₀ reads₁ : ReadTuple3)
    (hstate₀ : state₀ < D.stateCount)
    (hstate₁ : state₁ < D.stateCount)
    (hne : (state₀, reads₀) ≠ (state₁, reads₁)) :
    TransitionSourceDisjoint
      (noRowJumpTransitions D state₀ reads₀)
      (noRowJumpTransitions D state₁ reads₁) := by
  intro t u ht hu hsource
  have hpair :
      state₀ = state₁ -> reads₀ = reads₁ -> False := by
    intro hstate hreads
    exact hne (by cases hstate; cases hreads; rfl)
  have hleftCases :=
    noRowJumpTransitions_source_cases D reads₀ ht
  have hrightCases :=
    noRowJumpTransitions_source_cases D reads₁ hu
  rcases hleftCases with hleftSource | hleftScratch
  · rcases hrightCases with hrightSource | hrightScratch
    · have hinner :
          27 * state₀ + reads₀.code =
            27 * state₁ + reads₁.code := by
        rw [hleftSource, hrightSource] at hsource
        unfold StaticDispatcherState.afterRead at hsource
        lia
      have hidx :=
        boundedRemainderIndex_eq_of_eq
          (slots := 27)
          (state₀ := state₀)
          (state₁ := state₁)
          (code₀ := reads₀.code)
          (code₁ := reads₁.code)
          (ReadTuple3.code_lt_twentySeven reads₀)
          (ReadTuple3.code_lt_twentySeven reads₁)
          hinner
      exact hpair hidx.left (readTuple3Code_injective hidx.right)
    · have hlt :=
        afterRead_lt_noRowJumpScratch_of_states
          D (afterState := state₀) (scratchState := state₁)
          reads₀ reads₁ hstate₀
      rw [hleftSource, hrightScratch] at hsource
      lia
  · rcases hrightCases with hrightSource | hrightScratch
    · have hlt :=
        afterRead_lt_noRowJumpScratch_of_states
          D (afterState := state₁) (scratchState := state₀)
          reads₁ reads₀ hstate₁
      rw [hleftScratch, hrightSource] at hsource
      lia
    · have hinner :
          27 * state₀ + reads₀.code =
            27 * state₁ + reads₁.code := by
        rw [hleftScratch, hrightScratch] at hsource
        unfold noRowJumpScratch at hsource
        lia
      have hidx :=
        boundedRemainderIndex_eq_of_eq
          (slots := 27)
          (state₀ := state₀)
          (state₁ := state₁)
          (code₀ := reads₀.code)
          (code₁ := reads₁.code)
          (ReadTuple3.code_lt_twentySeven reads₀)
          (ReadTuple3.code_lt_twentySeven reads₁)
          hinner
      exact hpair hidx.left (readTuple3Code_injective hidx.right)

theorem noRowJumpItemTransitions_deterministic
    (D : Description) {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D) :
    TransitionListDeterministic
      (noRowJumpItemTransitions D item) := by
  by_cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 = none
  · simpa [noRowJumpItemTransitions, hlookup] using
      noRowJumpTransitions_deterministic
        D item.2 (noRowJumpItems_mem_state_lt hitem)
  · simp [noRowJumpItemTransitions, hlookup, TransitionListDeterministic]

theorem noRowJumpItemTransitions_sourceDisjoint_of_ne
    (D : Description) {item₀ item₁ : Nat × ReadTuple3}
    (hitem₀ : item₀ ∈ noRowJumpItems D)
    (hitem₁ : item₁ ∈ noRowJumpItems D)
    (hne : item₀ ≠ item₁) :
    TransitionSourceDisjoint
      (noRowJumpItemTransitions D item₀)
      (noRowJumpItemTransitions D item₁) := by
  by_cases hlookup₀ :
      lookupTransitionFromReadTuple3 D item₀.1 item₀.2 = none
  · by_cases hlookup₁ :
        lookupTransitionFromReadTuple3 D item₁.1 item₁.2 = none
    · simpa [noRowJumpItemTransitions, hlookup₀, hlookup₁] using
        noRowJumpTransitions_sourceDisjoint_of_ne
          D item₀.2 item₁.2
          (noRowJumpItems_mem_state_lt hitem₀)
          (noRowJumpItems_mem_state_lt hitem₁)
          hne
    · simp [noRowJumpItemTransitions, hlookup₀, hlookup₁,
        TransitionSourceDisjoint]
  · simp [noRowJumpItemTransitions, hlookup₀, TransitionSourceDisjoint]

theorem noRowJumpAllTransitions_deterministic
    (D : Description) :
    TransitionListDeterministic (noRowJumpAllTransitions D) := by
  unfold noRowJumpAllTransitions
  apply transitionListDeterministic_flatMap
  · intro item hitem
    exact noRowJumpItemTransitions_deterministic D hitem
  · intro item₀ hitem₀ item₁ hitem₁ hne
    exact
      noRowJumpItemTransitions_sourceDisjoint_of_ne
        D hitem₀ hitem₁ hne

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
