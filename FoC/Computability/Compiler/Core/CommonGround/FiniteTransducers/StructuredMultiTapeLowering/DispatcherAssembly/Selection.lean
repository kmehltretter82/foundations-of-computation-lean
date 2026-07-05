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

theorem readyJumpTape0ReaderTransitions_sources_ne_afterRead
    (D : Description) {readerState targetState : Nat}
    (reads : ReadTuple3)
    (hreader : readerState < D.stateCount)
    (htarget : targetState < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.afterRead D targetState reads)
      (readyJumpTape0ReaderTransitions D readerState) := by
  intro t ht
  rcases readyJumpTape0ReaderTransitions_source_cases D ht with
    hsource | hcases
  · rw [hsource]
    have hreadyLt :
        StaticDispatcherState.ready readerState < D.stateCount := by
      simpa [StaticDispatcherState.ready] using hreader
    have hafterGe :
        D.stateCount ≤
          StaticDispatcherState.afterRead D targetState reads := by
      unfold StaticDispatcherState.afterRead
      lia
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hreadyLt hafterGe)
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      have htargetLt :
          StaticDispatcherState.afterRead D targetState reads <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead_lt_afterRead0Base
            D reads htarget)
          (StaticDispatcherState.afterRead0Base_le_readerStateLimit D)
      have hscratchGe :
          StaticDispatcherState.readerStateLimit D ≤
            readyJumpScratch D readerState := by
        unfold readyJumpScratch readyJumpScratchBase
        exact Nat.le_add_right _ _
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hscratchGe)).symm
    · have htargetLt :
          StaticDispatcherState.afterRead D targetState reads <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead_lt_afterRead0Base
            D reads htarget)
          (StaticDispatcherState.afterRead0Base_le_readerStateLimit D)
      have hreaderGe :
          StaticDispatcherState.readerStateLimit D ≤ t.source :=
        Nat.le_trans
          (readerStateLimit_le_tape0ReaderOffset D readerState)
          hreader.left
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hreaderGe)).symm

theorem afterRead0JumpTape1ReaderTransitions_sources_ne_afterRead
    (D : Description) {readerState targetState : Nat}
    (read0 : Option Bool) (reads : ReadTuple3)
    (htarget : targetState < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.afterRead D targetState reads)
      (afterRead0JumpTape1ReaderTransitions D readerState read0) := by
  intro t ht
  rcases afterRead0JumpTape1ReaderTransitions_source_cases
      D read0 ht with
    hsource | hcases
  · rw [hsource]
    have htargetLt :
        StaticDispatcherState.afterRead D targetState reads <
          StaticDispatcherState.afterRead0Base D :=
      StaticDispatcherState.afterRead_lt_afterRead0Base
        D reads htarget
    have hsourceGe :
        StaticDispatcherState.afterRead0Base D ≤
          StaticDispatcherState.afterRead0 D readerState read0 :=
      StaticDispatcherState.afterRead0Base_le_afterRead0
        D readerState read0
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le htargetLt hsourceGe)).symm
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      have htargetLt :
          StaticDispatcherState.afterRead D targetState reads <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead_lt_afterRead0Base
            D reads htarget)
          (StaticDispatcherState.afterRead0Base_le_readerStateLimit D)
      have hscratchGe :
          StaticDispatcherState.readerStateLimit D ≤
            afterRead0JumpScratch D readerState read0 := by
        unfold afterRead0JumpScratch afterRead0JumpScratchBase
          tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
          readyJumpScratchBase
        lia
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hscratchGe)).symm
    · have htargetLt :
          StaticDispatcherState.afterRead D targetState reads <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead_lt_afterRead0Base
            D reads htarget)
          (StaticDispatcherState.afterRead0Base_le_readerStateLimit D)
      have hreaderGe :
          StaticDispatcherState.readerStateLimit D ≤ t.source :=
        Nat.le_trans
          (readerStateLimit_le_tape1ReaderOffset D readerState read0)
          hreader.left
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hreaderGe)).symm

theorem afterRead1JumpTape2ReaderTransitions_sources_ne_afterRead_any
    (D : Description) {readerState targetState : Nat}
    (read0 read1 : Option Bool) (reads : ReadTuple3)
    (htarget : targetState < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.afterRead D targetState reads)
      (afterRead1JumpTape2ReaderTransitions D readerState read0 read1) := by
  intro t ht
  rcases afterRead1JumpTape2ReaderTransitions_source_cases
      D read0 read1 ht with
    hsource | hcases
  · rw [hsource]
    have htargetLt :
        StaticDispatcherState.afterRead D targetState reads <
          StaticDispatcherState.afterRead0Base D :=
      StaticDispatcherState.afterRead_lt_afterRead0Base
        D reads htarget
    have hbaseLe :
        StaticDispatcherState.afterRead0Base D ≤
          StaticDispatcherState.afterRead1Base D := by
      unfold StaticDispatcherState.afterRead1Base
      lia
    have hsourceGe :
        StaticDispatcherState.afterRead1Base D ≤
          StaticDispatcherState.afterRead1 D readerState read0 read1 :=
      StaticDispatcherState.afterRead1Base_le_afterRead1
        D readerState read0 read1
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le htargetLt
          (Nat.le_trans hbaseLe hsourceGe))).symm
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      have htargetLt :
          StaticDispatcherState.afterRead D targetState reads <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead_lt_afterRead0Base
            D reads htarget)
          (StaticDispatcherState.afterRead0Base_le_readerStateLimit D)
      have hscratchGe :
          StaticDispatcherState.readerStateLimit D ≤
            afterRead1JumpScratch D readerState read0 read1 := by
        unfold afterRead1JumpScratch afterRead1JumpScratchBase
          tape1ReaderLimit tape1ReaderBlockBase afterRead0JumpLimit
          afterRead0JumpScratchBase tape0ReaderLimit
          tape0ReaderBlockBase readyJumpLimit readyJumpScratchBase
        lia
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hscratchGe)).symm
    · have htargetLt :
          StaticDispatcherState.afterRead D targetState reads <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead_lt_afterRead0Base
            D reads htarget)
          (StaticDispatcherState.afterRead0Base_le_readerStateLimit D)
      have hreaderGe :
          StaticDispatcherState.readerStateLimit D ≤ t.source :=
        Nat.le_trans
          (readerStateLimit_le_tape2ReaderOffset
            D readerState read0 read1)
          hreader.left
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hreaderGe)).symm

theorem threeHeadReaderTransitions_sources_ne_afterRead
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.afterRead D state reads)
      (threeHeadReaderTransitions D) := by
  simpa [threeHeadReaderTransitions] using
    transitionSourcesNe_append
      (transitionSourcesNe_append
        (by
          unfold readyJumpTape0ReaderAllTransitions
          apply transitionSourcesNe_bind
          intro readerState hreaderState
          exact
            readyJumpTape0ReaderTransitions_sources_ne_afterRead
              D reads (activeStateValues_mem_lt hreaderState) hstate)
        (by
          unfold afterRead0JumpTape1ReaderAllTransitions
          apply transitionSourcesNe_bind
          intro read0 _hread0
          apply transitionSourcesNe_bind
          intro readerState _hreaderState
          exact
            afterRead0JumpTape1ReaderTransitions_sources_ne_afterRead
              D read0 reads hstate))
      (by
        unfold afterRead1JumpTape2ReaderAllTransitions
        apply transitionSourcesNe_bind
        intro read0 _hread0
        apply transitionSourcesNe_bind
        intro read1 _hread1
        apply transitionSourcesNe_bind
        intro readerState _hreaderState
        exact
          afterRead1JumpTape2ReaderTransitions_sources_ne_afterRead_any
            D read0 read1 reads hstate)

theorem threeHeadReaderStateLimit_le_noRowJumpScratch
    (D : Description) (state : Nat) (reads : ReadTuple3) :
    threeHeadReaderStateLimit D ≤ noRowJumpScratch D state reads := by
  unfold noRowJumpScratch noRowJumpScratchBase
  lia

theorem noRowJumpItemTransitions_source_cases
    (D : Description) {item : Nat × ReadTuple3}
    {t : TransitionDescription}
    (ht : t ∈ noRowJumpItemTransitions D item) :
    t.source = StaticDispatcherState.afterRead D item.1 item.2 ∨
      t.source = noRowJumpScratch D item.1 item.2 := by
  by_cases hlookup :
      lookupTransitionFromReadTuple3 D item.1 item.2 = none
  · have ht' : t ∈ noRowJumpTransitions D item.1 item.2 := by
      simpa [noRowJumpItemTransitions, hlookup] using ht
    exact noRowJumpTransitions_source_cases D item.2 ht'
  · simp [noRowJumpItemTransitions, hlookup] at ht

theorem threeHeadReaderTransitions_noRowJumpItemTransitions_sourceDisjoint
    (D : Description) {item : Nat × ReadTuple3}
    (hitem : item ∈ noRowJumpItems D) :
    TransitionSourceDisjoint
      (threeHeadReaderTransitions D)
      (noRowJumpItemTransitions D item) := by
  intro t u ht hu hsource
  rcases noRowJumpItemTransitions_source_cases D hu with
    hrightSource | hrightScratch
  · rw [hrightSource] at hsource
    exact
      (threeHeadReaderTransitions_sources_ne_afterRead
        D item.2 (noRowJumpItems_mem_state_lt hitem) t ht)
        hsource
  · have hleftLt :=
      threeHeadReaderTransitions_sources_below_stateLimit D t ht
    have hrightGe :
        threeHeadReaderStateLimit D ≤ u.source := by
      rw [hrightScratch]
      exact threeHeadReaderStateLimit_le_noRowJumpScratch
        D item.1 item.2
    lia

theorem threeHeadReaderTransitions_noRowJumpAllTransitions_sourceDisjoint
    (D : Description) :
    TransitionSourceDisjoint
      (threeHeadReaderTransitions D)
      (noRowJumpAllTransitions D) := by
  unfold noRowJumpAllTransitions
  apply transitionSourceDisjoint_flatMap_right
  intro item hitem
  exact
    threeHeadReaderTransitions_noRowJumpItemTransitions_sourceDisjoint
      D hitem

def threeHeadReaderNoRowTransitions (D : Description) :
    List TransitionDescription :=
  threeHeadReaderTransitions D ++ noRowJumpAllTransitions D

theorem threeHeadReaderNoRowTransitions_deterministic
    (D : Description) :
    TransitionListDeterministic
      (threeHeadReaderNoRowTransitions D) := by
  simpa [threeHeadReaderNoRowTransitions] using
    transitionListDeterministic_append_of_sourceDisjoint
      (threeHeadReaderTransitions_deterministic D)
      (noRowJumpAllTransitions_deterministic D)
      (threeHeadReaderTransitions_noRowJumpAllTransitions_sourceDisjoint D)

theorem tableMachine_deterministic_of_transitionListDeterministic
    {stateCount start halt : Nat}
    {transitions : List TransitionDescription}
    (hdet : TransitionListDeterministic transitions) :
    (tableMachine stateCount start halt transitions).Deterministic := by
  simpa [tableMachine, MachineDescription.Deterministic] using hdet

theorem noRowJumpTransitions_subset_noRowJumpAllTransitions
    (D : Description) {state : Nat} {reads : ReadTuple3}
    (hstate : state ∈ activeStateValues D)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = none) :
    forall t : TransitionDescription,
      t ∈ noRowJumpTransitions D state reads ->
        t ∈ noRowJumpAllTransitions D := by
  intro t ht
  unfold noRowJumpAllTransitions noRowJumpItems
  rw [List.mem_flatMap]
  refine ⟨(state, reads), ?_, ?_⟩
  · rw [List.mem_flatMap]
    refine ⟨state, hstate, ?_⟩
    rw [List.mem_map]
    refine ⟨reads, ?_, rfl⟩
    -- The no-row item table ranges over all 27 read tuples; every concrete
    -- tuple is one of those finite values by case analysis.
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
  · simpa [noRowJumpItemTransitions, hlookup] using ht

theorem noRowJumpTransitions_sources_ne_ready
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.ready state)
      (noRowJumpTransitions D state reads) := by
  intro t ht
  rcases noRowJumpTransitions_source_cases D reads ht with
    hsource | hscratch
  · rw [hsource]
    exact
      (Nat.ne_of_lt (ready_lt_afterRead D reads hstate)).symm
  · rw [hscratch]
    exact
      (Nat.ne_of_lt (ready_lt_noRowJumpScratch D reads hstate)).symm

theorem noRowJumpItemTransitions_sources_ne_ready
    (D : Description) {targetState : Nat} {item : Nat × ReadTuple3}
    (htarget : targetState < D.stateCount)
    (_hitem : item ∈ noRowJumpItems D) :
    TransitionSourcesNe
      (StaticDispatcherState.ready targetState)
      (noRowJumpItemTransitions D item) := by
  intro t ht
  rcases noRowJumpItemTransitions_source_cases D ht with
    hsource | hscratch
  · rw [hsource]
    have hreadyLt :
        StaticDispatcherState.ready targetState < D.stateCount := by
      simpa [StaticDispatcherState.ready] using htarget
    have hsourceGe :
        D.stateCount ≤
          StaticDispatcherState.afterRead D item.1 item.2 := by
      unfold StaticDispatcherState.afterRead
      lia
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le hreadyLt hsourceGe)).symm
  · rw [hscratch]
    have hreadyLt :
        StaticDispatcherState.ready targetState < D.stateCount := by
      simpa [StaticDispatcherState.ready] using htarget
    have hscratchGe :
        D.stateCount ≤ noRowJumpScratch D item.1 item.2 := by
      have hbase : D.stateCount ≤ threeHeadReaderStateLimit D := by
        exact structuredStateCount_le_threeHeadReaderStateLimit D
      have hscratchBase :
          threeHeadReaderStateLimit D ≤ noRowJumpScratch D item.1 item.2 :=
        threeHeadReaderStateLimit_le_noRowJumpScratch D item.1 item.2
      exact Nat.le_trans hbase hscratchBase
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le hreadyLt hscratchGe)).symm

theorem noRowJumpAllTransitions_sources_ne_ready
    (D : Description) {targetState : Nat}
    (htarget : targetState < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.ready targetState)
      (noRowJumpAllTransitions D) := by
  unfold noRowJumpAllTransitions
  apply transitionSourcesNe_bind
  intro item hitem
  exact noRowJumpItemTransitions_sources_ne_ready
    D htarget hitem

theorem noRowJumpAllTransitions_runsFromExistingTapeSeparator
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state ∈ activeStateValues D)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = none)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical 2 physical) :
    RunsFromStateTapeEquiv
      (tableMachine (noRowJumpLimit D)
        (StaticDispatcherState.afterRead D state reads)
        (StaticDispatcherState.ready state)
        (noRowJumpAllTransitions D))
      (StaticDispatcherState.afterRead D state reads)
      (StaticDispatcherState.ready state)
      physical
      physical := by
  exact
    runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      (small :=
        tableMachine (noRowJumpLimit D)
          (StaticDispatcherState.afterRead D state reads)
          (StaticDispatcherState.ready state)
          (noRowJumpTransitions D state reads))
      (big :=
        tableMachine (noRowJumpLimit D)
          (StaticDispatcherState.afterRead D state reads)
          (StaticDispatcherState.ready state)
          (noRowJumpAllTransitions D))
      (hsubset := by
        intro t ht
        simpa [tableMachine] using
          noRowJumpTransitions_subset_noRowJumpAllTransitions
            D hstate hlookup t ht)
      (hdet :=
        tableMachine_deterministic_of_transitionListDeterministic
          (noRowJumpAllTransitions_deterministic D))
      (hfree :=
        tableMachine_transitionFreeAt_of_sourcesNe
          (noRowJumpTransitions_sources_ne_ready
            D reads (activeStateValues_mem_lt hstate)))
      (by
        simpa [tableMachine, noRowJumpTransitions] using
          noRowJumpDescription_runsFromExistingTapeSeparator
            D reads (activeStateValues_mem_lt hstate) hseparator)

theorem threeHeadReaderNoRowTransitions_runsNoRowFromExistingTapeSeparator
    (D : Description) {state : Nat} (reads : ReadTuple3)
    (hstate : state ∈ activeStateValues D)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = none)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical 2 physical) :
    RunsFromStateTapeEquiv
      (tableMachine (noRowJumpLimit D)
        (StaticDispatcherState.ready D.start)
        (StaticDispatcherState.ready D.halt)
        (threeHeadReaderNoRowTransitions D))
      (StaticDispatcherState.afterRead D state reads)
      (StaticDispatcherState.ready state)
      physical
      physical := by
  exact
    runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      (small :=
        tableMachine (noRowJumpLimit D)
          (StaticDispatcherState.afterRead D state reads)
          (StaticDispatcherState.ready state)
          (noRowJumpAllTransitions D))
      (big :=
        tableMachine (noRowJumpLimit D)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderNoRowTransitions D))
      (hsubset := by
        intro t ht
        simp [tableMachine, threeHeadReaderNoRowTransitions,
          noRowJumpAllTransitions] at ht ⊢
        exact Or.inr ht)
      (hdet :=
        tableMachine_deterministic_of_transitionListDeterministic
          (threeHeadReaderNoRowTransitions_deterministic D))
      (hfree :=
        tableMachine_transitionFreeAt_of_sourcesNe
          (noRowJumpAllTransitions_sources_ne_ready
            D (activeStateValues_mem_lt hstate)))
      (noRowJumpAllTransitions_runsFromExistingTapeSeparator
        D reads hstate hlookup hseparator)

theorem threeHeadReaderTransitions_subset_threeHeadReaderNoRowTransitions
    (D : Description) :
    forall t : TransitionDescription,
      t ∈ threeHeadReaderTransitions D ->
        t ∈ threeHeadReaderNoRowTransitions D := by
  intro t ht
  simpa [threeHeadReaderNoRowTransitions] using Or.inl ht

theorem threeHeadReaderNoRowTransitions_runsReader
    (D : Description) {state : Nat}
    (hstate : state ∈ activeStateValues D)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tableMachine (noRowJumpLimit D)
            (StaticDispatcherState.ready D.start)
            (StaticDispatcherState.ready D.halt)
            (threeHeadReaderNoRowTransitions D))
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
        tableMachine (noRowJumpLimit D)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderNoRowTransitions D))
      (hsubset := by
        intro t ht
        simpa [tableMachine, threeHeadReaderDescription] using
          threeHeadReaderTransitions_subset_threeHeadReaderNoRowTransitions
            D t ht)
      (hdet :=
        tableMachine_deterministic_of_transitionListDeterministic
          (threeHeadReaderNoRowTransitions_deterministic D))
      (hfree := by
        intro t ht
        simpa [threeHeadReaderDescription] using
          threeHeadReaderTransitions_sources_ne_afterRead
            D
            { read0 := Tape.read (Description.tapeAt logical 0),
              read1 := Tape.read (Description.tapeAt logical 1),
              read2 := Tape.read (Description.tapeAt logical 2) }
            (activeStateValues_mem_lt hstate) t ht)
      hrun

theorem staticDispatcher_noRow_runs
    (D : Description) {state : Nat}
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
          (tableMachine (noRowJumpLimit D)
            (StaticDispatcherState.ready D.start)
            (StaticDispatcherState.ready D.halt)
            (threeHeadReaderNoRowTransitions D))
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.ready state)
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases
      threeHeadReaderNoRowTransitions_runsReader
        D hstate hlength with
    ⟨separatorPhysical, hseparator, hreader⟩
  let reads := ReadTuple3.ofTapes logical
  have hbranch :
      RunsFromStateTapeEquiv
        (tableMachine (noRowJumpLimit D)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderNoRowTransitions D))
        (StaticDispatcherState.afterRead D state reads)
        (StaticDispatcherState.ready state)
        separatorPhysical
        separatorPhysical := by
    exact
      threeHeadReaderNoRowTransitions_runsNoRowFromExistingTapeSeparator
        D reads hstate hlookup hseparator
  have hreader' :
      RunsFromStateTapeEquiv
        (tableMachine (noRowJumpLimit D)
          (StaticDispatcherState.ready D.start)
          (StaticDispatcherState.ready D.halt)
          (threeHeadReaderNoRowTransitions D))
        (StaticDispatcherState.ready state)
        (StaticDispatcherState.afterRead D state reads)
        (encodedGuardedStructuredTapes logical)
        separatorPhysical := by
    simpa [reads, ReadTuple3.ofTapes] using hreader
  exact
    ⟨separatorPhysical, hseparator,
      runsFromStateTapeEquiv_trans hreader' hbranch⟩

def selectedRowCoreDescription
    (t : Transition) (refresh : MachineDescription) :
    MachineDescription :=
  readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
    t refresh

def selectedRowSeparatorDescription
    (t : Transition) (refresh : MachineDescription) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    returnFromTape2SeparatorToBlockStartDescription
    (selectedRowCoreDescription t refresh)

theorem runsFromStateTapeEquiv_to_haltsFromTapeEquiv
    {M : MachineDescription} {Tin Tout : Tape Bool}
    (hrun :
      RunsFromStateTapeEquiv M M.start M.halt Tin Tout) :
    M.HaltsFromTapeEquiv Tin Tout := by
  rcases hrun with ⟨n, actual, hrun, hequiv⟩
  exact
    ⟨actual,
      ⟨n, by
        constructor
        · simpa using
            congrArg
              (fun c : MachineDescription.Configuration => c.state)
              hrun
        · simpa using
            congrArg
              (fun c : MachineDescription.Configuration => c.tape)
              hrun⟩,
      hequiv⟩

theorem haltsFromTapeEquiv_to_runsFromStateTapeEquiv
    {M : MachineDescription} {Tin Tout : Tape Bool}
    (hhalt : M.HaltsFromTapeEquiv Tin Tout) :
    RunsFromStateTapeEquiv M M.start M.halt Tin Tout := by
  rcases hhalt with ⟨actual, hhalts, hequiv⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalts with
    ⟨n, hrun⟩
  exact ⟨n, actual, hrun, hequiv⟩

theorem returnFromTape2SeparatorToCanonicalBlockStart_runs
    {logical : List (Tape Bool)} (hlength : logical.length = 3)
    {physical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2 physical) :
    RunsFromStateTapeEquiv
      returnFromTape2SeparatorToBlockStartDescription
      returnFromTape2SeparatorToBlockStartDescription.start
      returnFromTape2SeparatorToBlockStartDescription.halt
      physical
      (encodedGuardedStructuredTapes logical) := by
  rcases
      returnFromTape2SeparatorToBlockStartDescription_runsFromTape2Separator
        hseparator (guardedHasAtLeastThreeTapes_of_length_three hlength) with
    ⟨blockStartPhysical, hblockStart, hrun⟩
  have hblockStartEq :
      blockStartPhysical = encodedGuardedStructuredTapes logical := by
    rcases hblockStart with ⟨_hle, heq⟩
    simpa [encodedGuardedStructuredTapes] using heq
  simpa [hblockStartEq] using hrun

theorem selectedRowCoreDescription_subroutineReady
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    (selectedRowCoreDescription t refresh).SubroutineReady := by
  simpa [selectedRowCoreDescription] using
    (hD.lookupFromReadTuple_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
      hlookup hrefresh).subroutineReady

theorem selectedRowCoreDescription_realizes_lookupFromReadTuple
    (D : Description) (hD : D.tapeCount = 3)
    (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {logical : List (Tape Bool)} {t : Transition}
    (hlength : logical.length = 3)
    (hlookup :
      lookupTransitionFromReadTuple3 D state
        (ReadTuple3.ofTapes logical) = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    let c : Configuration := { state := state, tapes := logical }
    let next : Configuration := structuredTransitionTarget D t c
    D.stepConfig c = some next ∧
      oneStepOrSelf D c = next ∧
      next.state = t.target ∧
      (selectedRowCoreDescription t refresh).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes logical)
        (encodedGuardedStructuredTapes next.tapes) := by
  intro c next
  have hlookupStructured : D.lookupTransition c = some t := by
    have hlookupConfig :
        lookupTransitionFromReadTuple3 D c.state
            (ReadTuple3.ofConfig c) = some t := by
      simpa [c, ReadTuple3.ofConfig] using hlookup
    rw [← lookupTransitionFromReadTuple3_eq_lookupTransition D hD c]
    exact hlookupConfig
  have hc : c.tapes.length = D.tapeCount := by
    simpa [c, hD] using hlength
  have hrealized :=
    hrows.lookup_realizes_structured_step_withStructuredSingleton3Refresh
      (c := c) (next := next) (t := t)
      hc hlookupStructured rfl hrefresh
  rcases hrealized with ⟨hstep, hrow⟩
  exact
    ⟨hstep,
      oneStepOrSelf_of_stepConfig_some hstep,
      by rfl,
      by simpa [selectedRowCoreDescription] using hrow⟩

theorem selectedRowSeparatorDescription_subroutineReady
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    (selectedRowSeparatorDescription t refresh).SubroutineReady := by
  exact
    canonicalPrimitiveSeqDescription_subroutineReady
      returnFromTape2SeparatorToBlockStartDescription_subroutineReady
      (selectedRowCoreDescription_subroutineReady
        hD hlookup hrefresh)

theorem selectedRowSeparatorDescription_haltsFromTapeEquiv
    (D : Description) (hD : D.tapeCount = 3)
    (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {logical : List (Tape Bool)} {t : Transition}
    (hlength : logical.length = 3)
    (hlookup :
      lookupTransitionFromReadTuple3 D state
        (ReadTuple3.ofTapes logical) = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {separatorPhysical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical) :
    let c : Configuration := { state := state, tapes := logical }
    let next : Configuration := structuredTransitionTarget D t c
    D.stepConfig c = some next ∧
      oneStepOrSelf D c = next ∧
      next.state = t.target ∧
      (selectedRowSeparatorDescription t refresh).HaltsFromTapeEquiv
        separatorPhysical
        (encodedGuardedStructuredTapes next.tapes) := by
  intro c next
  have hreturn :
      returnFromTape2SeparatorToBlockStartDescription.HaltsFromTapeEquiv
        separatorPhysical (encodedGuardedStructuredTapes logical) :=
    runsFromStateTapeEquiv_to_haltsFromTapeEquiv
      (returnFromTape2SeparatorToCanonicalBlockStart_runs
        hlength hseparator)
  have hcore :=
    selectedRowCoreDescription_realizes_lookupFromReadTuple
      D hD hrows hlength hlookup hrefresh
  rcases hcore with ⟨hstep, hone, htarget, hrow⟩
  have hready :
      (selectedRowCoreDescription t refresh).SubroutineReady :=
    selectedRowCoreDescription_subroutineReady
      hrows hlookup hrefresh
  exact
    ⟨hstep, hone, htarget,
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        returnFromTape2SeparatorToBlockStartDescription_subroutineReady
        hready hreturn hrow⟩

theorem selectedRowSeparatorDescription_runsFromTape2Separator
    (D : Description) (hD : D.tapeCount = 3)
    (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {logical : List (Tape Bool)} {t : Transition}
    (hlength : logical.length = 3)
    (hlookup :
      lookupTransitionFromReadTuple3 D state
        (ReadTuple3.ofTapes logical) = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {separatorPhysical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical) :
    let c : Configuration := { state := state, tapes := logical }
    (oneStepOrSelf D c).state = t.target ∧
      RunsFromStateTapeEquiv
        (selectedRowSeparatorDescription t refresh)
        (selectedRowSeparatorDescription t refresh).start
        (selectedRowSeparatorDescription t refresh).halt
        separatorPhysical
        (encodedGuardedStructuredTapes (oneStepOrSelf D c).tapes) := by
  intro c
  have hselected :=
    selectedRowSeparatorDescription_haltsFromTapeEquiv
      D hD hrows hlength hlookup hrefresh hseparator
  rcases hselected with ⟨_hstep, hone, htarget, hhalt⟩
  constructor
  · simpa [c, hone] using htarget
  · simpa [c, hone] using
      haltsFromTapeEquiv_to_runsFromStateTapeEquiv hhalt

def retargetedSelectedRowSeparatorDescription
    (offset target : Nat)
    (t : Transition) (refresh : MachineDescription) :
    MachineDescription :=
  MachineDescription.offsetRetargetDescription offset target
    (selectedRowSeparatorDescription t refresh)

theorem retargetedSelectedRowSeparatorDescription_subroutineReady
    {offset target : Nat} (htarget : target < offset)
    {D : Description} (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    (retargetedSelectedRowSeparatorDescription
      offset target t refresh).SubroutineReady := by
  exact
    MachineDescription.offsetRetargetDescription_subroutineReady
      htarget
      (selectedRowSeparatorDescription_subroutineReady
        hrows hlookup hrefresh).left

theorem retargetedSelectedRowSeparatorDescription_sources_in_offset_block
    {offset target : Nat}
    {D : Description} (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    forall u : TransitionDescription,
      u ∈ (retargetedSelectedRowSeparatorDescription
            offset target t refresh).transitions ->
        offset ≤ u.source ∧
          u.source <
            offset + (selectedRowSeparatorDescription t refresh).stateCount := by
  simpa [retargetedSelectedRowSeparatorDescription] using
    offsetRetargetDescription_sources_in_offset_block
      (selectedRowSeparatorDescription_subroutineReady
        hrows hlookup hrefresh).left

theorem retargetedSelectedRowSeparatorDescription_runsFromTape2Separator
    (D : Description) (hD : D.tapeCount = 3)
    (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {logical : List (Tape Bool)} {t : Transition}
    (hlength : logical.length = 3)
    (hlookup :
      lookupTransitionFromReadTuple3 D state
        (ReadTuple3.ofTapes logical) = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {offset : Nat}
    (htargetBelow : StaticDispatcherState.ready t.target < offset)
    {separatorPhysical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical) :
    let c : Configuration := { state := state, tapes := logical }
    (oneStepOrSelf D c).state = t.target ∧
      RunsFromStateTapeEquiv
        (retargetedSelectedRowSeparatorDescription
          offset (StaticDispatcherState.ready t.target) t refresh)
        (retargetedSelectedRowSeparatorDescription
          offset (StaticDispatcherState.ready t.target) t refresh).start
        (StaticDispatcherState.ready t.target)
        separatorPhysical
        (encodedGuardedStructuredTapes (oneStepOrSelf D c).tapes) := by
  intro c
  have hrun :=
    selectedRowSeparatorDescription_runsFromTape2Separator
      D hD hrows hlength hlookup hrefresh hseparator
  rcases hrun with ⟨honeState, hrun⟩
  have hready :
      (selectedRowSeparatorDescription t refresh).SubroutineReady :=
    selectedRowSeparatorDescription_subroutineReady
      hrows hlookup hrefresh
  have hcopy :=
    runsFromStateTapeEquiv_offsetRetargetDescription
      (offset := offset)
      (target := StaticDispatcherState.ready t.target)
      htargetBelow hready.right hrun
  constructor
  · exact honeState
  · simpa [retargetedSelectedRowSeparatorDescription] using hcopy

def selectedRowBranchJumpDescription
    (branchStateCount : Nat) (D : Description)
    (state : Nat) (reads : ReadTuple3)
    (scratch target : Nat) : MachineDescription :=
  blankHeadBounceJumpDescription branchStateCount
    (StaticDispatcherState.afterRead D state reads)
    scratch target

def selectedRowBranchTransitions
    (branchStateCount offset : Nat) (D : Description)
    (state : Nat) (reads : ReadTuple3)
    (scratch : Nat) (t : Transition)
    (refresh : MachineDescription) : List TransitionDescription :=
  (selectedRowBranchJumpDescription branchStateCount D state reads
      scratch
      (retargetedSelectedRowSeparatorDescription
        offset (StaticDispatcherState.ready t.target) t refresh).start).transitions ++
    (retargetedSelectedRowSeparatorDescription
      offset (StaticDispatcherState.ready t.target) t refresh).transitions

theorem selectedRowBranchJumpDescription_sources_below_offset
    {branchStateCount offset : Nat} {D : Description}
    {state scratch target : Nat} {reads : ReadTuple3}
    (hsourceBelow :
      StaticDispatcherState.afterRead D state reads < offset)
    (hscratchBelow : scratch < offset) :
    TransitionSourcesBelow offset
      (selectedRowBranchJumpDescription branchStateCount D state reads
        scratch target).transitions := by
  simpa [selectedRowBranchJumpDescription] using
    blankHeadBounceJumpDescription_sources_below
      hsourceBelow hscratchBelow

theorem retargetedSelectedRowSeparatorDescription_sources_atLeast_offset
    {offset target : Nat}
    {D : Description} (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {reads : ReadTuple3} {t : Transition}
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    TransitionSourcesAtLeast offset
      (retargetedSelectedRowSeparatorDescription
        offset target t refresh).transitions := by
  intro u hu
  exact
    (retargetedSelectedRowSeparatorDescription_sources_in_offset_block
      hrows hlookup hrefresh u hu).left

theorem selectedRowBranchTransitions_deterministic
    {branchStateCount offset : Nat} {D : Description}
    {state scratch : Nat} {reads : ReadTuple3} {t : Transition}
    {refresh : MachineDescription}
    (hrows : SupportsReadWriteRows3 D)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (hsourceScratch :
      StaticDispatcherState.afterRead D state reads ≠ scratch)
    (hsourceBelow :
      StaticDispatcherState.afterRead D state reads < offset)
    (hscratchBelow : scratch < offset)
    (htargetBelow : StaticDispatcherState.ready t.target < offset) :
    TransitionListDeterministic
      (selectedRowBranchTransitions branchStateCount offset D state reads
        scratch t refresh) := by
  let rowMachine :=
    retargetedSelectedRowSeparatorDescription
      offset (StaticDispatcherState.ready t.target) t refresh
  let jumpMachine :=
    selectedRowBranchJumpDescription branchStateCount D state reads
      scratch rowMachine.start
  have hjumpDet :
      TransitionListDeterministic jumpMachine.transitions := by
    simpa [jumpMachine, selectedRowBranchJumpDescription] using
      blankHeadBounceJumpDescription_transitionListDeterministic
        hsourceScratch
  have hrowDet :
      TransitionListDeterministic rowMachine.transitions :=
    transitionListDeterministic_of_wellFormed
      (retargetedSelectedRowSeparatorDescription_subroutineReady
        htargetBelow hrows hlookup hrefresh).left
  have hdisjoint :
      TransitionSourceDisjoint jumpMachine.transitions
        rowMachine.transitions :=
    transitionSourceDisjoint_of_below_atLeast
      (by
        simpa [jumpMachine] using
          selectedRowBranchJumpDescription_sources_below_offset
            (branchStateCount := branchStateCount) (offset := offset)
            (D := D) (state := state) (reads := reads)
            (scratch := scratch) (target := rowMachine.start)
            hsourceBelow hscratchBelow)
      (by
        simpa [rowMachine] using
          retargetedSelectedRowSeparatorDescription_sources_atLeast_offset
            (offset := offset)
            (target := StaticDispatcherState.ready t.target)
            hrows hlookup hrefresh)
  simpa [selectedRowBranchTransitions, jumpMachine, rowMachine] using
    transitionListDeterministic_append_of_sourceDisjoint
      hjumpDet hrowDet hdisjoint

theorem selectedRowBranchTransitions_source_cases
    {branchStateCount offset : Nat} {D : Description}
    {state scratch : Nat} {reads : ReadTuple3} {t : Transition}
    {refresh : MachineDescription}
    {u : TransitionDescription}
    (hrows : SupportsReadWriteRows3 D)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (hu :
      u ∈ selectedRowBranchTransitions branchStateCount offset D state reads
        scratch t refresh) :
    u.source = StaticDispatcherState.afterRead D state reads ∨
      u.source = scratch ∨ offset ≤ u.source := by
  let rowMachine :=
    retargetedSelectedRowSeparatorDescription
      offset (StaticDispatcherState.ready t.target) t refresh
  let jumpMachine :=
    selectedRowBranchJumpDescription branchStateCount D state reads
      scratch rowMachine.start
  have hu' :
      u ∈ jumpMachine.transitions ∨ u ∈ rowMachine.transitions := by
    simpa [selectedRowBranchTransitions, jumpMachine, rowMachine] using hu
  rcases hu' with huJump | huRow
  · rcases
        blankHeadBounceJumpDescription_transition_source_cases
          (by
            simpa [jumpMachine, selectedRowBranchJumpDescription] using
              huJump) with hsource | hscratch
    · exact Or.inl hsource
    · exact Or.inr (Or.inl hscratch)
  · exact
      Or.inr (Or.inr
        ((retargetedSelectedRowSeparatorDescription_sources_in_offset_block
          hrows hlookup hrefresh u (by simpa [rowMachine] using huRow)).left))

theorem threeHeadReaderTransitions_selectedRowBranchTransitions_sourceDisjoint
    {branchStateCount offset : Nat} {D : Description}
    {state scratch : Nat} {reads : ReadTuple3} {t : Transition}
    {refresh : MachineDescription}
    (hstate : state < D.stateCount)
    (hrows : SupportsReadWriteRows3 D)
    (hlookup :
      lookupTransitionFromReadTuple3 D state reads = some t)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (hscratchAtLeast : threeHeadReaderStateLimit D ≤ scratch)
    (hoffsetAtLeast : threeHeadReaderStateLimit D ≤ offset) :
    TransitionSourceDisjoint
      (threeHeadReaderTransitions D)
      (selectedRowBranchTransitions branchStateCount offset D state reads
        scratch t refresh) := by
  intro left right hleft hright hsource
  have hleftBelow :=
    threeHeadReaderTransitions_sources_below_stateLimit D left hleft
  rcases
      selectedRowBranchTransitions_source_cases
        hrows hlookup hrefresh hright with
    hrightAfter | hrightCases
  · rw [hrightAfter] at hsource
    exact
      (threeHeadReaderTransitions_sources_ne_afterRead
        D reads hstate left hleft) hsource
  · rcases hrightCases with hrightScratch | hrightOffset
    · rw [hrightScratch] at hsource
      have hrightGe :
          threeHeadReaderStateLimit D ≤ right.source := by
        simpa [hrightScratch] using hscratchAtLeast
      lia
    · have hrightGe :
          threeHeadReaderStateLimit D ≤ right.source :=
        Nat.le_trans hoffsetAtLeast hrightOffset
      lia

theorem selectedRowBranchTransitions_runsFromTape2Separator
    (D : Description) (hD : D.tapeCount = 3)
    (hrows : SupportsReadWriteRows3 D)
    {state : Nat} {logical : List (Tape Bool)} {t : Transition}
    (hlength : logical.length = 3)
    (hlookup :
      lookupTransitionFromReadTuple3 D state
        (ReadTuple3.ofTapes logical) = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {branchStateCount offset scratch : Nat}
    (hsourceScratch :
      StaticDispatcherState.afterRead D state (ReadTuple3.ofTapes logical) ≠
        scratch)
    (hsourceBelow :
      StaticDispatcherState.afterRead D state (ReadTuple3.ofTapes logical) <
        offset)
    (hscratchBelow : scratch < offset)
    (hsourceLimit :
      StaticDispatcherState.afterRead D state (ReadTuple3.ofTapes logical) <
        branchStateCount)
    (hscratchLimit : scratch < branchStateCount)
    (hrowStartAtLeast :
      offset ≤
        (retargetedSelectedRowSeparatorDescription
          offset (StaticDispatcherState.ready t.target) t refresh).start)
    (hrowStartLimit :
      (retargetedSelectedRowSeparatorDescription
        offset (StaticDispatcherState.ready t.target) t refresh).start <
        branchStateCount)
    (htargetBelow : StaticDispatcherState.ready t.target < offset)
    {separatorPhysical : Tape Bool}
    (hseparator :
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical) :
    let reads := ReadTuple3.ofTapes logical
    let c : Configuration := { state := state, tapes := logical }
    (oneStepOrSelf D c).state = t.target ∧
      RunsFromStateTapeEquiv
        (tableMachine branchStateCount
          (StaticDispatcherState.afterRead D state reads)
          (StaticDispatcherState.ready t.target)
          (selectedRowBranchTransitions branchStateCount offset D state reads
            scratch t refresh))
        (StaticDispatcherState.afterRead D state reads)
        (StaticDispatcherState.ready t.target)
        separatorPhysical
        (encodedGuardedStructuredTapes (oneStepOrSelf D c).tapes) := by
  intro reads c
  let rowMachine :=
    retargetedSelectedRowSeparatorDescription
      offset (StaticDispatcherState.ready t.target) t refresh
  let jumpMachine :=
    selectedRowBranchJumpDescription branchStateCount D state reads
      scratch rowMachine.start
  let branchMachine :=
    tableMachine branchStateCount
      (StaticDispatcherState.afterRead D state reads)
      (StaticDispatcherState.ready t.target)
      (selectedRowBranchTransitions branchStateCount offset D state reads
        scratch t refresh)
  have hsourceScratch' :
      StaticDispatcherState.afterRead D state reads ≠ scratch := by
    simpa [reads] using hsourceScratch
  have hsourceBelow' :
      StaticDispatcherState.afterRead D state reads < offset := by
    simpa [reads] using hsourceBelow
  have hsourceLimit' :
      StaticDispatcherState.afterRead D state reads < branchStateCount := by
    simpa [reads] using hsourceLimit
  have hrowStartAtLeast' : offset ≤ rowMachine.start := by
    simpa [rowMachine] using hrowStartAtLeast
  have hrowStartLimit' : rowMachine.start < branchStateCount := by
    simpa [rowMachine] using hrowStartLimit
  have hrowStartSource : rowMachine.start ≠
      StaticDispatcherState.afterRead D state reads := by
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le hsourceBelow' hrowStartAtLeast')).symm
  have hrowStartScratch : rowMachine.start ≠ scratch := by
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le hscratchBelow hrowStartAtLeast')).symm
  have hbranchDet : branchMachine.Deterministic := by
    exact
      tableMachine_deterministic_of_transitionListDeterministic
        (by
          simpa [branchMachine] using
            selectedRowBranchTransitions_deterministic
              (branchStateCount := branchStateCount) (offset := offset)
              (D := D) (state := state) (reads := reads)
              (scratch := scratch) (t := t) (refresh := refresh)
              hrows
              (by simpa [reads] using hlookup)
              hrefresh hsourceScratch' hsourceBelow' hscratchBelow
              htargetBelow)
  have hjumpReady : jumpMachine.SubroutineReady := by
    simpa [jumpMachine, selectedRowBranchJumpDescription] using
      blankHeadBounceJumpDescription_subroutineReady
        hsourceLimit' hscratchLimit hrowStartLimit'
        hsourceScratch' hrowStartSource hrowStartScratch
  have hjump :
      RunsFromStateTapeEquiv jumpMachine
        (StaticDispatcherState.afterRead D state reads)
        rowMachine.start
        separatorPhysical separatorPhysical := by
    simpa [jumpMachine, selectedRowBranchJumpDescription] using
      blankHeadBounceJumpDescription_runsFromTapeSeparator
        hsourceScratch' hseparator.left
  have hjumpBranch :
      RunsFromStateTapeEquiv branchMachine
        (StaticDispatcherState.afterRead D state reads)
        rowMachine.start
        separatorPhysical separatorPhysical := by
    exact
      runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
        (small := jumpMachine)
        (big := branchMachine)
        (hsubset := by
          intro u hu
          simpa [branchMachine, tableMachine, selectedRowBranchTransitions,
            jumpMachine, rowMachine] using Or.inl hu)
        hbranchDet hjumpReady.right hjump
  have hrowSelected :=
    retargetedSelectedRowSeparatorDescription_runsFromTape2Separator
      D hD hrows hlength hlookup hrefresh htargetBelow hseparator
  rcases hrowSelected with ⟨honeState, hrow⟩
  have hrowReady : rowMachine.SubroutineReady := by
    simpa [rowMachine] using
      retargetedSelectedRowSeparatorDescription_subroutineReady
        htargetBelow hrows
        (by simpa [reads] using hlookup)
        hrefresh
  have hrowBranch :
      RunsFromStateTapeEquiv branchMachine
        rowMachine.start
        (StaticDispatcherState.ready t.target)
        separatorPhysical
        (encodedGuardedStructuredTapes (oneStepOrSelf D c).tapes) := by
    exact
      runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
        (small := rowMachine)
        (big := branchMachine)
        (hsubset := by
          intro u hu
          simpa [branchMachine, tableMachine, selectedRowBranchTransitions,
            rowMachine] using Or.inr hu)
        hbranchDet hrowReady.right
        (by simpa [rowMachine, c] using hrow)
  exact ⟨by simpa [c] using honeState,
    runsFromStateTapeEquiv_trans hjumpBranch hrowBranch⟩

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
