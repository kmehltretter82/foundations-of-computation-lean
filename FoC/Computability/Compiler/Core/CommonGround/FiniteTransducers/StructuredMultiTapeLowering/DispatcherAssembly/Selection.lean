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

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
