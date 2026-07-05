import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Dispatcher

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

def tape0ReaderOffset (D : Description) : Nat :=
  readyJumpLimit D

def tape0ReaderDescription (D : Description) (state : Nat) :
    MachineDescription :=
  retargetedBranchingTape0ReadHeadCellAllExitsDescription
    (tape0ReaderOffset D)
    (StaticDispatcherState.tape0ReaderTargets D state)

def tape0ReaderStart (D : Description) (state : Nat) : Nat :=
  (tape0ReaderDescription D state).start

def tape0ReaderLimit (D : Description) : Nat :=
  tape0ReaderOffset D +
    branchingTape0ReadHeadCellAndReturnToSeparatorDescription.stateCount

def afterRead0JumpScratchBase (D : Description) : Nat :=
  tape0ReaderLimit D

def afterRead0JumpScratch (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  afterRead0JumpScratchBase D + 3 * state + ReadTuple3.readCode read0

def afterRead0JumpLimit (D : Description) : Nat :=
  afterRead0JumpScratchBase D + 3 * D.stateCount

def tape1ReaderOffset (D : Description) : Nat :=
  afterRead0JumpLimit D

def tape1ReaderDescription (D : Description) (state : Nat)
    (read0 : Option Bool) : MachineDescription :=
  retargetedBranchingTape1ReadHeadCellAllExitsDescription
    (tape1ReaderOffset D)
    (StaticDispatcherState.tape1ReaderTargets D state read0)

def tape1ReaderStart (D : Description) (state : Nat)
    (read0 : Option Bool) : Nat :=
  (tape1ReaderDescription D state read0).start

def tape1ReaderLimit (D : Description) : Nat :=
  tape1ReaderOffset D +
    branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount

def afterRead1JumpScratchBase (D : Description) : Nat :=
  tape1ReaderLimit D

def afterRead1JumpScratch (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Nat :=
  afterRead1JumpScratchBase D + 9 * state +
    ReadTuple3.code01 read0 read1

def afterRead1JumpLimit (D : Description) : Nat :=
  afterRead1JumpScratchBase D + 9 * D.stateCount

def tape2ReaderOffset (D : Description) : Nat :=
  afterRead1JumpLimit D

def tape2ReaderDescription (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : MachineDescription :=
  retargetedBranchingTape2ReadHeadCellAllExitsDescription
    (tape2ReaderOffset D)
    (StaticDispatcherState.tape2ReaderTargets D state read0 read1)

def tape2ReaderStart (D : Description) (state : Nat)
    (read0 read1 : Option Bool) : Nat :=
  (tape2ReaderDescription D state read0 read1).start

def tape2ReaderLimit (D : Description) : Nat :=
  tape2ReaderOffset D +
    branchingTape2ReadHeadCellAndReturnToSeparatorDescription.stateCount

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
    (D : Description) :
    StaticDispatcherState.readerStateLimit D ≤ tape0ReaderOffset D := by
  unfold tape0ReaderOffset readyJumpLimit readyJumpScratchBase
  lia

theorem readerStateLimit_le_tape1ReaderOffset
    (D : Description) :
    StaticDispatcherState.readerStateLimit D ≤ tape1ReaderOffset D := by
  unfold tape1ReaderOffset afterRead0JumpLimit afterRead0JumpScratchBase
    tape0ReaderLimit tape0ReaderOffset readyJumpLimit readyJumpScratchBase
  lia

theorem readerStateLimit_le_tape2ReaderOffset
    (D : Description) :
    StaticDispatcherState.readerStateLimit D ≤ tape2ReaderOffset D := by
  unfold tape2ReaderOffset afterRead1JumpLimit afterRead1JumpScratchBase
    tape1ReaderLimit tape1ReaderOffset afterRead0JumpLimit
    afterRead0JumpScratchBase tape0ReaderLimit tape0ReaderOffset
    readyJumpLimit readyJumpScratchBase
  lia

theorem tape0ReaderTargets_lt_tape0ReaderOffset
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount) :
    forall read0 : Option Bool,
      StaticDispatcherState.tape0ReaderTargets D state read0 < tape0ReaderOffset D := by
  intro read0
  exact
    Nat.lt_of_lt_of_le
      (StaticDispatcherState.tape0ReaderTargets_lt_readerStateLimit D hstate read0)
      (readerStateLimit_le_tape0ReaderOffset D)

theorem tape1ReaderTargets_lt_tape1ReaderOffset
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    forall read1 : Option Bool,
      StaticDispatcherState.tape1ReaderTargets D state read0 read1 < tape1ReaderOffset D := by
  intro read1
  exact
    Nat.lt_of_lt_of_le
      (StaticDispatcherState.tape1ReaderTargets_lt_readerStateLimit D read0 hstate read1)
      (readerStateLimit_le_tape1ReaderOffset D)

theorem tape2ReaderTargets_lt_tape2ReaderOffset
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    forall read2 : Option Bool,
      StaticDispatcherState.tape2ReaderTargets D state read0 read1 read2 <
        tape2ReaderOffset D := by
  intro read2
  exact
    Nat.lt_of_lt_of_le
      (StaticDispatcherState.tape2ReaderTargets_lt_readerStateLimit D read0 read1 hstate read2)
      (readerStateLimit_le_tape2ReaderOffset D)

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
    retargetedBranchingTape2ReadHeadCellAllExitsDescription_subroutineReady
      (tape2ReaderTargets_lt_tape2ReaderOffset D read0 read1 hstate)

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
      tape0ReaderLimit tape0ReaderOffset readyJumpLimit readyJumpScratchBase
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
      tape1ReaderLimit tape1ReaderOffset afterRead0JumpLimit
      afterRead0JumpScratchBase tape0ReaderLimit tape0ReaderOffset
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
      (offset := tape0ReaderOffset D)
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
      (offset := tape1ReaderOffset D)
      (target := StaticDispatcherState.tape1ReaderTargets D state read0)
      (tape1ReaderTargets_lt_tape1ReaderOffset D read0 hstate)
      hlength

theorem tape2ReaderDescription_runsFromGuardedBlockStart
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tape2ReaderDescription D state read0 read1)
          (tape2ReaderStart D state read0 read1)
          (StaticDispatcherState.afterRead D state
            { read0 := read0,
              read1 := read1,
              read2 := Tape.read (Description.tapeAt logical 2) })
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  simpa [tape2ReaderDescription, tape2ReaderStart,
    StaticDispatcherState.tape2ReaderTargets, StaticDispatcherState.tape2ReaderTarget] using
    retargetedBranchingTape2ReadHeadCellAllExitsDescription_runsFromGuardedBlockStart
      (offset := tape2ReaderOffset D)
      (target := StaticDispatcherState.tape2ReaderTargets D state read0 read1)
      (tape2ReaderTargets_lt_tape2ReaderOffset D read0 read1 hstate)
      hlength

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
