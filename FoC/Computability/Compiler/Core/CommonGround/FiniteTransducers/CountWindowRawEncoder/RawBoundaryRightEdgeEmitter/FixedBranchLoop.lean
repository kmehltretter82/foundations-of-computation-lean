import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.MarkedCellSuffixLoop

set_option doc.verso true

/-!
# Raw-boundary fixed branch loop

This module starts the fixed-control loop that replaces generated
remaining-raw-bit route descriptions.  The table copies the marker-aware puller,
dispatches on the post-pull left-neighbor shape, loops back after a real raw bit
is emitted, and exits after the boundary marker is erased and returned.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def rawBoundaryFixedBranchLoopHalt : Nat := 0

def rawBoundaryFixedBranchLoopPostPullStart : Nat := 1

def rawBoundaryFixedBranchLoopPostPullReadLeft : Nat := 2

def rawBoundaryFixedBranchLoopPullOffset : Nat := 3

def rawBoundaryFixedBranchLoopStart : Nat :=
  rawBoundaryFixedBranchLoopPullOffset +
    markerAwarePullNearestRawBitDescription.start

def rawBoundaryFixedBranchLoopRealBranchOffset : Nat :=
  rawBoundaryFixedBranchLoopPullOffset +
    markerAwarePullNearestRawBitDescription.stateCount

def rawBoundaryFixedBranchLoopBoundaryBranchOffset : Nat :=
  rawBoundaryFixedBranchLoopRealBranchOffset +
    emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.stateCount

def rawBoundaryFixedBranchLoopRealBranchTarget : Nat :=
  rawBoundaryFixedBranchLoopRealBranchOffset +
    emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.start

def rawBoundaryFixedBranchLoopBoundaryBranchTarget : Nat :=
  rawBoundaryFixedBranchLoopBoundaryBranchOffset +
    rawBoundaryMarkedCellSuffixEraseThenReturnDescription.start

def rawBoundaryFixedBranchLoopDescription : MachineDescription where
  stateCount :=
    rawBoundaryFixedBranchLoopBoundaryBranchOffset +
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription.stateCount
  start := rawBoundaryFixedBranchLoopStart
  halt := rawBoundaryFixedBranchLoopHalt
  transitions :=
    [ transition rawBoundaryFixedBranchLoopPostPullStart
        (some false) (some false) Direction.left
        rawBoundaryFixedBranchLoopPostPullReadLeft
    , transition rawBoundaryFixedBranchLoopPostPullStart
        (some true) (some true) Direction.left
        rawBoundaryFixedBranchLoopPostPullReadLeft
    , transition rawBoundaryFixedBranchLoopPostPullReadLeft
        none none Direction.right
        rawBoundaryFixedBranchLoopBoundaryBranchTarget
    , transition rawBoundaryFixedBranchLoopPostPullReadLeft
        (some false) (some false) Direction.right
        rawBoundaryFixedBranchLoopRealBranchTarget
    , transition rawBoundaryFixedBranchLoopPostPullReadLeft
        (some true) (some true) Direction.right
        rawBoundaryFixedBranchLoopRealBranchTarget ] ++
    (MachineDescription.offsetExitRetargetDescription
      rawBoundaryFixedBranchLoopPullOffset
      markerAwarePullNearestRawBitDescription.halt
      rawBoundaryFixedBranchLoopPostPullStart
      markerAwarePullNearestRawBitDescription).transitions ++
    (MachineDescription.offsetExitRetargetDescription
      rawBoundaryFixedBranchLoopRealBranchOffset
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt
      rawBoundaryFixedBranchLoopStart
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription).transitions ++
    (MachineDescription.offsetExitRetargetDescription
      rawBoundaryFixedBranchLoopBoundaryBranchOffset
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt
      rawBoundaryFixedBranchLoopHalt
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription).transitions

theorem rawBoundaryFixedBranchLoopDescription_wellFormed :
    rawBoundaryFixedBranchLoopDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rawBoundaryFixedBranchLoopDescription.transitions)
      (stateCount := rawBoundaryFixedBranchLoopDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rawBoundaryFixedBranchLoopDescription.transitions)
      (by decide)

theorem rawBoundaryFixedBranchLoopDescription_haltTransitionFree :
    rawBoundaryFixedBranchLoopDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rawBoundaryFixedBranchLoopDescription.transitions)
    (state := rawBoundaryFixedBranchLoopDescription.halt)
    (by decide)

theorem rawBoundaryFixedBranchLoopDescription_subroutineReady :
    rawBoundaryFixedBranchLoopDescription.SubroutineReady :=
  ⟨rawBoundaryFixedBranchLoopDescription_wellFormed,
    rawBoundaryFixedBranchLoopDescription_haltTransitionFree⟩

theorem rawBoundaryFixedBranchLoopDescription_run_postPull_dispatch_real
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    rawBoundaryFixedBranchLoopDescription.runConfig 2
        { state := rawBoundaryFixedBranchLoopPostPullStart
          tape :=
            pullNearestRawBitToHeadMarkerTargetTape
              (scratchTail + 3) baseLeft rawBit headBit right } =
      { state := rawBoundaryFixedBranchLoopRealBranchTarget
        tape :=
          pullNearestRawBitToHeadMarkerTargetTape
            (scratchTail + 3) baseLeft rawBit headBit right } := by
  cases rawBit <;> cases headBit <;>
    simp [rawBoundaryFixedBranchLoopDescription,
      rawBoundaryFixedBranchLoopPostPullStart,
      rawBoundaryFixedBranchLoopPostPullReadLeft,
      rawBoundaryFixedBranchLoopRealBranchTarget,
      pullNearestRawBitToHeadMarkerTargetTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rawBoundaryFixedBranchLoopDescription_run_postPull_dispatch_boundary
    (gap : Nat) (baseTail : List (Option Bool))
    (markerBit headBit : Bool) (right : List (Option Bool)) :
    rawBoundaryFixedBranchLoopDescription.runConfig 2
        { state := rawBoundaryFixedBranchLoopPostPullStart
          tape :=
            markerAwarePullNearestBoundaryToHeadMarkerTargetTape
              gap baseTail markerBit headBit right } =
      { state := rawBoundaryFixedBranchLoopBoundaryBranchTarget
        tape :=
          markerAwarePullNearestBoundaryToHeadMarkerTargetTape
            gap baseTail markerBit headBit right } := by
  cases markerBit <;> cases headBit <;>
    simp [rawBoundaryFixedBranchLoopDescription,
      rawBoundaryFixedBranchLoopPostPullStart,
      rawBoundaryFixedBranchLoopPostPullReadLeft,
      rawBoundaryFixedBranchLoopBoundaryBranchTarget,
      markerAwarePullNearestBoundaryToHeadMarkerTargetTape, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_realBranchTarget
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopRealBranchTarget
      rawBoundaryFixedBranchLoopStart
      (pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail baseLeft rawBit headBit right) := by
  let branch :=
    MachineDescription.offsetExitRetargetDescription
      rawBoundaryFixedBranchLoopRealBranchOffset
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt
      rawBoundaryFixedBranchLoopStart
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription
  have hlocal :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.start
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt
        (pullNearestRawBitToHeadMarkerTargetTape
          (scratchTail + 3) baseLeft rawBit headBit right)
        (emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right) := by
    rcases
        runConfig_eq_halt_of_haltsFromTape
          (emitPulledRawBitCellChunkThenMoveLeftEdgeDescription_haltsFrom_headGapPulled
            scratchTail baseLeft rawBit headBit right) with
      ⟨n, hrun⟩
    exact
      ⟨n,
        emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right,
        hrun,
        Tape.Equiv.refl
          (emitPulledRawBitCellChunkLeftEdgeTargetTape
            scratchTail baseLeft rawBit headBit right)⟩
  have hfree :
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.TransitionFreeAt
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt := by
    intro t ht
    exact
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription_subroutineReady.right
        t ht
  have hretarget :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        branch
        rawBoundaryFixedBranchLoopRealBranchTarget
        rawBoundaryFixedBranchLoopStart
        (pullNearestRawBitToHeadMarkerTargetTape
          (scratchTail + 3) baseLeft rawBit headBit right)
        (emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right) := by
    have hstart_ne :
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.start ≠
          emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt := by
      decide
    have h :=
      Structured.MultiTapeLowering.runsFromStateTapeEquiv_offsetExitRetargetDescription
        (offset := rawBoundaryFixedBranchLoopRealBranchOffset)
        (localExit :=
          emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt)
        (target := rawBoundaryFixedBranchLoopStart)
        (by decide)
        hfree
        hlocal
    simpa [branch, rawBoundaryFixedBranchLoopRealBranchTarget,
      hstart_ne] using h
  have hsubset :
      forall t : TransitionDescription,
        t ∈ branch.transitions ->
          t ∈ rawBoundaryFixedBranchLoopDescription.transitions := by
    intro t ht
    simp [branch, rawBoundaryFixedBranchLoopDescription, ht]
  have hdet : rawBoundaryFixedBranchLoopDescription.Deterministic :=
    rawBoundaryFixedBranchLoopDescription_wellFormed.right.right.right.right
  have hbranchFree :
      branch.TransitionFreeAt rawBoundaryFixedBranchLoopStart := by
    have hhalt :
        branch.HaltTransitionFree := by
      simpa [branch] using
        MachineDescription.offsetExitRetargetDescription_haltTransitionFree
          (offset := rawBoundaryFixedBranchLoopRealBranchOffset)
          (localExit :=
            emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt)
          (target := rawBoundaryFixedBranchLoopStart)
          (by decide)
          emitPulledRawBitCellChunkThenMoveLeftEdgeDescription
    intro t ht
    simpa [branch, MachineDescription.offsetExitRetargetDescription] using
      hhalt t ht
  exact
    Structured.MultiTapeLowering.StaticDispatcherReaderAssembly.runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hbranchFree hretarget

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_pull_real
    (scratchTail : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool)) (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopPostPullStart
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right)
      (markerAwarePullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right) := by
  let branch :=
    MachineDescription.offsetExitRetargetDescription
      rawBoundaryFixedBranchLoopPullOffset
      markerAwarePullNearestRawBitDescription.halt
      rawBoundaryFixedBranchLoopPostPullStart
      markerAwarePullNearestRawBitDescription
  have hlocal :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        markerAwarePullNearestRawBitDescription
        markerAwarePullNearestRawBitDescription.start
        markerAwarePullNearestRawBitDescription.halt
        (markerAwarePullNearestRawBitToHeadMarkerSourceTape
          (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right)
        (markerAwarePullNearestRawBitToHeadMarkerTargetTape
          (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right) := by
    rcases
        runConfig_eq_halt_of_haltsFromTape
          (markerAwarePullNearestRawBitDescription_haltsFromHeadGap_real
            (scratchTail + 3) leftBit rawBit headBit baseTail right) with
      ⟨n, hrun⟩
    exact
      ⟨n,
        markerAwarePullNearestRawBitToHeadMarkerTargetTape
          (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right,
        hrun,
        Tape.Equiv.refl
          (markerAwarePullNearestRawBitToHeadMarkerTargetTape
            (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right)⟩
  have hfree :
      markerAwarePullNearestRawBitDescription.TransitionFreeAt
        markerAwarePullNearestRawBitDescription.halt := by
    intro t ht
    exact markerAwarePullNearestRawBitDescription_subroutineReady.right t ht
  have hretarget :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        branch
        rawBoundaryFixedBranchLoopStart
        rawBoundaryFixedBranchLoopPostPullStart
        (markerAwarePullNearestRawBitToHeadMarkerSourceTape
          (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right)
        (markerAwarePullNearestRawBitToHeadMarkerTargetTape
          (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right) := by
    have hstart_ne :
        markerAwarePullNearestRawBitDescription.start ≠
          markerAwarePullNearestRawBitDescription.halt := by
      decide
    have h :=
      Structured.MultiTapeLowering.runsFromStateTapeEquiv_offsetExitRetargetDescription
        (offset := rawBoundaryFixedBranchLoopPullOffset)
        (localExit := markerAwarePullNearestRawBitDescription.halt)
        (target := rawBoundaryFixedBranchLoopPostPullStart)
        (by decide)
        hfree
        hlocal
    simpa [branch, rawBoundaryFixedBranchLoopStart, hstart_ne] using h
  have hsubset :
      forall t : TransitionDescription,
        t ∈ branch.transitions ->
          t ∈ rawBoundaryFixedBranchLoopDescription.transitions := by
    intro t ht
    simp [branch, rawBoundaryFixedBranchLoopDescription, ht]
  have hdet : rawBoundaryFixedBranchLoopDescription.Deterministic :=
    rawBoundaryFixedBranchLoopDescription_wellFormed.right.right.right.right
  have hbranchFree :
      branch.TransitionFreeAt rawBoundaryFixedBranchLoopPostPullStart := by
    have hhalt :
        branch.HaltTransitionFree := by
      simpa [branch] using
        MachineDescription.offsetExitRetargetDescription_haltTransitionFree
          (offset := rawBoundaryFixedBranchLoopPullOffset)
          (localExit := markerAwarePullNearestRawBitDescription.halt)
          (target := rawBoundaryFixedBranchLoopPostPullStart)
          (by decide)
          markerAwarePullNearestRawBitDescription
    intro t ht
    simpa [branch, MachineDescription.offsetExitRetargetDescription] using
      hhalt t ht
  exact
    Structured.MultiTapeLowering.StaticDispatcherReaderAssembly.runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hbranchFree hretarget

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_real
    (scratchTail : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool)) (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopStart
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail (some leftBit :: baseTail) rawBit headBit right) := by
  let Tpull :=
    markerAwarePullNearestRawBitToHeadMarkerTargetTape
      (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right
  have hpull :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopStart
        rawBoundaryFixedBranchLoopPostPullStart
        (markerAwarePullNearestRawBitToHeadMarkerSourceTape
          (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right)
        Tpull := by
    simpa [Tpull] using
      rawBoundaryFixedBranchLoopDescription_runsFrom_pull_real
        scratchTail leftBit rawBit headBit baseTail right
  have hdispatch :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopPostPullStart
        rawBoundaryFixedBranchLoopRealBranchTarget
        Tpull Tpull := by
    refine ⟨2, Tpull, ?_, Tape.Equiv.refl Tpull⟩
    simpa [Tpull, markerAwarePullNearestRawBitToHeadMarkerTargetTape] using
      rawBoundaryFixedBranchLoopDescription_run_postPull_dispatch_real
        scratchTail (some leftBit :: baseTail) rawBit headBit right
  have hbranch :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopRealBranchTarget
        rawBoundaryFixedBranchLoopStart
        Tpull
        (emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail (some leftBit :: baseTail) rawBit headBit right) := by
    simpa [Tpull, markerAwarePullNearestRawBitToHeadMarkerTargetTape] using
      rawBoundaryFixedBranchLoopDescription_runsFrom_realBranchTarget
        scratchTail (some leftBit :: baseTail) rawBit headBit right
  exact
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      (Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
        hpull hdispatch)
      hbranch

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
    (scratchTail : Nat) (pref : Word Bool)
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopStart
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) (List.append (pref.reverse.map some) [some false])
        rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail (List.append (pref.reverse.map some) [some false])
        rawBit headBit right) := by
  cases hbase :
      List.append (pref.reverse.map some) [some false] with
  | nil =>
      have hlen := congrArg List.length hbase
      simp at hlen
  | cons head baseTail =>
      cases head with
      | none =>
          cases hrev : pref.reverse <;> simp [hrev] at hbase
      | some leftBit =>
          exact
            rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_real
              scratchTail leftBit rawBit headBit baseTail right

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_markedCellSuffixLeftEdgeScratch_succ3
    (pref cellSuffix : Word Bool) (scratchTail : Nat)
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopStart
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append pref [rawBit]) (scratchTail + 3) cellSuffix
        tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail (rawBit :: cellSuffix) tailFirst tail) := by
  cases cellSuffix with
  | nil =>
      cases rawBit <;> cases tailFirst
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          List.reverse_append, List.map_reverse, List.append_assoc] using
          rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
            scratchTail pref false false tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          List.reverse_append, List.map_reverse, List.append_assoc] using
          rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
            scratchTail pref false true tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          List.reverse_append, List.map_reverse, List.append_assoc] using
          rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
            scratchTail pref true false tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          List.reverse_append, List.map_reverse, List.append_assoc] using
          rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
            scratchTail pref true true tail
  | cons suffixHead suffixRest =>
      cases rawBit <;> cases suffixHead
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          List.reverse_append, List.map_reverse, List.append_assoc] using
          rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
            scratchTail pref false false
            (some true :: some false :: some true ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          List.reverse_append, List.map_reverse, List.append_assoc] using
          rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
            scratchTail pref false false
            (some true :: some true :: some false ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          List.reverse_append, List.map_reverse, List.append_assoc] using
          rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
            scratchTail pref true false
            (some true :: some false :: some true ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          List.reverse_append, List.map_reverse, List.append_assoc] using
          rawBoundaryFixedBranchLoopDescription_runsFrom_headGap_leftMarkedBase
            scratchTail pref true false
            (some true :: some true :: some false ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_pull_boundary
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopPostPullStart
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail cellSuffix tailFirst tail) := by
  let branch :=
    MachineDescription.offsetExitRetargetDescription
      rawBoundaryFixedBranchLoopPullOffset
      markerAwarePullNearestRawBitDescription.halt
      rawBoundaryFixedBranchLoopPostPullStart
      markerAwarePullNearestRawBitDescription
  have hlocal :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        markerAwarePullNearestRawBitDescription
        markerAwarePullNearestRawBitDescription.start
        markerAwarePullNearestRawBitDescription.halt
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail)
        (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
          scratchTail cellSuffix tailFirst tail) := by
    rcases
        markerAwarePullNearestRawBitDescription_haltsFrom_markedCellSuffixLeftEdge_boundary_nonempty
          scratchTail cellSuffix tailFirst tail hnonempty with
      ⟨actual, hactual, hequiv⟩
    rcases runConfig_eq_halt_of_haltsFromTape hactual with ⟨n, hrun⟩
    exact ⟨n, actual, hrun, hequiv⟩
  have hfree :
      markerAwarePullNearestRawBitDescription.TransitionFreeAt
        markerAwarePullNearestRawBitDescription.halt := by
    intro t ht
    exact markerAwarePullNearestRawBitDescription_subroutineReady.right t ht
  have hretarget :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        branch
        rawBoundaryFixedBranchLoopStart
        rawBoundaryFixedBranchLoopPostPullStart
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail)
        (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
          scratchTail cellSuffix tailFirst tail) := by
    have hstart_ne :
        markerAwarePullNearestRawBitDescription.start ≠
          markerAwarePullNearestRawBitDescription.halt := by
      decide
    have h :=
      Structured.MultiTapeLowering.runsFromStateTapeEquiv_offsetExitRetargetDescription
        (offset := rawBoundaryFixedBranchLoopPullOffset)
        (localExit := markerAwarePullNearestRawBitDescription.halt)
        (target := rawBoundaryFixedBranchLoopPostPullStart)
        (by decide)
        hfree
        hlocal
    simpa [branch, rawBoundaryFixedBranchLoopStart, hstart_ne] using h
  have hsubset :
      forall t : TransitionDescription,
        t ∈ branch.transitions ->
          t ∈ rawBoundaryFixedBranchLoopDescription.transitions := by
    intro t ht
    simp [branch, rawBoundaryFixedBranchLoopDescription, ht]
  have hdet : rawBoundaryFixedBranchLoopDescription.Deterministic :=
    rawBoundaryFixedBranchLoopDescription_wellFormed.right.right.right.right
  have hbranchFree :
      branch.TransitionFreeAt rawBoundaryFixedBranchLoopPostPullStart := by
    have hhalt :
        branch.HaltTransitionFree := by
      simpa [branch] using
        MachineDescription.offsetExitRetargetDescription_haltTransitionFree
          (offset := rawBoundaryFixedBranchLoopPullOffset)
          (localExit := markerAwarePullNearestRawBitDescription.halt)
          (target := rawBoundaryFixedBranchLoopPostPullStart)
          (by decide)
          markerAwarePullNearestRawBitDescription
    intro t ht
    simpa [branch, MachineDescription.offsetExitRetargetDescription] using
      hhalt t ht
  exact
    Structured.MultiTapeLowering.StaticDispatcherReaderAssembly.runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hbranchFree hretarget

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_boundaryBranchTarget
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopBoundaryBranchTarget
      rawBoundaryFixedBranchLoopHalt
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
  let branch :=
    MachineDescription.offsetExitRetargetDescription
      rawBoundaryFixedBranchLoopBoundaryBranchOffset
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt
      rawBoundaryFixedBranchLoopHalt
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription
  have hlocal :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription.start
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt
        (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
          scratchTail cellSuffix tailFirst tail)
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
    rcases
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription_haltsFrom_boundaryMarker_nonempty
          scratchTail cellSuffix tailFirst tail hnonempty with
      ⟨actual, hactual, hequiv⟩
    rcases runConfig_eq_halt_of_haltsFromTape hactual with ⟨n, hrun⟩
    exact ⟨n, actual, hrun, hequiv⟩
  have hfree :
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription.TransitionFreeAt
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt := by
    intro t ht
    exact
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription_subroutineReady.right
        t ht
  have hretarget :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        branch
        rawBoundaryFixedBranchLoopBoundaryBranchTarget
        rawBoundaryFixedBranchLoopHalt
        (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
          scratchTail cellSuffix tailFirst tail)
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
    have hstart_ne :
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription.start ≠
          rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt := by
      decide
    have h :=
      Structured.MultiTapeLowering.runsFromStateTapeEquiv_offsetExitRetargetDescription
        (offset := rawBoundaryFixedBranchLoopBoundaryBranchOffset)
        (localExit :=
          rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt)
        (target := rawBoundaryFixedBranchLoopHalt)
        (by decide)
        hfree
        hlocal
    simpa [branch, rawBoundaryFixedBranchLoopBoundaryBranchTarget,
      hstart_ne] using h
  have hsubset :
      forall t : TransitionDescription,
        t ∈ branch.transitions ->
          t ∈ rawBoundaryFixedBranchLoopDescription.transitions := by
    intro t ht
    simp [branch, rawBoundaryFixedBranchLoopDescription, ht]
  have hdet : rawBoundaryFixedBranchLoopDescription.Deterministic :=
    rawBoundaryFixedBranchLoopDescription_wellFormed.right.right.right.right
  have hbranchFree :
      branch.TransitionFreeAt rawBoundaryFixedBranchLoopHalt := by
    have hhalt :
        branch.HaltTransitionFree := by
      simpa [branch] using
        MachineDescription.offsetExitRetargetDescription_haltTransitionFree
          (offset := rawBoundaryFixedBranchLoopBoundaryBranchOffset)
          (localExit :=
            rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt)
          (target := rawBoundaryFixedBranchLoopHalt)
          (by decide)
          rawBoundaryMarkedCellSuffixEraseThenReturnDescription
    intro t ht
    simpa [branch, MachineDescription.offsetExitRetargetDescription] using
      hhalt t ht
  exact
    Structured.MultiTapeLowering.StaticDispatcherReaderAssembly.runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hbranchFree hretarget

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_boundary
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopHalt
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
  let Tin :=
    rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
      scratchTail cellSuffix tailFirst tail
  have hpull :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopStart
        rawBoundaryFixedBranchLoopPostPullStart
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail)
        Tin := by
    simpa [Tin] using
      rawBoundaryFixedBranchLoopDescription_runsFrom_pull_boundary
        scratchTail cellSuffix tailFirst tail hnonempty
  have hdispatch :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopPostPullStart
        rawBoundaryFixedBranchLoopBoundaryBranchTarget
        Tin Tin := by
    cases cellSuffix with
    | nil =>
        exact False.elim (hnonempty rfl)
    | cons cellFirst cellRest =>
        refine ⟨2, Tin, ?_, Tape.Equiv.refl Tin⟩
        cases cellFirst
        · simpa [Tin, rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
            markerAwarePullNearestBoundaryToHeadMarkerTargetTape,
            rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
            preservingCellPassZeroBits, preservingCellPassOneBits,
            List.append_assoc] using
            rawBoundaryFixedBranchLoopDescription_run_postPull_dispatch_boundary
              scratchTail ([] : List (Option Bool)) false false
              (rawBoundaryCellSuffixRightAfterHead
                false cellRest tailFirst tail)
        · simpa [Tin, rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
            markerAwarePullNearestBoundaryToHeadMarkerTargetTape,
            rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
            preservingCellPassZeroBits, preservingCellPassOneBits,
            List.append_assoc] using
            rawBoundaryFixedBranchLoopDescription_run_postPull_dispatch_boundary
              scratchTail ([] : List (Option Bool)) false false
              (rawBoundaryCellSuffixRightAfterHead
                true cellRest tailFirst tail)
  have hbranch :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopBoundaryBranchTarget
        rawBoundaryFixedBranchLoopHalt
        Tin
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
    simpa [Tin] using
      rawBoundaryFixedBranchLoopDescription_runsFrom_boundaryBranchTarget
        scratchTail cellSuffix tailFirst tail hnonempty
  exact
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      (Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
        hpull hdispatch)
      hbranch

theorem rawBoundaryFixedBranchLoopDescription_runsFrom_remaining
    (base remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = finalScratch + 3 * remaining.length) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopStart
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append base remaining) currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        base finalScratch (List.append remaining cellSuffix) tailFirst tail) := by
  induction remaining generalizing base cellSuffix currentScratch finalScratch with
  | nil =>
      have hcurrent : currentScratch = finalScratch := by
        simpa using hscratch
      subst currentScratch
      simpa using
        Structured.MultiTapeLowering.runsFromStateTapeEquiv_refl
          rawBoundaryFixedBranchLoopDescription
          rawBoundaryFixedBranchLoopStart
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
            base finalScratch cellSuffix tailFirst tail)
  | cons bit rest ih =>
      have hrest :
          currentScratch = (finalScratch + 3) + 3 * rest.length := by
        rw [hscratch]
        simp
        lia
      have htail :
          Structured.MultiTapeLowering.RunsFromStateTapeEquiv
            rawBoundaryFixedBranchLoopDescription
            rawBoundaryFixedBranchLoopStart
            rawBoundaryFixedBranchLoopStart
            (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              (List.append base (bit :: rest)) currentScratch cellSuffix
              tailFirst tail)
            (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              (List.append base [bit]) (finalScratch + 3)
              (List.append rest cellSuffix) tailFirst tail) := by
        simpa [List.append_assoc] using
          ih (List.append base [bit]) cellSuffix currentScratch
            (finalScratch + 3) hrest
      have hbit :
          Structured.MultiTapeLowering.RunsFromStateTapeEquiv
            rawBoundaryFixedBranchLoopDescription
            rawBoundaryFixedBranchLoopStart
            rawBoundaryFixedBranchLoopStart
            (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              (List.append base [bit]) (finalScratch + 3)
              (List.append rest cellSuffix) tailFirst tail)
            (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              base finalScratch (List.append (bit :: rest) cellSuffix)
              tailFirst tail) := by
        simpa using
          rawBoundaryFixedBranchLoopDescription_runsFrom_markedCellSuffixLeftEdgeScratch_succ3
            base (List.append rest cellSuffix) finalScratch bit
            tailFirst tail
      exact
        Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
          htail hbit

theorem rawBoundaryFixedBranchLoopDescription_haltsFrom_markedCellSuffix
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    rawBoundaryFixedBranchLoopDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
        tailFirst tail) := by
  have hloop :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopStart
        rawBoundaryFixedBranchLoopStart
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          remaining currentScratch cellSuffix tailFirst tail)
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
          tailFirst tail) := by
    simpa using
      rawBoundaryFixedBranchLoopDescription_runsFrom_remaining
        ([] : Word Bool) remaining cellSuffix currentScratch finalScratch
        tailFirst tail hscratch
  have hboundary :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopStart
        rawBoundaryFixedBranchLoopHalt
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
          tailFirst tail)
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
          tailFirst tail) := by
    simpa using
      rawBoundaryFixedBranchLoopDescription_runsFrom_boundary
        finalScratch (List.append remaining cellSuffix) tailFirst tail
        hnonempty
  have hrun :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryFixedBranchLoopDescription
        rawBoundaryFixedBranchLoopStart
        rawBoundaryFixedBranchLoopHalt
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          remaining currentScratch cellSuffix tailFirst tail)
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
          tailFirst tail) :=
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      hloop hboundary
  exact
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv.toHaltsFromTapeEquiv
      hrun rfl (by rfl)

def rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
    (remaining cellSuffix : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundaryFixedBranchLoopDescription
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      (List.append remaining cellSuffix))

theorem rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_ready
    (remaining cellSuffix : Word Bool) :
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).SubroutineReady := by
  rw [rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      rawBoundaryFixedBranchLoopDescription_subroutineReady
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        (List.append remaining cellSuffix))

theorem rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_markedCellSuffix
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tapeAtCells
        ((encodedLayoutBits (List.append remaining cellSuffix)).reverse.map
          some)
        (some tailFirst :: tail)) := by
  rw [rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
      rawBoundaryFixedBranchLoopDescription_subroutineReady
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        (List.append remaining cellSuffix))
      (rawBoundaryFixedBranchLoopDescription_haltsFrom_markedCellSuffix
        remaining cellSuffix currentScratch finalScratch tailFirst tail
        hscratch hnonempty)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
        ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
        tailFirst tail)
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_equiv
        (List.append remaining cellSuffix) finalScratch tailFirst tail)

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_markedCellSuffixLeftEdgeScratch_singleton
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail =
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref count.length [rawBit] tailFirst tail := by
  cases rawBit <;>
    simp [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, pulledRawBitCellChunkBits]

def rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription
    (rawBit : Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      ([] : Word Bool) [rawBit])

theorem rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_ready
    (rawBit : Bool) :
    (rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription
      rawBit).SubroutineReady := by
  rw [rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
      (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_ready
        ([] : Word Bool) [rawBit])

theorem rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_haltsFrom_sourceTape
    (skipped count : Word Bool)
    (rawBit tailFirst : Bool) (tail : List (Option Bool))
    (hlayout : List.append skipped count = [rawBit]) :
    (rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription
      rawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  rw [rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
      (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_ready
        ([] : Word Bool) [rawBit])
      (rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape
        skipped count ([] : Word Bool) rawBit tailFirst tail
        (by simpa using hlayout))
      (by
        calc
          Tape.move Direction.right
              (Tape.move Direction.left
                (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
                  ([] : Word Bool) count rawBit tailFirst tail)) =
            rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
              ([] : Word Bool) count rawBit tailFirst tail :=
              rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_moveLeftRight
                ([] : Word Bool) count rawBit tailFirst tail
          _ =
            rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              ([] : Word Bool) count.length [rawBit] tailFirst tail :=
              rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_markedCellSuffixLeftEdgeScratch_singleton
                ([] : Word Bool) count rawBit tailFirst tail)
      (by
        rw [rightEdgeTape, hlayout]
        have htail :=
          rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_markedCellSuffix
            ([] : Word Bool) [rawBit] count.length count.length
            tailFirst tail (by simp) (by simp)
        simpa using htail)

theorem rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_one
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool))
    (hlength : (List.append skipped count).length = 1) :
    exists rawBit : Bool,
      List.append skipped count = [rawBit] ∧
        (rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription
          rawBit).HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_singleton_of_length_eq_one
        (List.append skipped count) hlength with
    ⟨rawBit, hlayout⟩
  exact
    ⟨rawBit, hlayout,
      rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_haltsFrom_sourceTape
        skipped count rawBit tailFirst tail hlayout⟩

def rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
    (remaining : Word Bool) (nextRawBit emittedRawBit : Bool) :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining [nextRawBit, emittedRawBit])

theorem rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_ready
    (remaining : Word Bool) (nextRawBit emittedRawBit : Bool) :
    (rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
      remaining nextRawBit emittedRawBit).SubroutineReady := by
  rw [rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
      (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_ready
        remaining [nextRawBit, emittedRawBit])

theorem rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths
    (skipped count remaining : Word Bool)
    (scratchAfterTwo finalScratch : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchAfterTwo + 3)
    (hremainingScratch :
      scratchAfterTwo = finalScratch + 3 * remaining.length) :
    (rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
      remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  have hlayoutFlat :
      List.append skipped count =
        List.append remaining [nextRawBit, emittedRawBit] := by
    simpa [List.append_assoc] using hlayout
  rw [rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
      (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_ready
        remaining [nextRawBit, emittedRawBit])
      (rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_length
        skipped count remaining scratchAfterTwo nextRawBit emittedRawBit
        tailFirst tail hlayout hcount)
      (by
        calc
          Tape.move Direction.right
              (Tape.move Direction.left
                (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
                  remaining scratchAfterTwo nextRawBit emittedRawBit
                  tailFirst tail)) =
            rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
              remaining scratchAfterTwo nextRawBit emittedRawBit
              tailFirst tail :=
              rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
                remaining scratchAfterTwo nextRawBit emittedRawBit
                tailFirst tail
          _ =
            rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              remaining scratchAfterTwo [nextRawBit, emittedRawBit]
              tailFirst tail :=
              rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_markedCellSuffixLeftEdgeScratch_pair
                remaining scratchAfterTwo nextRawBit emittedRawBit
                tailFirst tail)
      (by
        have htail :=
          rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_markedCellSuffix
            remaining [nextRawBit, emittedRawBit] scratchAfterTwo
            finalScratch tailFirst tail hremainingScratch (by simp)
        rw [← hlayoutFlat] at htail
        simpa [rightEdgeTape] using htail)

theorem rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_enough
    (skipped count remaining : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit]) [emittedRawBit])
    (hcountEnough : 3 * remaining.length + 3 <= count.length) :
    exists scratchAfterTwo : Nat, exists finalScratch : Nat,
      count.length = scratchAfterTwo + 3 ∧
        scratchAfterTwo = finalScratch + 3 * remaining.length ∧
          (rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
            remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
            (sourceTape skipped count (some tailFirst :: tail))
            (rightEdgeTape skipped count tailFirst tail) := by
  rcases nat_exists_eq_add_of_le hcountEnough with
    ⟨finalScratch, hlength⟩
  let scratchAfterTwo := finalScratch + 3 * remaining.length
  have hcount : count.length = scratchAfterTwo + 3 := by
    dsimp [scratchAfterTwo]
    rw [hlength]
    lia
  have hremainingScratch :
      scratchAfterTwo = finalScratch + 3 * remaining.length := rfl
  exact
    ⟨scratchAfterTwo, finalScratch, hcount, hremainingScratch,
      rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count remaining scratchAfterTwo finalScratch nextRawBit
        emittedRawBit tailFirst tail hlayout hcount hremainingScratch⟩

theorem firstTwoThenFixedRemaining_toRightEdge_exists_ofLayoutCount
    (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hlayoutLength : 2 <= (List.append skipped count).length)
    (hcountEnough :
      3 * ((List.append skipped count).length - 2) + 3 <=
        count.length) :
    exists remaining : Word Bool, exists nextRawBit : Bool,
      exists emittedRawBit : Bool, exists scratchAfterTwo : Nat,
        exists finalScratch : Nat,
          List.append skipped count =
              List.append (List.append remaining [nextRawBit])
                [emittedRawBit] ∧
            count.length = scratchAfterTwo + 3 ∧
              scratchAfterTwo =
                finalScratch + 3 * remaining.length ∧
                (rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
                  remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
                  (sourceTape skipped count (some tailFirst :: tail))
                  (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_two_of_two_le_length
        (List.append skipped count) hlayoutLength with
    ⟨remaining, nextRawBit, emittedRawBit, hlayoutBase⟩
  have hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit])
          [emittedRawBit] := by
    simpa [List.append_assoc] using hlayoutBase
  have hremainingLength :
      (List.append skipped count).length - 2 = remaining.length := by
    rw [hlayout]
    simp [List.length_append]
  have hcountRemaining :
      3 * remaining.length + 3 <= count.length := by
    rw [← hremainingLength]
    exact hcountEnough
  rcases
      rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_enough
        skipped count remaining nextRawBit emittedRawBit tailFirst tail
        hlayout hcountRemaining with
    ⟨scratchAfterTwo, finalScratch, hcount, hscratch, hroute⟩
  exact
    ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo, finalScratch,
      hlayout, hcount, hscratch, hroute⟩

theorem fixedSourceBranchRouteDescription_exists_haltsFrom_sourceTape_equiv
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool))
    (hbound : sourceBranchRouteCountBound skipped count) :
    exists emitter : MachineDescription,
      emitter.SubroutineReady ∧
        emitter.HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) := by
  rcases hbound with hlenOne | hrest
  · rcases
        rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_one
          skipped count tailFirst tail hlenOne with
      ⟨rawBit, _hlayout, hroute⟩
    exact
      ⟨rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription rawBit,
        rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_ready
          rawBit,
        hroute⟩
  · rcases hrest with hlenTwoAndCount | hlenThreeAndCount
    · rcases hlenTwoAndCount with ⟨hlenTwo, hcount⟩
      have htwo : 2 <= (List.append skipped count).length := by
        rw [hlenTwo]
        decide
      have hcountEnough :
          3 * ((List.append skipped count).length - 2) + 3 <=
            count.length := by
        rw [hlenTwo]
        simpa using hcount
      rcases
          firstTwoThenFixedRemaining_toRightEdge_exists_ofLayoutCount
            skipped count tailFirst tail htwo hcountEnough with
        ⟨remaining, nextRawBit, emittedRawBit, _scratchAfterTwo,
          _finalScratch, _hlayout, _hcount, _hscratch, hroute⟩
      exact
        ⟨rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
            remaining nextRawBit emittedRawBit,
          rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_ready
            remaining nextRawBit emittedRawBit,
          hroute⟩
    · rcases hlenThreeAndCount with ⟨hlayoutLength, hcountEnough⟩
      have hcountEnough' :
          3 * ((List.append skipped count).length - 2) + 3 <=
            count.length := by
        have heq :
            3 * ((List.append skipped count).length - 2) + 3 =
              3 * ((List.append skipped count).length - 3) + 6 := by
          lia
        rw [heq]
        exact hcountEnough
      rcases
          firstTwoThenFixedRemaining_toRightEdge_exists_ofLayoutCount
            skipped count tailFirst tail
            (Nat.le_trans (by decide) hlayoutLength)
            hcountEnough' with
        ⟨remaining, nextRawBit, emittedRawBit, _scratchAfterTwo,
          _finalScratch, _hlayout, _hcount, _hscratch, hroute⟩
      exact
        ⟨rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
            remaining nextRawBit emittedRawBit,
          rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_ready
            remaining nextRawBit emittedRawBit,
          hroute⟩

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
