import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.MarkerAwarePull
import FoC.Computability.Compiler.Structured.Lowering.Dispatcher
import FoC.Computability.Compiler.Structured.Lowering.DispatcherAssembly.Runs

set_option doc.verso true

/-!
# Raw-boundary block migration loop

This module contains the uniform fixed-control loop that migrates a
contiguous nonblank block rightward across a constant-width blank gap to the
live head, one cell per iteration.  Unlike the chunk-emitting fixed branch
loop, each pulled cell lands unchanged at the marker cell immediately left of
the live head, so the gap width is invariant and the loop needs no scratch
budget.  A guard cell installed immediately left of the block drives the
exit branch: when the marker-aware puller reports the guard (a nonblank cell
with a blank left neighbor), the loop erases the guard, walks right across
the gap, and halts on the left edge of the migrated block.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def rawBoundaryBlockMigrationLoopHalt : Nat := 0

def rawBoundaryBlockMigrationLoopPostPullStart : Nat := 1

def rawBoundaryBlockMigrationLoopPostPullReadLeft : Nat := 2

def rawBoundaryBlockMigrationLoopStepBack : Nat := 3

def rawBoundaryBlockMigrationLoopBoundaryErase : Nat := 4

def rawBoundaryBlockMigrationLoopBoundaryWalk : Nat := 5

def rawBoundaryBlockMigrationLoopBoundaryBounce : Nat := 6

def rawBoundaryBlockMigrationLoopPullOffset : Nat := 7

def rawBoundaryBlockMigrationLoopStart : Nat :=
  rawBoundaryBlockMigrationLoopPullOffset +
    markerAwarePullNearestRawBitDescription.start

def rawBoundaryBlockMigrationLoopDescription : MachineDescription where
  stateCount :=
    rawBoundaryBlockMigrationLoopPullOffset +
      markerAwarePullNearestRawBitDescription.stateCount
  start := rawBoundaryBlockMigrationLoopStart
  halt := rawBoundaryBlockMigrationLoopHalt
  transitions :=
    [ transition rawBoundaryBlockMigrationLoopPostPullStart
        (some false) (some false) Direction.left
        rawBoundaryBlockMigrationLoopPostPullReadLeft
    , transition rawBoundaryBlockMigrationLoopPostPullStart
        (some true) (some true) Direction.left
        rawBoundaryBlockMigrationLoopPostPullReadLeft
    , transition rawBoundaryBlockMigrationLoopPostPullReadLeft
        none none Direction.right
        rawBoundaryBlockMigrationLoopBoundaryErase
    , transition rawBoundaryBlockMigrationLoopPostPullReadLeft
        (some false) (some false) Direction.left
        rawBoundaryBlockMigrationLoopStepBack
    , transition rawBoundaryBlockMigrationLoopPostPullReadLeft
        (some true) (some true) Direction.left
        rawBoundaryBlockMigrationLoopStepBack
    , transition rawBoundaryBlockMigrationLoopStepBack
        none none Direction.right
        rawBoundaryBlockMigrationLoopStart
    , transition rawBoundaryBlockMigrationLoopStepBack
        (some false) (some false) Direction.right
        rawBoundaryBlockMigrationLoopStart
    , transition rawBoundaryBlockMigrationLoopStepBack
        (some true) (some true) Direction.right
        rawBoundaryBlockMigrationLoopStart
    , transition rawBoundaryBlockMigrationLoopBoundaryErase
        (some false) none Direction.right
        rawBoundaryBlockMigrationLoopBoundaryWalk
    , transition rawBoundaryBlockMigrationLoopBoundaryErase
        (some true) none Direction.right
        rawBoundaryBlockMigrationLoopBoundaryWalk
    , transition rawBoundaryBlockMigrationLoopBoundaryWalk
        none none Direction.right
        rawBoundaryBlockMigrationLoopBoundaryWalk
    , transition rawBoundaryBlockMigrationLoopBoundaryWalk
        (some false) (some false) Direction.left
        rawBoundaryBlockMigrationLoopBoundaryBounce
    , transition rawBoundaryBlockMigrationLoopBoundaryWalk
        (some true) (some true) Direction.left
        rawBoundaryBlockMigrationLoopBoundaryBounce
    , transition rawBoundaryBlockMigrationLoopBoundaryBounce
        none none Direction.right
        rawBoundaryBlockMigrationLoopHalt ] ++
    (MachineDescription.offsetExitRetargetDescription
      rawBoundaryBlockMigrationLoopPullOffset
      markerAwarePullNearestRawBitDescription.halt
      rawBoundaryBlockMigrationLoopPostPullStart
      markerAwarePullNearestRawBitDescription).transitions

theorem rawBoundaryBlockMigrationLoopDescription_wellFormed :
    rawBoundaryBlockMigrationLoopDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rawBoundaryBlockMigrationLoopDescription.transitions)
      (stateCount := rawBoundaryBlockMigrationLoopDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rawBoundaryBlockMigrationLoopDescription.transitions)
      (by decide)

theorem rawBoundaryBlockMigrationLoopDescription_haltTransitionFree :
    rawBoundaryBlockMigrationLoopDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rawBoundaryBlockMigrationLoopDescription.transitions)
    (state := rawBoundaryBlockMigrationLoopDescription.halt)
    (by decide)

theorem rawBoundaryBlockMigrationLoopDescription_subroutineReady :
    rawBoundaryBlockMigrationLoopDescription.SubroutineReady :=
  ⟨rawBoundaryBlockMigrationLoopDescription_wellFormed,
    rawBoundaryBlockMigrationLoopDescription_haltTransitionFree⟩

/--
Loop invariant tape: the still-pending block bits sit left of a
constant-width blank gap, guarded on their left by a nonblank guard cell
whose own left neighbor is blank; the head rests on the current live head
cell immediately right of the gap.
-/
def rawBoundaryBlockMigrationTape
    (baseTail : List (Option Bool)) (guard : Bool)
    (pending : Word Bool) (gap : Nat)
    (headBit : Bool) (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate gap (none : Option Bool))
      (List.append (pending.reverse.map some)
        (some guard :: none :: baseTail)))
    (some headBit :: right)

/--
Loop endpoint tape: the guard is erased and the head rests on the left edge
of the fully migrated block, with the residual gap blanks to its left.
-/
def rawBoundaryBlockMigrationFinishedTape
    (baseTail : List (Option Bool)) (gap : Nat)
    (headBit : Bool) (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate gap (none : Option Bool))
      (none :: none :: baseTail))
    (some headBit :: right)

theorem rawBoundaryBlockMigrationLoopDescription_run_postPull_real
    (gap : Nat) (leftBit landedBit headBit : Bool)
    (baseTail right : List (Option Bool)) :
    rawBoundaryBlockMigrationLoopDescription.runConfig 3
        { state := rawBoundaryBlockMigrationLoopPostPullStart
          tape :=
            pullNearestRawBitToHeadMarkerTargetTape
              gap (some leftBit :: baseTail) landedBit headBit right } =
      { state := rawBoundaryBlockMigrationLoopStart
        tape :=
          tapeAtCells
            (List.append (List.replicate gap (none : Option Bool))
              (some leftBit :: baseTail))
            (some landedBit :: some headBit :: right) } := by
  cases gap <;> cases leftBit <;> cases landedBit <;> cases headBit <;>
    simp [rawBoundaryBlockMigrationLoopDescription,
      rawBoundaryBlockMigrationLoopHalt,
      rawBoundaryBlockMigrationLoopPostPullStart,
      rawBoundaryBlockMigrationLoopPostPullReadLeft,
      rawBoundaryBlockMigrationLoopStepBack,
      rawBoundaryBlockMigrationLoopBoundaryErase,
      rawBoundaryBlockMigrationLoopBoundaryWalk,
      rawBoundaryBlockMigrationLoopBoundaryBounce,
      rawBoundaryBlockMigrationLoopPullOffset,
      rawBoundaryBlockMigrationLoopStart,
      markerAwarePullNearestRawBitDescription,
      pullNearestRawBitToHeadMarkerTargetTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
      List.replicate_succ]

theorem rawBoundaryBlockMigrationLoopDescription_run_postPull_boundary
    (gap : Nat) (markerBit headBit : Bool)
    (baseTail right : List (Option Bool)) :
    rawBoundaryBlockMigrationLoopDescription.runConfig 2
        { state := rawBoundaryBlockMigrationLoopPostPullStart
          tape :=
            markerAwarePullNearestBoundaryToHeadMarkerTargetTape
              gap baseTail markerBit headBit right } =
      { state := rawBoundaryBlockMigrationLoopBoundaryErase
        tape :=
          markerAwarePullNearestBoundaryToHeadMarkerTargetTape
            gap baseTail markerBit headBit right } := by
  cases markerBit <;> cases headBit <;>
    simp [rawBoundaryBlockMigrationLoopDescription,
      rawBoundaryBlockMigrationLoopHalt,
      rawBoundaryBlockMigrationLoopPostPullStart,
      rawBoundaryBlockMigrationLoopPostPullReadLeft,
      rawBoundaryBlockMigrationLoopStepBack,
      rawBoundaryBlockMigrationLoopBoundaryErase,
      rawBoundaryBlockMigrationLoopBoundaryWalk,
      rawBoundaryBlockMigrationLoopBoundaryBounce,
      rawBoundaryBlockMigrationLoopPullOffset,
      rawBoundaryBlockMigrationLoopStart,
      markerAwarePullNearestBoundaryToHeadMarkerTargetTape, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem replicate_none_append_none_cons_pull
    (n : Nat) (xs : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool)) (none :: xs) =
      none :: List.append (List.replicate n (none : Option Bool)) xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ] using
        congrArg (fun cells => (none : Option Bool) :: cells) ih

private theorem rawBoundaryBlockMigrationLoopDescription_step_boundaryWalk_blank
    (left right : List (Option Bool)) :
    rawBoundaryBlockMigrationLoopDescription.runConfig 1
        { state := rawBoundaryBlockMigrationLoopBoundaryWalk
          tape := tapeAtCells left (none :: right) } =
      { state := rawBoundaryBlockMigrationLoopBoundaryWalk
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [rawBoundaryBlockMigrationLoopDescription,
      rawBoundaryBlockMigrationLoopHalt,
      rawBoundaryBlockMigrationLoopPostPullStart,
      rawBoundaryBlockMigrationLoopPostPullReadLeft,
      rawBoundaryBlockMigrationLoopStepBack,
      rawBoundaryBlockMigrationLoopBoundaryErase,
      rawBoundaryBlockMigrationLoopBoundaryWalk,
      rawBoundaryBlockMigrationLoopBoundaryBounce,
      rawBoundaryBlockMigrationLoopPullOffset,
      rawBoundaryBlockMigrationLoopStart,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryBlockMigrationLoopDescription_run_boundaryBounce
    (headBit : Bool) (left right : List (Option Bool)) :
    rawBoundaryBlockMigrationLoopDescription.runConfig 2
        { state := rawBoundaryBlockMigrationLoopBoundaryWalk
          tape := tapeAtCells (none :: left) (some headBit :: right) } =
      { state := rawBoundaryBlockMigrationLoopHalt
        tape := tapeAtCells (none :: left) (some headBit :: right) } := by
  cases headBit <;>
    simp [rawBoundaryBlockMigrationLoopDescription,
      rawBoundaryBlockMigrationLoopHalt,
      rawBoundaryBlockMigrationLoopPostPullStart,
      rawBoundaryBlockMigrationLoopPostPullReadLeft,
      rawBoundaryBlockMigrationLoopStepBack,
      rawBoundaryBlockMigrationLoopBoundaryErase,
      rawBoundaryBlockMigrationLoopBoundaryWalk,
      rawBoundaryBlockMigrationLoopBoundaryBounce,
      rawBoundaryBlockMigrationLoopPullOffset,
      rawBoundaryBlockMigrationLoopStart,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private theorem rawBoundaryBlockMigrationLoopDescription_run_boundaryWalk
    (gap : Nat) (base : List (Option Bool)) (headBit : Bool)
    (right : List (Option Bool)) :
    rawBoundaryBlockMigrationLoopDescription.runConfig (gap + 2)
        { state := rawBoundaryBlockMigrationLoopBoundaryWalk
          tape :=
            tapeAtCells (none :: base)
              (List.append (List.replicate gap (none : Option Bool))
                (some headBit :: right)) } =
      { state := rawBoundaryBlockMigrationLoopHalt
        tape :=
          tapeAtCells
            (List.append (List.replicate gap (none : Option Bool))
              (none :: base))
            (some headBit :: right) } := by
  induction gap generalizing base with
  | zero =>
      simpa using
        rawBoundaryBlockMigrationLoopDescription_run_boundaryBounce
          headBit base right
  | succ gap ih =>
      rw [show gap + 1 + 2 = 1 + (gap + 2) by lia]
      rw [MachineDescription.runConfig_add]
      rw [show
          List.replicate (gap + 1) (none : Option Bool) =
            none :: List.replicate gap none by
        rw [show gap + 1 = Nat.succ gap by lia]
        rfl]
      rw [show
          List.append
              ((none : Option Bool) :: List.replicate gap none)
              (some headBit :: right) =
            none ::
              List.append (List.replicate gap (none : Option Bool))
                (some headBit :: right) by
        rfl]
      rw [rawBoundaryBlockMigrationLoopDescription_step_boundaryWalk_blank]
      rw [ih (none :: base)]
      rw [replicate_none_append_none_cons_pull gap (none :: base)]
      rw [show
          List.append
              ((none : Option Bool) :: List.replicate gap none)
              (none :: base) =
            none ::
              List.append (List.replicate gap (none : Option Bool))
                (none :: base) by
        rfl]

private theorem rawBoundaryBlockMigrationLoopDescription_step_boundaryErase
    (markerBit : Bool) (left rest : List (Option Bool)) :
    rawBoundaryBlockMigrationLoopDescription.runConfig 1
        { state := rawBoundaryBlockMigrationLoopBoundaryErase
          tape := tapeAtCells left (some markerBit :: rest) } =
      { state := rawBoundaryBlockMigrationLoopBoundaryWalk
        tape := tapeAtCells (none :: left) rest } := by
  cases markerBit <;> cases rest <;>
    simp [rawBoundaryBlockMigrationLoopDescription,
      rawBoundaryBlockMigrationLoopHalt,
      rawBoundaryBlockMigrationLoopPostPullStart,
      rawBoundaryBlockMigrationLoopPostPullReadLeft,
      rawBoundaryBlockMigrationLoopStepBack,
      rawBoundaryBlockMigrationLoopBoundaryErase,
      rawBoundaryBlockMigrationLoopBoundaryWalk,
      rawBoundaryBlockMigrationLoopBoundaryBounce,
      rawBoundaryBlockMigrationLoopPullOffset,
      rawBoundaryBlockMigrationLoopStart,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem rawBoundaryBlockMigrationLoopDescription_run_boundaryFinish
    (gap : Nat) (markerBit headBit : Bool)
    (baseTail right : List (Option Bool)) :
    rawBoundaryBlockMigrationLoopDescription.runConfig (gap + 3)
        { state := rawBoundaryBlockMigrationLoopBoundaryErase
          tape :=
            markerAwarePullNearestBoundaryToHeadMarkerTargetTape
              gap baseTail markerBit headBit right } =
      { state := rawBoundaryBlockMigrationLoopHalt
        tape :=
          rawBoundaryBlockMigrationFinishedTape
            baseTail gap headBit right } := by
  rw [show gap + 3 = 1 + (gap + 2) by lia]
  rw [MachineDescription.runConfig_add]
  rw [markerAwarePullNearestBoundaryToHeadMarkerTargetTape]
  rw [rawBoundaryBlockMigrationLoopDescription_step_boundaryErase]
  rw [rawBoundaryBlockMigrationLoopDescription_run_boundaryWalk
    gap (none :: baseTail) headBit right]
  rw [rawBoundaryBlockMigrationFinishedTape]

theorem rawBoundaryBlockMigrationLoopDescription_runsFrom_pull
    (gap : Nat) (leftBit rawBit headBit : Bool)
    (baseTail right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryBlockMigrationLoopDescription
      rawBoundaryBlockMigrationLoopStart
      rawBoundaryBlockMigrationLoopPostPullStart
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap (some leftBit :: baseTail) rawBit headBit right)
      (markerAwarePullNearestRawBitToHeadMarkerTargetTape
        gap (some leftBit :: baseTail) rawBit headBit right) := by
  let branch :=
    MachineDescription.offsetExitRetargetDescription
      rawBoundaryBlockMigrationLoopPullOffset
      markerAwarePullNearestRawBitDescription.halt
      rawBoundaryBlockMigrationLoopPostPullStart
      markerAwarePullNearestRawBitDescription
  have hlocal :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        markerAwarePullNearestRawBitDescription
        markerAwarePullNearestRawBitDescription.start
        markerAwarePullNearestRawBitDescription.halt
        (markerAwarePullNearestRawBitToHeadMarkerSourceTape
          gap (some leftBit :: baseTail) rawBit headBit right)
        (markerAwarePullNearestRawBitToHeadMarkerTargetTape
          gap (some leftBit :: baseTail) rawBit headBit right) := by
    rcases
        runConfig_eq_halt_of_haltsFromTape
          (markerAwarePullNearestRawBitDescription_haltsFromHeadGap_real
            gap leftBit rawBit headBit baseTail right) with
      ⟨n, hrun⟩
    exact
      ⟨n,
        markerAwarePullNearestRawBitToHeadMarkerTargetTape
          gap (some leftBit :: baseTail) rawBit headBit right,
        hrun,
        Tape.Equiv.refl
          (markerAwarePullNearestRawBitToHeadMarkerTargetTape
            gap (some leftBit :: baseTail) rawBit headBit right)⟩
  have hfree :
      markerAwarePullNearestRawBitDescription.TransitionFreeAt
        markerAwarePullNearestRawBitDescription.halt := by
    intro t ht
    exact markerAwarePullNearestRawBitDescription_subroutineReady.right t ht
  have hretarget :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        branch
        rawBoundaryBlockMigrationLoopStart
        rawBoundaryBlockMigrationLoopPostPullStart
        (markerAwarePullNearestRawBitToHeadMarkerSourceTape
          gap (some leftBit :: baseTail) rawBit headBit right)
        (markerAwarePullNearestRawBitToHeadMarkerTargetTape
          gap (some leftBit :: baseTail) rawBit headBit right) := by
    have hstart_ne :
        markerAwarePullNearestRawBitDescription.start ≠
          markerAwarePullNearestRawBitDescription.halt := by
      decide
    have h :=
      Structured.MultiTapeLowering.runsFromStateTapeEquiv_offsetExitRetargetDescription
        (offset := rawBoundaryBlockMigrationLoopPullOffset)
        (localExit := markerAwarePullNearestRawBitDescription.halt)
        (target := rawBoundaryBlockMigrationLoopPostPullStart)
        (by decide)
        hfree
        hlocal
    simpa [branch, rawBoundaryBlockMigrationLoopStart, hstart_ne] using h
  have hsubset :
      forall t : TransitionDescription,
        t ∈ branch.transitions ->
          t ∈ rawBoundaryBlockMigrationLoopDescription.transitions := by
    intro t ht
    simp [branch, rawBoundaryBlockMigrationLoopDescription, ht]
  have hdet : rawBoundaryBlockMigrationLoopDescription.Deterministic :=
    rawBoundaryBlockMigrationLoopDescription_wellFormed.right.right.right.right
  have hbranchFree :
      branch.TransitionFreeAt
        rawBoundaryBlockMigrationLoopPostPullStart := by
    have hhalt : branch.HaltTransitionFree := by
      simpa [branch] using
        MachineDescription.offsetExitRetargetDescription_haltTransitionFree
          (offset := rawBoundaryBlockMigrationLoopPullOffset)
          (localExit := markerAwarePullNearestRawBitDescription.halt)
          (target := rawBoundaryBlockMigrationLoopPostPullStart)
          (by decide)
          markerAwarePullNearestRawBitDescription
    intro t ht
    simpa [branch, MachineDescription.offsetExitRetargetDescription] using
      hhalt t ht
  exact
    Structured.MultiTapeLowering.StaticDispatcherReaderAssembly.runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hbranchFree hretarget

theorem rawBoundaryBlockMigrationLoopDescription_runsFrom_step
    (gap : Nat) (leftBit rawBit headBit : Bool)
    (baseTail right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryBlockMigrationLoopDescription
      rawBoundaryBlockMigrationLoopStart
      rawBoundaryBlockMigrationLoopStart
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap (some leftBit :: baseTail) rawBit headBit right)
      (tapeAtCells
        (List.append (List.replicate gap (none : Option Bool))
          (some leftBit :: baseTail))
        (some rawBit :: some headBit :: right)) := by
  let Tpull :=
    markerAwarePullNearestRawBitToHeadMarkerTargetTape
      gap (some leftBit :: baseTail) rawBit headBit right
  have hpull :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryBlockMigrationLoopDescription
        rawBoundaryBlockMigrationLoopStart
        rawBoundaryBlockMigrationLoopPostPullStart
        (markerAwarePullNearestRawBitToHeadMarkerSourceTape
          gap (some leftBit :: baseTail) rawBit headBit right)
        Tpull := by
    simpa [Tpull] using
      rawBoundaryBlockMigrationLoopDescription_runsFrom_pull
        gap leftBit rawBit headBit baseTail right
  have hdispatch :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryBlockMigrationLoopDescription
        rawBoundaryBlockMigrationLoopPostPullStart
        rawBoundaryBlockMigrationLoopStart
        Tpull
        (tapeAtCells
          (List.append (List.replicate gap (none : Option Bool))
            (some leftBit :: baseTail))
          (some rawBit :: some headBit :: right)) := by
    refine
      ⟨3,
        tapeAtCells
          (List.append (List.replicate gap (none : Option Bool))
            (some leftBit :: baseTail))
          (some rawBit :: some headBit :: right),
        ?_,
        Tape.Equiv.refl _⟩
    simpa [Tpull, markerAwarePullNearestRawBitToHeadMarkerTargetTape] using
      rawBoundaryBlockMigrationLoopDescription_run_postPull_real
        gap leftBit rawBit headBit baseTail right
  exact
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      hpull hdispatch

private theorem blockMigrationTape_eq_pullSource
    (baseTail : List (Option Bool)) (guard : Bool)
    (pendingInit : Word Bool) (rawBit : Bool) (gap : Nat)
    (headBit : Bool) (right : List (Option Bool)) :
    rawBoundaryBlockMigrationTape baseTail guard
        (List.append pendingInit [rawBit]) gap headBit right =
      markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap
        (List.append (pendingInit.reverse.map some)
          (some guard :: none :: baseTail))
        rawBit headBit right := by
  simp [rawBoundaryBlockMigrationTape,
    markerAwarePullNearestRawBitToHeadMarkerSourceTape,
    pullNearestRawBitToHeadMarkerSourceTape, List.reverse_append]

theorem rawBoundaryBlockMigrationLoopDescription_runsFrom_migrate_bit
    (baseTail : List (Option Bool)) (guard : Bool)
    (pendingInit : Word Bool) (rawBit : Bool) (gap : Nat)
    (headBit : Bool) (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryBlockMigrationLoopDescription
      rawBoundaryBlockMigrationLoopStart
      rawBoundaryBlockMigrationLoopStart
      (rawBoundaryBlockMigrationTape baseTail guard
        (List.append pendingInit [rawBit]) gap headBit right)
      (rawBoundaryBlockMigrationTape baseTail guard
        pendingInit gap rawBit (some headBit :: right)) := by
  rw [blockMigrationTape_eq_pullSource]
  rw [show
      rawBoundaryBlockMigrationTape baseTail guard pendingInit gap
          rawBit (some headBit :: right) =
        tapeAtCells
          (List.append (List.replicate gap (none : Option Bool))
            (List.append (pendingInit.reverse.map some)
              (some guard :: none :: baseTail)))
          (some rawBit :: some headBit :: right) from rfl]
  cases hsplit : List.append (pendingInit.reverse.map some)
      (some guard :: none :: baseTail) with
  | nil =>
      have hlen := congrArg List.length hsplit
      simp at hlen
  | cons headCell restCells =>
      cases headCell with
      | none =>
          exact absurd hsplit (by
            cases hrev : pendingInit.reverse with
            | nil => simp
            | cons bit rest => simp)
      | some leftBit =>
          exact
            rawBoundaryBlockMigrationLoopDescription_runsFrom_step
              gap leftBit rawBit headBit restCells right

theorem rawBoundaryBlockMigrationLoopDescription_runsFrom_migrate_pending
    (baseTail : List (Option Bool)) (guard : Bool)
    (base pending : Word Bool) (gap : Nat)
    (headBit : Bool) (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryBlockMigrationLoopDescription
      rawBoundaryBlockMigrationLoopStart
      rawBoundaryBlockMigrationLoopStart
      (rawBoundaryBlockMigrationTape baseTail guard
        (List.append base pending) gap headBit right)
      (tapeAtCells
        (List.append (List.replicate gap (none : Option Bool))
          (List.append (base.reverse.map some)
            (some guard :: none :: baseTail)))
        (List.append (pending.map some) (some headBit :: right))) := by
  induction pending generalizing base with
  | nil =>
      simpa [rawBoundaryBlockMigrationTape] using
        Structured.MultiTapeLowering.runsFromStateTapeEquiv_refl
          rawBoundaryBlockMigrationLoopDescription
          rawBoundaryBlockMigrationLoopStart
          (rawBoundaryBlockMigrationTape baseTail guard base gap
            headBit right)
  | cons bit rest ih =>
      have hrest :
          Structured.MultiTapeLowering.RunsFromStateTapeEquiv
            rawBoundaryBlockMigrationLoopDescription
            rawBoundaryBlockMigrationLoopStart
            rawBoundaryBlockMigrationLoopStart
            (rawBoundaryBlockMigrationTape baseTail guard
              (List.append base (bit :: rest)) gap headBit right)
            (tapeAtCells
              (List.append (List.replicate gap (none : Option Bool))
                (List.append ((List.append base [bit]).reverse.map some)
                  (some guard :: none :: baseTail)))
              (List.append (rest.map some) (some headBit :: right))) := by
        simpa [List.append_assoc] using
          ih (List.append base [bit])
      have hbit :
          Structured.MultiTapeLowering.RunsFromStateTapeEquiv
            rawBoundaryBlockMigrationLoopDescription
            rawBoundaryBlockMigrationLoopStart
            rawBoundaryBlockMigrationLoopStart
            (tapeAtCells
              (List.append (List.replicate gap (none : Option Bool))
                (List.append ((List.append base [bit]).reverse.map some)
                  (some guard :: none :: baseTail)))
              (List.append (rest.map some) (some headBit :: right)))
            (tapeAtCells
              (List.append (List.replicate gap (none : Option Bool))
                (List.append (base.reverse.map some)
                  (some guard :: none :: baseTail)))
              (some bit ::
                List.append (rest.map some) (some headBit :: right))) := by
        cases rest with
        | nil =>
            simpa [rawBoundaryBlockMigrationTape, List.reverse_append,
              List.map_append, List.append_assoc] using
              rawBoundaryBlockMigrationLoopDescription_runsFrom_migrate_bit
                baseTail guard base bit gap headBit right
        | cons restBit restRest =>
            have h :=
              rawBoundaryBlockMigrationLoopDescription_runsFrom_migrate_bit
                baseTail guard base bit gap restBit
                (List.append (restRest.map some)
                  (some headBit :: right))
            simpa [rawBoundaryBlockMigrationTape, List.reverse_append,
              List.map_append, List.append_assoc] using h
      exact
        Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
          hrest hbit

theorem rawBoundaryBlockMigrationLoopDescription_runsFrom_boundary
    (baseTail : List (Option Bool)) (guard : Bool) (gap : Nat)
    (headBit : Bool) (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryBlockMigrationLoopDescription
      rawBoundaryBlockMigrationLoopStart
      rawBoundaryBlockMigrationLoopHalt
      (rawBoundaryBlockMigrationTape baseTail guard
        ([] : Word Bool) gap headBit right)
      (rawBoundaryBlockMigrationFinishedTape baseTail gap headBit right) := by
  let branch :=
    MachineDescription.offsetExitRetargetDescription
      rawBoundaryBlockMigrationLoopPullOffset
      markerAwarePullNearestRawBitDescription.halt
      rawBoundaryBlockMigrationLoopPostPullStart
      markerAwarePullNearestRawBitDescription
  let Tboundary :=
    markerAwarePullNearestBoundaryToHeadMarkerTargetTape
      gap baseTail guard headBit right
  have hlocal :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        markerAwarePullNearestRawBitDescription
        markerAwarePullNearestRawBitDescription.start
        markerAwarePullNearestRawBitDescription.halt
        (rawBoundaryBlockMigrationTape baseTail guard
          ([] : Word Bool) gap headBit right)
        Tboundary := by
    rcases
        runConfig_eq_halt_of_haltsFromTape
          (markerAwarePullNearestRawBitDescription_haltsFromHeadGap_boundary
            gap baseTail guard headBit right) with
      ⟨n, hrun⟩
    refine ⟨n, Tboundary, ?_, Tape.Equiv.refl Tboundary⟩
    have hsource :
        rawBoundaryBlockMigrationTape baseTail guard
            ([] : Word Bool) gap headBit right =
          markerAwarePullNearestRawBitToHeadMarkerSourceTape
            gap (none :: baseTail) guard headBit right := by
      simp [rawBoundaryBlockMigrationTape,
        markerAwarePullNearestRawBitToHeadMarkerSourceTape,
        pullNearestRawBitToHeadMarkerSourceTape]
    rw [hsource]
    exact hrun
  have hfree :
      markerAwarePullNearestRawBitDescription.TransitionFreeAt
        markerAwarePullNearestRawBitDescription.halt := by
    intro t ht
    exact markerAwarePullNearestRawBitDescription_subroutineReady.right t ht
  have hretarget :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        branch
        rawBoundaryBlockMigrationLoopStart
        rawBoundaryBlockMigrationLoopPostPullStart
        (rawBoundaryBlockMigrationTape baseTail guard
          ([] : Word Bool) gap headBit right)
        Tboundary := by
    have hstart_ne :
        markerAwarePullNearestRawBitDescription.start ≠
          markerAwarePullNearestRawBitDescription.halt := by
      decide
    have h :=
      Structured.MultiTapeLowering.runsFromStateTapeEquiv_offsetExitRetargetDescription
        (offset := rawBoundaryBlockMigrationLoopPullOffset)
        (localExit := markerAwarePullNearestRawBitDescription.halt)
        (target := rawBoundaryBlockMigrationLoopPostPullStart)
        (by decide)
        hfree
        hlocal
    simpa [branch, rawBoundaryBlockMigrationLoopStart, hstart_ne] using h
  have hsubset :
      forall t : TransitionDescription,
        t ∈ branch.transitions ->
          t ∈ rawBoundaryBlockMigrationLoopDescription.transitions := by
    intro t ht
    simp [branch, rawBoundaryBlockMigrationLoopDescription, ht]
  have hdet : rawBoundaryBlockMigrationLoopDescription.Deterministic :=
    rawBoundaryBlockMigrationLoopDescription_wellFormed.right.right.right.right
  have hbranchFree :
      branch.TransitionFreeAt
        rawBoundaryBlockMigrationLoopPostPullStart := by
    have hhalt : branch.HaltTransitionFree := by
      simpa [branch] using
        MachineDescription.offsetExitRetargetDescription_haltTransitionFree
          (offset := rawBoundaryBlockMigrationLoopPullOffset)
          (localExit := markerAwarePullNearestRawBitDescription.halt)
          (target := rawBoundaryBlockMigrationLoopPostPullStart)
          (by decide)
          markerAwarePullNearestRawBitDescription
    intro t ht
    simpa [branch, MachineDescription.offsetExitRetargetDescription] using
      hhalt t ht
  have hpull :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryBlockMigrationLoopDescription
        rawBoundaryBlockMigrationLoopStart
        rawBoundaryBlockMigrationLoopPostPullStart
        (rawBoundaryBlockMigrationTape baseTail guard
          ([] : Word Bool) gap headBit right)
        Tboundary :=
    Structured.MultiTapeLowering.StaticDispatcherReaderAssembly.runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hbranchFree hretarget
  have hdispatch :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryBlockMigrationLoopDescription
        rawBoundaryBlockMigrationLoopPostPullStart
        rawBoundaryBlockMigrationLoopBoundaryErase
        Tboundary Tboundary := by
    refine ⟨2, Tboundary, ?_, Tape.Equiv.refl Tboundary⟩
    simpa [Tboundary] using
      rawBoundaryBlockMigrationLoopDescription_run_postPull_boundary
        gap guard headBit baseTail right
  have hfinish :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryBlockMigrationLoopDescription
        rawBoundaryBlockMigrationLoopBoundaryErase
        rawBoundaryBlockMigrationLoopHalt
        Tboundary
        (rawBoundaryBlockMigrationFinishedTape
          baseTail gap headBit right) := by
    refine
      ⟨gap + 3,
        rawBoundaryBlockMigrationFinishedTape baseTail gap headBit right,
        ?_,
        Tape.Equiv.refl _⟩
    simpa [Tboundary] using
      rawBoundaryBlockMigrationLoopDescription_run_boundaryFinish
        gap guard headBit baseTail right
  exact
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      (Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
        hpull hdispatch)
      hfinish

/--
Headline loop endpoint: from the invariant tape with the full pending block,
the migration loop halts with the guard erased, the block migrated to abut
the previous live head, and the head on the migrated block's left edge.
-/
theorem rawBoundaryBlockMigrationLoopDescription_haltsFrom_blockMigration
    (baseTail : List (Option Bool)) (guard : Bool)
    (pending : Word Bool) (gap : Nat)
    (headBit : Bool) (right : List (Option Bool)) :
    rawBoundaryBlockMigrationLoopDescription.HaltsFromTapeEquiv
      (rawBoundaryBlockMigrationTape baseTail guard pending gap
        headBit right)
      (tapeAtCells
        (List.append (List.replicate gap (none : Option Bool))
          (none :: none :: baseTail))
        (List.append (pending.map some) (some headBit :: right))) := by
  have hloop :=
    rawBoundaryBlockMigrationLoopDescription_runsFrom_migrate_pending
      baseTail guard ([] : Word Bool) pending gap headBit right
  have hboundary :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryBlockMigrationLoopDescription
        rawBoundaryBlockMigrationLoopStart
        rawBoundaryBlockMigrationLoopHalt
        (tapeAtCells
          (List.append (List.replicate gap (none : Option Bool))
            (List.append (([] : Word Bool).reverse.map some)
              (some guard :: none :: baseTail)))
          (List.append (pending.map some) (some headBit :: right)))
        (tapeAtCells
          (List.append (List.replicate gap (none : Option Bool))
            (none :: none :: baseTail))
          (List.append (pending.map some) (some headBit :: right))) := by
    cases pending with
    | nil =>
        simpa [rawBoundaryBlockMigrationTape,
          rawBoundaryBlockMigrationFinishedTape] using
          rawBoundaryBlockMigrationLoopDescription_runsFrom_boundary
            baseTail guard gap headBit right
    | cons bit rest =>
        have h :=
          rawBoundaryBlockMigrationLoopDescription_runsFrom_boundary
            baseTail guard gap bit
            (List.append (rest.map some) (some headBit :: right))
        simpa [rawBoundaryBlockMigrationTape,
          rawBoundaryBlockMigrationFinishedTape, List.append_assoc] using h
  have hrun :=
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      (by simpa using hloop) hboundary
  exact
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv.toHaltsFromTapeEquiv
      hrun rfl (by rfl)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
