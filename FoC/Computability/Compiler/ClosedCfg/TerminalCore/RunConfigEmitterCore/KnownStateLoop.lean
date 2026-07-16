import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FixedStep
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterTheory.Iteration

set_option doc.verso true

/-!
# Known-state fixed-description run loop

This module turns the one-step fixed-description microkernel into a finite
unary-counter loop.  The simulated tape stays live on logical tape 0, logical
tape 1 contains a raw block of unary {lit}`true` cells, and the head cell of
logical tape 2 contains the accumulated halt-hit bit.  The simulated state is
kept in typed finite control and is therefore restricted to
{lit}`fixedStepValues`.

The explicit {lit}`done q` control state is the important composition seam.
The integrated dispatcher consumes this transition kernel directly, retains
the final simulated state without decoding it again, and continues from
{lit}`done q` without a separate halting boundary.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-!
## Exact logical tapes
-/

/-- A raw unary counter with explicit consumed blanks and terminal padding.

The head is on the first remaining marker, or on the terminal blank when no
marker remains.  Keeping the original left context and right padding explicit
makes the loop usable inside a larger field layout.
-/
def knownStateLoopCounterTape
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate consumed (none : Option Bool)) leftRev)
    (List.append (List.replicate remaining (some true : Option Bool))
      (none :: rightPadding))

@[simp] theorem knownStateLoopCounterTape_read_zero
    (leftRev : List (Option Bool)) (consumed : Nat)
    (rightPadding : List (Option Bool)) :
    Tape.read
        (knownStateLoopCounterTape leftRev consumed 0 rightPadding) = none := by
  simp [knownStateLoopCounterTape, tapeAtCells, Tape.read]
  done

@[simp] theorem knownStateLoopCounterTape_read_succ
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    Tape.read
        (knownStateLoopCounterTape leftRev consumed (remaining + 1)
          rightPadding) = some true := by
  simp [knownStateLoopCounterTape, tapeAtCells, Tape.read,
    List.replicate_succ]
  done

@[simp] theorem eraseR_apply_knownStateLoopCounterTape_succ
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    eraseR.apply
        (knownStateLoopCounterTape leftRev consumed (remaining + 1)
          rightPadding) =
      knownStateLoopCounterTape leftRev (consumed + 1) remaining
        rightPadding := by
  cases remaining <;> simp [knownStateLoopCounterTape, eraseR, writeR, TapeAction.apply,
    HeadMove.apply, Tape.write, Tape.move, Tape.moveRight, tapeAtCells,
    List.replicate_succ]
  done

/-!
## Typed finite-control table
-/

/-- Typed states of the known-state loop. -/
inductive KnownStateLoopState where
  | seed (state : Nat)
  | loop (state : Nat)
  | done (state : Nat)
  | halt
deriving DecidableEq, Repr

/-- Finite typed-state enumeration generated from the baked description. -/
def knownStateLoopStates (D : MachineDescription) :
    List KnownStateLoopState :=
  List.append
    ((fixedStepValues D).map KnownStateLoopState.seed)
    (List.append
      ((fixedStepValues D).map KnownStateLoopState.loop)
      (List.append
        ((fixedStepValues D).map KnownStateLoopState.done)
        [KnownStateLoopState.halt]))

theorem seed_mem_knownStateLoopStates
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    KnownStateLoopState.seed state ∈ knownStateLoopStates D := by
  simp [knownStateLoopStates, hstate]
  done

theorem loop_mem_knownStateLoopStates
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    KnownStateLoopState.loop state ∈ knownStateLoopStates D := by
  simp [knownStateLoopStates, hstate]
  done

theorem done_mem_knownStateLoopStates
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    KnownStateLoopState.done state ∈ knownStateLoopStates D := by
  simp [knownStateLoopStates, hstate]
  done

theorem halt_mem_knownStateLoopStates (D : MachineDescription) :
    KnownStateLoopState.halt ∈ knownStateLoopStates D := by
  simp [knownStateLoopStates]
  done

theorem fixedStepValues_of_seed_mem
    {D : MachineDescription} {state : Nat}
    (hstate :
      KnownStateLoopState.seed state ∈ knownStateLoopStates D) :
    state ∈ fixedStepValues D := by
  simpa [knownStateLoopStates] using hstate
  done

theorem fixedStepValues_of_loop_mem
    {D : MachineDescription} {state : Nat}
    (hstate :
      KnownStateLoopState.loop state ∈ knownStateLoopStates D) :
    state ∈ fixedStepValues D := by
  simpa [knownStateLoopStates] using hstate
  done

theorem fixedStepValues_of_knownStateLoopDone_mem
    {D : MachineDescription} {state : Nat}
    (hstate :
      KnownStateLoopState.done state ∈ knownStateLoopStates D) :
    state ∈ fixedStepValues D := by
  simpa [knownStateLoopStates] using hstate
  done

/-- Initialize the hit bit, execute one simulated step per unary marker, and
expose the final simulated state at a typed done control. -/
def knownStateLoopNext (D : MachineDescription) :
    KnownStateLoopState -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep KnownStateLoopState)
  | .seed state, _, _, some hit =>
      some
        { target := .loop state
          action0 := keepS
          action1 := keepS
          action2 := writeS (some (hit || (state == D.halt))) }
  | .loop state, read0, some true, some hit =>
      let target := fixedStepTargetState D state read0
      some
        { target := .loop target
          action0 := fixedStepTapeAction D state read0
          action1 := eraseR
          action2 := writeS (some (hit || (target == D.halt))) }
  | .loop state, _, none, _ =>
      some
        { target := .done state
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | .done _, _, _, _ =>
      some
        { target := .halt
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | _, _, _, _ => none

theorem knownStateLoopNext_target_mem (D : MachineDescription) :
    forall s : KnownStateLoopState, s ∈ knownStateLoopStates D ->
      forall (r0 r1 r2 : Option Bool)
        (st : TypedStep KnownStateLoopState),
        knownStateLoopNext D s r0 r1 r2 = some st ->
          st.target ∈ knownStateLoopStates D := by
  intro s hs r0 r1 r2 st hnext
  cases s with
  | seed state =>
      cases r2 with
      | none => simp [knownStateLoopNext] at hnext
      | some hit =>
          simp only [knownStateLoopNext] at hnext
          cases hnext
          exact loop_mem_knownStateLoopStates
            (fixedStepValues_of_seed_mem hs)
  | loop state =>
      cases r1 with
      | none =>
          simp only [knownStateLoopNext] at hnext
          cases hnext
          exact done_mem_knownStateLoopStates
            (fixedStepValues_of_loop_mem hs)
      | some counter =>
          cases counter with
          | false => simp [knownStateLoopNext] at hnext
          | true =>
              cases r2 with
              | none => simp [knownStateLoopNext] at hnext
              | some hit =>
                  simp only [knownStateLoopNext] at hnext
                  cases hnext
                  exact loop_mem_knownStateLoopStates
                    (fixedStepTargetState_mem
                      (fixedStepValues_of_loop_mem hs) r0)
  | done state =>
      simp only [knownStateLoopNext] at hnext
      cases hnext
      exact halt_mem_knownStateLoopStates D
  | halt =>
      simp [knownStateLoopNext] at hnext
  done

/-!
## Exact typed execution
-/

/-- Every executable iteration stays in the finite set of baked-in states. -/
theorem iterateStep_config_state_mem_fixedStepValues
    (D : MachineDescription) (L : SimulatorLayout)
    (hstate : L.config.state ∈ fixedStepValues D) :
    forall n : Nat,
      (RunConfigEmitterTheory.iterateStep D n L).config.state ∈
        fixedStepValues D := by
  intro n
  induction n with
  | zero =>
      simpa [RunConfigEmitterTheory.iterateStep] using hstate
      done
  | succ n ih =>
      have htarget :=
        fixedStepTargetState_mem ih
          (Tape.read
            (RunConfigEmitterTheory.iterateStep D n L).config.tape)
      simpa [RunConfigEmitterTheory.iterateStep, SimulatorLayout.step,
        RunConfigEmitterTheory.nextConfig_eq_runConfig_one,
        fixedStepTargetState_eq_runConfig_one_state] using htarget
      done

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
