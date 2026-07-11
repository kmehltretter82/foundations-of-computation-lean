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
The standalone table takes one further bookkeeping step to a common halt, but
the eventual terminal serializer can retarget the {lit}`done q` rows and retain
the final simulated state without decoding it again.
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

/-- Replace only the head cell of an arbitrary tape context with the hit bit.

In particular, both context lists may carry metadata belonging to later
phases; the loop never moves this head.
-/
def knownStateLoopHitTape (context : Tape Bool) (hit : Bool) : Tape Bool :=
  Tape.write (some hit) context

@[simp] theorem knownStateLoopHitTape_read
    (context : Tape Bool) (hit : Bool) :
    Tape.read (knownStateLoopHitTape context hit) = some hit := by
  rfl

@[simp] theorem writeS_apply_knownStateLoopHitTape
    (context : Tape Bool) (oldHit newHit : Bool) :
    (writeS (some newHit)).apply
        (knownStateLoopHitTape context oldHit) =
      knownStateLoopHitTape context newHit := by
  cases context
  rfl

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

/-- Generated finite typed table for the known-state loop. -/
def knownStateLoopTable (D : MachineDescription) :
    TypedStateTable KnownStateLoopState :=
  TypedStateTable.ofList
    (knownStateLoopStates D)
    (.seed D.start)
    .halt
    (knownStateLoopNext D)
    (seed_mem_knownStateLoopStates (start_mem_fixedStepValues D))
    (halt_mem_knownStateLoopStates D)
    (by intro r0 r1 r2; rfl)
    (knownStateLoopNext_target_mem D)

/-- Standalone structured three-tape description of the known-state loop. -/
def knownStateLoopDescription (D : MachineDescription) : Description :=
  (knownStateLoopTable D).description

theorem knownStateLoopDescription_wellFormed (D : MachineDescription) :
    (knownStateLoopDescription D).WellFormed := by
  exact (knownStateLoopTable D).description_wellFormed
  done

theorem knownStateLoopDescription_haltTransitionFree
    (D : MachineDescription) :
    (knownStateLoopDescription D).HaltTransitionFree := by
  exact (knownStateLoopTable D).description_haltTransitionFree
  done

theorem knownStateLoopDescription_supportsReadWriteRows3
    (D : MachineDescription) :
    SupportsReadWriteRows3 (knownStateLoopDescription D) := by
  exact (knownStateLoopTable D).description_supportsReadWriteRows3
  done

theorem knownStateLoopDescription_subroutineReady
    (D : MachineDescription) :
    (knownStateLoopDescription D).SubroutineReady := by
  exact (knownStateLoopTable D).description_subroutineReady
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

/-- One seed step records whether the input configuration is already halted. -/
theorem knownStateLoopDescription_runConfig_one_seed
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 context : Tape Bool) (hit : Bool) :
    (knownStateLoopDescription D).runConfig 1
        (ThreeTape.config
          ((knownStateLoopTable D).stateId (.seed state))
          T0 T1 (knownStateLoopHitTape context hit)) =
      ThreeTape.config
        ((knownStateLoopTable D).stateId (.loop state))
        T0 T1
        (knownStateLoopHitTape context
          (hit || (state == D.halt))) := by
  have hnext :
      knownStateLoopNext D (.seed state)
          (Tape.read T0) (Tape.read T1)
          (Tape.read (knownStateLoopHitTape context hit)) =
        some
          { target := .loop state
            action0 := keepS
            action1 := keepS
            action2 := writeS (some (hit || (state == D.halt))) } := by
    simp [knownStateLoopNext]
    done
  change
    (knownStateLoopTable D).description.runConfig (0 + 1)
        (ThreeTape.config
          ((knownStateLoopTable D).stateId (.seed state))
          T0 T1 (knownStateLoopHitTape context hit)) = _
  rw [(knownStateLoopTable D).runConfig_succ_config
    (s := .seed state)
    (T0 := T0)
    (T1 := T1)
    (T2 := knownStateLoopHitTape context hit)
    (st :=
      { target := .loop state
        action0 := keepS
        action1 := keepS
        action2 := writeS (some (hit || (state == D.halt))) })
    (seed_mem_knownStateLoopStates hstate) hnext 0]
  simp [Structured.Description.runConfig, keepS, TapeAction.stay,
    TapeAction.apply, HeadMove.apply]
  cases context
  rfl
  done

/-- One unary marker performs exactly one baked-in simulated transition. -/
theorem knownStateLoopDescription_runConfig_one_loop_succ
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 context : Tape Bool) (hit : Bool)
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    (knownStateLoopDescription D).runConfig 1
        (ThreeTape.config
          ((knownStateLoopTable D).stateId (.loop state))
          T0
          (knownStateLoopCounterTape leftRev consumed (remaining + 1)
            rightPadding)
          (knownStateLoopHitTape context hit)) =
      ThreeTape.config
        ((knownStateLoopTable D).stateId
          (.loop (fixedStepTargetState D state (Tape.read T0))))
        ((fixedStepTapeAction D state (Tape.read T0)).apply T0)
        (knownStateLoopCounterTape leftRev (consumed + 1) remaining
          rightPadding)
        (knownStateLoopHitTape context
          (hit ||
            (fixedStepTargetState D state (Tape.read T0) == D.halt))) := by
  have hnext :
      knownStateLoopNext D (.loop state)
          (Tape.read T0)
          (Tape.read
            (knownStateLoopCounterTape leftRev consumed (remaining + 1)
              rightPadding))
          (Tape.read (knownStateLoopHitTape context hit)) =
        some
          { target :=
              .loop (fixedStepTargetState D state (Tape.read T0))
            action0 := fixedStepTapeAction D state (Tape.read T0)
            action1 := eraseR
            action2 := writeS (some
              (hit ||
                (fixedStepTargetState D state (Tape.read T0) == D.halt))) } := by
    simp [knownStateLoopNext]
    done
  change
    (knownStateLoopTable D).description.runConfig (0 + 1)
        (ThreeTape.config
          ((knownStateLoopTable D).stateId (.loop state))
          T0
          (knownStateLoopCounterTape leftRev consumed (remaining + 1)
            rightPadding)
          (knownStateLoopHitTape context hit)) = _
  rw [(knownStateLoopTable D).runConfig_succ_config
    (s := .loop state)
    (T0 := T0)
    (T1 := knownStateLoopCounterTape leftRev consumed (remaining + 1)
      rightPadding)
    (T2 := knownStateLoopHitTape context hit)
    (st :=
      { target := .loop (fixedStepTargetState D state (Tape.read T0))
        action0 := fixedStepTapeAction D state (Tape.read T0)
        action1 := eraseR
        action2 := writeS (some
          (hit ||
            (fixedStepTargetState D state (Tape.read T0) == D.halt))) })
    (loop_mem_knownStateLoopStates hstate) hnext 0]
  simp [Structured.Description.runConfig]
  change
    ThreeTape.config
        ((knownStateLoopTable D).stateId
          (.loop (fixedStepTargetState D state (Tape.read T0))))
        ((fixedStepTapeAction D state (Tape.read T0)).apply T0)
        (eraseR.apply
          (knownStateLoopCounterTape leftRev consumed (remaining + 1)
            rightPadding))
        ((writeS (some
          (hit ||
            (fixedStepTargetState D state (Tape.read T0) == D.halt)))).apply
          (knownStateLoopHitTape context hit)) = _
  rw [eraseR_apply_knownStateLoopCounterTape_succ]
  rw [writeS_apply_knownStateLoopHitTape]
  done

/-- The terminal counter blank exposes the final simulated state. -/
theorem knownStateLoopDescription_runConfig_one_loop_zero
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 context : Tape Bool) (hit : Bool)
    (leftRev : List (Option Bool)) (consumed : Nat)
    (rightPadding : List (Option Bool)) :
    (knownStateLoopDescription D).runConfig 1
        (ThreeTape.config
          ((knownStateLoopTable D).stateId (.loop state))
          T0
          (knownStateLoopCounterTape leftRev consumed 0 rightPadding)
          (knownStateLoopHitTape context hit)) =
      ThreeTape.config
        ((knownStateLoopTable D).stateId (.done state))
        T0
        (knownStateLoopCounterTape leftRev consumed 0 rightPadding)
        (knownStateLoopHitTape context hit) := by
  have hnext :
      knownStateLoopNext D (.loop state)
          (Tape.read T0)
          (Tape.read
            (knownStateLoopCounterTape leftRev consumed 0 rightPadding))
          (Tape.read (knownStateLoopHitTape context hit)) =
        some
          { target := .done state
            action0 := keepS
            action1 := keepS
            action2 := keepS } := by
    simp [knownStateLoopNext]
    done
  change
    (knownStateLoopTable D).description.runConfig (0 + 1)
        (ThreeTape.config
          ((knownStateLoopTable D).stateId (.loop state))
          T0
          (knownStateLoopCounterTape leftRev consumed 0 rightPadding)
          (knownStateLoopHitTape context hit)) = _
  rw [(knownStateLoopTable D).runConfig_succ_config
    (s := .loop state)
    (T0 := T0)
    (T1 := knownStateLoopCounterTape leftRev consumed 0 rightPadding)
    (T2 := knownStateLoopHitTape context hit)
    (st :=
      { target := .done state
        action0 := keepS
        action1 := keepS
        action2 := keepS })
    (loop_mem_knownStateLoopStates hstate) hnext 0]
  simp [Structured.Description.runConfig, keepS, TapeAction.stay,
    TapeAction.apply, HeadMove.apply]
  done

/-- Standalone bookkeeping from an exposed final state to the common halt. -/
theorem knownStateLoopDescription_runConfig_one_done
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 T2 : Tape Bool) :
    (knownStateLoopDescription D).runConfig 1
        (ThreeTape.config
          ((knownStateLoopTable D).stateId (.done state))
          T0 T1 T2) =
      ThreeTape.config
        ((knownStateLoopTable D).stateId .halt)
        T0 T1 T2 := by
  have hnext :
      knownStateLoopNext D (.done state)
          (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some
          { target := .halt
            action0 := keepS
            action1 := keepS
            action2 := keepS } := by
    rfl
  change
    (knownStateLoopTable D).description.runConfig (0 + 1)
        (ThreeTape.config
          ((knownStateLoopTable D).stateId (.done state))
          T0 T1 T2) = _
  rw [(knownStateLoopTable D).runConfig_succ_config
    (s := .done state)
    (T0 := T0) (T1 := T1) (T2 := T2)
    (st :=
      { target := .halt
        action0 := keepS
        action1 := keepS
        action2 := keepS })
    (done_mem_knownStateLoopStates hstate) hnext 0]
  simp [Structured.Description.runConfig, keepS, TapeAction.stay,
    TapeAction.apply, HeadMove.apply]
  done

/-- Exact loop configuration for an executable semantic layout. -/
def knownStateLoopIterationConfig
    (D : MachineDescription) (L : SimulatorLayout)
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) (context : Tape Bool) :
    Structured.Configuration :=
  ThreeTape.config
    ((knownStateLoopTable D).stateId (.loop L.config.state))
    L.config.tape
    (knownStateLoopCounterTape leftRev consumed remaining rightPadding)
    (knownStateLoopHitTape context L.hit)

/-- Running a prefix of the raw counter agrees exactly with executable layout
iteration, including the accumulated hit bit. -/
theorem knownStateLoopDescription_runConfig_loop
    (D : MachineDescription) (L : SimulatorLayout)
    (hstate : L.config.state ∈ fixedStepValues D)
    (leftRev : List (Option Bool)) (consumed steps tail : Nat)
    (rightPadding : List (Option Bool)) (context : Tape Bool) :
    (knownStateLoopDescription D).runConfig steps
        (knownStateLoopIterationConfig D
          (RunConfigEmitterTheory.iterateStep D consumed L)
          leftRev consumed (steps + tail) rightPadding context) =
      knownStateLoopIterationConfig D
        (RunConfigEmitterTheory.iterateStep D (consumed + steps) L)
        leftRev (consumed + steps) tail rightPadding context := by
  induction steps generalizing consumed with
  | zero =>
      simp [knownStateLoopIterationConfig, Structured.Description.runConfig]
      done
  | succ steps ih =>
      rw [show Nat.succ steps + tail = (steps + tail) + 1 by lia]
      rw [show steps + 1 = 1 + steps by lia]
      rw [Structured.Description.runConfig_add]
      have hiterState :=
        iterateStep_config_state_mem_fixedStepValues D L hstate consumed
      unfold knownStateLoopIterationConfig
      rw [knownStateLoopDescription_runConfig_one_loop_succ D
        (RunConfigEmitterTheory.iterateStep D consumed L).config.state
        hiterState
        (RunConfigEmitterTheory.iterateStep D consumed L).config.tape
        context
        (RunConfigEmitterTheory.iterateStep D consumed L).hit
        leftRev consumed (steps + tail) rightPadding]
      rw [fixedStepTargetState_eq_runConfig_one_state]
      rw [fixedStepTapeAction_apply_eq_runConfig_one_tape]
      rw [← RunConfigEmitterTheory.nextConfig_eq_runConfig_one]
      change
        (knownStateLoopDescription D).runConfig steps
            (knownStateLoopIterationConfig D
              (SimulatorLayout.step D
                (RunConfigEmitterTheory.iterateStep D consumed L))
              leftRev (consumed + 1) (steps + tail)
              rightPadding context) = _
      change
        (knownStateLoopDescription D).runConfig steps
            (knownStateLoopIterationConfig D
              (RunConfigEmitterTheory.iterateStep D (consumed + 1) L)
              leftRev (consumed + 1) (steps + tail)
              rightPadding context) = _
      rw [ih (consumed + 1)]
      simp [knownStateLoopIterationConfig, Nat.add_assoc]
      done

/-- Source configuration for a complete semantic simulator-layout run. -/
def knownStateLoopSourceConfig
    (D : MachineDescription) (L : SimulatorLayout)
    (leftRev : List (Option Bool)) (rightPadding : List (Option Bool))
    (context : Tape Bool) : Structured.Configuration :=
  ThreeTape.config
    ((knownStateLoopTable D).stateId (.seed L.config.state))
    L.config.tape
    (knownStateLoopCounterTape leftRev 0 L.stage rightPadding)
    (knownStateLoopHitTape context L.hit)

/-- Exact pre-halt endpoint retaining the final simulated state in control. -/
def knownStateLoopDoneConfig
    (D : MachineDescription) (L : SimulatorLayout)
    (leftRev : List (Option Bool)) (consumed : Nat)
    (rightPadding : List (Option Bool)) (context : Tape Bool) :
    Structured.Configuration :=
  ThreeTape.config
    ((knownStateLoopTable D).stateId (.done L.config.state))
    L.config.tape
    (knownStateLoopCounterTape leftRev consumed 0 rightPadding)
    (knownStateLoopHitTape context L.hit)

/-- The complete known-state loop is exactly {name}`SimulatorLayout.run`.

The first step seeds the stage-zero hit, the next {lit}`L.stage` steps consume
the unary counter, and the final counter-blank step exposes the resulting state
as {lit}`done q`.  Tape-2 context is preserved verbatim around the hit cell.
-/
theorem knownStateLoopDescription_runConfig_to_done
    (D : MachineDescription) (L : SimulatorLayout)
    (hstate : L.config.state ∈ fixedStepValues D)
    (leftRev rightPadding : List (Option Bool))
    (context : Tape Bool) :
    (knownStateLoopDescription D).runConfig (L.stage + 2)
        (knownStateLoopSourceConfig D L leftRev rightPadding context) =
      knownStateLoopDoneConfig D
        (SimulatorLayout.run D L.stage L)
        leftRev L.stage rightPadding context := by
  rw [show L.stage + 2 = 1 + L.stage + 1 by lia]
  rw [Structured.Description.runConfig_add]
  rw [Structured.Description.runConfig_add]
  unfold knownStateLoopSourceConfig
  rw [knownStateLoopDescription_runConfig_one_seed D
    L.config.state hstate L.config.tape
    (knownStateLoopCounterTape leftRev 0 L.stage rightPadding)
    context L.hit]
  change
    (knownStateLoopDescription D).runConfig 1
      ((knownStateLoopDescription D).runConfig L.stage
        (knownStateLoopIterationConfig D
          (RunConfigEmitterTheory.seedHit D L)
          leftRev 0 (L.stage + 0) rightPadding context)) = _
  have hseedState :
      (RunConfigEmitterTheory.seedHit D L).config.state ∈
        fixedStepValues D := by
    simpa [RunConfigEmitterTheory.seedHit] using hstate
    done
  change
    (knownStateLoopDescription D).runConfig 1
      ((knownStateLoopDescription D).runConfig L.stage
        (knownStateLoopIterationConfig D
          (RunConfigEmitterTheory.iterateStep D 0
            (RunConfigEmitterTheory.seedHit D L))
          leftRev 0 (L.stage + 0) rightPadding context)) = _
  rw [knownStateLoopDescription_runConfig_loop D
    (RunConfigEmitterTheory.seedHit D L) hseedState
    leftRev 0 L.stage 0 rightPadding context]
  simp only [Nat.zero_add]
  rw [RunConfigEmitterTheory.iterateStep_seedHit_eq_run]
  have hfinalState :
      (SimulatorLayout.run D L.stage L).config.state ∈
        fixedStepValues D := by
    rw [← RunConfigEmitterTheory.iterateStep_seedHit_eq_run]
    exact iterateStep_config_state_mem_fixedStepValues D
      (RunConfigEmitterTheory.seedHit D L) hseedState L.stage
    done
  unfold knownStateLoopIterationConfig knownStateLoopDoneConfig
  exact knownStateLoopDescription_runConfig_one_loop_zero D
    (SimulatorLayout.run D L.stage L).config.state hfinalState
    (SimulatorLayout.run D L.stage L).config.tape context
    (SimulatorLayout.run D L.stage L).hit
    leftRev L.stage rightPadding
  done

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
