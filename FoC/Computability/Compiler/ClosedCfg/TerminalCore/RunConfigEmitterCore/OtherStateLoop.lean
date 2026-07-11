import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.StateClassifier

set_option doc.verso true

/-!
# Unmatched-state unary loop

An arbitrary configuration state not mentioned by the fixed description cannot
be stored in finite control.  The state classifier leaves that raw state
encoding on tape and selects one generic {lit}`other` branch.  This module is
the physical counter loop for that branch: logical tape 1 contains a raw unary
counter, while logical tapes 0 and 2 are preserved exactly.

Because an unmatched state has no fixed-description transition and cannot be
the description halt state, consuming the counter without changing the
configuration or accumulated hit bit is exactly the bounded simulator
semantics.
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

/-- Raw unary counter with explicit consumed cells and surrounding context.

The head is on the first remaining {lit}`true` marker, or on the terminal
blank when no marker remains. -/
def otherStateLoopCounterTape
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate consumed (none : Option Bool)) leftRev)
    (List.append (List.replicate remaining (some true : Option Bool))
      (none :: rightPadding))

@[simp] theorem otherStateLoopCounterTape_read_zero
    (leftRev : List (Option Bool)) (consumed : Nat)
    (rightPadding : List (Option Bool)) :
    Tape.read
        (otherStateLoopCounterTape leftRev consumed 0 rightPadding) = none := by
  simp [otherStateLoopCounterTape, tapeAtCells, Tape.read]

@[simp] theorem otherStateLoopCounterTape_read_succ
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    Tape.read
        (otherStateLoopCounterTape leftRev consumed (remaining + 1)
          rightPadding) = some true := by
  simp [otherStateLoopCounterTape, tapeAtCells, Tape.read,
    List.replicate_succ]

@[simp] theorem eraseR_apply_otherStateLoopCounterTape_succ
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    eraseR.apply
        (otherStateLoopCounterTape leftRev consumed (remaining + 1)
          rightPadding) =
      otherStateLoopCounterTape leftRev (consumed + 1) remaining
        rightPadding := by
  cases remaining <;>
    simp [otherStateLoopCounterTape, eraseR, writeR, TapeAction.apply,
      HeadMove.apply, Tape.write, Tape.move, Tape.moveRight, tapeAtCells,
      List.replicate_succ]

/-!
## Typed finite-control table
-/

/-- Typed states of the unmatched-state counter loop. -/
inductive OtherStateLoopState where
  | loop
  | done
  | halt
deriving DecidableEq, Repr

/-- Complete finite state enumeration. -/
def otherStateLoopStates : List OtherStateLoopState :=
  [.loop, .done, .halt]

theorem loop_mem_otherStateLoopStates :
    OtherStateLoopState.loop ∈ otherStateLoopStates := by
  simp [otherStateLoopStates]

theorem done_mem_otherStateLoopStates :
    OtherStateLoopState.done ∈ otherStateLoopStates := by
  simp [otherStateLoopStates]

theorem halt_mem_otherStateLoopStates :
    OtherStateLoopState.halt ∈ otherStateLoopStates := by
  simp [otherStateLoopStates]

/-- Erase one unary marker, expose the terminal blank as {lit}`done`, then
enter the common halt state. -/
def otherStateLoopNext :
    OtherStateLoopState -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep OtherStateLoopState)
  | .loop, _, some true, _ =>
      some
        { target := .loop
          action0 := keepS
          action1 := eraseR
          action2 := keepS }
  | .loop, _, none, _ =>
      some
        { target := .done
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | .done, _, _, _ =>
      some
        { target := .halt
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | _, _, _, _ => none

theorem otherStateLoopNext_target_mem :
    forall s : OtherStateLoopState, s ∈ otherStateLoopStates ->
      forall (r0 r1 r2 : Option Bool)
        (st : TypedStep OtherStateLoopState),
        otherStateLoopNext s r0 r1 r2 = some st ->
          st.target ∈ otherStateLoopStates := by
  intro s hs r0 r1 r2 st hnext
  cases s with
  | loop =>
      cases r1 with
      | none =>
          cases hnext
          exact done_mem_otherStateLoopStates
      | some marker =>
          cases marker with
          | false => simp [otherStateLoopNext] at hnext
          | true =>
              cases hnext
              exact loop_mem_otherStateLoopStates
  | done =>
      cases hnext
      exact halt_mem_otherStateLoopStates
  | halt =>
      simp [otherStateLoopNext] at hnext

/-- Generated typed table for the unmatched-state loop. -/
def otherStateLoopTable : TypedStateTable OtherStateLoopState :=
  TypedStateTable.ofList
    otherStateLoopStates
    .loop
    .halt
    otherStateLoopNext
    loop_mem_otherStateLoopStates
    halt_mem_otherStateLoopStates
    (by intro r0 r1 r2; rfl)
    otherStateLoopNext_target_mem

/-- Standalone structured three-tape unmatched-state loop. -/
def otherStateLoopDescription : Description :=
  otherStateLoopTable.description

theorem otherStateLoopDescription_wellFormed :
    otherStateLoopDescription.WellFormed := by
  exact otherStateLoopTable.description_wellFormed

theorem otherStateLoopDescription_haltTransitionFree :
    otherStateLoopDescription.HaltTransitionFree := by
  exact otherStateLoopTable.description_haltTransitionFree

theorem otherStateLoopDescription_supportsReadWriteRows3 :
    SupportsReadWriteRows3 otherStateLoopDescription := by
  exact otherStateLoopTable.description_supportsReadWriteRows3

theorem otherStateLoopDescription_subroutineReady :
    otherStateLoopDescription.SubroutineReady := by
  exact otherStateLoopTable.description_subroutineReady

/-!
## Exact typed execution
-/

/-- One remaining unary marker is erased while the other logical tapes are
preserved exactly. -/
theorem otherStateLoopDescription_stepConfig_loop_succ
    (T0 T2 : Tape Bool)
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    otherStateLoopDescription.stepConfig
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev consumed (remaining + 1)
            rightPadding)
          T2) =
      some
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev (consumed + 1) remaining
            rightPadding)
          T2) := by
  unfold otherStateLoopDescription
  rw [otherStateLoopTable.stepConfig_config
    loop_mem_otherStateLoopStates]
  change
    (otherStateLoopNext .loop
      (Tape.read T0)
      (Tape.read
        (otherStateLoopCounterTape leftRev consumed (remaining + 1)
          rightPadding))
      (Tape.read T2)).map _ = _
  rw [otherStateLoopCounterTape_read_succ]
  simp only [otherStateLoopNext, Option.map_some]
  rw [eraseR_apply_otherStateLoopCounterTape_succ]
  simp [keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]

/-- The terminal counter blank exposes the explicit pre-halt state. -/
theorem otherStateLoopDescription_stepConfig_loop_zero
    (T0 T2 : Tape Bool)
    (leftRev : List (Option Bool)) (consumed : Nat)
    (rightPadding : List (Option Bool)) :
    otherStateLoopDescription.stepConfig
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev consumed 0 rightPadding)
          T2) =
      some
        (ThreeTape.config
          (otherStateLoopTable.stateId .done)
          T0
          (otherStateLoopCounterTape leftRev consumed 0 rightPadding)
          T2) := by
  unfold otherStateLoopDescription
  rw [otherStateLoopTable.stepConfig_config
    loop_mem_otherStateLoopStates]
  change
    (otherStateLoopNext .loop
      (Tape.read T0)
      (Tape.read
        (otherStateLoopCounterTape leftRev consumed 0 rightPadding))
      (Tape.read T2)).map _ = _
  rw [otherStateLoopCounterTape_read_zero]
  simp [otherStateLoopNext, keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply]

/-- Standalone bookkeeping enters the common halt state without changing any
logical tape. -/
theorem otherStateLoopDescription_stepConfig_done
    (T0 T1 T2 : Tape Bool) :
    otherStateLoopDescription.stepConfig
        (ThreeTape.config
          (otherStateLoopTable.stateId .done) T0 T1 T2) =
      some
        (ThreeTape.config
          (otherStateLoopTable.stateId .halt) T0 T1 T2) := by
  unfold otherStateLoopDescription
  rw [otherStateLoopTable.stepConfig_config
    done_mem_otherStateLoopStates]
  change
    (otherStateLoopNext .done
      (Tape.read T0) (Tape.read T1) (Tape.read T2)).map _ = _
  simp [otherStateLoopNext, keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply]

theorem otherStateLoopDescription_runConfig_one_loop_succ
    (T0 T2 : Tape Bool)
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    otherStateLoopDescription.runConfig 1
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev consumed (remaining + 1)
            rightPadding)
          T2) =
      ThreeTape.config
        (otherStateLoopTable.stateId .loop)
        T0
        (otherStateLoopCounterTape leftRev (consumed + 1) remaining
          rightPadding)
        T2 := by
  change
    (match
      otherStateLoopDescription.stepConfig
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev consumed (remaining + 1)
            rightPadding)
          T2) with
    | none => _
    | some next => otherStateLoopDescription.runConfig 0 next) = _
  rw [otherStateLoopDescription_stepConfig_loop_succ]
  rfl

theorem otherStateLoopDescription_runConfig_one_loop_zero
    (T0 T2 : Tape Bool)
    (leftRev : List (Option Bool)) (consumed : Nat)
    (rightPadding : List (Option Bool)) :
    otherStateLoopDescription.runConfig 1
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev consumed 0 rightPadding)
          T2) =
      ThreeTape.config
        (otherStateLoopTable.stateId .done)
        T0
        (otherStateLoopCounterTape leftRev consumed 0 rightPadding)
        T2 := by
  change
    (match
      otherStateLoopDescription.stepConfig
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev consumed 0 rightPadding)
          T2) with
    | none => _
    | some next => otherStateLoopDescription.runConfig 0 next) = _
  rw [otherStateLoopDescription_stepConfig_loop_zero]
  rfl

theorem otherStateLoopDescription_runConfig_one_done
    (T0 T1 T2 : Tape Bool) :
    otherStateLoopDescription.runConfig 1
        (ThreeTape.config
          (otherStateLoopTable.stateId .done) T0 T1 T2) =
      ThreeTape.config
        (otherStateLoopTable.stateId .halt) T0 T1 T2 := by
  change
    (match
      otherStateLoopDescription.stepConfig
        (ThreeTape.config
          (otherStateLoopTable.stateId .done) T0 T1 T2) with
    | none => _
    | some next => otherStateLoopDescription.runConfig 0 next) = _
  rw [otherStateLoopDescription_stepConfig_done]
  rfl

/-- Running a prefix of the unary counter erases exactly that many markers and
preserves both non-counter logical tapes. -/
theorem otherStateLoopDescription_runConfig_markers
    (T0 T2 : Tape Bool)
    (leftRev : List (Option Bool)) (consumed markers tail : Nat)
    (rightPadding : List (Option Bool)) :
    otherStateLoopDescription.runConfig markers
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev consumed (markers + tail)
            rightPadding)
          T2) =
      ThreeTape.config
        (otherStateLoopTable.stateId .loop)
        T0
        (otherStateLoopCounterTape leftRev (consumed + markers) tail
          rightPadding)
        T2 := by
  induction markers generalizing consumed with
  | zero =>
      simp [Description.runConfig]
  | succ markers ih =>
      rw [show Nat.succ markers + tail = (markers + tail) + 1 by lia]
      rw [show markers + 1 = 1 + markers by lia]
      rw [Description.runConfig_add]
      rw [otherStateLoopDescription_runConfig_one_loop_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (consumed + 1)

/-- An exact block of {lit}`markers` is consumed and the following blank
reaches the explicit {lit}`done` control state. -/
theorem otherStateLoopDescription_runConfig_to_done
    (T0 T2 : Tape Bool)
    (leftRev : List (Option Bool)) (markers : Nat)
    (rightPadding : List (Option Bool)) :
    otherStateLoopDescription.runConfig (markers + 1)
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev 0 markers rightPadding)
          T2) =
      ThreeTape.config
        (otherStateLoopTable.stateId .done)
        T0
        (otherStateLoopCounterTape leftRev markers 0 rightPadding)
        T2 := by
  rw [Description.runConfig_add]
  have hmarkers :=
    otherStateLoopDescription_runConfig_markers
      T0 T2 leftRev 0 markers 0 rightPadding
  simp only [Nat.add_zero, Nat.zero_add] at hmarkers
  rw [hmarkers]
  exact otherStateLoopDescription_runConfig_one_loop_zero
    T0 T2 leftRev markers rightPadding

/-- Standalone exact run through the common halt state. -/
theorem otherStateLoopDescription_runConfig_to_halt
    (T0 T2 : Tape Bool)
    (leftRev : List (Option Bool)) (markers : Nat)
    (rightPadding : List (Option Bool)) :
    otherStateLoopDescription.runConfig (markers + 2)
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev 0 markers rightPadding)
          T2) =
      ThreeTape.config
        (otherStateLoopTable.stateId .halt)
        T0
        (otherStateLoopCounterTape leftRev markers 0 rightPadding)
        T2 := by
  rw [show markers + 2 = (markers + 1) + 1 by lia]
  rw [Description.runConfig_add]
  rw [otherStateLoopDescription_runConfig_to_done]
  exact otherStateLoopDescription_runConfig_one_done _ _ _

/-- Standalone structured halting contract for the exact counter family. -/
theorem otherStateLoopDescription_haltsWithTapes
    (T0 T2 : Tape Bool)
    (leftRev : List (Option Bool)) (markers : Nat)
    (rightPadding : List (Option Bool)) :
    otherStateLoopDescription.HaltsWithTapes
        (ThreeTape.config otherStateLoopDescription.start
          T0
          (otherStateLoopCounterTape leftRev 0 markers rightPadding)
          T2)
        [ T0
        , otherStateLoopCounterTape leftRev markers 0 rightPadding
        , T2 ] := by
  refine ⟨markers + 2, ?_⟩
  change
    otherStateLoopDescription.runConfig (markers + 2)
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          T0
          (otherStateLoopCounterTape leftRev 0 markers rightPadding)
          T2) =
      ThreeTape.config
        (otherStateLoopTable.stateId .halt)
        T0
        (otherStateLoopCounterTape leftRev markers 0 rightPadding)
        T2
  exact otherStateLoopDescription_runConfig_to_halt
    T0 T2 leftRev markers rightPadding

/-!
## Unmatched-state simulator semantics
-/

/-- An unmatched state cannot be the fixed description's halt state, since
the halt value is explicitly included in the finite classification list. -/
theorem state_ne_halt_of_classifyState_other
    {D : MachineDescription} {state : Nat}
    (hclass : classifyState D state = StateClass.other) :
    state ≠ D.halt := by
  intro hhalt
  have hnot : state ∉ fixedStepValues D :=
    (classifyState_eq_other_iff D state).mp hclass
  apply hnot
  rw [hhalt]
  exact halt_mem_fixedStepValues D

theorem haltedFromConfigInBool_eq_false_of_classifyState_other
    {D : MachineDescription} {state : Nat}
    (hclass : classifyState D state = StateClass.other)
    (T : Tape Bool) (fuel : Nat) :
    SimulatorLayout.haltedFromConfigInBool D
        { state := state, tape := T } fuel = false := by
  have hrun :=
    runConfig_eq_self_of_classifyState_other hclass T fuel
  have hne := state_ne_halt_of_classifyState_other hclass
  simp [SimulatorLayout.haltedFromConfigInBool, hrun, hne]

/-- No bounded prefix starting at an unmatched state can set the accumulated
halt-hit bit. -/
theorem hitsFromConfigByBool_eq_false_of_classifyState_other
    {D : MachineDescription} {state : Nat}
    (hclass : classifyState D state = StateClass.other)
    (T : Tape Bool) (fuel : Nat) :
    SimulatorLayout.hitsFromConfigByBool D
        { state := state, tape := T } fuel = false := by
  induction fuel with
  | zero =>
      exact
        haltedFromConfigInBool_eq_false_of_classifyState_other
          hclass T 0
  | succ fuel ih =>
      simp only [SimulatorLayout.hitsFromConfigByBool]
      rw [ih]
      rw [haltedFromConfigInBool_eq_false_of_classifyState_other
        hclass T (fuel + 1)]
      rfl

/-- The complete semantic simulator layout is unchanged on the generic branch:
input and stage are definitionally preserved, the configuration stutters, and
the accumulated hit bit remains unchanged. -/
theorem simulatorLayout_run_eq_self_of_classifyState_other
    (D : MachineDescription) (L : SimulatorLayout) (fuel : Nat)
    (hclass : classifyState D L.config.state = StateClass.other) :
    SimulatorLayout.run D fuel L = L := by
  rcases L with ⟨input, stage, config, hit⟩
  rcases config with ⟨state, T⟩
  change
    ({ input := input
       stage := stage
       config := D.runConfig fuel { state := state, tape := T }
       hit := hit ||
        SimulatorLayout.hitsFromConfigByBool D
          { state := state, tape := T } fuel } : SimulatorLayout) =
      { input := input
        stage := stage
        config := { state := state, tape := T }
        hit := hit }
  rw [runConfig_eq_self_of_classifyState_other hclass T fuel]
  rw [hitsFromConfigByBool_eq_false_of_classifyState_other
    hclass T fuel]
  simp

/-- Install the accumulated hit bit at the head of an arbitrary preserved tape
context. -/
def otherStateLoopHitTape (context : Tape Bool) (hit : Bool) : Tape Bool :=
  Tape.write (some hit) context

@[simp] theorem otherStateLoopHitTape_read
    (context : Tape Bool) (hit : Bool) :
    Tape.read (otherStateLoopHitTape context hit) = some hit := by
  rfl

/-- Semantic pre-halt endpoint for the classifier's generic branch.  The
physical loop consumes exactly {lit}`L.stage` markers; its preserved logical
tapes are exactly the configuration tape and accumulated hit context of the
semantic bounded run. -/
theorem otherStateLoopDescription_runConfig_to_done_semantic
    (D : MachineDescription) (L : SimulatorLayout)
    (hclass : classifyState D L.config.state = StateClass.other)
    (leftRev rightPadding : List (Option Bool))
    (hitContext : Tape Bool) :
    otherStateLoopDescription.runConfig (L.stage + 1)
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          L.config.tape
          (otherStateLoopCounterTape leftRev 0 L.stage rightPadding)
          (otherStateLoopHitTape hitContext L.hit)) =
      ThreeTape.config
        (otherStateLoopTable.stateId .done)
        (SimulatorLayout.run D L.stage L).config.tape
        (otherStateLoopCounterTape leftRev L.stage 0 rightPadding)
        (otherStateLoopHitTape hitContext
          (SimulatorLayout.run D L.stage L).hit) := by
  rw [simulatorLayout_run_eq_self_of_classifyState_other
    D L L.stage hclass]
  exact otherStateLoopDescription_runConfig_to_done
    L.config.tape (otherStateLoopHitTape hitContext L.hit)
    leftRev L.stage rightPadding

/-- Standalone semantic endpoint after the bookkeeping step to the common halt
state. -/
theorem otherStateLoopDescription_runConfig_to_halt_semantic
    (D : MachineDescription) (L : SimulatorLayout)
    (hclass : classifyState D L.config.state = StateClass.other)
    (leftRev rightPadding : List (Option Bool))
    (hitContext : Tape Bool) :
    otherStateLoopDescription.runConfig (L.stage + 2)
        (ThreeTape.config
          (otherStateLoopTable.stateId .loop)
          L.config.tape
          (otherStateLoopCounterTape leftRev 0 L.stage rightPadding)
          (otherStateLoopHitTape hitContext L.hit)) =
      ThreeTape.config
        (otherStateLoopTable.stateId .halt)
        (SimulatorLayout.run D L.stage L).config.tape
        (otherStateLoopCounterTape leftRev L.stage 0 rightPadding)
        (otherStateLoopHitTape hitContext
          (SimulatorLayout.run D L.stage L).hit) := by
  rw [simulatorLayout_run_eq_self_of_classifyState_other
    D L L.stage hclass]
  exact otherStateLoopDescription_runConfig_to_halt
    L.config.tape (otherStateLoopHitTape hitContext L.hit)
    leftRev L.stage rightPadding

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
