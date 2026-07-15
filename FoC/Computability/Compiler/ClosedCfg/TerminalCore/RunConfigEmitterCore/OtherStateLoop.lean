import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.StateClassifier

set_option doc.verso true

/-!
# Unmatched-state unary loop

An arbitrary configuration state not mentioned by the fixed description cannot
be stored in finite control.  The state classifier leaves that raw state
encoding on tape and selects one generic {lit}`other` branch. This module
supplies the transition kernel for that branch: logical tape 1 is treated as a
raw unary counter, while logical tapes 0 and 2 are preserved exactly by the
integrated dispatcher.

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

/-- Common raw unary-counter currency shared definitionally with the known
branch and consumed by the integrated dispatcher. -/
def otherStateLoopCounterTape
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate consumed (none : Option Bool)) leftRev)
    (List.append (List.replicate remaining (some true : Option Bool))
      (none :: rightPadding))

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

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
