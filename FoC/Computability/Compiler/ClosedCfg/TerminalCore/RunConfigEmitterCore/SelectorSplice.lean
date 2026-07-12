import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.SelectorIngress
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.LoopDispatcherDoneWitnessCloseout
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

set_option doc.verso true

/-!
# Fixed-start selector/dispatcher splice

This table preserves the existing dispatcher/closeout identifiers, appends the
selector ingress in a disjoint state block, and bridges each restored selector
result directly into its classified dispatcher entry. The fixed start is the
selector start; the common halt remains the closeout halt.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.SelectorSplice

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open FieldDecomposition.ClassifiedBoundary

inductive State (D : MachineDescription) where
  | core (state : LoopDispatcherCloseoutState D)
  | ingress (state : FieldDecomposition.SelectorIngress.State D)
deriving DecidableEq

def states (D : MachineDescription) : List (State D) :=
  List.append
    ((loopDispatcherCloseoutStates D).map State.core)
    ((FieldDecomposition.SelectorIngress.states D).map State.ingress)

theorem core_mem_states
    {D : MachineDescription} {state : LoopDispatcherCloseoutState D}
    (hstate : state ∈ loopDispatcherCloseoutStates D) :
    State.core state ∈ states D := by
  simp [states, hstate]
  done

theorem ingress_mem_states
    {D : MachineDescription} {state : FieldDecomposition.SelectorIngress.State D}
    (hstate : state ∈ FieldDecomposition.SelectorIngress.states D) :
    State.ingress state ∈ states D := by
  simp [states, hstate]
  done

def stateId (D : MachineDescription) : State D -> Nat
  | .core state => loopDispatcherCloseoutStateId D state
  | .ingress state =>
      (loopDispatcherCloseoutTable D).stateCount +
        (FieldDecomposition.SelectorIngress.table D).stateId state

def stateCount (D : MachineDescription) : Nat :=
  (loopDispatcherCloseoutTable D).stateCount +
    (FieldDecomposition.SelectorIngress.table D).stateCount

theorem stateId_lt (D : MachineDescription) :
    forall state : State D, state ∈ states D ->
      stateId D state < stateCount D := by
  intro state hstate
  cases state with
  | core state =>
      have hcore : state ∈ loopDispatcherCloseoutStates D := by
        simpa [states] using hstate
      exact Nat.lt_of_lt_of_le
        ((loopDispatcherCloseoutTable D).stateId_lt state hcore)
        (Nat.le_add_right _ _)
  | ingress state =>
      have hingress : state ∈ FieldDecomposition.SelectorIngress.states D := by
        simpa [states] using hstate
      exact Nat.add_lt_add_left
        ((FieldDecomposition.SelectorIngress.table D).stateId_lt state hingress) _
  done

theorem stateId_inj (D : MachineDescription) :
    forall state : State D, state ∈ states D ->
      forall target : State D, target ∈ states D ->
        stateId D state = stateId D target -> state = target := by
  intro state hstate target htarget hid
  cases state with
  | core state =>
      have hstateCore : state ∈ loopDispatcherCloseoutStates D := by
        simpa [states] using hstate
      cases target with
      | core target =>
          have htargetCore : target ∈ loopDispatcherCloseoutStates D := by
            simpa [states] using htarget
          have := (loopDispatcherCloseoutTable D).stateId_inj
            state hstateCore target htargetCore hid
          cases this
          rfl
      | ingress target =>
          have hstateLt :=
            (loopDispatcherCloseoutTable D).stateId_lt state hstateCore
          simp only [stateId] at hid
          have hge :
              (loopDispatcherCloseoutTable D).stateCount ≤
                loopDispatcherCloseoutStateId D state := by
            rw [hid]
            exact Nat.le_add_right _ _
          exact False.elim ((Nat.not_le_of_lt hstateLt) hge)
  | ingress state =>
      have hstateIngress : state ∈ FieldDecomposition.SelectorIngress.states D := by
        simpa [states] using hstate
      cases target with
      | core target =>
          have htargetCore : target ∈ loopDispatcherCloseoutStates D := by
            simpa [states] using htarget
          have htargetLt :=
            (loopDispatcherCloseoutTable D).stateId_lt target htargetCore
          simp only [stateId] at hid
          have hge :
              (loopDispatcherCloseoutTable D).stateCount ≤
                loopDispatcherCloseoutStateId D target := by
            rw [← hid]
            exact Nat.le_add_right _ _
          exact False.elim ((Nat.not_le_of_lt htargetLt) hge)
      | ingress target =>
          have htargetIngress : target ∈ FieldDecomposition.SelectorIngress.states D := by
            simpa [states] using htarget
          simp only [stateId] at hid
          have hid' := Nat.add_left_cancel hid
          have := (FieldDecomposition.SelectorIngress.table D).stateId_inj
            state hstateIngress target htargetIngress hid'
          cases this
          rfl
  done

def liftCoreStep {D : MachineDescription}
    (step : TypedStep (LoopDispatcherCloseoutState D)) :
    TypedStep (State D) :=
  { target := .core step.target
    action0 := step.action0
    action1 := step.action1
    action2 := step.action2 }

def liftIngressStep {D : MachineDescription}
    (step : TypedStep (FieldDecomposition.SelectorIngress.State D)) : TypedStep (State D) :=
  { target := .ingress step.target
    action0 := step.action0
    action1 := step.action1
    action2 := step.action2 }

def next (D : MachineDescription) :
    State D -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep (State D))
  | .core state, r0, r1, r2 =>
      (loopDispatcherCloseoutNext D state r0 r1 r2).map liftCoreStep
  | .ingress (.done tag), _, _, _ =>
      some
        { target := .core (.base (.dispatch tag))
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | .ingress state, r0, r1, r2 =>
      (FieldDecomposition.SelectorIngress.next D state r0 r1 r2).map liftIngressStep

theorem mappedIngress_target_mem
    (D : MachineDescription) (state : FieldDecomposition.SelectorIngress.State D)
    (hstate : state ∈ FieldDecomposition.SelectorIngress.states D)
    (hnext : forall r0 r1 r2,
      next D (.ingress state) r0 r1 r2 =
        (FieldDecomposition.SelectorIngress.next D state r0 r1 r2).map liftIngressStep) :
    forall (r0 r1 r2 : Option Bool) (step : TypedStep (State D)),
      next D (.ingress state) r0 r1 r2 = some step ->
        step.target ∈ states D := by
  intro r0 r1 r2 step hstep
  rw [hnext] at hstep
  cases hold : FieldDecomposition.SelectorIngress.next D state r0 r1 r2 with
  | none => simp [hold] at hstep
  | some oldStep =>
      simp only [hold, Option.map_some] at hstep
      cases hstep
      apply ingress_mem_states
      exact (FieldDecomposition.SelectorIngress.table D).next_target_mem state hstate
        r0 r1 r2 oldStep hold
  done

theorem next_target_mem (D : MachineDescription) :
    forall state : State D, state ∈ states D ->
      forall (r0 r1 r2 : Option Bool) (step : TypedStep (State D)),
        next D state r0 r1 r2 = some step -> step.target ∈ states D := by
  intro state hstate r0 r1 r2 step hnext
  cases state with
  | core state =>
      have hcore : state ∈ loopDispatcherCloseoutStates D := by
        simpa [states] using hstate
      cases hold : loopDispatcherCloseoutNext D state r0 r1 r2 with
      | none => simp [next, hold] at hnext
      | some oldStep =>
          simp only [next, hold, Option.map_some] at hnext
          cases hnext
          apply core_mem_states
          exact (loopDispatcherCloseoutTable D).next_target_mem
            state hcore r0 r1 r2 oldStep hold
  | ingress state =>
      have hingress : state ∈ FieldDecomposition.SelectorIngress.states D := by
        simpa [states] using hstate
      cases state with
      | done tag =>
          cases hnext
          apply core_mem_states
          apply base_mem_loopDispatcherCloseoutStates
          exact dispatch_mem_loopDispatcherStates tag
      | start =>
          exact mappedIngress_target_mem D .start hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | bool0 hit =>
          exact mappedIngress_target_mem D (.bool0 hit) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | bool1 hit =>
          exact mappedIngress_target_mem D (.bool1 hit) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | bool2 hit =>
          exact mappedIngress_target_mem D (.bool2 hit) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | bool3 hit branch =>
          exact mappedIngress_target_mem D (.bool3 hit branch) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | nat0 hit value =>
          exact mappedIngress_target_mem D (.nat0 hit value) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | nat1 hit value =>
          exact mappedIngress_target_mem D (.nat1 hit value) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | nat2 hit value =>
          exact mappedIngress_target_mem D (.nat2 hit value) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | nat3 hit value =>
          exact mappedIngress_target_mem D (.nat3 hit value) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | seekDelimiter hit tag =>
          exact mappedIngress_target_mem D (.seekDelimiter hit tag) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | returnToHit hit tag =>
          exact mappedIngress_target_mem D (.returnToHit hit tag) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | restoreHit hit tag =>
          exact mappedIngress_target_mem D (.restoreHit hit tag) hingress
            (by intros; rfl) r0 r1 r2 step hnext
      | halt =>
          exact mappedIngress_target_mem D .halt hingress
            (by intros; rfl) r0 r1 r2 step hnext
  done

def table (D : MachineDescription) : TypedStateTable (State D) where
  states := states D
  stateCount := stateCount D
  stateId := stateId D
  start := .ingress .start
  halt := .core (.base .halt)
  next := next D
  start_mem := ingress_mem_states (FieldDecomposition.SelectorIngress.start_mem_states D)
  halt_mem := core_mem_states
    (base_mem_loopDispatcherCloseoutStates
      (halt_mem_loopDispatcherStates D))
  stateId_lt := stateId_lt D
  stateId_inj := stateId_inj D
  halt_next := by intro r0 r1 r2; rfl
  next_target_mem := next_target_mem D

def description (D : MachineDescription) : Description :=
  (table D).description

theorem runConfig_core
    (D : MachineDescription) (steps : Nat)
    (state : LoopDispatcherCloseoutState D)
    (hstate : state ∈ loopDispatcherCloseoutStates D)
    (T0 T1 T2 : Tape Bool) :
    (description D).runConfig steps
        ((table D).config (.core state) T0 T1 T2) =
      (loopDispatcherCloseoutDescription D).runConfig steps
        ((loopDispatcherCloseoutTable D).config state T0 T1 T2) := by
  change
    (table D).description.runConfig steps
        (ThreeTape.config ((table D).stateId (.core state)) T0 T1 T2) =
      (loopDispatcherCloseoutTable D).description.runConfig steps
        (ThreeTape.config
          ((loopDispatcherCloseoutTable D).stateId state) T0 T1 T2)
  induction steps generalizing state T0 T1 T2 with
  | zero => rfl
  | succ steps ih =>
      cases hnext : loopDispatcherCloseoutNext D state
          (Tape.read T0) (Tape.read T1) (Tape.read T2) with
      | none =>
          have hold := (loopDispatcherCloseoutTable D).stepConfig_config_none
            hstate hnext
          have hnewNext :
              next D (.core state)
                  (Tape.read T0) (Tape.read T1) (Tape.read T2) = none := by
            simp [next, hnext]
          have hnew := (table D).stepConfig_config_none
            (core_mem_states hstate) hnewNext
          rw [Structured.Description.runConfig,
            Structured.Description.runConfig, hnew, hold]
          rfl
      | some step =>
          have hnewNext :
              next D (.core state)
                  (Tape.read T0) (Tape.read T1) (Tape.read T2) =
                some (liftCoreStep step) := by
            simp [next, hnext]
          rw [(table D).runConfig_succ_config
            (core_mem_states hstate) hnewNext steps]
          rw [(loopDispatcherCloseoutTable D).runConfig_succ_config
            hstate hnext steps]
          exact ih step.target
            ((loopDispatcherCloseoutTable D).next_target_mem
              state hstate (Tape.read T0) (Tape.read T1) (Tape.read T2)
              step hnext)
            (step.action0.apply T0) (step.action1.apply T1)
            (step.action2.apply T2)
  done

end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.SelectorSplice
