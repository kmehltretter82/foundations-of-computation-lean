import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable

set_option doc.verso true

/-!
# Execution combinators for typed state tables

This module packages exact executions of a typed state table without exposing
its compiled numeric control states.  An exact-step relation is the primitive
currency; the existential lead relation
hides the step count for phase proofs.  The continuation theorem recovers the
older local convention in which a lead agrees after every additional number
of steps.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-- A structured three-tape configuration whose control state remains typed. -/
structure TypedThreeTapeConfig (sigma : Type) where
  state : sigma
  tape0 : Tape Bool
  tape1 : Tape Bool
  tape2 : Tape Bool

namespace TypedThreeTapeConfig

variable {sigma : Type}

/-- Compile a typed configuration using the state embedding of a typed table. -/
def toConfiguration
    (config : TypedThreeTapeConfig sigma) (M : TypedStateTable sigma) :
    Configuration :=
  ThreeTape.config (M.stateId config.state)
    config.tape0 config.tape1 config.tape2

@[simp] theorem toConfiguration_state
    (config : TypedThreeTapeConfig sigma) (M : TypedStateTable sigma) :
    (config.toConfiguration M).state = M.stateId config.state := by
  rfl

@[simp] theorem toConfiguration_tapes
    (config : TypedThreeTapeConfig sigma) (M : TypedStateTable sigma) :
    (config.toConfiguration M).tapes =
      [config.tape0, config.tape1, config.tape2] := by
  rfl

end TypedThreeTapeConfig

/-- Constructor shorthand for a typed three-tape configuration. -/
def typedConfig {sigma : Type}
    (state : sigma) (tape0 tape1 tape2 : Tape Bool) :
    TypedThreeTapeConfig sigma :=
  { state := state, tape0 := tape0, tape1 := tape1, tape2 := tape2 }

namespace TypedStateTable

variable {sigma : Type} (M : TypedStateTable sigma)

/-- Exact execution between typed configurations in a prescribed step count. -/
def ExecutesIn (steps : Nat)
    (source target : TypedThreeTapeConfig sigma) : Prop :=
  M.description.runConfig steps (source.toConfiguration M) =
    target.toConfiguration M

/-- Step-count-free exact reachability between typed configurations. -/
def Leads (source target : TypedThreeTapeConfig sigma) : Prop :=
  exists steps : Nat, M.ExecutesIn steps source target

namespace ExecutesIn

theorem refl (config : TypedThreeTapeConfig sigma) :
    M.ExecutesIn 0 config config := by
  rfl

theorem trans
    {first second third : TypedThreeTapeConfig sigma}
    {firstSteps secondSteps : Nat}
    (hfirst : M.ExecutesIn firstSteps first second)
    (hsecond : M.ExecutesIn secondSteps second third) :
    M.ExecutesIn (firstSteps + secondSteps) first third := by
  unfold TypedStateTable.ExecutesIn at hfirst hsecond ⊢
  rw [M.description.runConfig_add, hfirst, hsecond]

/-- An exact execution remains valid before any common continuation. -/
theorem continues
    {steps tail : Nat} {source target : TypedThreeTapeConfig sigma}
    (h : M.ExecutesIn steps source target) :
    M.description.runConfig (tail + steps) (source.toConfiguration M) =
      M.description.runConfig tail (target.toConfiguration M) := by
  rw [Nat.add_comm, M.description.runConfig_add]
  rw [h]

end ExecutesIn

namespace Leads

theorem refl (config : TypedThreeTapeConfig sigma) :
    M.Leads config config := by
  exact ⟨0, ExecutesIn.refl M config⟩

theorem trans
    {first second third : TypedThreeTapeConfig sigma}
    (hfirst : M.Leads first second)
    (hsecond : M.Leads second third) :
    M.Leads first third := by
  rcases hfirst with ⟨firstSteps, hfirst⟩
  rcases hsecond with ⟨secondSteps, hsecond⟩
  exact
    ⟨firstSteps + secondSteps,
      ExecutesIn.trans M hfirst hsecond⟩

theorem to_runConfig
    {source target : TypedThreeTapeConfig sigma}
    (h : M.Leads source target) :
    exists steps : Nat,
      M.description.runConfig steps (source.toConfiguration M) =
        target.toConfiguration M := by
  rcases h with ⟨steps, hsteps⟩
  exact ⟨steps, hsteps⟩

/-- Recover the continuation-oriented formulation used by older phase files. -/
theorem exists_continues
    {source target : TypedThreeTapeConfig sigma}
    (h : M.Leads source target) :
    exists steps : Nat, forall tail : Nat,
      M.description.runConfig (tail + steps) (source.toConfiguration M) =
        M.description.runConfig tail (target.toConfiguration M) := by
  rcases h with ⟨steps, hsteps⟩
  exact ⟨steps, fun tail => ExecutesIn.continues M hsteps⟩

end Leads

/-- A defined typed transition executes in exactly one compiled step. -/
theorem executesIn_one_of_next [DecidableEq sigma]
    {state : sigma} (hstate : state ∈ M.states)
    (tape0 tape1 tape2 : Tape Bool) {step : TypedStep sigma}
    (hnext :
      M.next state (Tape.read tape0) (Tape.read tape1) (Tape.read tape2) =
        some step) :
    M.ExecutesIn 1
      (typedConfig state tape0 tape1 tape2)
      (typedConfig step.target
        (step.action0.apply tape0)
        (step.action1.apply tape1)
        (step.action2.apply tape2)) := by
  change
    M.description.runConfig (0 + 1)
        (ThreeTape.config (M.stateId state) tape0 tape1 tape2) =
      ThreeTape.config (M.stateId step.target)
        (step.action0.apply tape0)
        (step.action1.apply tape1)
        (step.action2.apply tape2)
  rw [M.runConfig_succ_config hstate hnext 0]
  rfl

/-- Step-count-free form of {name}`executesIn_one_of_next`. -/
theorem leads_step [DecidableEq sigma]
    {state : sigma} (hstate : state ∈ M.states)
    (tape0 tape1 tape2 : Tape Bool) {step : TypedStep sigma}
    (hnext :
      M.next state (Tape.read tape0) (Tape.read tape1) (Tape.read tape2) =
        some step) :
    M.Leads
      (typedConfig state tape0 tape1 tape2)
      (typedConfig step.target
        (step.action0.apply tape0)
        (step.action1.apply tape1)
        (step.action2.apply tape2)) := by
  exact
    ⟨1, executesIn_one_of_next M hstate tape0 tape1 tape2 hnext⟩

end TypedStateTable

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
