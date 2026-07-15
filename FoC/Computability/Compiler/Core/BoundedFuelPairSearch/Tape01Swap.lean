import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable

set_option doc.verso true

/-!
# Swapping the first two logical tapes

The bounded fuel-pair search must reuse a structured emitter while preserving
the scratch tape left by its first simulation.  This module swaps logical
tapes 0 and 1 of a typed three-tape table and proves an exact run-transfer
theorem.
-/

namespace FoC
namespace Computability

open Languages
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace BoundedFuelPairSearch
namespace Tape01Swap

/-- Exchange the first two actions of a typed three-tape step. -/
def swapStep {σ : Type} (st : TypedStep σ) : TypedStep σ :=
  ⟨st.target, st.action1, st.action0, st.action2⟩

/-- Read the first two logical tapes in exchanged order. -/
def next {σ : Type} (M : TypedStateTable σ)
    (s : σ) (r0 r1 r2 : Option Bool) : Option (TypedStep σ) :=
  (M.next s r1 r0 r2).map swapStep

/-- Typed table obtained by exchanging logical tapes 0 and 1. -/
def table {σ : Type} (M : TypedStateTable σ) : TypedStateTable σ where
  states := M.states
  stateCount := M.stateCount
  stateId := M.stateId
  start := M.start
  halt := M.halt
  next := next M
  start_mem := M.start_mem
  halt_mem := M.halt_mem
  stateId_lt := M.stateId_lt
  stateId_inj := M.stateId_inj
  halt_next := by
    intro r0 r1 r2
    simp [next, M.halt_next]
  next_target_mem := by
    intro s hs r0 r1 r2 st hnext
    unfold next at hnext
    cases hM : M.next s r1 r0 r2 with
    | none => simp [hM] at hnext
    | some localStep =>
        simp [hM, swapStep] at hnext
        subst st
        exact M.next_target_mem s hs r1 r0 r2 localStep hM

@[simp] theorem table_states {σ : Type} (M : TypedStateTable σ) :
    (table M).states = M.states := rfl

@[simp] theorem table_stateId {σ : Type} (M : TypedStateTable σ) :
    (table M).stateId = M.stateId := rfl

/-- Transfer an exact typed run while exchanging its first two tapes. -/
theorem runConfig_of_runConfig {σ : Type} [DecidableEq σ]
    (M : TypedStateTable σ) :
    forall (steps : Nat) (s : σ), s ∈ M.states ->
      forall (T0 T1 T2 : Tape Bool) (target : σ)
        (U0 U1 U2 : Tape Bool),
        M.description.runConfig steps
            (ThreeTape.config (M.stateId s) T1 T0 T2) =
          ThreeTape.config (M.stateId target) U1 U0 U2 ->
        (table M).description.runConfig steps
            (ThreeTape.config (M.stateId s) T0 T1 T2) =
          ThreeTape.config (M.stateId target) U0 U1 U2 := by
  intro steps
  induction steps with
  | zero =>
      intro s _hs T0 T1 T2 target U0 U1 U2 hrun
      simp only [CommonGround.FiniteTransducers.Structured.Description.runConfig]
        at hrun ⊢
      injection hrun with hstate htapes
      injection htapes with hT1 htail1
      injection htail1 with hT0 htail2
      injection htail2 with hT2
      simp [ThreeTape.config, hstate, hT1, hT0, hT2]
  | succ steps ih =>
      intro s hs T0 T1 T2 target U0 U1 U2 hrun
      unfold CommonGround.FiniteTransducers.Structured.Description.runConfig
        at hrun ⊢
      rw [M.stepConfig_config hs T1 T0 T2] at hrun
      change
        (match
            (table M).description.stepConfig
              (ThreeTape.config ((table M).stateId s) T0 T1 T2) with
          | none => ThreeTape.config (M.stateId s) T0 T1 T2
          | some next => (table M).description.runConfig steps next) = _
      rw [(table M).stepConfig_config hs T0 T1 T2]
      cases hnext : M.next s (Tape.read T1) (Tape.read T0) (Tape.read T2) with
      | none =>
          simp [table, next, hnext] at hrun ⊢
          injection hrun with hstate htapes
          injection htapes with hT1 htail1
          injection htail1 with hT0 htail2
          injection htail2 with hT2
          simp [ThreeTape.config, hstate, hT1, hT0, hT2]
      | some st =>
          simp [table, next, hnext, swapStep] at hrun ⊢
          exact ih st.target
            (M.next_target_mem s hs _ _ _ st hnext)
            (st.action1.apply T0) (st.action0.apply T1)
            (st.action2.apply T2) target U0 U1 U2 hrun

end Tape01Swap
end BoundedFuelPairSearch

end Computability
end FoC
