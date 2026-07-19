import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Halt-stopped finite machines

The finite-description boundary omits transitions from its designated halt
state.  This adapter gives an arbitrary finite Turing machine the same
halt-stable convention without changing ordinary reachability-based halting.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages

/-- Disable every transition out of the designated halt state. -/
def haltStoppedMachine [DecidableEq state]
    (M : TuringMachine symbol state) : TuringMachine symbol state where
  start := M.start
  halt := M.halt
  transition := fun source read =>
    if source = M.halt then none else M.transition source read
  statesFinite := M.statesFinite

theorem haltStoppedMachine_stepConfig [DecidableEq state]
    (M : TuringMachine symbol state)
    (configuration : TuringMachine.Configuration symbol state) :
    (haltStoppedMachine M).stepConfig configuration =
      if configuration.state = M.halt then none
      else M.stepConfig configuration := by
  by_cases hhalt : configuration.state = M.halt
  · simp [haltStoppedMachine, TuringMachine.stepConfig, hhalt]
  · simp [haltStoppedMachine, TuringMachine.stepConfig, hhalt]

theorem haltStoppedMachine_haltingTransitionsDisabled [DecidableEq state]
    (M : TuringMachine symbol state) :
    TuringMachine.HaltingTransitionsDisabled (haltStoppedMachine M) := by
  intro read
  simp [haltStoppedMachine]

theorem runConfigBounded_computes
    (M : TuringMachine symbol state) (steps : Nat)
    (configuration : TuringMachine.Configuration symbol state) :
    TuringMachine.Computes M configuration
      (M.runConfigBounded steps configuration) := by
  induction steps generalizing configuration with
  | zero => exact TuringMachine.Computes.refl _
  | succ steps ih =>
      rw [TuringMachine.runConfigBounded]
      cases hstep : M.stepConfig configuration with
      | none => exact TuringMachine.Computes.refl _
      | some next =>
          exact TuringMachine.Computes.step
            (TuringMachine.stepConfig_eq_some_iff_step.mp hstep)
            (ih next)

theorem runConfigBounded_eq_of_computesIn
    {M : TuringMachine symbol state} {steps : Nat}
    {source target : TuringMachine.Configuration symbol state}
    (hcomputes : TuringMachine.ComputesIn M steps source target) :
    M.runConfigBounded steps source = target := by
  induction hcomputes with
  | zero _ => rfl
  | succ hstep _ ih =>
      rw [TuringMachine.runConfigBounded]
      rw [TuringMachine.stepConfig_eq_some_iff_step.mpr hstep]
      exact ih

theorem haltStoppedMachine_step_to_original
    [DecidableEq state]
    {M : TuringMachine symbol state}
    {source target : TuringMachine.Configuration symbol state}
    (hstep : TuringMachine.Step (haltStoppedMachine M) source target) :
    TuringMachine.Step M source target := by
  cases hstep with
  | mk htransition =>
      by_cases hhalt : source.state = M.halt
      · simp [haltStoppedMachine, hhalt] at htransition
      · exact TuringMachine.Step.mk (by
          simpa [haltStoppedMachine, hhalt] using htransition)

theorem haltStoppedMachine_computes_to_original
    [DecidableEq state]
    {M : TuringMachine symbol state}
    {source target : TuringMachine.Configuration symbol state}
    (hcomputes :
      TuringMachine.Computes (haltStoppedMachine M) source target) :
    TuringMachine.Computes M source target := by
  induction hcomputes with
  | refl configuration => exact TuringMachine.Computes.refl configuration
  | step hstep _ ih =>
      exact TuringMachine.Computes.step
        (haltStoppedMachine_step_to_original hstep) ih

theorem original_haltsFrom_to_haltStoppedMachine
    [DecidableEq state]
    {M : TuringMachine symbol state}
    {source : TuringMachine.Configuration symbol state}
    (hhalts : TuringMachine.HaltsFrom M source) :
    TuringMachine.HaltsFrom (haltStoppedMachine M) source := by
  rcases hhalts with ⟨final, hcomputes, hhalt⟩
  have go : forall
      {first last : TuringMachine.Configuration symbol state},
      TuringMachine.Computes M first last ->
      last.state = M.halt ->
      TuringMachine.HaltsFrom (haltStoppedMachine M) first := by
    intro first last hrun
    induction hrun with
    | refl configuration =>
        intro hstate
        exact ⟨configuration, TuringMachine.Computes.refl _, hstate⟩
    | @step first second last hstep htail ih =>
        intro hstate
        by_cases hfirst : first.state = M.halt
        · exact ⟨first, TuringMachine.Computes.refl _, hfirst⟩
        · rcases ih hstate with ⟨stoppedFinal, hstopped, hstoppedHalt⟩
          have hstepStopped :
              TuringMachine.Step (haltStoppedMachine M) first second := by
            cases hstep with
            | mk htransition =>
                exact TuringMachine.Step.mk (by
                  simpa [haltStoppedMachine, hfirst] using htransition)
          exact ⟨stoppedFinal,
            TuringMachine.Computes.step hstepStopped hstopped,
            hstoppedHalt⟩
  exact go hcomputes hhalt

theorem haltStoppedMachine_haltsFrom_iff
    [DecidableEq state]
    (M : TuringMachine symbol state)
    (source : TuringMachine.Configuration symbol state) :
    TuringMachine.HaltsFrom (haltStoppedMachine M) source <->
      TuringMachine.HaltsFrom M source := by
  constructor
  · rintro ⟨final, hcomputes, hhalt⟩
    exact ⟨final,
      haltStoppedMachine_computes_to_original hcomputes, hhalt⟩
  · exact original_haltsFrom_to_haltStoppedMachine

theorem haltStoppedMachine_haltsOnInput_iff
    [DecidableEq state]
    (M : TuringMachine symbol state) (input : Word symbol) :
    TuringMachine.HaltsOnInput (haltStoppedMachine M) input <->
      TuringMachine.HaltsOnInput M input := by
  simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
    haltStoppedMachine] using
    haltStoppedMachine_haltsFrom_iff M (TuringMachine.initial M input)

/-- Ordinary Turing-machine halting is invariant under trailing-blank tape
representatives. -/
theorem turingMachine_haltsFrom_of_tape_equiv
    {M : TuringMachine symbol state}
    {logicalState : state} {source target : Tape symbol}
    (htape : Tape.Equiv source target)
    (hhalt : TuringMachine.HaltsFrom M
      { state := logicalState, tape := source }) :
    TuringMachine.HaltsFrom M
      { state := logicalState, tape := target } := by
  rcases hhalt with ⟨final, hrun, hfinal⟩
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hrunIn htape with
    ⟨final', hrunIn', hstate, _htapeFinal⟩
  exact ⟨final', TuringMachine.computesIn_to_computes hrunIn',
    by simpa [TuringMachine.Halted, hstate] using hfinal⟩

/-- A halting run that shares a deterministic prefix continues from the end
of that prefix.  Halt-stability rules out a shorter run that already stopped. -/
theorem haltsFromIn_suffix_of_computesIn
    {M : TuringMachine symbol state}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    {prefixSteps totalSteps : Nat}
    {source middle : TuringMachine.Configuration symbol state}
    (hprefix : TuringMachine.ComputesIn M prefixSteps source middle)
    (hhalt : TuringMachine.HaltsFromIn M totalSteps source) :
    exists remaining : Nat,
      totalSteps = prefixSteps + remaining ∧
      TuringMachine.HaltsFromIn M remaining middle := by
  induction hprefix generalizing totalSteps with
  | zero source =>
      exact ⟨totalSteps, by simp, hhalt⟩
  | @succ prefixSteps source next middle hstep hrest ih =>
      cases totalSteps with
      | zero =>
          have hhalted : TuringMachine.Halted M source :=
            TuringMachine.haltsFromIn_zero_iff.mp hhalt
          exact False.elim
            (TuringMachine.no_step_from_halted hstop hhalted hstep)
      | succ totalSteps =>
          have htail : TuringMachine.HaltsFromIn M totalSteps next :=
            TuringMachine.haltsFromIn_tail_of_step hstep (by
              simpa [Nat.succ_eq_add_one] using hhalt)
          rcases ih htail with ⟨remaining, htotal, hremaining⟩
          refine ⟨remaining, ?_, hremaining⟩
          lia

end SelfHaltingRecognizer
end Computability
end FoC
