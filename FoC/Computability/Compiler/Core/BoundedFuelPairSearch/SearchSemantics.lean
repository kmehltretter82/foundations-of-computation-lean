import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Contract

set_option doc.verso true

/-!
# Fair bounded-search semantics for fuel-pair search

The encoded candidate fuel and the number of steps used to test the supplied
runner are distinct.  A single schedule bound controls both candidate counters
and the finite runner simulation, which makes the square search fair even when
some candidate computations diverge.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-- Evidence visible after testing every coordinate for exactly {name}`bound` steps. -/
def PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceAtBound
    (runner : MachineDescription) (w : Word Bool) (b : Bool)
    (bound : Nat) : Prop :=
  exists limit : Nat,
  exists fuel : Nat,
    limit <= bound ∧
    fuel <= bound ∧
    runner.HaltsWithOutputIn bound
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w limit fuel))
      (encodeCodeWordAsInput (encodeBoolWord [b]))

/-- Concrete lexicographic square used at one schedule bound. -/
def pairedRecognizerDovetailControllerStageAttemptFuelPairSchedule
    (bound : Nat) : List (Nat × Nat) :=
  (List.range (bound + 1)).flatMap fun limit =>
    (List.range (bound + 1)).map fun fuel => (limit, fuel)

/-- The concrete square contains exactly the pairs bounded by {name}`bound`. -/
theorem mem_pairedRecognizerDovetailControllerStageAttemptFuelPairSchedule_iff
    {bound limit fuel : Nat} :
    (limit, fuel) ∈
        pairedRecognizerDovetailControllerStageAttemptFuelPairSchedule bound <->
      limit <= bound ∧ fuel <= bound := by
  simp [pairedRecognizerDovetailControllerStageAttemptFuelPairSchedule,
    Nat.lt_succ_iff]

/-- A halt-transition-free output observation remains true at every later fuel. -/
theorem MachineDescription.HaltsWithOutputIn.mono
    {D : MachineDescription} {n m : Nat} {w out : Word Bool}
    (hD : D.HaltTransitionFree)
    (hnm : n <= m)
    (h : D.HaltsWithOutputIn n w out) :
    D.HaltsWithOutputIn m w out := by
  let T : Tape Bool := (D.runConfig n (D.initial w)).tape
  have hn :
      D.runConfig n (D.initial w) =
        { state := D.halt, tape := T } := by
    cases hcfg : D.runConfig n (D.initial w) with
    | mk state tape =>
      have hs : state = D.halt := by
        simpa [HaltsWithOutputIn, hcfg] using h.left
      subst state
      simp [T, hcfg]
  let rem := m - n
  have hm : m = n + rem := by lia
  change
    (D.runConfig m (D.initial w)).state = D.halt ∧
      Tape.normalizedOutput (D.runConfig m (D.initial w)).tape = out
  rw [hm, MachineDescription.runConfig_add, hn,
    MachineDescription.runConfig_halt hD T rem]
  constructor
  · rfl
  · simpa [T] using h.right

/-- Fair bounded simulation is equivalent to ordinary existential evidence. -/
theorem pairedRecognizerDovetailControllerStageAttemptFuelPairEvidence_iff_exists_atBound
    {runner : MachineDescription}
    (hrunner : runner.SubroutineReady)
    (w : Word Bool) (b : Bool) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence runner w b <->
      exists bound : Nat,
        PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceAtBound
          runner w b bound := by
  constructor
  · intro h
    rcases h with ⟨limit, fuel, hrun⟩
    rcases hrun with ⟨runnerSteps, hsteps⟩
    let bound := Nat.max (Nat.max limit fuel) runnerSteps
    refine ⟨bound, limit, fuel, ?_, ?_, ?_⟩
    · exact Nat.le_trans (Nat.le_max_left limit fuel)
        (Nat.le_max_left (Nat.max limit fuel) runnerSteps)
    · exact Nat.le_trans (Nat.le_max_right limit fuel)
        (Nat.le_max_left (Nat.max limit fuel) runnerSteps)
    · exact hsteps.mono hrunner.right (Nat.le_max_right _ _)
  · intro h
    rcases h with ⟨bound, limit, fuel, _hlimit, _hfuel, hrun⟩
    exact ⟨limit, fuel, ⟨bound, hrun⟩⟩

end Computability
end FoC
