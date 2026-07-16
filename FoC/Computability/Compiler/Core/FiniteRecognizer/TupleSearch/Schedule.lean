import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic

set_option doc.verso true

/-!
# Round schedules for hidden-fuel tuple search

Finite candidate schedules for the unbounded and budget-bounded tuple
searchers.  The bounded schedule constrains its two public coordinates while
allowing the selected recognizer's exact fuel to grow independently.
-/

namespace FoC
namespace Computability
namespace FiniteRecognizer
namespace TupleSearch

/-- A generated nested-input candidate and its selected-machine exact fuel. -/
abbrev HiddenFuelCandidate := Nat × Nat × Nat

/-- Candidates whose three coordinates lie in the cube from zero through {lit}`round`. -/
def unboundedRoundCandidates (round : Nat) : List HiddenFuelCandidate :=
  (List.range (round + 1)).flatMap fun inner =>
    (List.range (round + 1)).flatMap fun outer =>
      (List.range (round + 1)).map fun selectedFuel =>
        (inner, outer, selectedFuel)

/--
Candidates whose public coordinates are budget-bounded and whose selected
fuel lies between zero and {lit}`round`.
-/
def boundedRoundCandidates (budget round : Nat) : List HiddenFuelCandidate :=
  (List.range (budget + 1)).flatMap fun inner =>
    (List.range (budget + 1)).flatMap fun outer =>
      (List.range (round + 1)).map fun selectedFuel =>
        (inner, outer, selectedFuel)

/-- Membership in an unbounded round is exactly coordinatewise boundedness. -/
theorem mem_unboundedRoundCandidates_iff
    (round inner outer selectedFuel : Nat) :
    (inner, outer, selectedFuel) ∈ unboundedRoundCandidates round ↔
      inner ≤ round ∧ outer ≤ round ∧ selectedFuel ≤ round := by
  simp [unboundedRoundCandidates, Nat.lt_succ_iff]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl, rfl, rfl⟩
    exact ⟨ha, hb, hc⟩
  · rintro ⟨hinner, houter, hfuel⟩
    exact
      ⟨inner, hinner, outer, houter, selectedFuel, hfuel,
        rfl, rfl, rfl⟩

/-- Every candidate occurs by the maximum of its three coordinates. -/
theorem unboundedRoundCandidates_mem_max
    (inner outer selectedFuel : Nat) :
    (inner, outer, selectedFuel) ∈
      unboundedRoundCandidates (Nat.max inner (Nat.max outer selectedFuel)) := by
  exact
    (mem_unboundedRoundCandidates_iff (Nat.max inner (Nat.max outer selectedFuel))
      inner outer selectedFuel).2
      ⟨Nat.le_max_left inner (Nat.max outer selectedFuel),
        Nat.le_trans
          (Nat.le_max_left outer selectedFuel)
          (Nat.le_max_right inner (Nat.max outer selectedFuel)),
        Nat.le_trans
          (Nat.le_max_right outer selectedFuel)
          (Nat.le_max_right inner (Nat.max outer selectedFuel))⟩

/-- Membership in a bounded round separates the public budget from exact fuel. -/
theorem mem_boundedRoundCandidates_iff
    (budget round inner outer selectedFuel : Nat) :
    (inner, outer, selectedFuel) ∈ boundedRoundCandidates budget round ↔
      inner ≤ budget ∧ outer ≤ budget ∧ selectedFuel ≤ round := by
  simp [boundedRoundCandidates, Nat.lt_succ_iff]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl, rfl, rfl⟩
    exact ⟨ha, hb, hc⟩
  · rintro ⟨hinner, houter, hfuel⟩
    exact
      ⟨inner, hinner, outer, houter, selectedFuel, hfuel,
        rfl, rfl, rfl⟩

/-- A budget-admissible candidate occurs at the round equal to its exact fuel. -/
theorem boundedRoundCandidates_mem_selectedFuel
    {budget inner outer : Nat} (selectedFuel : Nat)
    (hinner : inner ≤ budget) (houter : outer ≤ budget) :
    (inner, outer, selectedFuel) ∈
      boundedRoundCandidates budget selectedFuel := by
  exact
    (mem_boundedRoundCandidates_iff
      budget selectedFuel inner outer selectedFuel).2
      ⟨hinner, houter, Nat.le_refl selectedFuel⟩

/-- Regression: exact fuel can exceed the public budget. -/
theorem boundedRoundCandidates_selectedFuel_gt_budget_regression :
    (2, 2, 5) ∈ boundedRoundCandidates 2 5 ∧ 2 < 5 := by
  decide

end TupleSearch
end FiniteRecognizer
end Computability
end FoC
