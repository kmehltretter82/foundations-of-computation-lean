import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SearchSemantics

set_option doc.verso true

/-!
# Concrete fuel-pair schedule cursor

The cursor scans candidate fuel inside limit, then advances to the next square.
These pure facts are the arithmetic interface used by the finite control loop.
-/

namespace FoC
namespace Computability

/-- The schedule cursor stores {lit}`(bound, limit, candidateFuel)`. -/
structure PairedRecognizerFuelPairScheduleCursor where
  bound : Nat
  limit : Nat
  candidateFuel : Nat
deriving DecidableEq

def PairedRecognizerFuelPairScheduleCursor.Valid
    (c : PairedRecognizerFuelPairScheduleCursor) : Prop :=
  c.limit <= c.bound ∧ c.candidateFuel <= c.bound

def PairedRecognizerFuelPairScheduleCursor.initial :
    PairedRecognizerFuelPairScheduleCursor :=
  ⟨0, 0, 0⟩

def PairedRecognizerFuelPairScheduleCursor.advance
    (c : PairedRecognizerFuelPairScheduleCursor) :
    PairedRecognizerFuelPairScheduleCursor :=
  if c.candidateFuel < c.bound then
    ⟨c.bound, c.limit, c.candidateFuel + 1⟩
  else if c.limit < c.bound then
    ⟨c.bound, c.limit + 1, 0⟩
  else
    ⟨c.bound + 1, 0, 0⟩

@[simp] theorem PairedRecognizerFuelPairScheduleCursor.initial_valid :
    PairedRecognizerFuelPairScheduleCursor.initial.Valid := by
  simp [PairedRecognizerFuelPairScheduleCursor.initial,
    PairedRecognizerFuelPairScheduleCursor.Valid]

theorem PairedRecognizerFuelPairScheduleCursor.advance_of_candidateFuel_lt
    (c : PairedRecognizerFuelPairScheduleCursor)
    (h : c.candidateFuel < c.bound) :
    c.advance = ⟨c.bound, c.limit, c.candidateFuel + 1⟩ := by
  simp [PairedRecognizerFuelPairScheduleCursor.advance, h]

theorem PairedRecognizerFuelPairScheduleCursor.advance_of_candidateFuel_eq
    (c : PairedRecognizerFuelPairScheduleCursor)
    (hfuel : c.candidateFuel = c.bound)
    (hlimit : c.limit < c.bound) :
    c.advance = ⟨c.bound, c.limit + 1, 0⟩ := by
  simp [PairedRecognizerFuelPairScheduleCursor.advance, hfuel, hlimit]

theorem PairedRecognizerFuelPairScheduleCursor.advance_of_square_end
    (c : PairedRecognizerFuelPairScheduleCursor)
    (hfuel : c.candidateFuel = c.bound)
    (hlimit : c.limit = c.bound) :
    c.advance = ⟨c.bound + 1, 0, 0⟩ := by
  simp [PairedRecognizerFuelPairScheduleCursor.advance, hfuel, hlimit]

theorem PairedRecognizerFuelPairScheduleCursor.advance_valid
    (c : PairedRecognizerFuelPairScheduleCursor)
    (hvalid : c.Valid) :
    c.advance.Valid := by
  rcases hvalid with ⟨hlimitLe, hfuelLe⟩
  by_cases hfuelLt : c.candidateFuel < c.bound
  · simp [PairedRecognizerFuelPairScheduleCursor.advance, hfuelLt,
      PairedRecognizerFuelPairScheduleCursor.Valid]
    exact ⟨hlimitLe, hfuelLt⟩
  · have hfuelEq : c.candidateFuel = c.bound := by lia
    by_cases hlimitLt : c.limit < c.bound
    · simp [PairedRecognizerFuelPairScheduleCursor.advance, hfuelLt,
        hlimitLt, PairedRecognizerFuelPairScheduleCursor.Valid]
      exact hlimitLt
    · simp [PairedRecognizerFuelPairScheduleCursor.advance, hfuelLt,
        hlimitLt, PairedRecognizerFuelPairScheduleCursor.Valid]

theorem PairedRecognizerFuelPairScheduleCursor.advance_ne
    (c : PairedRecognizerFuelPairScheduleCursor)
    (hvalid : c.Valid) :
    c.advance ≠ c := by
  rcases hvalid with ⟨hlimitLe, hfuelLe⟩
  by_cases hfuelLt : c.candidateFuel < c.bound
  · rw [PairedRecognizerFuelPairScheduleCursor.advance_of_candidateFuel_lt
      c hfuelLt]
    intro heq
    have hcomponent :=
      congrArg PairedRecognizerFuelPairScheduleCursor.candidateFuel heq
    simp at hcomponent
  · have hfuelEq : c.candidateFuel = c.bound := by lia
    by_cases hlimitLt : c.limit < c.bound
    · rw [PairedRecognizerFuelPairScheduleCursor.advance_of_candidateFuel_eq
        c hfuelEq hlimitLt]
      intro heq
      have hcomponent :=
        congrArg PairedRecognizerFuelPairScheduleCursor.limit heq
      simp at hcomponent
    · have hlimitEq : c.limit = c.bound := by lia
      rw [PairedRecognizerFuelPairScheduleCursor.advance_of_square_end
        c hfuelEq hlimitEq]
      intro heq
      have hcomponent :=
        congrArg PairedRecognizerFuelPairScheduleCursor.bound heq
      simp at hcomponent

end Computability
end FoC
