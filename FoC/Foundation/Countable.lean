import FoC.Foundation.Sets
import FoC.Foundation.Finite

namespace FoC
namespace Foundation

/-!
Countability via explicit partial enumerations by natural numbers.

Used by:
- Chapter 2, Section 2.6: Counting Past Infinity
-/

namespace FSet

def EnumeratedBy (A : FSet alpha) (f : Nat -> Option alpha) : Prop :=
  forall x, x ∈ A <-> exists n, f n = some x

def Countable (A : FSet alpha) : Prop :=
  exists f : Nat -> Option alpha, EnumeratedBy A f

def CountablyInfinite (A : FSet alpha) : Prop :=
  Countable A ∧ ¬ Finite A

def Uncountable (A : FSet alpha) : Prop :=
  ¬ Countable A

def EvenNaturals : FSet Nat :=
  fun n => exists k, n = 2 * k

theorem empty_countable : Countable (Empty : FSet alpha) := by
  exists fun _ => none
  intro x
  constructor
  · intro hx
    cases hx
  · intro hx
    cases hx with
    | intro n hn =>
        cases hn

theorem nat_univ_countable : Countable (Univ : FSet Nat) := by
  exists fun n => some n
  intro x
  constructor
  · intro _
    exact Exists.intro x rfl
  · intro _
    exact True.intro

theorem even_naturals_countable : Countable EvenNaturals := by
  exists fun n => some (2 * n)
  intro x
  constructor
  · intro hx
    cases hx with
    | intro k hk =>
        exists k
        rw [hk]
  · intro hx
    cases hx with
    | intro n hn =>
        cases hn
        exact Exists.intro n rfl

end FSet

end Foundation
end FoC
