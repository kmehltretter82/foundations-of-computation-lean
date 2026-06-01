import FoC.Foundation.Sets
import FoC.Foundation.Finite
import FoC.Foundation.Functions

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

theorem exists_outside_of_uncountable_and_countable_cover {A B : FSet alpha}
    (hA : Uncountable A)
    (hsub_countable : forall C : FSet alpha, Subset C B -> Countable C) :
    exists x, x ∈ A ∧ ¬ x ∈ B := by
  classical
  by_cases hex : exists x, x ∈ A ∧ ¬ x ∈ B
  · exact hex
  · exfalso
    apply hA
    apply hsub_countable A
    intro x hxA
    by_cases hxB : x ∈ B
    · exact hxB
    · exact False.elim (hex (Exists.intro x (And.intro hxA hxB)))

end FSet

namespace Countability

def EncodableByNat (alpha : Type u) : Prop :=
  exists code : alpha -> Nat, Fn.Injective code

def IntCode : Int -> Nat
  | Int.ofNat n => 2 * n
  | Int.negSucc n => 2 * n + 1

-- Book: Chapter 2, Section 2.6, integers are countable by explicit coding.
theorem intCode_injective : Fn.Injective IntCode := by
  intro x y h
  cases x <;> cases y <;> simp [IntCode] at h ⊢ <;> omega

theorem nat_encodable : EncodableByNat Nat := by
  exists fun n => n
  intro x y h
  exact h

theorem int_encodable : EncodableByNat Int := by
  exact Exists.intro IntCode intCode_injective

def DiagonalList : Nat -> List (Nat × Nat)
  | 0 => [(0, 0)]
  | n + 1 => (0, n + 1) :: (DiagonalList n).map (fun p => (p.1 + 1, p.2))

theorem zero_mem_diagonalList (b : Nat) : (0, b) ∈ DiagonalList b := by
  cases b with
  | zero => simp [DiagonalList]
  | succ b => simp [DiagonalList]

-- Book: Chapter 2, Section 2.6, diagonal model for enumerating Nat x Nat.
theorem pair_mem_diagonalList (a b : Nat) :
    (a, b) ∈ DiagonalList (a + b) := by
  induction a with
  | zero => simpa using zero_mem_diagonalList b
  | succ a ih =>
      rw [Nat.succ_add]
      simpa [DiagonalList] using ih

theorem length_diagonalList (s : Nat) :
    (DiagonalList s).length = s + 1 := by
  induction s with
  | zero => rfl
  | succ s ih => simp [DiagonalList, ih]

end Countability

end Foundation
end FoC
