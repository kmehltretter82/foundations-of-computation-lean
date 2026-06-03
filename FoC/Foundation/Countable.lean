import FoC.Foundation.Sets
import FoC.Foundation.Finite
import FoC.Foundation.Functions

set_option doc.verso true

/-!
# Countability

## Enumerations by natural numbers

Countability is formalized by explicit partial enumerations from natural
numbers.  A set is countable when every member appears somewhere in such an
enumeration.  This representation fits the book's "list the elements in a
sequence" intuition while allowing enumerations to skip positions with
{lean}`Option.none`.

The module contains reusable constructions for empty sets, natural numbers,
even naturals, finite sets, products, unions, integers, and selected diagonal
arguments.

## Book coordinates

Used by:
- Chapter 2, Section 2.6: Counting Past Infinity
-/

namespace FoC
namespace Foundation

namespace FSet

/-!
# Countability predicates

A countable set is one that can be enumerated by a partial function from natural
numbers.  The partial codomain lets an enumeration skip positions without
changing the set it enumerates.
-/

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

def InterleaveEnumerations (f g : Nat -> Option alpha) (n : Nat) : Option alpha :=
  if n % 2 = 0 then f (n / 2) else g (n / 2)

/-!
# Basic enumerations

The first examples enumerate the empty set, all natural numbers, and the even
natural numbers.
-/

theorem interleave_even (f g : Nat -> Option alpha) (n : Nat) :
    InterleaveEnumerations f g (2 * n) = f n := by
  simp [InterleaveEnumerations]

theorem interleave_odd (f g : Nat -> Option alpha) (n : Nat) :
    InterleaveEnumerations f g (2 * n + 1) = g n := by
  have hdiv : (2 * n + 1) / 2 = n := by
    rw [Nat.mul_add_div (by decide : 2 > 0)]
    simp
  simp [InterleaveEnumerations, hdiv]

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

theorem countable_of_equal {A B : FSet alpha}
    (hAB : Equal A B) (hA : Countable A) : Countable B := by
  cases hA with
  | intro f hf =>
      exists f
      intro x
      constructor
      · intro hxB
        exact (hf x).mp ((hAB x).mpr hxB)
      · intro hx
        exact (hAB x).mp ((hf x).mpr hx)

/-!
# Countable unions

Exercise 11(b) from Section 2.6 is represented by interleaving two
enumerations.  Even positions enumerate the first set and odd positions
enumerate the second.
-/
theorem countable_union {A B : FSet alpha}
    (hA : Countable A) (hB : Countable B) :
    Countable (Union A B) := by
  cases hA with
  | intro f hf =>
      cases hB with
      | intro g hg =>
          exists InterleaveEnumerations f g
          intro x
          constructor
          · intro hx
            cases hx with
            | inl hxA =>
                cases (hf x).mp hxA with
                | intro n hn =>
                    exists 2 * n
                    rw [interleave_even, hn]
            | inr hxB =>
                cases (hg x).mp hxB with
                | intro n hn =>
                    exists 2 * n + 1
                    rw [interleave_odd, hn]
          · intro hx
            cases hx with
            | intro n hn =>
                by_cases hpar : n % 2 = 0
                · left
                  exact (hf x).mpr (Exists.intro (n / 2) (by
                    simp [InterleaveEnumerations, hpar] at hn
                    exact hn))
                · right
                  exact (hg x).mpr (Exists.intro (n / 2) (by
                    simp [InterleaveEnumerations, hpar] at hn
                    exact hn))

/-!
Exercise 11(a) uses the union construction above.  If the first input is
already infinite, then the union cannot become finite.
-/
theorem countably_infinite_union {A B : FSet alpha}
    (hA : CountablyInfinite A) (hB : CountablyInfinite B) :
    CountablyInfinite (Union A B) := by
  constructor
  · exact countable_union hA.left hB.left
  · intro hfinite
    exact hA.right (finite_subset (union_left_subset A B) hfinite)

/-!
# Removing countable subsets

Theorem 2.9 says that removing a countable subset from an uncountable set still
leaves an uncountable set.  The formal proof argues by contradiction: if the
difference were countable, the original set would be the union of two countable
sets.
-/
theorem uncountable_diff_countable_subset {X K : FSet alpha}
    (hX : Uncountable X) (hK : Countable K) (hKX : Subset K X) :
    Uncountable (Diff X K) := by
  intro hdiff
  apply hX
  apply countable_of_equal
    (A := Union K (Diff X K))
    (B := X)
  · intro x
    constructor
    · intro hx
      cases hx with
      | inl hxK => exact hKX x hxK
      | inr hxDiff => exact hxDiff.left
    · intro hxX
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr (And.intro hxX hxK)
  · exact countable_union hK hdiff

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

/-!
# Encodable types

An encodable type injects into natural numbers.  Such an injection gives a
countable universal set by searching for the first value with a given code.
-/

def EncodableByNat (alpha : Type u) : Prop :=
  exists code : alpha -> Nat, Fn.Injective code

theorem countable_univ_of_encodableByNat {alpha : Type u}
    (henc : EncodableByNat alpha) :
    FSet.Countable (FSet.Univ : FSet alpha) := by
  classical
  cases henc with
  | intro code hcode =>
      let enum : Nat -> Option alpha := fun n =>
        if h : exists x : alpha, code x = n then some (Classical.choose h) else none
      exists enum
      intro x
      constructor
      · intro _
        let h : exists y : alpha, code y = code x := Exists.intro x rfl
        exists code x
        dsimp [enum]
        rw [dif_pos h]
        exact congrArg some (hcode (Classical.choose_spec h))
      · intro _
        exact True.intro

def IntCode : Int -> Nat
  | Int.ofNat n => 2 * n
  | Int.negSucc n => 2 * n + 1

/-!
# Integer encodings

Integers are countable by an explicit code into natural numbers: nonnegative
integers go to even codes and negative successors go to odd codes.
-/
theorem intCode_injective : Fn.Injective IntCode := by
  intro x y h
  cases x <;> cases y <;> simp [IntCode] at h ⊢ <;> omega

theorem nat_encodable : EncodableByNat Nat := by
  exists fun n => n
  intro x y h
  exact h

theorem int_encodable : EncodableByNat Int := by
  exact Exists.intro IntCode intCode_injective

/-!
# Compound encodings

Pairs, options, sums, products, and lists are encoded by combining natural
number codes.  These are the reusable countability constructions used by later
grammar and computability representations.
-/

def PairCode : Nat -> Nat -> Nat
  | 0, b => 2 * b
  | a + 1, b => 2 * PairCode a b + 1

theorem pairCode_injective_left {a c b d : Nat}
    (h : PairCode a b = PairCode c d) : a = c ∧ b = d := by
  induction a generalizing c b d with
  | zero =>
      cases c with
      | zero =>
          simp [PairCode] at h
          omega
      | succ c =>
          simp [PairCode] at h
          omega
  | succ a ih =>
      cases c with
      | zero =>
          simp [PairCode] at h
          omega
      | succ c =>
          simp [PairCode] at h
          have hprev : PairCode a b = PairCode c d := by omega
          cases ih hprev with
          | intro ha hb =>
              constructor <;> omega

theorem pairCode_injective : Fn.Injective (fun p : Nat × Nat => PairCode p.1 p.2) := by
  intro p q h
  cases p with
  | mk a b =>
      cases q with
      | mk c d =>
          cases pairCode_injective_left h with
          | intro ha hb =>
              cases ha
              cases hb
              rfl

def OptionCode (code : alpha -> Nat) : Option alpha -> Nat
  | none => 0
  | some x => code x + 1

theorem optionCode_injective {code : alpha -> Nat}
    (hcode : Fn.Injective code) :
    Fn.Injective (OptionCode code) := by
  intro x y h
  cases x <;> cases y <;> simp [OptionCode] at h ⊢
  exact hcode h

theorem option_encodable {alpha : Type u}
    (hα : EncodableByNat alpha) :
    EncodableByNat (Option alpha) := by
  rcases hα with ⟨code, hcode⟩
  exact ⟨OptionCode code, optionCode_injective hcode⟩

def SumCode (leftCode : alpha -> Nat) (rightCode : beta -> Nat) :
    Sum alpha beta -> Nat
  | Sum.inl x => 2 * leftCode x
  | Sum.inr y => 2 * rightCode y + 1

theorem sumCode_injective {leftCode : alpha -> Nat} {rightCode : beta -> Nat}
    (hleft : Fn.Injective leftCode) (hright : Fn.Injective rightCode) :
    Fn.Injective (SumCode leftCode rightCode) := by
  intro x y h
  cases x <;> cases y <;> simp [SumCode] at h ⊢
  · exact hleft (by omega)
  · omega
  · omega
  · exact hright (by omega)

theorem sum_encodable {alpha : Type u} {beta : Type v}
    (hα : EncodableByNat alpha) (hβ : EncodableByNat beta) :
    EncodableByNat (Sum alpha beta) := by
  rcases hα with ⟨leftCode, hleft⟩
  rcases hβ with ⟨rightCode, hright⟩
  exact ⟨SumCode leftCode rightCode,
    sumCode_injective hleft hright⟩

def ProdCode (leftCode : alpha -> Nat) (rightCode : beta -> Nat)
    (p : alpha × beta) : Nat :=
  PairCode (leftCode p.1) (rightCode p.2)

theorem prodCode_injective {leftCode : alpha -> Nat} {rightCode : beta -> Nat}
    (hleft : Fn.Injective leftCode) (hright : Fn.Injective rightCode) :
    Fn.Injective (ProdCode leftCode rightCode) := by
  intro x y h
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rcases pairCode_injective_left h with ⟨h₁, h₂⟩
  exact Prod.ext (hleft h₁) (hright h₂)

theorem prod_encodable {alpha : Type u} {beta : Type v}
    (hα : EncodableByNat alpha) (hβ : EncodableByNat beta) :
    EncodableByNat (alpha × beta) := by
  rcases hα with ⟨leftCode, hleft⟩
  rcases hβ with ⟨rightCode, hright⟩
  exact ⟨ProdCode leftCode rightCode,
    prodCode_injective hleft hright⟩

def ListCode (code : alpha -> Nat) : List alpha -> Nat
  | [] => 0
  | x :: xs => PairCode (code x) (ListCode code xs) + 1

theorem listCode_injective {code : alpha -> Nat}
    (hcode : Fn.Injective code) :
    Fn.Injective (ListCode code) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ =>
          simp [ListCode] at h
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [ListCode] at h
      | cons y ys =>
          have hpair :
              PairCode (code x) (ListCode code xs) =
                PairCode (code y) (ListCode code ys) := by
            simp [ListCode] at h
            omega
          rcases pairCode_injective_left hpair with ⟨hhead, htail⟩
          have hxy : x = y := hcode hhead
          have hxsys : xs = ys := ih htail
          cases hxy
          cases hxsys
          rfl

theorem list_encodable {alpha : Type u}
    (hα : EncodableByNat alpha) :
    EncodableByNat (List alpha) := by
  rcases hα with ⟨code, hcode⟩
  exact ⟨ListCode code, listCode_injective hcode⟩

/-!
# Diagonal pair enumeration

The diagonal lists enumerate pairs by increasing sum of coordinates, matching
the standard grid-walk proof that {lit}`Nat × Nat` is countable.
-/

def DiagonalList : Nat -> List (Nat × Nat)
  | 0 => [(0, 0)]
  | n + 1 => (0, n + 1) :: (DiagonalList n).map (fun p => (p.1 + 1, p.2))

theorem zero_mem_diagonalList (b : Nat) : (0, b) ∈ DiagonalList b := by
  cases b with
  | zero => simp [DiagonalList]
  | succ b => simp [DiagonalList]

/-!
The usual diagonal enumeration of pairs is modeled by collecting all pairs with
the same sum.  This theorem shows that a pair appears on the diagonal indexed by
that sum.
-/
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
