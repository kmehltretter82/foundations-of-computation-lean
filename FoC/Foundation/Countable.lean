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

The module contains reusable constructions for natural numbers, even naturals,
finite sets, unions, integers, pairs, encodable lists, and selected diagonal
arguments.  It also proves the infiniteness facts that separate countably
infinite sets from finite ones: no list enumerates all natural numbers or all
even natural numbers, so both sets are countably infinite.

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

private def InterleaveEnumerations (f g : Nat -> Option alpha) (n : Nat) : Option alpha :=
  if n % 2 = 0 then f (n / 2) else g (n / 2)

/-!
# Basic enumerations

The first examples enumerate all natural numbers and the even natural numbers.
-/

private theorem interleave_even (f g : Nat -> Option alpha) (n : Nat) :
    InterleaveEnumerations f g (2 * n) = f n := by
  simp [InterleaveEnumerations]

private theorem interleave_odd (f g : Nat -> Option alpha) (n : Nat) :
    InterleaveEnumerations f g (2 * n + 1) = g n := by
  have hdiv : (2 * n + 1) / 2 = n := by
    rw [Nat.mul_add_div (by decide : 2 > 0)]
    simp
  simp [InterleaveEnumerations, hdiv]

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

theorem countable_subset {A B : FSet alpha}
    [DecidablePred (fun x => x ∈ A)]
    (hAB : Subset A B) (hB : Countable B) : Countable A := by
  cases hB with
  | intro f hf =>
      let filtered : Nat -> Option alpha := fun n =>
        match f n with
        | none => none
        | some x => if x ∈ A then some x else none
      exists filtered
      intro x
      constructor
      · intro hxA
        have hxB : x ∈ B := hAB x hxA
        cases (hf x).mp hxB with
        | intro n hn =>
            exists n
            dsimp [filtered]
            rw [hn]
            simp [hxA]
      · intro hx
        cases hx with
        | intro n hn =>
            dsimp [filtered] at hn
            cases hfn : f n with
            | none =>
                simp [hfn] at hn
            | some y =>
                by_cases hyA : y ∈ A
                · simp [hfn, hyA] at hn
                  rw [← hn]
                  exact hyA
                · simp [hfn, hyA] at hn

/-!
The book states the countable-subset principle for arbitrary sets.  The
classical corollary discharges the decidability hypothesis of
{name}`countable_subset`, so book-facing wrappers can state the principle
unconditionally.
-/
theorem countable_subset_classical {A B : FSet alpha}
    (hAB : Subset A B) (hB : Countable B) : Countable A := by
  classical
  exact countable_subset hAB hB

/-!
# Finite sets are countable

The book defines a countable set as one that is finite or countably infinite.
The formal connection is that every finite enumeration is in particular a
partial enumeration by natural numbers: position {lit}`n` of the list is the
{lit}`n`-th enumerated element.
-/
theorem countable_of_finite {A : FSet alpha} (hA : Finite A) : Countable A := by
  cases hA with
  | intro xs hxs =>
      exists fun n => xs[n]?
      intro x
      constructor
      · intro hxA
        exact List.mem_iff_getElem?.mp ((hxs x).mp hxA)
      · intro hx
        exact (hxs x).mpr (List.mem_iff_getElem?.mpr hx)

/-!
# Infinite sets

A finite list of natural numbers cannot contain a number larger than its
maximum, so no list enumerates all of {lit}`Nat`: the set of natural numbers
is infinite.  The same bound shows that the even natural numbers are
infinite.  Combined with the enumerations above, both sets are countably
infinite in the book's sense.
-/

private theorem list_mem_le_foldr_max (xs : List Nat) :
    forall x, x ∈ xs -> x <= xs.foldr Nat.max 0 := by
  induction xs with
  | nil =>
      intro x hx
      cases hx
  | cons y ys ih =>
      intro x hx
      cases hx with
      | head =>
          exact Nat.le_max_left y (ys.foldr Nat.max 0)
      | tail _ h =>
          exact Nat.le_trans (ih x h) (Nat.le_max_right y (ys.foldr Nat.max 0))

theorem nat_univ_not_finite : ¬ Finite (Univ : FSet Nat) := by
  intro hfin
  cases hfin with
  | intro xs hxs =>
      have hmem : xs.foldr Nat.max 0 + 1 ∈ xs :=
        (hxs (xs.foldr Nat.max 0 + 1)).mp True.intro
      have hle := list_mem_le_foldr_max xs _ hmem
      lia

theorem even_naturals_not_finite : ¬ Finite EvenNaturals := by
  intro hfin
  cases hfin with
  | intro xs hxs =>
      have hmem : 2 * (xs.foldr Nat.max 0 + 1) ∈ xs :=
        (hxs (2 * (xs.foldr Nat.max 0 + 1))).mp
          (Exists.intro (xs.foldr Nat.max 0 + 1) rfl)
      have hle := list_mem_le_foldr_max xs _ hmem
      lia

theorem nat_univ_countably_infinite : CountablyInfinite (Univ : FSet Nat) :=
  And.intro nat_univ_countable nat_univ_not_finite

theorem even_naturals_countably_infinite : CountablyInfinite EvenNaturals :=
  And.intro even_naturals_countable even_naturals_not_finite

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
  classical
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

end FSet

namespace Countability

/-!
# Encodable types

An encodable type injects into natural numbers.  Such an injection gives a
countable universal set by searching for the first value with a given code.
-/

def EncodableByNat (alpha : Type u) : Prop :=
  exists code : alpha -> Nat, Fn.Injective code

structure NatCodec (alpha : Type u) where
  encode : alpha -> Nat
  decode : Nat -> Option alpha
  decode_encode : forall x, decode (encode x) = some x

namespace NatCodec

def nat : NatCodec Nat where
  encode := fun n => n
  decode := fun n => some n
  decode_encode := by
    intro x
    rfl

end NatCodec

theorem countable_univ_of_natCodec {alpha : Type u}
    (codec : NatCodec alpha) :
    FSet.Countable (FSet.Univ : FSet alpha) := by
  exists codec.decode
  intro x
  constructor
  · intro _
    exact Exists.intro (codec.encode x) (codec.decode_encode x)
  · intro _
    exact True.intro

theorem natCodec_encodableByNat {alpha : Type u}
    (codec : NatCodec alpha) : EncodableByNat alpha := by
  exists codec.encode
  intro x y h
  have hx := codec.decode_encode x
  have hy := codec.decode_encode y
  rw [h] at hx
  rw [hy] at hx
  cases hx
  rfl

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

def NatCodec.int : NatCodec Int where
  encode := IntCode
  decode := fun n =>
    if n % 2 = 0 then
      some (Int.ofNat (n / 2))
    else
      some (Int.negSucc (n / 2))
  decode_encode := by
    intro x
    cases x with
    | ofNat n =>
        simp [IntCode]
    | negSucc n =>
        have hdiv : (2 * n + 1) / 2 = n := by
          have hpos : 2 > 0 := by decide
          rw [Nat.mul_add_div hpos]
          simp
        simp [IntCode, hdiv]

/-!
# Integer encodings

Integers are countable by an explicit code into natural numbers: nonnegative
integers go to even codes and negative successors go to odd codes.
-/
theorem intCode_injective : Fn.Injective IntCode := by
  intro x y h
  cases x <;> cases y <;> simp [IntCode] at h ⊢ <;> lia

theorem nat_encodable : EncodableByNat Nat := by
  exists fun n => n
  intro x y h
  exact h

theorem int_encodable : EncodableByNat Int := by
  exact Exists.intro IntCode intCode_injective

/-!
# Compound encodings

Pairs, options, sums, products, and lists are encoded by combining natural
number codes.  The list encoding is the reusable countability construction used
by later grammar and computability representations.
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
          lia
      | succ c =>
          simp [PairCode] at h
          lia
  | succ a ih =>
      cases c with
      | zero =>
          simp [PairCode] at h
          lia
      | succ c =>
          simp [PairCode] at h
          have hprev : PairCode a b = PairCode c d := by lia
          cases ih hprev with
          | intro ha hb =>
              constructor <;> lia

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

/-!
Exercise 10 from Section 2.6 asks for the countability of {lit}`Nat × Nat`.
The injective pair code above is the required encoding, and searching for
codes enumerates the full set of pairs.
-/
theorem natPair_encodable : EncodableByNat (Nat × Nat) :=
  Exists.intro (fun p => PairCode p.1 p.2) pairCode_injective

theorem natPair_univ_countable :
    FSet.Countable (FSet.Univ : FSet (Nat × Nat)) :=
  countable_univ_of_encodableByNat natPair_encodable

def OptionCode (code : alpha -> Nat) : Option alpha -> Nat
  | none => 0
  | some x => code x + 1

def SumCode (leftCode : alpha -> Nat) (rightCode : beta -> Nat) :
    Sum alpha beta -> Nat
  | Sum.inl x => 2 * leftCode x
  | Sum.inr y => 2 * rightCode y + 1

def ProdCode (leftCode : alpha -> Nat) (rightCode : beta -> Nat)
    (p : alpha × beta) : Nat :=
  PairCode (leftCode p.1) (rightCode p.2)

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
            lia
          rcases pairCode_injective_left hpair with ⟨hhead, htail⟩
          have hxy : x = y := hcode hhead
          have hxsys : xs = ys := ih htail
          cases hxy
          cases hxsys
          rfl

theorem list_encodable {alpha : Type u}
    (h : EncodableByNat alpha) : EncodableByNat (List alpha) := by
  cases h with
  | intro code hcode =>
      exists ListCode code
      exact listCode_injective hcode

/-!
# Diagonal pair enumeration

The diagonal lists enumerate pairs by increasing sum of coordinates, matching
the standard grid-walk proof that {lit}`Nat × Nat` is countable.
-/

def DiagonalList : Nat -> List (Nat × Nat)
  | 0 => [(0, 0)]
  | n + 1 => (0, n + 1) :: (DiagonalList n).map (fun p => (p.1 + 1, p.2))

private theorem zero_mem_diagonalList (b : Nat) : (0, b) ∈ DiagonalList b := by
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
