set_option doc.verso true

/-!
# Sets

## Predicate sets

The book treats sets extensionally. We represent a set of {lit}`alpha` as a
predicate {lit}`alpha -> Prop`, and use {lit}`FSet.Equal` for book-style equality.
This keeps set membership and set equality close to the textbook notation while
remaining simple enough to use throughout the formalization.

## Book coordinates

Used by:
- Chapter 2, Section 2.1: Basic Concepts
- Chapter 2, Section 2.2: The Boolean Algebra of Sets
- Chapter 2, Section 2.4: Functions
- Chapter 2, Section 2.6: Counting Past Infinity
- Chapter 2, Section 2.7: Relations
-/

namespace FoC
namespace Foundation

/-!
# Set representation

Sets are predicates, so membership is function application and extensional
equality is pointwise equivalence of membership.
-/

def FSet (alpha : Type u) : Type u :=
  alpha -> Prop

namespace FSet

instance : Membership alpha (FSet alpha) where
  mem A x := A x

def Empty : FSet alpha :=
  fun _ => False

def Univ : FSet alpha :=
  fun _ => True

def Singleton (a : alpha) : FSet alpha :=
  fun x => x = a

def Pair (a b : alpha) : FSet alpha :=
  fun x => x = a ∨ x = b

def Subset (A B : FSet alpha) : Prop :=
  forall x, x ∈ A -> x ∈ B

def Equal (A B : FSet alpha) : Prop :=
  forall x, x ∈ A <-> x ∈ B

def ProperSubset (A B : FSet alpha) : Prop :=
  Subset A B ∧ ¬ Subset B A

def Union (A B : FSet alpha) : FSet alpha :=
  fun x => x ∈ A ∨ x ∈ B

def Inter (A B : FSet alpha) : FSet alpha :=
  fun x => x ∈ A ∧ x ∈ B

def Compl (A : FSet alpha) : FSet alpha :=
  fun x => ¬ x ∈ A

def Diff (A B : FSet alpha) : FSet alpha :=
  fun x => x ∈ A ∧ ¬ x ∈ B

def Powerset (A : FSet alpha) : FSet (FSet alpha) :=
  fun B => Subset B A

def Disjoint (A B : FSet alpha) : Prop :=
  forall x, ¬ (x ∈ A ∧ x ∈ B)

def Product (A : FSet alpha) (B : FSet beta) : FSet (alpha × beta) :=
  fun p => p.1 ∈ A ∧ p.2 ∈ B

def ListUnion : List (FSet alpha) -> FSet alpha
  | [] => Empty
  | A :: As => Union A (ListUnion As)

def ListInter : List (FSet alpha) -> FSet alpha
  | [] => Univ
  | A :: As => Inter A (ListInter As)

/-!
# Subsets and extensional equality

Subset and equality lemmas provide the basic rewriting API for predicate sets.
-/

theorem subset_trans {A B C : FSet alpha}
    (hAB : Subset A B) (hBC : Subset B C) : Subset A C := by
  intro x hx
  exact hBC x (hAB x hx)

theorem equal_refl (A : FSet alpha) : Equal A A := by
  intro x
  constructor <;> intro hx <;> exact hx

theorem equal_symm {A B : FSet alpha} (h : Equal A B) : Equal B A := by
  intro x
  constructor
  · intro hx
    exact (h x).mpr hx
  · intro hx
    exact (h x).mp hx

theorem equal_trans {A B C : FSet alpha}
    (hAB : Equal A B) (hBC : Equal B C) : Equal A C := by
  intro x
  constructor
  · intro hx
    exact (hBC x).mp ((hAB x).mp hx)
  · intro hx
    exact (hAB x).mpr ((hBC x).mpr hx)

theorem equal_of_subsets {A B : FSet alpha}
    (hAB : Subset A B) (hBA : Subset B A) : Equal A B := by
  intro x
  constructor
  · intro hx
    exact hAB x hx
  · intro hx
    exact hBA x hx

/-!
# Boolean algebra of sets

The algebraic laws cover union, intersection, complements, distributivity, and
De Morgan laws.
-/

theorem union_left_subset (A B : FSet alpha) : Subset A (Union A B) := by
  intro x hx
  exact Or.inl hx

theorem empty_subset (A : FSet alpha) : Subset Empty A := by
  intro x hx
  cases hx

theorem union_comm (A B : FSet alpha) : Equal (Union A B) (Union B A) := by
  intro x
  constructor
  · intro hx
    cases hx with
    | inl hA => exact Or.inr hA
    | inr hB => exact Or.inl hB
  · intro hx
    cases hx with
    | inl hB => exact Or.inr hB
    | inr hA => exact Or.inl hA

theorem union_assoc (A B C : FSet alpha) :
    Equal (Union A (Union B C)) (Union (Union A B) C) := by
  intro x
  constructor
  · intro hx
    cases hx with
    | inl hA => exact Or.inl (Or.inl hA)
    | inr hBC =>
        cases hBC with
        | inl hB => exact Or.inl (Or.inr hB)
        | inr hC => exact Or.inr hC
  · intro hx
    cases hx with
    | inl hAB =>
        cases hAB with
        | inl hA => exact Or.inl hA
        | inr hB => exact Or.inr (Or.inl hB)
    | inr hC => exact Or.inr (Or.inr hC)

theorem union_idempotent (A : FSet alpha) : Equal (Union A A) A := by
  intro x
  constructor
  · intro hx
    cases hx with
    | inl hA => exact hA
    | inr hA => exact hA
  · intro hx
    exact Or.inl hx

theorem empty_union (A : FSet alpha) : Equal (Union Empty A) A := by
  intro x
  constructor
  · intro hx
    cases hx with
    | inl hEmpty => cases hEmpty
    | inr hA => exact hA
  · intro hx
    exact Or.inr hx

theorem union_empty (A : FSet alpha) : Equal (Union A Empty) A := by
  exact equal_trans (union_comm A Empty) (empty_union A)

theorem union_univ (A : FSet alpha) : Equal (Union A Univ) Univ := by
  intro x
  constructor
  · intro _
    exact True.intro
  · intro _
    exact Or.inr True.intro

theorem inter_comm (A B : FSet alpha) : Equal (Inter A B) (Inter B A) := by
  intro x
  constructor
  · intro hx
    exact And.intro hx.right hx.left
  · intro hx
    exact And.intro hx.right hx.left

theorem inter_assoc (A B C : FSet alpha) :
    Equal (Inter A (Inter B C)) (Inter (Inter A B) C) := by
  intro x
  constructor
  · intro hx
    exact And.intro (And.intro hx.left hx.right.left) hx.right.right
  · intro hx
    exact And.intro hx.left.left (And.intro hx.left.right hx.right)

theorem inter_idempotent (A : FSet alpha) : Equal (Inter A A) A := by
  intro x
  constructor
  · intro hx
    exact hx.left
  · intro hx
    exact And.intro hx hx

theorem empty_inter (A : FSet alpha) : Equal (Inter Empty A) Empty := by
  intro x
  constructor
  · intro hx
    exact hx.left
  · intro hx
    cases hx

theorem inter_empty (A : FSet alpha) : Equal (Inter A Empty) Empty := by
  exact equal_trans (inter_comm A Empty) (empty_inter A)

theorem univ_inter (A : FSet alpha) : Equal (Inter Univ A) A := by
  intro x
  constructor
  · intro hx
    exact hx.right
  · intro hx
    exact And.intro True.intro hx

theorem inter_univ (A : FSet alpha) : Equal (Inter A Univ) A := by
  exact equal_trans (inter_comm A Univ) (univ_inter A)

theorem union_absorption (A B : FSet alpha) : Equal (Union A (Inter A B)) A := by
  intro x
  constructor
  · intro hx
    cases hx with
    | inl hA => exact hA
    | inr hAB => exact hAB.left
  · intro hx
    exact Or.inl hx

theorem inter_absorption (A B : FSet alpha) : Equal (Inter A (Union A B)) A := by
  intro x
  constructor
  · intro hx
    exact hx.left
  · intro hx
    exact And.intro hx (Or.inl hx)

theorem diff_self (A : FSet alpha) : Equal (Diff A A) Empty := by
  intro x
  constructor
  · intro hx
    exact hx.right hx.left
  · intro hx
    cases hx

theorem diff_empty (A : FSet alpha) : Equal (Diff A Empty) A := by
  intro x
  constructor
  · intro hx
    exact hx.left
  · intro hx
    exact And.intro hx (fun hEmpty => hEmpty)

theorem diff_univ (A : FSet alpha) : Equal (Diff A Univ) Empty := by
  intro x
  constructor
  · intro hx
    exact hx.right True.intro
  · intro hx
    cases hx

theorem union_distrib_inter (A B C : FSet alpha) :
    Equal (Union A (Inter B C)) (Inter (Union A B) (Union A C)) := by
  intro x
  constructor
  · intro hx
    cases hx with
    | inl hA => exact And.intro (Or.inl hA) (Or.inl hA)
    | inr hBC => exact And.intro (Or.inr hBC.left) (Or.inr hBC.right)
  · intro hx
    cases hx.left with
    | inl hA => exact Or.inl hA
    | inr hB =>
        cases hx.right with
        | inl hA => exact Or.inl hA
        | inr hC => exact Or.inr (And.intro hB hC)

theorem inter_distrib_union (A B C : FSet alpha) :
    Equal (Inter A (Union B C)) (Union (Inter A B) (Inter A C)) := by
  intro x
  constructor
  · intro hx
    cases hx.right with
    | inl hB => exact Or.inl (And.intro hx.left hB)
    | inr hC => exact Or.inr (And.intro hx.left hC)
  · intro hx
    cases hx with
    | inl hAB => exact And.intro hAB.left (Or.inl hAB.right)
    | inr hAC => exact And.intro hAC.left (Or.inr hAC.right)

theorem double_compl (A : FSet alpha) : Equal (Compl (Compl A)) A := by
  classical
  intro x
  constructor
  · intro hx
    by_cases hA : x ∈ A
    · exact hA
    · exact False.elim (hx hA)
  · intro hx hnot
    exact hnot hx

theorem union_compl_univ (A : FSet alpha) : Equal (Union A (Compl A)) Univ := by
  classical
  intro x
  constructor
  · intro _
    exact True.intro
  · intro _
    by_cases hA : x ∈ A
    · exact Or.inl hA
    · exact Or.inr hA

theorem inter_compl_empty (A : FSet alpha) : Equal (Inter A (Compl A)) Empty := by
  intro x
  constructor
  · intro hx
    exact hx.right hx.left
  · intro hx
    cases hx

theorem demorgan_union (A B : FSet alpha) :
    Equal (Compl (Union A B)) (Inter (Compl A) (Compl B)) := by
  intro x
  constructor
  · intro hx
    constructor
    · intro hA
      exact hx (Or.inl hA)
    · intro hB
      exact hx (Or.inr hB)
  · intro hx hAB
    cases hAB with
    | inl hA => exact hx.left hA
    | inr hB => exact hx.right hB

theorem demorgan_inter (A B : FSet alpha) :
    Equal (Compl (Inter A B)) (Union (Compl A) (Compl B)) := by
  classical
  intro x
  constructor
  · intro hx
    by_cases hA : x ∈ A
    · have hnotB : ¬ x ∈ B := by
        intro hB
        exact hx (And.intro hA hB)
      exact Or.inr hnotB
    · exact Or.inl hA
  · intro hx hAB
    cases hx with
    | inl hnotA => exact hnotA hAB.left
    | inr hnotB => exact hnotB hAB.right

theorem compl_listUnion (sets : List (FSet alpha)) :
    Equal (Compl (ListUnion sets)) (ListInter (sets.map Compl)) := by
  induction sets with
  | nil =>
      intro x
      constructor
      · intro _
        exact True.intro
      · intro _ hx
        cases hx
  | cons A As ih =>
      intro x
      constructor
      · intro hx
        constructor
        · intro hA
          exact hx (Or.inl hA)
        · have htail : x ∈ Compl (ListUnion As) := by
            intro hAs
            exact hx (Or.inr hAs)
          exact (ih x).mp htail
      · intro hx hUnion
        cases hUnion with
        | inl hA => exact hx.left hA
        | inr hAs =>
            have htail : x ∈ Compl (ListUnion As) := (ih x).mpr hx.right
            exact htail hAs

theorem compl_listInter (sets : List (FSet alpha)) :
    Equal (Compl (ListInter sets)) (ListUnion (sets.map Compl)) := by
  classical
  induction sets with
  | nil =>
      intro x
      constructor
      · intro hx
        exact False.elim (hx True.intro)
      · intro hx
        cases hx
  | cons A As ih =>
      intro x
      constructor
      · intro hx
        by_cases hA : x ∈ A
        · have htail : x ∈ Compl (ListInter As) := by
            intro hAs
            exact hx (And.intro hA hAs)
          exact Or.inr ((ih x).mp htail)
        · exact Or.inl hA
      · intro hx hInter
        cases hx with
        | inl hnotA => exact hnotA hInter.left
        | inr htail =>
            have htailCompl : x ∈ Compl (ListInter As) := (ih x).mpr htail
            exact htailCompl hInter.right

/-!
# Cantor diagonalization

Cantor's powerset argument is formalized directly: no function from a type to
its powerset can be surjective.
-/
theorem cantor_no_surjective_powerset (f : alpha -> FSet alpha) :
    ¬ (forall A : FSet alpha, exists x : alpha, Equal (f x) A) := by
  intro hsurj
  let diagonal : FSet alpha := fun x => ¬ x ∈ f x
  cases hsurj diagonal with
  | intro y hy =>
      have hyiff : y ∈ f y <-> y ∈ diagonal := hy y
      by_cases hmem : y ∈ f y
      · exact hyiff.mp hmem hmem
      · exact hmem (hyiff.mpr hmem)

end FSet

end Foundation
end FoC
