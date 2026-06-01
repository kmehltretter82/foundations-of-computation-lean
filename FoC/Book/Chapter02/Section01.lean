import FoC.Foundation.Sets
import FoC.Book.Chapter01.Section08

namespace FoC
namespace Book
namespace Chapter02
namespace Section01

/-!
Book: Chapter 2, Section 2.1, Basic Concepts.
-/

open Foundation

-- Book: Chapter 2, Section 2.1, set equality criterion.
theorem set_equality_iff_mutual_subset {A B : FSet alpha} :
    FSet.Equal A B <-> FSet.Subset A B ∧ FSet.Subset B A := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact (h x).mp hx
    · intro x hx
      exact (h x).mpr hx
  · intro h
    exact FSet.equal_of_subsets h.left h.right

-- Book: Chapter 2, Section 2.1, subset transitivity exercise.
theorem subset_transitive {A B C : FSet alpha}
    (hAB : FSet.Subset A B) (hBC : FSet.Subset B C) :
    FSet.Subset A C :=
  FSet.subset_trans hAB hBC

-- Book: Chapter 2, Section 2.1, powerset definition.
theorem powerset_membership {A B : FSet alpha} :
    B ∈ FSet.Powerset A <-> FSet.Subset B A :=
  Iff.rfl

-- Book: Chapter 2, Section 2.1, empty set subset fact.
theorem empty_is_subset (A : FSet alpha) : FSet.Subset FSet.Empty A :=
  FSet.empty_subset A

-- Book: Chapter 2, Section 2.1, induction principle used in the chapter.
theorem mathematical_induction (P : Nat -> Prop)
    (base : P 0)
    (step : forall k, P k -> P (k + 1)) :
    forall n, P n :=
  Chapter01.Section08.mathematical_induction P base step

-- Book: Chapter 2, Section 2.1, second form of induction.
theorem strong_induction (P : Nat -> Prop)
    (step : forall n, (forall k, k < n -> P k) -> P n) :
    forall n, P n :=
  Chapter01.Section08.strong_induction_book P step

/-!
Russell's paradox is discussed in this section as a warning about unrestricted
set comprehension. The standalone development avoids the paradox by using
typed predicate sets, so self-membership is not a well-typed operation here.
-/

end Section01
end Chapter02
end Book
end FoC
