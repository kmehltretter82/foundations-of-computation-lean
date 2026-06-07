import FoC.Foundation.Sets
import FoC.Book.Chapter01.Section08

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section01

/-!
# Chapter 2, Section 2.1: Basic Concepts

This section formalizes the first set-theoretic vocabulary from the book:
equality, subset, powerset, the empty set, and the induction principles reused
later in Chapter 2.

The project represents a set over a type as a predicate on that type. Set
equality is therefore extensional equality: two sets are equal when every
object has the same membership status in both sets.

This representation keeps the set theory typed. A set of {lit}`alpha` values can
only contain {lit}`alpha` values, and membership is a proposition rather than a
runtime lookup. As a result, many familiar set identities become direct logical
equivalences about a generic element.
-/

open Foundation

/-!
## Set Equality and Subsets

The book's usual criterion for equality is captured as mutual subset inclusion.
The subset exercise then reuses the transitivity theorem from
{module}`FoC.Foundation.Sets`.

The first theorem is the extensionality principle readers use informally: to
show two sets are equal, prove inclusion both ways. The second theorem is a
typical reuse of that inclusion vocabulary.
-/

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

theorem subset_transitive {A B C : FSet alpha}
    (hAB : FSet.Subset A B) (hBC : FSet.Subset B C) :
    FSet.Subset A C :=
  FSet.subset_trans hAB hBC

/-!
## Powersets and the Empty Set

Membership in the powerset is definitionally the same thing as being a subset.
The empty set subset statement is the typed predicate-set version of the
ordinary fact that no element can witness a failure of inclusion.
-/

theorem powerset_membership {A B : FSet alpha} :
    B ∈ FSet.Powerset A <-> FSet.Subset B A :=
  Iff.rfl

theorem empty_is_subset (A : FSet alpha) : FSet.Subset FSet.Empty A :=
  FSet.empty_subset A

/-!
## Induction

The chapter states ordinary mathematical induction and strong induction before
using them in later set and counting arguments. These wrappers point back to
the Chapter 1 formalization of the same principles.
-/

theorem mathematical_induction (P : Nat -> Prop)
    (base : P 0)
    (step : forall k, P k -> P (k + 1)) :
    forall n, P n :=
  Chapter01.Section08.mathematical_induction P base step

theorem strong_induction (P : Nat -> Prop)
    (step : forall n, (forall k, k < n -> P k) -> P n) :
    forall n, P n :=
  Chapter01.Section08.strong_induction_book P step

/-!
## Typed Sets and Russell's Paradox

Russell's paradox is discussed in this section as a warning about unrestricted
set comprehension. The standalone development avoids the paradox by using
typed predicate sets, so self-membership is not a well-typed operation here.

Because there is no universal type of all sets in this model, the expression
"the set of all sets that do not contain themselves" cannot be formed directly
as a typed predicate set.  The two theorems below record the book's paradox as
an abstract schema over a hypothetical self-membership relation.
-/

theorem russell_no_unrestricted_comprehension
    (Mem : entity -> entity -> Prop) :
    ¬ (forall P : entity -> Prop,
        exists R : entity, forall X : entity, Mem X R <-> P X) := by
  intro hcomp
  cases hcomp (fun X => ¬ Mem X X) with
  | intro R hR =>
      have hnot : ¬ Mem R R := by
        intro hmem
        exact (hR R).mp hmem hmem
      exact hnot ((hR R).mpr hnot)

theorem russell_no_universal_set_with_separation
    (Mem : entity -> entity -> Prop)
    (separation :
      forall A : entity, forall P : entity -> Prop,
        exists R : entity, forall X : entity, Mem X R <-> Mem X A ∧ P X) :
    ¬ (exists V : entity, forall X : entity, Mem X V) := by
  intro hVexists
  cases hVexists with
  | intro V hV =>
      cases separation V (fun X => ¬ Mem X X) with
      | intro R hR =>
          have hnot : ¬ Mem R R := by
            intro hmem
            exact ((hR R).mp hmem).right hmem
          exact hnot ((hR R).mpr (And.intro (hV R) hnot))

end Section01
end Chapter02
end Book
end FoC
