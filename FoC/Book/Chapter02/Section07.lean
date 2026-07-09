import FoC.Foundation.Relations

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section07

/-!
# Chapter 2, Section 2.7: Relations

This section formalizes the chapter's relation vocabulary using the reusable
definitions in {module}`FoC.Foundation.Relations`. The focus is on equivalence
relations, equivalence classes, partitions, partial and total orders, and
transitive closure.

A relation is modeled as a proposition-valued function of two inputs. The
properties below, such as reflexive, symmetric, antisymmetric, and transitive,
are predicates on that two-input function.
-/

open Foundation

/-!
## Equivalence Relations and Classes

Equality is the canonical equivalence relation. For an arbitrary equivalence
relation, each element belongs to its own class, and related representatives
determine the same class.

The class of an element is the set of all elements related to it. The theorem
about related representatives is the familiar fact that equivalence classes do
not depend on which representative from the class is chosen.
-/

theorem equality_is_equivalence : Rel.Equivalence (fun x y : alpha => x = y) :=
  Rel.equality_equivalence

theorem representative_in_equivalence_class {R : Rel alpha}
    (h : Rel.Equivalence R) (x : alpha) :
    x ∈ Rel.Class R x :=
  Rel.class_self h x

theorem related_representatives_have_equal_classes {R : Rel alpha}
    (h : Rel.Equivalence R) {a b : alpha} (hab : R a b) :
    FSet.Equal (Rel.Class R a) (Rel.Class R b) :=
  Rel.class_equal_of_related h hab

theorem equal_classes_iff_related_representatives {R : Rel alpha}
    (h : Rel.Equivalence R) {a b : alpha} :
    FSet.Equal (Rel.Class R a) (Rel.Class R b) <-> R a b :=
  Rel.class_equal_iff_related h

theorem overlapping_equivalence_classes_are_equal {R : Rel alpha}
    (h : Rel.Equivalence R) {a b : alpha}
    (hoverlap : exists x, x ∈ Rel.Class R a ∧ x ∈ Rel.Class R b) :
    FSet.Equal (Rel.Class R a) (Rel.Class R b) :=
  Rel.overlapping_classes_equal h hoverlap

theorem equivalence_classes_equal_or_disjoint {R : Rel alpha}
    (h : Rel.Equivalence R) (a b : alpha) :
    FSet.Equal (Rel.Class R a) (Rel.Class R b) ∨
      FSet.Disjoint (Rel.Class R a) (Rel.Class R b) :=
  Rel.classes_equal_or_disjoint_classical h a b

/-!
## Partitions and Fibers

The classes of an equivalence relation form a partition. Conversely, functions
give natural equivalence relations by putting two inputs in the same class when
they have the same output.
-/

def equivalence_classes_form_partition {R : Rel alpha}
    (h : Rel.Equivalence R) : Rel.Partition alpha :=
  Rel.classes_partition h

theorem function_fiber_equivalence (f : alpha -> beta) :
    Rel.Equivalence (fun x y : alpha => f x = f y) :=
  Rel.same_fiber_equivalence f

/-!
## Partial and Total Orders

The book's two standard examples witness the order vocabulary. The numeric
order on the natural numbers is reflexive, antisymmetric, transitive, and
total. Set inclusion is a partial order: reflexivity and transitivity are
immediate, and antisymmetry is Theorem 2.1, that mutual inclusion forces
equality. The book states the inclusion example for the power set of a set;
here it is stated for all predicate sets over a type, which is the power set
of the universal set. In this model, mutual inclusion yields extensional
equality of the membership predicates, which function and proposition
extensionality upgrade to Lean equality.

Inclusion is not a total order: as soon as the underlying type has two
distinct elements, the corresponding singleton sets are incomparable.
-/

theorem natural_order_is_total_order :
    Rel.TotalOrder (fun m n : Nat => m ≤ n) :=
  Rel.nat_le_total_order

theorem subset_is_partial_order :
    Rel.PartialOrder (fun A B : FSet alpha => FSet.Subset A B) :=
  Rel.subset_partial_order

theorem subset_is_not_total {a b : alpha} (hab : a ≠ b) :
    ¬ (forall A B : FSet alpha, FSet.Subset A B ∨ FSet.Subset B A) :=
  Rel.subset_not_total_order a b hab

/-!
## Relation Properties and Closure

The final statements connect the named relation properties. A relation that is
both symmetric and antisymmetric cannot relate distinct elements, and the
transitive closure construction produces a transitive relation. If the starting
relation is reflexive and symmetric, that closure is an equivalence relation.
-/

theorem symmetric_antisymmetric_relation_is_subidentity {R : Rel alpha}
    (hs : Rel.Symmetric R) (ha : Rel.Antisymmetric R) :
    forall {x y}, R x y -> x = y :=
  Rel.symmetric_antisymmetric_implies_eq hs ha

theorem transitive_closure_is_transitive {R : Rel alpha} :
    Rel.Transitive (Rel.TransitiveClosure R) :=
  Rel.transitiveClosure_transitive

theorem transitive_closure_equivalence_of_reflexive_symmetric {R : Rel alpha}
    (hr : Rel.Reflexive R) (hs : Rel.Symmetric R) :
    Rel.Equivalence (Rel.TransitiveClosure R) :=
  Rel.transitiveClosure_equivalence_of_reflexive_symmetric hr hs

end Section07
end Chapter02
end Book
end FoC
