import FoC.Foundation.Relations

namespace FoC
namespace Book
namespace Chapter02
namespace Section07

/-!
Book: Chapter 2, Section 2.7, Relations.
-/

open Foundation

-- Book: Chapter 2, Section 2.7, equality is an equivalence relation.
theorem equality_is_equivalence : Rel.Equivalence (fun x y : alpha => x = y) :=
  Rel.equality_equivalence

-- Book: Chapter 2, Section 2.7, equivalence classes contain their representative.
theorem representative_in_equivalence_class {R : Rel alpha}
    (h : Rel.Equivalence R) (x : alpha) :
    x ∈ Rel.Class R x :=
  Rel.class_self h x

-- Book: Chapter 2, Section 2.7, related representatives have equal classes.
theorem related_representatives_have_equal_classes {R : Rel alpha}
    (h : Rel.Equivalence R) {a b : alpha} (hab : R a b) :
    FSet.Equal (Rel.Class R a) (Rel.Class R b) :=
  Rel.class_equal_of_related h hab

-- Book: Chapter 2, Section 2.7, Theorem: equivalence classes form a partition.
def equivalence_classes_form_partition {R : Rel alpha}
    (h : Rel.Equivalence R) : Rel.Partition alpha :=
  Rel.classes_partition h

-- Book: Chapter 2, Section 2.7, a function induces an equivalence relation by equal values.
theorem function_fiber_equivalence (f : alpha -> beta) :
    Rel.Equivalence (fun x y : alpha => f x = f y) :=
  Rel.same_fiber_equivalence f

-- Book: Chapter 2, Section 2.7, symmetric and antisymmetric relations imply equality.
theorem symmetric_antisymmetric_relation_is_subidentity {R : Rel alpha}
    (hs : Rel.Symmetric R) (ha : Rel.Antisymmetric R) :
    forall {x y}, R x y -> x = y :=
  Rel.symmetric_antisymmetric_implies_eq hs ha

-- Book: Chapter 2, Section 2.7, transitive closure is transitive.
theorem transitive_closure_is_transitive {R : Rel alpha} :
    Rel.Transitive (Rel.TransitiveClosure R) :=
  Rel.transitiveClosure_transitive

-- Book: Chapter 2, Section 2.7, transitive closure of a reflexive symmetric relation is an equivalence relation.
theorem transitive_closure_equivalence_of_reflexive_symmetric {R : Rel alpha}
    (hr : Rel.Reflexive R) (hs : Rel.Symmetric R) :
    Rel.Equivalence (Rel.TransitiveClosure R) :=
  Rel.transitiveClosure_equivalence_of_reflexive_symmetric hr hs

end Section07
end Chapter02
end Book
end FoC
