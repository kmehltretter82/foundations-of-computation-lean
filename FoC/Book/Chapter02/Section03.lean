import FoC.Foundation.Sets

namespace FoC
namespace Book
namespace Chapter02
namespace Section03

/-!
Book: Chapter 2, Section 2.3, Application: Programming with Sets.

This section is mainly an application bridge from set operations to
programming representations. The formal core records the pointwise membership
tests that an implementation would compute.
-/

open Foundation

-- Book: Chapter 2, Section 2.3, union as an elementwise test.
theorem union_membership_test (A B : FSet alpha) (x : alpha) :
    x ∈ FSet.Union A B <-> x ∈ A ∨ x ∈ B :=
  Iff.rfl

-- Book: Chapter 2, Section 2.3, intersection as an elementwise test.
theorem intersection_membership_test (A B : FSet alpha) (x : alpha) :
    x ∈ FSet.Inter A B <-> x ∈ A ∧ x ∈ B :=
  Iff.rfl

-- Book: Chapter 2, Section 2.3, set difference as an elementwise test.
theorem difference_membership_test (A B : FSet alpha) (x : alpha) :
    x ∈ FSet.Diff A B <-> x ∈ A ∧ ¬ x ∈ B :=
  Iff.rfl

-- Book: Chapter 2, Section 2.3, complement as an elementwise test.
theorem complement_membership_test (A : FSet alpha) (x : alpha) :
    x ∈ FSet.Compl A <-> ¬ x ∈ A :=
  Iff.rfl

end Section03
end Chapter02
end Book
end FoC
