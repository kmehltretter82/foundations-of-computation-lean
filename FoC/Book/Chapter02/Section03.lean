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

namespace BitVectorSet

abbrev BitSet : Type :=
  Nat -> Bool

def empty : BitSet :=
  fun _ => false

def universal : BitSet :=
  fun _ => true

def union (A B : BitSet) : BitSet :=
  fun i => A i || B i

def inter (A B : BitSet) : BitSet :=
  fun i => A i && B i

def diff (A B : BitSet) : BitSet :=
  fun i => A i && !(B i)

def compl (A : BitSet) : BitSet :=
  fun i => !(A i)

-- Book: Chapter 2, Section 2.3, bit-vector union is pointwise Boolean or.
theorem union_apply (A B : BitSet) (i : Nat) :
    union A B i = (A i || B i) :=
  rfl

-- Book: Chapter 2, Section 2.3, bit-vector intersection is pointwise Boolean and.
theorem inter_apply (A B : BitSet) (i : Nat) :
    inter A B i = (A i && B i) :=
  rfl

-- Book: Chapter 2, Section 2.3, bit-vector difference is pointwise and-not.
theorem diff_apply (A B : BitSet) (i : Nat) :
    diff A B i = (A i && !(B i)) :=
  rfl

-- Book: Chapter 2, Section 2.3, bit-vector complement is pointwise negation.
theorem compl_apply (A : BitSet) (i : Nat) :
    compl A i = !(A i) :=
  rfl

end BitVectorSet

end Section03
end Chapter02
end Book
end FoC
