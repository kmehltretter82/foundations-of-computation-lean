import FoC.Foundation.Sets

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section03

/-!
# Chapter 2, Section 2.3: Application - Programming with Sets

This section is mainly an application bridge from set operations to
programming representations. The formal core records the pointwise membership
tests that an implementation would compute.

The first group works with predicate sets from {module}`FoC.Foundation.Sets`.
The second group introduces a bit-vector style model, represented as a Boolean
function from indices to bits.

The point of the page is the translation between mathematics and simple
programming representations. Predicate sets give clean specifications; bit
vectors show how finite-set operations can be implemented by applying Boolean
operations independently at each index.
-/

open Foundation

/-!
## Predicate-Set Membership Tests

These statements make the computational reading of the set operations explicit:
to test membership in a compound set, test the corresponding Boolean condition
on the component memberships. The complement test is not repeated here; it is
already recorded in the Section 2.2 file as {lit}`complement_membership`.
-/

theorem union_membership_test (A B : FSet alpha) (x : alpha) :
    x ∈ FSet.Union A B <-> x ∈ A ∨ x ∈ B :=
  Iff.rfl

theorem intersection_membership_test (A B : FSet alpha) (x : alpha) :
    x ∈ FSet.Inter A B <-> x ∈ A ∧ x ∈ B :=
  Iff.rfl

theorem difference_membership_test (A B : FSet alpha) (x : alpha) :
    x ∈ FSet.Diff A B <-> x ∈ A ∧ ¬ x ∈ B :=
  Iff.rfl

/-!
## Bit-Vector Sets

For finite universes, the book describes sets as bit vectors: 32-bit binary
numbers whose universal set is the fixed index range 0 through 31. This model
uses {lit}`Fin width -> Bool`, so the width is part of the type.  The alias
{lit}`BookBitSet` specializes the reusable model to the book's 32-bit range;
complement therefore flips exactly those 32 membership bits.

The theorems in this namespace are intentionally definitional: evaluating an
operation at index {lit}`i` immediately reduces to the Boolean expression for that
bit.
-/

namespace BitVectorSet

abbrev BitSet (width : Nat) : Type :=
  Fin width -> Bool

abbrev BookBitSet : Type :=
  BitSet 32

def union (A B : BitSet width) : BitSet width :=
  fun i => A i || B i

def inter (A B : BitSet width) : BitSet width :=
  fun i => A i && B i

def diff (A B : BitSet width) : BitSet width :=
  fun i => A i && !(B i)

def compl (A : BitSet width) : BitSet width :=
  fun i => !(A i)

theorem union_apply (A B : BitSet width) (i : Fin width) :
    union A B i = (A i || B i) :=
  rfl

theorem inter_apply (A B : BitSet width) (i : Fin width) :
    inter A B i = (A i && B i) :=
  rfl

theorem diff_apply (A B : BitSet width) (i : Fin width) :
    diff A B i = (A i && !(B i)) :=
  rfl

theorem compl_apply (A : BitSet width) (i : Fin width) :
    compl A i = !(A i) :=
  rfl

theorem union_commutative (A B : BitSet width) :
    union A B = union B A := by
  funext i
  simp [union, Bool.or_comm]

theorem inter_commutative (A B : BitSet width) :
    inter A B = inter B A := by
  funext i
  simp [inter, Bool.and_comm]

theorem union_absorption (A B : BitSet width) :
    union A (inter A B) = A := by
  funext i
  simp [union, inter]
  cases A i <;> simp

theorem inter_absorption (A B : BitSet width) :
    inter A (union A B) = A := by
  funext i
  simp [inter, union]
  cases A i <;> simp

theorem double_complement (A : BitSet width) :
    compl (compl A) = A := by
  funext i
  simp [compl, Bool.not_not]

end BitVectorSet

end Section03
end Chapter02
end Book
end FoC
