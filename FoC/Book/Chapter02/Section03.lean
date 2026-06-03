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
-/

open Foundation

/-!
## Predicate-Set Membership Tests

These statements make the computational reading of the set operations explicit:
to test membership in a compound set, test the corresponding Boolean condition
on the component memberships.
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

theorem complement_membership_test (A : FSet alpha) (x : alpha) :
    x ∈ FSet.Compl A <-> ¬ x ∈ A :=
  Iff.rfl

/-!
## Bit-Vector Sets

For finite universes, the book describes sets as bit vectors. This model uses
{lean}`Nat -> Bool`, so each operation becomes a pointwise Boolean operation on
indices.
-/

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

theorem union_apply (A B : BitSet) (i : Nat) :
    union A B i = (A i || B i) :=
  rfl

theorem inter_apply (A B : BitSet) (i : Nat) :
    inter A B i = (A i && B i) :=
  rfl

theorem diff_apply (A B : BitSet) (i : Nat) :
    diff A B i = (A i && !(B i)) :=
  rfl

theorem compl_apply (A : BitSet) (i : Nat) :
    compl A i = !(A i) :=
  rfl

end BitVectorSet

end Section03
end Chapter02
end Book
end FoC
