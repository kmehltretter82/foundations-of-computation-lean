import FoC.Foundation.Sets

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section02

/-!
# Chapter 2, Section 2.2: The Boolean Algebra of Sets

This section formalizes the set laws from Figure 2.1. The statements are close
to the propositional laws from Chapter 1, but now the connectives act on
membership predicates: union is disjunction, intersection is conjunction, and
complement is negation.
-/

open Foundation

/-!
## Complement

The complement statement exposes the definition used throughout the section:
an element is in the complement of {lit}`A` exactly when it is not in {lit}`A`.
-/

theorem complement_membership (A : FSet alpha) (x : alpha) :
    x ∈ FSet.Compl A <-> ¬ x ∈ A :=
  Iff.rfl

/-!
## Figure 2.1 Laws

The figure's laws are packaged as extensional equality of sets. Each theorem
says that the two displayed set expressions have exactly the same members.
-/

theorem double_complement (A : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Compl A)) A :=
  FSet.double_compl A

theorem union_with_complement (A : FSet alpha) :
    FSet.Equal (FSet.Union A (FSet.Compl A)) FSet.Univ :=
  FSet.union_compl_univ A

theorem intersection_with_complement (A : FSet alpha) :
    FSet.Equal (FSet.Inter A (FSet.Compl A)) FSet.Empty :=
  FSet.inter_compl_empty A

theorem union_commutative (A B : FSet alpha) :
    FSet.Equal (FSet.Union A B) (FSet.Union B A) :=
  FSet.union_comm A B

theorem intersection_commutative (A B : FSet alpha) :
    FSet.Equal (FSet.Inter A B) (FSet.Inter B A) :=
  FSet.inter_comm A B

theorem union_associative (A B C : FSet alpha) :
    FSet.Equal (FSet.Union A (FSet.Union B C)) (FSet.Union (FSet.Union A B) C) :=
  FSet.union_assoc A B C

theorem intersection_associative (A B C : FSet alpha) :
    FSet.Equal (FSet.Inter A (FSet.Inter B C)) (FSet.Inter (FSet.Inter A B) C) :=
  FSet.inter_assoc A B C

theorem union_distributes_over_intersection (A B C : FSet alpha) :
    FSet.Equal (FSet.Union A (FSet.Inter B C))
      (FSet.Inter (FSet.Union A B) (FSet.Union A C)) :=
  FSet.union_distrib_inter A B C

theorem intersection_distributes_over_union (A B C : FSet alpha) :
    FSet.Equal (FSet.Inter A (FSet.Union B C))
      (FSet.Union (FSet.Inter A B) (FSet.Inter A C)) :=
  FSet.inter_distrib_union A B C

/-!
## De Morgan's Laws

The finite-family versions express the same complement-switching principle for
lists of sets, which is enough for the book-facing finite examples.
-/

theorem demorgan_union (A B : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Union A B))
      (FSet.Inter (FSet.Compl A) (FSet.Compl B)) :=
  FSet.demorgan_union A B

theorem demorgan_intersection (A B : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Inter A B))
      (FSet.Union (FSet.Compl A) (FSet.Compl B)) :=
  FSet.demorgan_inter A B

theorem generalized_demorgan_union (sets : List (FSet alpha)) :
    FSet.Equal (FSet.Compl (FSet.ListUnion sets))
      (FSet.ListInter (sets.map FSet.Compl)) :=
  FSet.compl_listUnion sets

theorem generalized_demorgan_intersection (sets : List (FSet alpha)) :
    FSet.Equal (FSet.Compl (FSet.ListInter sets))
      (FSet.ListUnion (sets.map FSet.Compl)) :=
  FSet.compl_listInter sets

end Section02
end Chapter02
end Book
end FoC
