import FoC.Foundation.Sets

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section02

/-!
# Chapter 2, Section 2.2: The Boolean Algebra of Sets

This section formalizes the set laws from Figure 2.2, together with a few
companion identities the chapter uses but does not display in a figure. The
statements are close to the propositional laws from Chapter 1, but now the
connectives act on membership predicates: union is disjunction, intersection
is conjunction, and complement is negation.

A set equality theorem here should be read pointwise. To prove, for example,
that two compound set expressions are equal, Lean unfolds membership in each
side and proves the corresponding logical statement about an arbitrary element.
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
## Figure 2.2 Laws

The figure's laws are packaged as extensional equality of sets. Each theorem
says that the two displayed set expressions have exactly the same members.
The empty-set laws are stated with the empty set on the right; the figure's
forms follow by commutativity. The complement laws are stated classically,
with no decidability side conditions, exactly as in the book.

This mirrors Section 1.2: Boolean algebra of formulas and Boolean algebra of
sets have the same logical shape once membership in a set is read as a
proposition.
-/

theorem double_complement (A : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Compl A)) A :=
  FSet.double_compl_classical A

theorem union_with_complement (A : FSet alpha) :
    FSet.Equal (FSet.Union A (FSet.Compl A)) FSet.Univ :=
  FSet.union_compl_univ_classical A

theorem intersection_with_complement (A : FSet alpha) :
    FSet.Equal (FSet.Inter A (FSet.Compl A)) FSet.Empty :=
  FSet.inter_compl_empty A

theorem union_idempotent (A : FSet alpha) :
    FSet.Equal (FSet.Union A A) A :=
  FSet.union_idempotent A

theorem intersection_idempotent (A : FSet alpha) :
    FSet.Equal (FSet.Inter A A) A :=
  FSet.inter_idempotent A

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

theorem union_with_empty_set (A : FSet alpha) :
    FSet.Equal (FSet.Union A FSet.Empty) A :=
  FSet.union_empty A

theorem intersection_with_empty_set (A : FSet alpha) :
    FSet.Equal (FSet.Inter A FSet.Empty) FSet.Empty :=
  FSet.inter_empty A

/-!
## Laws Beyond the Figure

The remaining identities are not displayed in Figure 2.2. The absorption laws
are exercise material for this section (the union form is Exercise 8), the
universal-set identities are duals of the figure's empty-set laws, and the
difference simplifications appear in no figure of the chapter. They are
collected here because later sections use them alongside the figure's laws.
-/

theorem union_absorption (A B : FSet alpha) :
    FSet.Equal (FSet.Union A (FSet.Inter A B)) A :=
  FSet.union_absorption A B

theorem intersection_absorption (A B : FSet alpha) :
    FSet.Equal (FSet.Inter A (FSet.Union A B)) A :=
  FSet.inter_absorption A B

theorem union_with_universal_set (A : FSet alpha) :
    FSet.Equal (FSet.Union A FSet.Univ) FSet.Univ :=
  FSet.union_univ A

theorem intersection_with_universal_set (A : FSet alpha) :
    FSet.Equal (FSet.Inter A FSet.Univ) A :=
  FSet.inter_univ A

theorem difference_with_self (A : FSet alpha) :
    FSet.Equal (FSet.Diff A A) FSet.Empty :=
  FSet.diff_self A

theorem difference_with_empty_set (A : FSet alpha) :
    FSet.Equal (FSet.Diff A FSet.Empty) A :=
  FSet.diff_empty A

theorem difference_with_universal_set (A : FSet alpha) :
    FSet.Equal (FSet.Diff A FSet.Univ) FSet.Empty :=
  FSet.diff_univ A

/-!
## De Morgan's Laws

The finite-family versions express the same complement-switching principle for
lists of sets, which is enough for the book-facing finite examples.

The list-based versions are the formal counterpart of applying De Morgan's law
to a finite union or finite intersection one set at a time.
-/

theorem demorgan_union (A B : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Union A B))
      (FSet.Inter (FSet.Compl A) (FSet.Compl B)) :=
  FSet.demorgan_union A B

theorem demorgan_intersection (A B : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Inter A B))
      (FSet.Union (FSet.Compl A) (FSet.Compl B)) :=
  FSet.demorgan_inter_classical A B

theorem generalized_demorgan_union (sets : List (FSet alpha)) :
    FSet.Equal (FSet.Compl (FSet.ListUnion sets))
      (FSet.ListInter (sets.map FSet.Compl)) :=
  FSet.compl_listUnion sets

theorem generalized_demorgan_intersection (sets : List (FSet alpha)) :
    FSet.Equal (FSet.Compl (FSet.ListInter sets))
      (FSet.ListUnion (sets.map FSet.Compl)) :=
  FSet.compl_listInter_classical sets

end Section02
end Chapter02
end Book
end FoC
