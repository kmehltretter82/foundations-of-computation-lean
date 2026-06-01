import FoC.Foundation.Sets

namespace FoC
namespace Book
namespace Chapter02
namespace Section02

/-!
Book: Chapter 2, Section 2.2, The Boolean Algebra of Sets.
-/

open Foundation

-- Book: Chapter 2, Section 2.2, complement definition.
theorem complement_membership (A : FSet alpha) (x : alpha) :
    x ∈ FSet.Compl A <-> ¬ x ∈ A :=
  Iff.rfl

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem double_complement (A : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Compl A)) A :=
  FSet.double_compl A

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem union_with_complement (A : FSet alpha) :
    FSet.Equal (FSet.Union A (FSet.Compl A)) FSet.Univ :=
  FSet.union_compl_univ A

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem intersection_with_complement (A : FSet alpha) :
    FSet.Equal (FSet.Inter A (FSet.Compl A)) FSet.Empty :=
  FSet.inter_compl_empty A

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem union_commutative (A B : FSet alpha) :
    FSet.Equal (FSet.Union A B) (FSet.Union B A) :=
  FSet.union_comm A B

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem intersection_commutative (A B : FSet alpha) :
    FSet.Equal (FSet.Inter A B) (FSet.Inter B A) :=
  FSet.inter_comm A B

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem union_associative (A B C : FSet alpha) :
    FSet.Equal (FSet.Union A (FSet.Union B C)) (FSet.Union (FSet.Union A B) C) :=
  FSet.union_assoc A B C

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem intersection_associative (A B C : FSet alpha) :
    FSet.Equal (FSet.Inter A (FSet.Inter B C)) (FSet.Inter (FSet.Inter A B) C) :=
  FSet.inter_assoc A B C

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem union_distributes_over_intersection (A B C : FSet alpha) :
    FSet.Equal (FSet.Union A (FSet.Inter B C))
      (FSet.Inter (FSet.Union A B) (FSet.Union A C)) :=
  FSet.union_distrib_inter A B C

-- Book: Chapter 2, Section 2.2, Figure 2.1.
theorem intersection_distributes_over_union (A B C : FSet alpha) :
    FSet.Equal (FSet.Inter A (FSet.Union B C))
      (FSet.Union (FSet.Inter A B) (FSet.Inter A C)) :=
  FSet.inter_distrib_union A B C

-- Book: Chapter 2, Section 2.2, De Morgan's laws.
theorem demorgan_union (A B : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Union A B))
      (FSet.Inter (FSet.Compl A) (FSet.Compl B)) :=
  FSet.demorgan_union A B

-- Book: Chapter 2, Section 2.2, De Morgan's laws.
theorem demorgan_intersection (A B : FSet alpha) :
    FSet.Equal (FSet.Compl (FSet.Inter A B))
      (FSet.Union (FSet.Compl A) (FSet.Compl B)) :=
  FSet.demorgan_inter A B

-- Book: Chapter 2, Section 2.2, generalized De Morgan law for finite families.
theorem generalized_demorgan_union (sets : List (FSet alpha)) :
    FSet.Equal (FSet.Compl (FSet.ListUnion sets))
      (FSet.ListInter (sets.map FSet.Compl)) :=
  FSet.compl_listUnion sets

-- Book: Chapter 2, Section 2.2, dual generalized De Morgan law for finite families.
theorem generalized_demorgan_intersection (sets : List (FSet alpha)) :
    FSet.Equal (FSet.Compl (FSet.ListInter sets))
      (FSet.ListUnion (sets.map FSet.Compl)) :=
  FSet.compl_listInter sets

end Section02
end Chapter02
end Book
end FoC
