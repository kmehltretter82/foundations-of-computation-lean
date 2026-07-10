import FoC.Book.Chapter04.Section05.Pumping

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section05

open Languages
open Grammars

/-!
# Context-Free Nonclosure Consequences

The concrete {lit}`a^n b^n c^n` witnesses yield nonclosure under
intersection. Combining union closure with De Morgan's law then gives
nonclosure under complement.
-/

/-!
## Nonclosure Consequences

Because `{ a^n b^n c^* }` and `{ a^* b^n c^n }` are context-free but their
intersection is {lit}`{ a^n b^n c^n }`, finite-production context-free languages
are not closed under intersection. If they were closed under complement as
well as union, De Morgan's law would give intersection closure, so complement
closure fails too.
-/

theorem finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
    {L M : Language ABC}
    (hL : FiniteProductionContextFreeLanguage L)
    (hM : FiniteProductionContextFreeLanguage M)
    (hEq : Language.Equal (Language.Inter L M) anbncnLanguage) :
    ¬ ClosedUnderIntersection
      (FiniteProductionContextFreeLanguage (terminal := ABC)) := by
  intro hClosed
  have hInter : FiniteProductionContextFreeLanguage (Language.Inter L M) :=
    hClosed L M hL hM
  exact anbncn_not_finite_production_context_free
    (finite_production_context_free_of_equal hEq hInter)

theorem finite_production_cfls_not_closed_under_intersection :
    ¬ ClosedUnderIntersection
      (FiniteProductionContextFreeLanguage (terminal := ABC)) :=
  finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
    anbnCstar_finite_production_context_free
    astarBnCn_finite_production_context_free
    anbnCstar_inter_astarBnCn_exact

theorem complement_closure_and_union_closure_imply_intersection_closure
    {C : Language terminal -> Prop}
    (hExt : LanguageClassExtensional C)
    (hUnion : ClosedUnderUnion C)
    (hCompl : ClosedUnderComplement C) :
    ClosedUnderIntersection C := by
  classical
  intro L M hL hM
  let N : Language terminal :=
    Language.Compl (Language.Union (Language.Compl L) (Language.Compl M))
  have hN : C N := by
    have hUnionCompl : C (Language.Union (Language.Compl L) (Language.Compl M)) :=
      hUnion (Language.Compl L) (Language.Compl M)
      (hCompl L hL) (hCompl M hM)
    simpa [N] using hCompl
      (Language.Union (Language.Compl L) (Language.Compl M)) hUnionCompl
  apply hExt N (Language.Inter L M)
  · intro w
    constructor
    · intro hw
      change ¬ w ∈ Language.Union (Language.Compl L) (Language.Compl M) at hw
      constructor
      · by_cases hmem : w ∈ L
        · exact hmem
        · exact False.elim (hw (Or.inl hmem))
      · by_cases hmem : w ∈ M
        · exact hmem
        · exact False.elim (hw (Or.inr hmem))
    · intro hw
      change ¬ w ∈ Language.Union (Language.Compl L) (Language.Compl M)
      intro hUnionMem
      cases hUnionMem with
      | inl hnotL => exact hnotL hw.left
      | inr hnotM => exact hnotM hw.right
  · exact hN

theorem finite_production_cfl_complement_nonclosure_from_anbncn_witnesses
    {L M : Language ABC}
    (hL : FiniteProductionContextFreeLanguage L)
    (hM : FiniteProductionContextFreeLanguage M)
    (hEq : Language.Equal (Language.Inter L M) anbncnLanguage)
    (hUnion :
      ClosedUnderUnion
        (FiniteProductionContextFreeLanguage (terminal := ABC))) :
    ¬ ClosedUnderComplement
      (FiniteProductionContextFreeLanguage (terminal := ABC)) := by
  intro hCompl
  have hInterClosed :
      ClosedUnderIntersection
        (FiniteProductionContextFreeLanguage (terminal := ABC)) :=
    complement_closure_and_union_closure_imply_intersection_closure
      finite_production_context_free_extensional hUnion hCompl
  exact
    finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
      hL hM hEq hInterClosed

theorem finite_production_cfls_not_closed_under_complement :
    ¬ ClosedUnderComplement
      (FiniteProductionContextFreeLanguage (terminal := ABC)) :=
  finite_production_cfl_complement_nonclosure_from_anbncn_witnesses
    anbnCstar_finite_production_context_free
    astarBnCn_finite_production_context_free
    anbnCstar_inter_astarBnCn_exact
    finite_production_cfls_closed_under_union

/-!
The concrete contradiction for `{ a^n b^n c^n | n >= 0 }` is now formalized:
no pumping length can satisfy the book's quantified CFL pumping property for
this language. Since the public {lean}`CFL.ContextFreeLanguage` predicate is
now the book-facing finite-production predicate, this gives the unconditional
{lean}`anbncn_not_context_free` theorem.
-/

end Section05
end Chapter04
end Book
end FoC

