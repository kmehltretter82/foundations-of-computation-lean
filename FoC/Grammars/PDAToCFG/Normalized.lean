import FoC.Grammars.PDAToCFG.Completeness

set_option doc.verso true

/-!
# Normalized PDA-to-CFG exactness
-/

namespace FoC
namespace Grammars

open Languages

namespace PDA

/-!
# Normalized PDA conversion

For an arbitrary finitely presented PDA, pop normalization produces the
top-pop form needed by the exact PDA-to-CFG construction.
-/

def PopNormalizeLanguageExact
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    Prop :=
  Language.Equal (AcceptedLanguage (PopNormalize M presentation))
    (AcceptedLanguage M)

theorem popNormalizeLanguageExact
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    PopNormalizeLanguageExact M presentation :=
  popNormalize_acceptedLanguage_exact presentation

def ToCFGNormalized (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    CFG input
      (ToCFGNonterminal stack
        (PopNormalizedState (M := M) presentation)) :=
  ToCFG (PopNormalize M presentation)
    (popNormalizeFinitePresentation M presentation)

theorem toCFGNormalized_hasFiniteProductions
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    CFG.HasFiniteProductions (ToCFGNormalized M presentation) :=
  toCFG_hasFiniteProductions (PopNormalize M presentation)
    (popNormalizeFinitePresentation M presentation)

theorem toCFGNormalized_language_exact
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFGNormalized M presentation))
      (AcceptedLanguage (PopNormalize M presentation)) :=
  toCFG_language_exact_of_topPop
    (M := PopNormalize M presentation)
    (presentation := popNormalizeFinitePresentation M presentation)
    (popNormalize_popsAtMostOne M presentation)

theorem toCFGNormalized_language_exact_of_popNormalizeLanguageExact
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hexact : PopNormalizeLanguageExact M presentation) :
    Language.Equal (CFG.GeneratedLanguage (ToCFGNormalized M presentation))
      (AcceptedLanguage M) := by
  intro w
  exact Iff.trans (toCFGNormalized_language_exact M presentation w)
    (hexact w)

theorem toCFGNormalized_language_exact_original
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFGNormalized M presentation))
      (AcceptedLanguage M) :=
  toCFGNormalized_language_exact_of_popNormalizeLanguageExact
    (M := M) (presentation := presentation)
    (popNormalizeLanguageExact M presentation)

theorem acceptedLanguage_subset_popNormalizeLanguage
    {M : PDA input stack state} (presentation : FinitePresentation M) :
    Language.Subset (AcceptedLanguage M)
      (AcceptedLanguage (PopNormalize M presentation)) :=
  acceptedLanguage_subset_popNormalize presentation

theorem toCFGNormalized_generates_of_accepts
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input}
    (haccepts : w ∈ AcceptedLanguage M) :
    w ∈ CFG.GeneratedLanguage (ToCFGNormalized M presentation) :=
  (toCFGNormalized_language_exact M presentation w).mpr
    (acceptedLanguage_subset_popNormalize presentation w haccepts)

theorem acceptedLanguage_subset_toCFGNormalized
    {M : PDA input stack state} (presentation : FinitePresentation M) :
    Language.Subset (AcceptedLanguage M)
      (CFG.GeneratedLanguage (ToCFGNormalized M presentation)) := by
  intro w hw
  exact toCFGNormalized_generates_of_accepts
    (M := M) (presentation := presentation) hw

theorem toCFG_nonterminals_finite
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    (ToCFG M presentation).nonterminalsFinite =
      ToCFGNonterminal.finite presentation.stackFinite M.statesFinite :=
  rfl


end PDA

end Grammars
end FoC
