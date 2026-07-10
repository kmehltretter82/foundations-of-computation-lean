import FoC.Book.Chapter04.Section04.Basic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

/-!
# Chapter 4 PDA-to-CFG Consequences

The reusable normalization, summary-nonterminal construction, and exactness
proofs live in {module}`FoC.Grammars.PDAToCFG`. This book-facing module keeps
only the consequences stated by Chapter 4:

- a finitely presented top-pop PDA accepts a context-free language;
- every finitely presented PDA accepts a context-free language after pop
  normalization;
- finite-presentation PDA recognizability implies context-freeness; and
- over a finite input alphabet, context-freeness is equivalent to
  finite-presentation PDA recognizability.

The conversion's internal trace, summary, and derivation lemmas are intentionally
not republished under chapter-specific names. Their canonical declarations are
in the foundational PDA namespace.
-/

/-- A finitely presented top-pop PDA accepts a context-free language. -/
theorem finite_presentation_top_pop_pda_context_free
    {input stack state : Type}
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hnorm : PDA.PopsAtMostOne M) :
    CFL.ContextFreeLanguage (PDA.AcceptedLanguage M) := by
  exists PDA.ToCFGNonterminal stack state
  exists PDA.ToCFG M presentation
  constructor
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      (PDA.toCFG_hasFiniteProductions M presentation)
  · exact PDA.toCFG_language_exact_of_topPop
      (M := M) (presentation := presentation) hnorm

/-- Every finitely presented PDA accepts a context-free language. -/
theorem finite_presentation_pda_context_free
    {input stack state : Type}
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M} :
    CFL.ContextFreeLanguage (PDA.AcceptedLanguage M) := by
  exists PDA.ToCFGNonterminal stack
    (PDA.PopNormalizedState (M := M) presentation)
  exists PDA.ToCFGNormalized M presentation
  constructor
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      (PDA.toCFGNormalized_hasFiniteProductions M presentation)
  · exact PDA.toCFGNormalized_language_exact_original M presentation

/-- Every language recognized by a finitely presented PDA is context-free. -/
theorem finite_presentation_pda_recognizable_context_free
    {input : Type} {L : Language input}
    (hL : PDA.FinitePresentationRecognizable L) :
    CFL.ContextFreeLanguage L := by
  rcases hL with ⟨stack, state, M, presentation, hM⟩
  rcases finite_presentation_pda_context_free
      (M := M) (presentation := presentation) with
    ⟨nonterminal, G, hGfinite, hGexact⟩
  exact ⟨nonterminal, G, hGfinite,
    Foundation.FSet.equal_trans hGexact hM⟩

/--
Over a finite input alphabet, context-free languages are exactly the languages
recognized by finitely presented PDAs.
-/
theorem context_free_iff_finite_presentation_pda_recognizable
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input} :
    CFL.ContextFreeLanguage L <->
      PDA.FinitePresentationRecognizable L := by
  constructor
  · exact
      finite_production_context_free_language_finite_presentation_pda_recognizable
        inputFinite
  · exact finite_presentation_pda_recognizable_context_free

end Section04
end Chapter04
end Book
end FoC
