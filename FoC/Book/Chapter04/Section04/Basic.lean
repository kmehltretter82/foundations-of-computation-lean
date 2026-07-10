import FoC.Book.Chapter04.Section04.Common
import FoC.Grammars.CFGToPDA
import FoC.Grammars.PDAToCFG

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

/-!
# Chapter 4, Section 4.4: Pushdown Automata

Pushdown automata add a stack to finite-state control. The reusable computation,
acceptance, determinism, and conversion APIs live in
{module}`FoC.Grammars.PDA`, {module}`FoC.Grammars.CFGToPDA`, and
{module}`FoC.Grammars.PDAToCFG`.

This book-facing module records the CFG-to-PDA consequence needed for the
chapter's equivalence theorem. It deliberately does not republish the
foundational computation algebra under chapter-specific names. Concrete
machines are independent sibling modules under {lit}`Section04`.
-/

/--
A finitely presented CFG over a finite terminal alphabet is recognized by the
standard finitely presented PDA construction.
-/
theorem cfg_generated_language_finite_presentation_pda_recognizable
    {terminal nonterminal : Type}
    (G : CFG terminal nonterminal)
    (terminalFinite : Foundation.FiniteType terminal)
    (hG : CFG.HasFinitePresentation G) :
    PDA.FinitePresentationRecognizable (CFG.GeneratedLanguage G) := by
  rcases hG with ⟨presentation⟩
  exact ⟨Symbol terminal nonterminal, CFG.ToPDAState, CFG.ToPDA G,
    CFG.toPDA_finitePresentation G terminalFinite
      presentation.rules presentation.complete,
    CFG.toPDA_acceptedLanguage_exact G⟩

/--
Every context-free language over a finite alphabet is recognized by a finitely
presented PDA.
-/
theorem finite_production_context_free_language_finite_presentation_pda_recognizable
    {terminal : Type} {L : Language terminal}
    (terminalFinite : Foundation.FiniteType terminal)
    (hL : CFL.ContextFreeLanguage L) :
    PDA.FinitePresentationRecognizable L := by
  rcases hL with ⟨nonterminal, G, hGfinite, hGexact⟩
  rcases cfg_generated_language_finite_presentation_pda_recognizable
      G terminalFinite hGfinite with
    ⟨stack, state, M, presentation, hM⟩
  exact ⟨stack, state, M, presentation,
    Foundation.FSet.equal_trans hM hGexact⟩

end Section04
end Chapter04
end Book
end FoC
