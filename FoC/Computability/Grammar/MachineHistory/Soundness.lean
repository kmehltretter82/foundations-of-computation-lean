import FoC.Computability.Grammar.MachineHistory.Cleanup

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open Grammars

namespace MachineDescriptionHistoryGrammar

theorem terminalWord_no_yields {D : MachineDescription}
    (w : Word Bool) {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D) (SententialForm.terminalWord w) y) :
    False := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  have hcontains := (grammar D).lhsContainsNonterminal lhs rhs hprod
  rcases containsNonterminal_exists_mem (D := D) hcontains with ⟨A, hA⟩
  have hmem : Symbol.nonterminal A ∈ SententialForm.terminalWord w := by
    rw [hx]
    simp [hA]
  exact nonterminal_not_mem_terminalWord A w hmem

theorem historySoundForm_yields {D : MachineDescription}
    (hD : D.WellFormed)
    {x y : SententialForm Bool (NT D)}
    (hshape : HistorySoundForm D x)
    (h : GeneralGrammar.Yields (grammar D) x y) :
    HistorySoundForm D y := by
  cases hshape with
  | start =>
      exact historySoundForm_start_yields h
  | lockedLeft left =>
      exact historySoundForm_lockedLeft_yields left h
  | lockedRight left head right =>
      exact historySoundForm_lockedRight_yields hD left head right h
  | active c hstate hc =>
      exact historySoundForm_active_yields hD c hstate hc h
  | cleanup pref rest hclean =>
      exact historySoundForm_cleanup_yields pref rest hclean h
  | terminal w hw =>
      exact False.elim (terminalWord_no_yields w h)

theorem historySoundForm_derives {D : MachineDescription}
    (hD : D.WellFormed)
    {x y : SententialForm Bool (NT D)}
    (hshape : HistorySoundForm D x)
    (h : GeneralGrammar.Derives (grammar D) x y) :
    HistorySoundForm D y := by
  induction h with
  | refl x =>
      exact hshape
  | step hstep hrest ih =>
      exact ih (historySoundForm_yields hD hshape hstep)

theorem sound {D : MachineDescription} {w : Word Bool}
    (hD : D.WellFormed)
    (h : w ∈ GeneralGrammar.GeneratedLanguage (grammar D)) :
    D.HaltsOnInput w := by
  have hshape :
      HistorySoundForm D (SententialForm.terminalWord w) :=
    historySoundForm_derives (D := D) hD
      (HistorySoundForm.start (D := D)) h
  exact historySoundForm_terminal hshape rfl

end MachineDescriptionHistoryGrammar

end Computability
end FoC
