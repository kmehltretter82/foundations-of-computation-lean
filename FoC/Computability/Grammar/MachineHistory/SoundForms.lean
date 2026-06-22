import FoC.Computability.Grammar.MachineHistory.Syntax

set_option doc.verso true

/-!
# SoundForms

Supporting declarations and helper lemmas for Computability Grammar MachineHistory SoundForms.
-/


namespace FoC
namespace Computability

open Languages
open Grammars

namespace MachineDescriptionHistoryGrammar

def lockedLeftForm (D : MachineDescription)
    (left : List (Option Bool)) :
    SententialForm Bool (NT D) :=
  [leftBoundary] ++ cellForm left ++
    [nt MachineHistoryNonterminal.genLeft,
      lockedState (D.stateOfNat D.halt), rightBoundary]

def lockedRightForm (D : MachineDescription)
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) :
    SententialForm Bool (NT D) :=
  [leftBoundary] ++ cellForm left ++
    [lockedState (D.stateOfNat D.halt), cell head,
      nt MachineHistoryNonterminal.genRight] ++
    cellForm right ++ [rightBoundary]

def inputCellForm {D : MachineDescription} (w : Word Bool) :
    SententialForm Bool (NT D) :=
  w.map (fun b => cell (some b))

def cleanupForm {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool)) :
    SententialForm Bool (NT D) :=
  SententialForm.terminalWord pref ++
    [nt MachineHistoryNonterminal.cleanup] ++
    cellForm rest ++ [rightBoundary]

inductive HistorySoundForm (D : MachineDescription) :
    SententialForm Bool (NT D) -> Prop where
  | start :
      HistorySoundForm D [nt MachineHistoryNonterminal.start]
  | lockedLeft (left : List (Option Bool)) :
      HistorySoundForm D (lockedLeftForm D left)
  | lockedRight
      (left : List (Option Bool)) (head : Option Bool)
      (right : List (Option Bool)) :
      HistorySoundForm D (lockedRightForm D left head right)
  | active (c : MachineDescription.Configuration)
      (hstate : c.state < D.stateCount)
      (hc : ReachesHalt D c) :
      HistorySoundForm D (configForm D c)
  | cleanup (pref : Word Bool) (rest : List (Option Bool))
      (h : forall suffix : Word Bool,
        rest = suffix.map some ->
          D.HaltsOnInput (Word.Concat pref suffix)) :
      HistorySoundForm D (cleanupForm (D := D) pref rest)
  | terminal (w : Word Bool)
      (h : D.HaltsOnInput w) :
      HistorySoundForm D (SententialForm.terminalWord w)

 /-- {name}`nonterminal_not_mem_terminalWord` captures the core lemma for this local construction. -/
theorem nonterminal_not_mem_terminalWord {D : MachineDescription}
    (A : NT D) (w : Word Bool) :
    Symbol.nonterminal A ∉ SententialForm.terminalWord w := by
  induction w with
  | nil =>
      simp [SententialForm.terminalWord]
  | cons _ _ ih =>
      simp [SententialForm.terminalWord]

 /-- {name}`containsNonterminal_ne_nil` captures the core lemma for this local construction. -/
theorem containsNonterminal_ne_nil {D : MachineDescription}
    {xs : SententialForm Bool (NT D)}
    (h : SententialForm.containsNonterminal xs) :
    xs ≠ [] := by
  cases xs with
  | nil =>
      simp [SententialForm.containsNonterminal] at h
  | cons _ _ =>
      simp

 /-- {name}`singleton_context_eq_of_containsNonterminal` provides an important equivalence or equality lemma. -/
theorem singleton_context_eq_of_containsNonterminal
    {D : MachineDescription} {s : Symbol Bool (NT D)}
    {u lhs v : SententialForm Bool (NT D)}
    (hcontains : SententialForm.containsNonterminal lhs)
    (hx : [s] = u ++ lhs ++ v) :
    u = [] ∧ v = [] ∧ lhs = [s] := by
  have hne : lhs ≠ [] := containsNonterminal_ne_nil hcontains
  cases lhs with
  | nil =>
      exact False.elim (hne rfl)
  | cons a rest =>
      have hlen := congrArg List.length hx
      simp at hlen
      have huLen : u.length = 0 := by omega
      have hvLen : v.length = 0 := by omega
      have hrestLen : rest.length = 0 := by omega
      have hu : u = [] := List.eq_nil_of_length_eq_zero huLen
      have hv : v = [] := List.eq_nil_of_length_eq_zero hvLen
      have hrest : rest = [] := List.eq_nil_of_length_eq_zero hrestLen
      subst u
      subst v
      subst rest
      simp at hx
      cases hx
      exact ⟨rfl, rfl, rfl⟩

 /-- {name}`containsNonterminal_exists_mem` provides the witness needed for existential progress. -/
theorem containsNonterminal_exists_mem {D : MachineDescription}
    {xs : SententialForm Bool (NT D)}
    (h : SententialForm.containsNonterminal xs) :
    exists A : NT D, Symbol.nonterminal A ∈ xs := by
  induction xs with
  | nil =>
      simp [SententialForm.containsNonterminal] at h
  | cons s rest ih =>
      cases s with
      | terminal b =>
          simp [SententialForm.containsNonterminal] at h
          rcases ih h with ⟨A, hA⟩
          exact ⟨A, by simp [hA]⟩
      | nonterminal A =>
          exact ⟨A, by simp⟩

 /-- {name}`historySoundForm_terminal` captures the core lemma for this local construction. -/
theorem historySoundForm_terminal {D : MachineDescription}
    {sf : SententialForm Bool (NT D)} {w : Word Bool}
    (hshape : HistorySoundForm D sf)
    (hsf : sf = SententialForm.terminalWord w) :
    D.HaltsOnInput w := by
  induction hshape with
  | start =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.start ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | lockedLeft left =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.leftBoundary ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [lockedLeftForm, leftBoundary, nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | lockedRight left head right =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.leftBoundary ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [lockedRightForm, leftBoundary, nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | active c hstate hc =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.leftBoundary ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [configForm, leftBoundary, nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | cleanup pref rest hclean =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.cleanup ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [cleanupForm, nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | terminal w0 h =>
      have hword := congrArg SententialForm.toWord? hsf
      simp [SententialForm.terminalWord_toWord] at hword
      cases hword
      exact h

 /-- {name}`historySoundForm_start_yields` captures the core lemma for this local construction. -/
theorem historySoundForm_start_yields {D : MachineDescription}
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D)
      [nt MachineHistoryNonterminal.start] y) :
    HistorySoundForm D y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  have hcontains := (grammar D).lhsContainsNonterminal lhs rhs hprod
  rcases singleton_context_eq_of_containsNonterminal hcontains hx with
    ⟨hu, hv, hlhs⟩
  subst u
  subst v
  subst lhs
  rcases hprod with ⟨rule, hrule, hlhsRule, hrhsRule⟩
  simp at hy
  subst y
  rw [← hrhsRule]
  simp [productions, startProduction, leftGeneratorProductions,
    headSelectionProductions, rightGeneratorProductions,
    activationProductions, reverseStepProductions,
    reverseRightMoveProductions, reverseLeftMoveProductions,
    cleanupProductions, prod,
    MachineHistoryNonterminal.optionBoolValues] at hrule
  rcases hrule with h | h | h | h | hselection | h | h | h |
    hactivation | htrans | h | h | h | h | h | h
  · subst rule
    simp
    exact HistorySoundForm.lockedLeft []
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · rcases hselection with ⟨q, hq | hq | hq⟩ <;>
      subst rule <;> simp at hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · rcases hactivation with ⟨q, hq | hq | hq⟩ <;>
      subst rule <;> simp at hlhsRule
  · rcases htrans with ⟨t, ht, hmem⟩
    cases hmove : t.move <;> simp [hmove] at hmem
    all_goals
      rcases hmem with hmem | hmem | hmem | hmem <;>
        subst rule <;> simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule


end MachineDescriptionHistoryGrammar

end Computability
end FoC
