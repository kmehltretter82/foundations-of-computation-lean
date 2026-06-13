import FoC.Computability.Grammar.MachineHistory.Contexts

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open Grammars

namespace MachineDescriptionHistoryGrammar

theorem lockedLeft_leftGenerator_yields {D : MachineDescription}
    (left : List (Option Bool)) (c : Option Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : lockedLeftForm D left =
      u ++ [nt MachineHistoryNonterminal.genLeft] ++ v)
    (hy : y = u ++ [cell c, nt MachineHistoryNonterminal.genLeft] ++ v) :
    HistorySoundForm D y := by
  rcases genLeft_lockedLeft_context left hx with ⟨hu, hv⟩
  subst u
  subst v
  subst y
  simpa [lockedLeftForm, cellForm, List.map_append, List.append_assoc] using
    (HistorySoundForm.lockedLeft (D := D) (left ++ [c]))

theorem lockedLeft_headSelection_yields {D : MachineDescription}
    (left : List (Option Bool)) (q : Fin (D.stateCount + 1))
    (h : Option Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : lockedLeftForm D left =
      u ++ [nt MachineHistoryNonterminal.genLeft, lockedState q] ++ v)
    (hy : y = u ++
      [lockedState q, cell h, nt MachineHistoryNonterminal.genRight] ++ v) :
    HistorySoundForm D y := by
  rcases genLeft_lockedLeft_pair_context left q hx with ⟨hu, hq, hv⟩
  subst u
  subst q
  subst v
  subst y
  simpa [lockedRightForm, cellForm, List.append_assoc] using
    (HistorySoundForm.lockedRight (D := D) left h [])

theorem lockedRight_rightGenerator_yields {D : MachineDescription}
    (left : List (Option Bool)) (head c : Option Bool)
    (right : List (Option Bool))
    {u v y : SententialForm Bool (NT D)}
    (hx : lockedRightForm D left head right =
      u ++ [nt MachineHistoryNonterminal.genRight] ++ v)
    (hy : y = u ++ [nt MachineHistoryNonterminal.genRight, cell c] ++ v) :
    HistorySoundForm D y := by
  rcases genRight_lockedRight_context left head right hx with ⟨hu, hv⟩
  subst u
  subst v
  subst y
  simpa [lockedRightForm, cellForm, List.append_assoc] using
    (HistorySoundForm.lockedRight (D := D) left head (c :: right))

theorem lockedRight_activation_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (q : Fin (D.stateCount + 1))
    (h : Option Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : lockedRightForm D left head right =
      u ++ [lockedState q, cell h, nt MachineHistoryNonterminal.genRight] ++ v)
    (hy : y = u ++ [state q, cell h] ++ v) :
    HistorySoundForm D y := by
  rcases genRight_lockedRight_triple_context left head right q h hx with
    ⟨hu, hq, hh, hv⟩
  subst u
  subst q
  subst h
  subst v
  subst y
  let c : MachineDescription.Configuration :=
    { state := D.halt
      tape := { left := left.reverse, head := head, right := right } }
  have hstate : c.state < D.stateCount := hD.right.right.left
  have hc : ReachesHalt D c := reachesHalt_of_state_halt (D := D) rfl
  simpa [configForm, lockedRightForm, cellForm, c, List.map_reverse,
    List.reverse_reverse, List.append_assoc] using
    (HistorySoundForm.active (D := D) c hstate hc)

theorem historySoundForm_lockedLeft_yields {D : MachineDescription}
    (left : List (Option Bool))
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D) (lockedLeftForm D left) y) :
    HistorySoundForm D y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  rcases hprod with ⟨rule, hrule, hlhsRule, hrhsRule⟩
  simp at hy
  subst y
  rw [← hrhsRule]
  rw [← hlhsRule] at hx
  simp [productions, startProduction, leftGeneratorProductions,
    headSelectionProductions, rightGeneratorProductions,
    activationProductions, reverseStepProductions,
    reverseRightMoveProductions, reverseLeftMoveProductions,
    cleanupProductions, prod,
    MachineHistoryNonterminal.optionBoolValues] at hrule
  rcases hrule with h | h | h | h | hselection | h | h | h |
    hactivation | htrans | h | h | h | h | h | h
  · subst rule
    have hmem : nt MachineHistoryNonterminal.start ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    simpa [prod] using
      lockedLeft_leftGenerator_yields (D := D) left none hx rfl
  · subst rule
    simpa [prod] using
      lockedLeft_leftGenerator_yields (D := D) left (some false) hx rfl
  · subst rule
    simpa [prod] using
      lockedLeft_leftGenerator_yields (D := D) left (some true) hx rfl
  · rcases hselection with ⟨q, hq | hq | hq⟩
    · subst rule
      simpa [prod] using
        lockedLeft_headSelection_yields (D := D) left q none hx rfl
    · subst rule
      simpa [prod] using
        lockedLeft_headSelection_yields (D := D) left q (some false) hx rfl
    · subst rule
      simpa [prod] using
        lockedLeft_headSelection_yields (D := D) left q (some true) hx rfl
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · rcases hactivation with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem :
          nt MachineHistoryNonterminal.genRight ∈
            lockedLeftForm D left := by
        rw [hx]
        simp [nt]
      simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
        lockedState] at hmem
  · rcases htrans with ⟨t, ht, hmemRule⟩
    cases hmove : t.move <;> simp [hmove] at hmemRule
    all_goals
      rcases hmemRule with hmemRule | hmemRule | hmemRule | hmemRule <;>
        subst rule
      all_goals
        have hmem :
            state (D.stateOfNat t.target) ∈ lockedLeftForm D left := by
          rw [hx]
          simp [state, nt]
        simp [lockedLeftForm, cellForm, cell, state, nt, leftBoundary,
          rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈ lockedLeftForm D left := by
      rw [hx]
      simp [state, nt]
    simp [lockedLeftForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈ lockedLeftForm D left := by
      rw [hx]
      simp [state, nt]
    simp [lockedLeftForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈ lockedLeftForm D left := by
      rw [hx]
      simp [state, nt]
    simp [lockedLeftForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem

theorem historySoundForm_lockedRight_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool))
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D)
      (lockedRightForm D left head right) y) :
    HistorySoundForm D y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  rcases hprod with ⟨rule, hrule, hlhsRule, hrhsRule⟩
  simp at hy
  subst y
  rw [← hrhsRule]
  rw [← hlhsRule] at hx
  simp [productions, startProduction, leftGeneratorProductions,
    headSelectionProductions, rightGeneratorProductions,
    activationProductions, reverseStepProductions,
    reverseRightMoveProductions, reverseLeftMoveProductions,
    cleanupProductions, prod,
    MachineHistoryNonterminal.optionBoolValues] at hrule
  rcases hrule with h | h | h | h | hselection | h | h | h |
    hactivation | htrans | h | h | h | h | h | h
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.start ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · rcases hselection with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem :
          nt MachineHistoryNonterminal.genLeft ∈
            lockedRightForm D left head right := by
        rw [hx]
        simp [nt]
      simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
        lockedState] at hmem
  · subst rule
    simpa [prod] using
      lockedRight_rightGenerator_yields
        (D := D) left head none right hx rfl
  · subst rule
    simpa [prod] using
      lockedRight_rightGenerator_yields
        (D := D) left head (some false) right hx rfl
  · subst rule
    simpa [prod] using
      lockedRight_rightGenerator_yields
        (D := D) left head (some true) right hx rfl
  · rcases hactivation with ⟨q, hq | hq | hq⟩
    · subst rule
      simpa [prod] using
        lockedRight_activation_yields
          (D := D) hD left head right q none hx rfl
    · subst rule
      simpa [prod] using
        lockedRight_activation_yields
          (D := D) hD left head right q (some false) hx rfl
    · subst rule
      simpa [prod] using
        lockedRight_activation_yields
          (D := D) hD left head right q (some true) hx rfl
  · rcases htrans with ⟨t, ht, hmemRule⟩
    cases hmove : t.move <;> simp [hmove] at hmemRule
    all_goals
      rcases hmemRule with hmemRule | hmemRule | hmemRule | hmemRule <;>
        subst rule
      all_goals
        have hmem :
            state (D.stateOfNat t.target) ∈
              lockedRightForm D left head right := by
          rw [hx]
          simp [state, nt]
        simp [lockedRightForm, cellForm, cell, state, nt, leftBoundary,
          rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [state, nt]
    simp [lockedRightForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [state, nt]
    simp [lockedRightForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [state, nt]
    simp [lockedRightForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem


end MachineDescriptionHistoryGrammar

end Computability
end FoC
