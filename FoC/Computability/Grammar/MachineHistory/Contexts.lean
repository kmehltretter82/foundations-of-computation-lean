import FoC.Computability.Grammar.MachineHistory.SoundForms

set_option doc.verso true

/-!
# Contexts

Supporting declarations and helper lemmas for Computability Grammar MachineHistory Contexts.
-/


namespace FoC
namespace Computability

open Languages
open Grammars

namespace MachineDescriptionHistoryGrammar

 /-- {name}`genLeft_not_mem_cellForm` captures the core lemma for this local construction. -/
theorem genLeft_not_mem_cellForm {D : MachineDescription}
    (xs : List (Option Bool)) :
    nt MachineHistoryNonterminal.genLeft ∉ cellForm (D := D) xs := by
  induction xs with
  | nil =>
      simp [cellForm]
  | cons x xs ih =>
      cases x <;> simp [cellForm, cell, nt]

 /-- {name}`genLeft_not_mem_tail` captures the core lemma for this local construction. -/
theorem genLeft_not_mem_tail {D : MachineDescription} :
    nt MachineHistoryNonterminal.genLeft ∉
      ([lockedState (D.stateOfNat D.halt), rightBoundary] :
        SententialForm Bool (NT D)) := by
  simp [nt, lockedState, rightBoundary]

 /-- {name}`genLeft_cellForm_context` captures the core lemma for this local construction. -/
theorem genLeft_cellForm_context {D : MachineDescription}
    (left : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : cellForm (D := D) left ++
        [nt MachineHistoryNonterminal.genLeft,
          lockedState (D.stateOfNat D.halt), rightBoundary] =
      u ++ [nt MachineHistoryNonterminal.genLeft] ++ v) :
    u = cellForm (D := D) left ∧
      v = [lockedState (D.stateOfNat D.halt), rightBoundary] := by
  induction left generalizing u with
  | nil =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          exact ⟨rfl, hx.symm⟩
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have hmem : nt MachineHistoryNonterminal.genLeft ∈
              ([lockedState (D.stateOfNat D.halt), rightBoundary] :
                SententialForm Bool (NT D)) := by
            rw [htail]
            simp
          exact False.elim (genLeft_not_mem_tail hmem)
  | cons x xs ih =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hbad, _⟩
          cases x <;> simp [cell, nt] at hbad
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              cellForm (D := D) xs ++
                  [nt MachineHistoryNonterminal.genLeft,
                    lockedState (D.stateOfNat D.halt), rightBoundary] =
                us ++ [nt MachineHistoryNonterminal.genLeft] ++ v := by
            simpa [cellForm] using htail
          rcases ih htailForm with ⟨hus, hv⟩
          rw [hus, hv]
          exact ⟨rfl, rfl⟩

 /-- {name}`genLeft_lockedLeft_context` captures the core lemma for this local construction. -/
theorem genLeft_lockedLeft_context {D : MachineDescription}
    (left : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : lockedLeftForm D left =
      u ++ [nt MachineHistoryNonterminal.genLeft] ++ v) :
    u = [leftBoundary] ++ cellForm (D := D) left ∧
      v = [lockedState (D.stateOfNat D.halt), rightBoundary] := by
  cases u with
  | nil =>
      simp [lockedLeftForm, leftBoundary, nt] at hx
  | cons a us =>
      simp [lockedLeftForm] at hx
      rcases hx with ⟨ha, htail⟩
      subst a
      have htailForm :
          cellForm (D := D) left ++
              [nt MachineHistoryNonterminal.genLeft,
                lockedState (D.stateOfNat D.halt), rightBoundary] =
            us ++ [nt MachineHistoryNonterminal.genLeft] ++ v := by
        simpa [lockedLeftForm] using htail
      rcases genLeft_cellForm_context left htailForm with ⟨hus, hv⟩
      subst us
      subst v
      simp

 /-- {name}`genLeft_lockedLeft_pair_context` captures the core lemma for this local construction. -/
theorem genLeft_lockedLeft_pair_context {D : MachineDescription}
    (left : List (Option Bool)) (q : Fin (D.stateCount + 1))
    {u v : SententialForm Bool (NT D)}
    (hx : lockedLeftForm D left =
      u ++ [nt MachineHistoryNonterminal.genLeft, lockedState q] ++ v) :
    u = [leftBoundary] ++ cellForm (D := D) left ∧
      q = D.stateOfNat D.halt ∧ v = [rightBoundary] := by
  have hxSingle :
      lockedLeftForm D left =
        u ++ [nt MachineHistoryNonterminal.genLeft] ++
          (lockedState q :: v) := by
    simpa [List.append_assoc] using hx
  rcases genLeft_lockedLeft_context left hxSingle with ⟨hu, hv⟩
  subst u
  simp at hv
  rcases hv with ⟨hq, hv⟩
  cases hq
  exact ⟨rfl, rfl, hv⟩

 /-- {name}`genRight_not_mem_cellForm` captures the core lemma for this local construction. -/
theorem genRight_not_mem_cellForm {D : MachineDescription}
    (xs : List (Option Bool)) :
    nt MachineHistoryNonterminal.genRight ∉ cellForm (D := D) xs := by
  induction xs with
  | nil =>
      simp [cellForm]
  | cons x xs ih =>
      cases x <;> simp [cellForm, cell, nt]

 /-- {name}`genRight_not_mem_tail` captures the core lemma for this local construction. -/
theorem genRight_not_mem_tail {D : MachineDescription} :
    nt MachineHistoryNonterminal.genRight ∉
      ([rightBoundary] : SententialForm Bool (NT D)) := by
  simp [nt, rightBoundary]

 /-- {name}`genRight_cellForm_context` captures the core lemma for this local construction. -/
theorem genRight_cellForm_context {D : MachineDescription}
    (right : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : cellForm (D := D) right ++ [rightBoundary] =
      u ++ [nt MachineHistoryNonterminal.genRight] ++ v) :
    False := by
  induction right generalizing u with
  | nil =>
      simp [cellForm] at hx
      cases u with
      | nil =>
          simp [rightBoundary, nt] at hx
      | cons a us =>
          simp at hx
  | cons x xs ih =>
      simp [cellForm] at hx
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hbad, _⟩
          cases x <;> simp [cell, nt] at hbad
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              cellForm (D := D) xs ++ [rightBoundary] =
                us ++ [nt MachineHistoryNonterminal.genRight] ++ v := by
            simpa [cellForm] using htail
          exact ih htailForm

 /-- {name}`genRight_cellForm_locked_context` captures the core lemma for this local construction. -/
theorem genRight_cellForm_locked_context {D : MachineDescription}
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : cellForm (D := D) left ++
        [lockedState (D.stateOfNat D.halt), cell head,
          nt MachineHistoryNonterminal.genRight] ++
        cellForm right ++ [rightBoundary] =
      u ++ [nt MachineHistoryNonterminal.genRight] ++ v) :
    u = cellForm (D := D) left ++
        [lockedState (D.stateOfNat D.halt), cell head] ∧
      v = cellForm (D := D) right ++ [rightBoundary] := by
  induction left generalizing u with
  | nil =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp [lockedState, nt] at hx
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          cases us with
          | nil =>
              simp [cell, nt] at htail
          | cons b us =>
              simp at htail
              rcases htail with ⟨hb, htail⟩
              subst b
              cases us with
              | nil =>
                  simp at htail
                  exact ⟨rfl, htail.symm⟩
              | cons c us =>
                  simp at htail
                  rcases htail with ⟨hc, htail⟩
                  subst c
                  exact False.elim
                    (genRight_cellForm_context right
                      (by simpa [cellForm] using htail))
  | cons x xs ih =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hbad, _⟩
          cases x <;> simp [cell, nt] at hbad
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              cellForm (D := D) xs ++
                  [lockedState (D.stateOfNat D.halt), cell head,
                    nt MachineHistoryNonterminal.genRight] ++
                  cellForm right ++ [rightBoundary] =
                us ++ [nt MachineHistoryNonterminal.genRight] ++ v := by
            simpa [cellForm, List.append_assoc] using htail
          rcases ih htailForm with ⟨hus, hv⟩
          subst us
          subst v
          simp [cellForm]

 /-- {name}`genRight_lockedRight_context` captures the core lemma for this local construction. -/
theorem genRight_lockedRight_context {D : MachineDescription}
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : lockedRightForm D left head right =
      u ++ [nt MachineHistoryNonterminal.genRight] ++ v) :
    u = [leftBoundary] ++ cellForm (D := D) left ++
        [lockedState (D.stateOfNat D.halt), cell head] ∧
      v = cellForm (D := D) right ++ [rightBoundary] := by
  cases u with
  | nil =>
      simp [lockedRightForm, leftBoundary, nt] at hx
  | cons a us =>
      simp [lockedRightForm] at hx
      rcases hx with ⟨ha, htail⟩
      subst a
      have htailForm :
          cellForm (D := D) left ++
              [lockedState (D.stateOfNat D.halt), cell head,
                nt MachineHistoryNonterminal.genRight] ++
              cellForm right ++ [rightBoundary] =
            us ++ [nt MachineHistoryNonterminal.genRight] ++ v := by
        simpa [lockedRightForm, List.append_assoc] using htail
      rcases genRight_cellForm_locked_context left head right htailForm with
        ⟨hus, hv⟩
      subst us
      subst v
      simp [cellForm]

 /-- {name}`genRight_lockedRight_triple_context` captures the core lemma for this local construction. -/
theorem genRight_lockedRight_triple_context {D : MachineDescription}
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (q : Fin (D.stateCount + 1))
    (h : Option Bool)
    {u v : SententialForm Bool (NT D)}
    (hx : lockedRightForm D left head right =
      u ++ [lockedState q, cell h, nt MachineHistoryNonterminal.genRight] ++
        v) :
    u = [leftBoundary] ++ cellForm (D := D) left ∧
      q = D.stateOfNat D.halt ∧ h = head ∧
      v = cellForm (D := D) right ++ [rightBoundary] := by
  have hxSingle :
      lockedRightForm D left head right =
        (u ++ [lockedState q, cell h]) ++
          [nt MachineHistoryNonterminal.genRight] ++ v := by
    simpa using hx
  rcases genRight_lockedRight_context left head right hxSingle with
    ⟨hu, hv⟩
  have hprefix :
      u ++ [lockedState q, cell h] =
        [leftBoundary] ++ cellForm (D := D) left ++
          [lockedState (D.stateOfNat D.halt), cell head] := hu
  have hlen := congrArg List.length hprefix
  simp at hlen
  have huLen : u.length =
      ([leftBoundary] ++ cellForm (D := D) left).length := by
    simpa using hlen
  have hu :
      u = [leftBoundary] ++ cellForm (D := D) left := by
    have htakeLeft :
        (u ++ [lockedState q, cell h]).take
            ([leftBoundary] ++ cellForm (D := D) left).length = u := by
      rw [← huLen]
      simp
    have htakeRight :
        (([leftBoundary] ++ cellForm (D := D) left) ++
            [lockedState (D.stateOfNat D.halt), cell head]).take
            ([leftBoundary] ++ cellForm (D := D) left).length =
          [leftBoundary] ++ cellForm (D := D) left := by
      simp
    have htaken := congrArg
      (fun xs => xs.take
        ([leftBoundary] ++ cellForm (D := D) left).length) hprefix
    have htaken' :
        (u ++ [lockedState q, cell h]).take
            ([leftBoundary] ++ cellForm (D := D) left).length =
          (([leftBoundary] ++ cellForm (D := D) left) ++
              [lockedState (D.stateOfNat D.halt), cell head]).take
            ([leftBoundary] ++ cellForm (D := D) left).length := by
      simpa using htaken
    rw [← htakeLeft]
    exact htaken'.trans htakeRight
  subst u
  simp at hprefix
  rcases hprefix with ⟨hq, hh⟩
  cases hq
  cases hh
  exact ⟨rfl, rfl, rfl, hv⟩

 /-- {name}`append_singleton_eq_append_singleton` provides an important equivalence or equality lemma. -/
theorem append_singleton_eq_append_singleton {α : Type}
    {u p : List α} {x y : α}
    (h : u ++ [x] = p ++ [y]) :
    u = p ∧ x = y := by
  have hlen := congrArg List.length h
  simp at hlen
  have huLen : u.length = p.length := by omega
  have hu : u = p := by
    have htakeLeft : (u ++ [x]).take p.length = u := by
      rw [← huLen]
      simp
    have htakeRight : (p ++ [y]).take p.length = p := by
      simp
    have htaken := congrArg (fun xs => xs.take p.length) h
    have htaken' : (u ++ [x]).take p.length =
        (p ++ [y]).take p.length := by
      simpa using htaken
    rw [← htakeLeft]
    exact htaken'.trans htakeRight
  subst u
  simp at h
  exact ⟨rfl, h⟩

 /-- {name}`state_cellForm_context` captures the core lemma for this local construction. -/
theorem state_cellForm_context {D : MachineDescription}
    (left : List (Option Bool)) (q0 : Fin (D.stateCount + 1))
    (head : Option Bool) (right : List (Option Bool))
    {u v : SententialForm Bool (NT D)} (q : Fin (D.stateCount + 1))
    (hx : cellForm (D := D) left ++ [state q0, cell head] ++
        cellForm right ++ [rightBoundary] =
      u ++ [state q] ++ v) :
    u = cellForm (D := D) left ∧ q = q0 ∧
      v = [cell head] ++ cellForm (D := D) right ++ [rightBoundary] := by
  induction left generalizing u with
  | nil =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hq, hv⟩
          cases hq
          exact ⟨rfl, rfl, hv.symm⟩
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have hmem :
              state q ∈
                cell head :: (List.map cell right ++ [rightBoundary]) := by
            rw [htail]
            simp
          simp [cell, state, nt, rightBoundary] at hmem
  | cons x xs ih =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hbad, _⟩
          cases x <;> simp [cell, state, nt] at hbad
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              cellForm (D := D) xs ++ [state q0, cell head] ++
                  cellForm right ++ [rightBoundary] =
                us ++ [state q] ++ v := by
            simpa [cellForm, List.append_assoc] using htail
          rcases ih htailForm with ⟨hus, hq, hv⟩
          subst us
          subst q
          subst v
          simp [cellForm]

 /-- {name}`state_config_context` captures the core lemma for this local construction. -/
theorem state_config_context {D : MachineDescription}
    (c : MachineDescription.Configuration)
    {u v : SententialForm Bool (NT D)} (q : Fin (D.stateCount + 1))
    (hx : configForm D c = u ++ [state q] ++ v) :
    u = [leftBoundary] ++ cellForm (D := D) c.tape.left.reverse ∧
      q = D.stateOfNat c.state ∧
      v = [cell c.tape.head] ++ cellForm (D := D) c.tape.right ++
        [rightBoundary] := by
  cases u with
  | nil =>
      simp [configForm, leftBoundary, state, nt] at hx
  | cons a us =>
      simp [configForm] at hx
      rcases hx with ⟨ha, htail⟩
      subst a
      have htailForm :
          cellForm (D := D) c.tape.left.reverse ++
              [state (D.stateOfNat c.state), cell c.tape.head] ++
              cellForm c.tape.right ++ [rightBoundary] =
            us ++ [state q] ++ v := by
        simpa [configForm, cellForm, List.append_assoc] using htail
      rcases state_cellForm_context c.tape.left.reverse
          (D.stateOfNat c.state) c.tape.head c.tape.right q htailForm with
        ⟨hus, hq, hv⟩
      subst us
      subst q
      subst v
      simp [cellForm]

 /-- {name}`leftBoundary_config_context` captures the core lemma for this local construction. -/
theorem leftBoundary_config_context {D : MachineDescription}
    (c : MachineDescription.Configuration)
    {u v : SententialForm Bool (NT D)}
    (hx : configForm D c = u ++ [leftBoundary] ++ v) :
    u = [] ∧
      v = cellForm (D := D) c.tape.left.reverse ++
        [state (D.stateOfNat c.state), cell c.tape.head] ++
        cellForm c.tape.right ++ [rightBoundary] := by
  cases u with
  | nil =>
      simp [configForm, cellForm] at hx ⊢
      exact hx.symm
  | cons a us =>
      simp [configForm] at hx
      rcases hx with ⟨ha, htail⟩
      subst a
      have hmem :
          leftBoundary ∈
            (List.map cell c.tape.left).reverse ++
              state (D.stateOfNat c.state) ::
              cell c.tape.head ::
              (List.map cell c.tape.right ++ [rightBoundary]) := by
        rw [htail]
        simp
      simp [cell, state, nt, leftBoundary, rightBoundary] at hmem


end MachineDescriptionHistoryGrammar

end Computability
end FoC
