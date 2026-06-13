import FoC.Computability.Grammar.MachineHistory.ReverseMoves

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open Grammars

namespace MachineDescriptionHistoryGrammar

theorem cleanupEmpty_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    {u v y : SententialForm Bool (NT D)}
    (hx : configForm D c =
      u ++ [leftBoundary, state (D.stateOfNat D.start), cell none,
        rightBoundary] ++ v)
    (hy : y = u ++ ([] : SententialForm Bool (NT D)) ++ v) :
    HistorySoundForm D y := by
  subst y
  rcases c with ⟨qcur, T⟩
  rcases T with ⟨leftTape, headCur, rightTape⟩
  let cur : MachineDescription.Configuration :=
    { state := qcur,
      tape := { left := leftTape, head := headCur, right := rightTape } }
  have hxLB :
      configForm D cur = u ++ [leftBoundary] ++
        ([state (D.stateOfNat D.start), cell none, rightBoundary] ++ v) := by
    simpa [cur, List.append_assoc] using hx
  rcases leftBoundary_config_context cur hxLB with ⟨hu, htail⟩
  simp [cur] at hu htail
  subst u
  have hxState :
      cellForm (D := D) leftTape.reverse ++
          [state (D.stateOfNat qcur), cell headCur] ++
          cellForm rightTape ++ [rightBoundary] =
        [] ++ [state (D.stateOfNat D.start)] ++
          (cell none :: rightBoundary :: v) := by
    simpa [List.append_assoc] using htail.symm
  rcases state_cellForm_context leftTape.reverse (D.stateOfNat qcur)
      headCur rightTape (D.stateOfNat D.start) hxState with
    ⟨hleft, hq, hsuffix⟩
  have hqnat : D.start = qcur :=
    stateOfNat_injective_of_state_bound
      (D := D) hD.right.left hstate hq
  subst qcur
  cases leftTape with
  | nil =>
      simp [cellForm] at hsuffix
      rcases hsuffix with ⟨hhead, htail2⟩
      cases hhead
      cases rightTape with
      | nil =>
          simp at htail2
          subst v
          have hinitReach : ReachesHalt D (D.initial []) := by
            simpa [MachineDescription.initial, Tape.input, Tape.blank] using hc
          simpa [SententialForm.terminalWord] using
            (HistorySoundForm.terminal (D := D) []
              (haltsOnInput_of_initial_reachesHalt hinitReach))
      | cons r restRight =>
          cases r <;> simp [cell, nt, rightBoundary] at htail2
  | cons l restLeft =>
      simp [cellForm, List.map_append] at hleft

theorem cleanupStart_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    (b : Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : configForm D c =
      u ++ [leftBoundary, state (D.stateOfNat D.start), cell (some b)] ++ v)
    (hy : y = u ++ [tm b, nt MachineHistoryNonterminal.cleanup] ++ v) :
    HistorySoundForm D y := by
  subst y
  rcases c with ⟨qcur, T⟩
  rcases T with ⟨leftTape, headCur, rightTape⟩
  let cur : MachineDescription.Configuration :=
    { state := qcur,
      tape := { left := leftTape, head := headCur, right := rightTape } }
  have hxLB :
      configForm D cur = u ++ [leftBoundary] ++
        ([state (D.stateOfNat D.start), cell (some b)] ++ v) := by
    simpa [cur, List.append_assoc] using hx
  rcases leftBoundary_config_context cur hxLB with ⟨hu, htail⟩
  simp [cur] at hu htail
  subst u
  have hxState :
      cellForm (D := D) leftTape.reverse ++
          [state (D.stateOfNat qcur), cell headCur] ++
          cellForm rightTape ++ [rightBoundary] =
        [] ++ [state (D.stateOfNat D.start)] ++
          (cell (some b) :: v) := by
    simpa [List.append_assoc] using htail.symm
  rcases state_cellForm_context leftTape.reverse (D.stateOfNat qcur)
      headCur rightTape (D.stateOfNat D.start) hxState with
    ⟨hleft, hq, hsuffix⟩
  have hqnat : D.start = qcur :=
    stateOfNat_injective_of_state_bound
      (D := D) hD.right.left hstate hq
  subst qcur
  cases leftTape with
  | nil =>
      simp [cellForm] at hsuffix
      rcases hsuffix with ⟨hhead, hv⟩
      cases hhead
      subst v
      refine HistorySoundForm.cleanup (D := D) [b] rightTape ?_
      intro suffix hrest
      have hinitReach : ReachesHalt D (D.initial (b :: suffix)) := by
        simpa [MachineDescription.initial, Tape.input, hrest] using hc
      simpa [Word.Concat] using
        haltsOnInput_of_initial_reachesHalt hinitReach
  | cons l restLeft =>
      simp [cellForm, List.map_append] at hleft

theorem cleanup_context {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : cleanupForm (D := D) pref rest =
      u ++ [nt MachineHistoryNonterminal.cleanup] ++ v) :
    u = SententialForm.terminalWord pref ∧
      v = cellForm (D := D) rest ++ [rightBoundary] := by
  induction pref generalizing u with
  | nil =>
      simp [cleanupForm, SententialForm.terminalWord] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          exact ⟨rfl, hx.symm⟩
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have hmem :
              nt MachineHistoryNonterminal.cleanup ∈
                cellForm (D := D) rest ++ [rightBoundary] := by
            rw [htail]
            simp
          simp [cellForm, cell, nt, rightBoundary] at hmem
  | cons b pref ih =>
      simp [cleanupForm, SententialForm.terminalWord] at hx ⊢
      cases u with
      | nil =>
          simp [nt] at hx
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              SententialForm.terminalWord pref ++
                  [nt MachineHistoryNonterminal.cleanup] ++
                  cellForm rest ++ [rightBoundary] =
                us ++ [nt MachineHistoryNonterminal.cleanup] ++ v := by
            simpa [cleanupForm, SententialForm.terminalWord,
              List.append_assoc] using htail
          rcases ih htailForm with ⟨hus, hv⟩
          subst us
          subst v
          simp [SententialForm.terminalWord]

theorem cleanupCell_yields {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool))
    (hclean : forall suffix : Word Bool,
      rest = suffix.map some ->
        D.HaltsOnInput (Word.Concat pref suffix))
    (b : Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : cleanupForm (D := D) pref rest =
      u ++ [nt MachineHistoryNonterminal.cleanup, cell (some b)] ++ v)
    (hy : y = u ++ [tm b, nt MachineHistoryNonterminal.cleanup] ++ v) :
    HistorySoundForm D y := by
  subst y
  have hxCleanup :
      cleanupForm (D := D) pref rest =
        u ++ [nt MachineHistoryNonterminal.cleanup] ++
          (cell (some b) :: v) := by
    simpa [List.append_assoc] using hx
  rcases cleanup_context pref rest hxCleanup with ⟨hu, hv⟩
  subst u
  cases rest with
  | nil =>
      simp [cellForm, cell, nt, rightBoundary] at hv
  | cons r restTail =>
      simp [cellForm] at hv
      rcases hv with ⟨hcell, hv⟩
      cases r with
      | none =>
          simp [cell, nt] at hcell
      | some rb =>
          cases hcell
          subst v
          have hnext : HistorySoundForm D
              (cleanupForm (D := D) (Word.Concat pref [b]) restTail) := by
            refine
              HistorySoundForm.cleanup
                (D := D) (Word.Concat pref [b]) restTail ?_
            intro suffix hrest
            have horig : some b :: restTail = (b :: suffix).map some := by
              simp [hrest]
            have hh := hclean (b :: suffix) horig
            simpa [Word.Concat, List.append_assoc] using hh
          simpa [cleanupForm, SententialForm.terminalWord, Word.Concat,
            List.append_assoc] using hnext

theorem cleanupEnd_yields {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool))
    (hclean : forall suffix : Word Bool,
      rest = suffix.map some ->
        D.HaltsOnInput (Word.Concat pref suffix))
    {u v y : SententialForm Bool (NT D)}
    (hx : cleanupForm (D := D) pref rest =
      u ++ [nt MachineHistoryNonterminal.cleanup, rightBoundary] ++ v)
    (hy : y = u ++ ([] : SententialForm Bool (NT D)) ++ v) :
    HistorySoundForm D y := by
  subst y
  have hxCleanup :
      cleanupForm (D := D) pref rest =
        u ++ [nt MachineHistoryNonterminal.cleanup] ++
          (rightBoundary :: v) := by
    simpa [List.append_assoc] using hx
  rcases cleanup_context pref rest hxCleanup with ⟨hu, hv⟩
  subst u
  cases rest with
  | nil =>
      simp [cellForm] at hv
      subst v
      have hh := hclean [] rfl
      simpa using
        (HistorySoundForm.terminal (D := D) pref
          (by simpa [Word.Concat] using hh))
  | cons r restTail =>
      cases r <;> simp [cellForm, cell, nt, rightBoundary] at hv

theorem historySoundForm_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D) (configForm D c) y) :
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
    have hmem : nt MachineHistoryNonterminal.start ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genLeft ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genLeft ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genLeft ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · rcases hselection with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem : nt MachineHistoryNonterminal.genLeft ∈ configForm D c := by
        rw [hx]
        simp [nt]
      simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genRight ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genRight ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genRight ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · rcases hactivation with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem : lockedState q ∈ configForm D c := by
        rw [hx]
        simp [lockedState, nt]
      simp [configForm, cell, state, lockedState, nt, leftBoundary,
        rightBoundary] at hmem
  · rcases htrans with ⟨t, ht, hmemRule⟩
    cases hmove : t.move <;> simp [hmove] at hmemRule
    · rcases hmemRule with hnone | hfalse | htrue | hboundary
      · subst rule
        simpa [prod] using
          reverseLeftMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove none hx rfl
      · subst rule
        simpa [prod] using
          reverseLeftMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove (some false) hx rfl
      · subst rule
        simpa [prod] using
          reverseLeftMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove (some true) hx rfl
      · subst rule
        simpa [prod] using
          reverseLeftMoveBoundary_active_yields
            (D := D) hD c hstate hc t ht hmove hx rfl
    · rcases hmemRule with hnone | hfalse | htrue | hboundary
      · subst rule
        simpa [prod] using
          reverseRightMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove none hx rfl
      · subst rule
        simpa [prod] using
          reverseRightMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove (some false) hx rfl
      · subst rule
        simpa [prod] using
          reverseRightMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove (some true) hx rfl
      · subst rule
        simpa [prod] using
          reverseRightMoveBoundary_active_yields
            (D := D) hD c hstate hc t ht hmove hx rfl
  · subst rule
    simpa [prod] using
      cleanupEmpty_active_yields (D := D) hD c hstate hc hx rfl
  · subst rule
    simpa [prod] using
      cleanupStart_active_yields (D := D) hD c hstate hc false hx rfl
  · subst rule
    simpa [prod] using
      cleanupStart_active_yields (D := D) hD c hstate hc true hx rfl
  · subst rule
    have hmem : nt MachineHistoryNonterminal.cleanup ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.cleanup ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.cleanup ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem

theorem historySoundForm_cleanup_yields {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool))
    (hclean : forall suffix : Word Bool,
      rest = suffix.map some ->
        D.HaltsOnInput (Word.Concat pref suffix))
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D)
      (cleanupForm (D := D) pref rest) y) :
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
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · rcases hselection with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem :
          nt MachineHistoryNonterminal.genLeft ∈
            cleanupForm (D := D) pref rest := by
        rw [hx]
        simp [nt]
      simp [cleanupForm, cellForm, cell, nt, rightBoundary,
        nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · rcases hactivation with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem :
          lockedState q ∈ cleanupForm (D := D) pref rest := by
        rw [hx]
        simp [lockedState, nt]
      simp [cleanupForm, cellForm, cell, lockedState, nt, rightBoundary,
        nonterminal_not_mem_terminalWord] at hmem
  · rcases htrans with ⟨t, ht, hmemRule⟩
    cases hmove : t.move <;> simp [hmove] at hmemRule
    all_goals
      rcases hmemRule with hmemRule | hmemRule | hmemRule | hmemRule <;>
        subst rule
      all_goals
        have hmem :
            state (D.stateOfNat t.target) ∈
              cleanupForm (D := D) pref rest := by
          rw [hx]
          simp [state, nt]
        simp [cleanupForm, cellForm, cell, state, nt, rightBoundary,
          nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem : leftBoundary ∈ cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [leftBoundary, nt]
    simp [cleanupForm, cellForm, cell, leftBoundary, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem : leftBoundary ∈ cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [leftBoundary, nt]
    simp [cleanupForm, cellForm, cell, leftBoundary, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem : leftBoundary ∈ cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [leftBoundary, nt]
    simp [cleanupForm, cellForm, cell, leftBoundary, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    simpa [prod] using
      cleanupCell_yields (D := D) pref rest hclean false hx rfl
  · subst rule
    simpa [prod] using
      cleanupCell_yields (D := D) pref rest hclean true hx rfl
  · subst rule
    simpa [prod] using
      cleanupEnd_yields (D := D) pref rest hclean hx rfl


end MachineDescriptionHistoryGrammar

end Computability
end FoC
