import FoC.Grammars.PDAToCFG.Syntax

set_option doc.verso true

/-!
# PDA-to-CFG production soundness
-/

namespace FoC
namespace Grammars

open Languages

namespace PDA

/-!
# Production soundness

Each generated CFG production corresponds to a valid summarized PDA
computation, first for abstract productions and then for the finite list.
-/

theorem toCFG_production_sound
    {M : PDA input stack state}
    {A : ToCFGNonterminal stack state}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    (hprod : ToCFGProduces M A rhs) :
    forall w, w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) rhs ->
      w ∈ ToCFGSymbolLanguage M (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | start haccept =>
      rename_i q
      change Accepts M w
      rcases hw with ⟨first, tailWord, hfirst, htail, hwEq⟩
      cases htail
      rw [hwEq, Word.concat_empty_right]
      exists q
      constructor
      · exact haccept
      · simpa [initial, Word.Concat] using hfirst [] []
  | emptyRefl =>
      rename_i q
      change EmptySummary M q q w
      intro restInput tail
      cases hw
      simpa [Word.Concat] using
        Computes.refl
          ({ state := q, unread := restInput, stack := tail } :
            Configuration _ _ _)
  | emptyStep htransition hchain =>
      rename_i p r s q a? push chainRhs
      change EmptySummary M p q w
      intro restInput tail
      have hwAssoc : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M)
          (inputPrefix (nonterminal := ToCFGNonterminal stack state) a? ++
            (chainRhs ++
              [Symbol.nonterminal (ToCFGNonterminal.empty s q)])) := by
        simpa [List.append_assoc] using hw
      have hsplit :=
        (CFG.formLanguage_append (ToCFGSymbolLanguage M)
          (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?)
          (chainRhs ++
            [Symbol.nonterminal (ToCFGNonterminal.empty s q)]) w).mp hwAssoc
      rcases hsplit with ⟨pref, suffix, hpref, hsuffix, hwEq⟩
      have hsuffixSplit :=
        (CFG.formLanguage_append (ToCFGSymbolLanguage M)
          chainRhs [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
          suffix).mp hsuffix
      rcases hsuffixSplit with
        ⟨chainWord, emptyWord, hchainWord, hemptyForm, hsuffixEq⟩
      rcases hemptyForm with
        ⟨emptyHead, emptyTail, hempty, hemptyTail, hemptyEq⟩
      cases hemptyTail
      have hemptyWordEq : emptyWord = emptyHead := by
        simpa [Word.Concat, Word.Empty] using hemptyEq
      have hstep :=
        inputPrefix_formLanguage_step htransition hpref
          (Word.Concat suffix restInput) tail
      have hchainComp :=
        toCFGChain_formLanguage_computes hchain hchainWord
          (Word.Concat emptyWord restInput) tail
      have hemptyComp := hempty restInput tail
      have hstep' : Computes M
          { state := p, unread := Word.Concat w restInput,
            stack := tail }
          { state := r,
            unread := Word.Concat chainWord (Word.Concat emptyWord restInput),
            stack := Word.Concat push tail } := by
        simpa [Word.Concat, Word.Empty, List.append_assoc, hwEq,
          hsuffixEq, hemptyWordEq] using hstep
      have hchainComp' : Computes M
          { state := r,
            unread := Word.Concat chainWord (Word.Concat emptyWord restInput),
            stack := Word.Concat push tail }
          { state := s, unread := Word.Concat emptyWord restInput,
            stack := tail } := by
        simpa [Word.Concat, List.append_assoc] using hchainComp
      have hemptyComp' : Computes M
          { state := s, unread := Word.Concat emptyWord restInput,
            stack := tail }
          { state := q, unread := restInput, stack := tail } := by
        rw [hemptyWordEq]
        exact hemptyComp
      exact computes_trans hstep'
        (computes_trans hchainComp' hemptyComp')
  | popStep htransition hchain =>
      rename_i p r q A a? push chainRhs
      change BetweenSummary M p A q w
      intro restInput tail
      have hsplit :=
        (CFG.formLanguage_append (ToCFGSymbolLanguage M)
          (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?)
          chainRhs w).mp hw
      rcases hsplit with ⟨pref, chainWord, hpref, hchainWord, hwEq⟩
      have hstep :=
        inputPrefix_formLanguage_step htransition hpref
          (Word.Concat chainWord restInput) tail
      have hchainComp :=
        toCFGChain_formLanguage_computes hchain hchainWord restInput tail
      have hstep' : Computes M
          { state := p, unread := Word.Concat w restInput,
            stack := A :: tail }
          { state := r, unread := Word.Concat chainWord restInput,
            stack := Word.Concat push tail } := by
        rw [hwEq]
        simpa [Word.Concat, List.append_assoc] using hstep
      exact computes_trans hstep' hchainComp
  | emptyBeforeTop htransition hchain =>
      rename_i p r s q A a? push chainRhs
      change BetweenSummary M p A q w
      intro restInput tail
      have hwAssoc : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M)
          (inputPrefix (nonterminal := ToCFGNonterminal stack state) a? ++
            (chainRhs ++
              [Symbol.nonterminal (ToCFGNonterminal.between s A q)])) := by
        simpa [List.append_assoc] using hw
      have hsplit :=
        (CFG.formLanguage_append (ToCFGSymbolLanguage M)
          (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?)
          (chainRhs ++
            [Symbol.nonterminal (ToCFGNonterminal.between s A q)]) w).mp hwAssoc
      rcases hsplit with ⟨pref, suffix, hpref, hsuffix, hwEq⟩
      have hsuffixSplit :=
        (CFG.formLanguage_append (ToCFGSymbolLanguage M)
          chainRhs [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
          suffix).mp hsuffix
      rcases hsuffixSplit with
        ⟨chainWord, topWord, hchainWord, htopForm, hsuffixEq⟩
      rcases htopForm with
        ⟨topHead, topTail, htop, htopTail, htopEq⟩
      cases htopTail
      have htopWordEq : topWord = topHead := by
        simpa [Word.Concat, Word.Empty] using htopEq
      have hstep :=
        inputPrefix_formLanguage_step htransition hpref
          (Word.Concat suffix restInput) (A :: tail)
      have hchainComp :=
        toCFGChain_formLanguage_computes hchain hchainWord
          (Word.Concat topWord restInput) (A :: tail)
      have htopComp := htop restInput tail
      have hstep' : Computes M
          { state := p, unread := Word.Concat w restInput,
            stack := A :: tail }
          { state := r,
            unread := Word.Concat chainWord (Word.Concat topWord restInput),
            stack := Word.Concat push (A :: tail) } := by
        simpa [Word.Concat, Word.Empty, List.append_assoc, hwEq,
          hsuffixEq, htopWordEq] using hstep
      have hchainComp' : Computes M
          { state := r,
            unread := Word.Concat chainWord (Word.Concat topWord restInput),
            stack := Word.Concat push (A :: tail) }
          { state := s, unread := Word.Concat topWord restInput,
            stack := A :: tail } := by
        simpa [Word.Concat, List.append_assoc] using hchainComp
      have htopComp' : Computes M
          { state := s, unread := Word.Concat topWord restInput,
            stack := A :: tail }
          { state := q, unread := restInput, stack := tail } := by
        rw [htopWordEq]
        exact htopComp
      exact computes_trans hstep'
        (computes_trans hchainComp' htopComp')

/-!
The abstract production relation is implemented by a finite production list.
Soundness reads a list entry back into one of the abstract production cases, and
completeness shows that every abstract production was emitted by the finite
enumeration.
-/

theorem toCFG_producesFromList_sound
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {A : ToCFGNonterminal stack state}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    (hprod : ToCFGProducesFromList M presentation A rhs) :
    ToCFGProduces M A rhs := by
  rcases hprod with ⟨rule, hmem, hlhs, hrhs⟩
  unfold productionList at hmem
  rcases List.mem_append.mp hmem with hprefix | htransition
  · rcases List.mem_append.mp hprefix with hstart | hempty
    · unfold startProductions at hstart
      rcases List.mem_map.mp hstart with ⟨q, hq, hqrule⟩
      rw [← hlhs, ← hrhs, ← hqrule]
      exact ToCFGProduces.start ((presentation.accept_complete q).mpr hq)
    · unfold emptyReflProductions at hempty
      rcases List.mem_map.mp hempty with ⟨q, _hq, hqrule⟩
      rw [← hlhs, ← hrhs, ← hqrule]
      exact ToCFGProduces.emptyRefl
  · unfold transitionProductions at htransition
    simp only [List.mem_flatMap, List.mem_append] at htransition
    rcases htransition with ⟨transitionRule, htransitionRule, hcase⟩
    rcases hcase with hprefix | hbefore
    rcases hprefix with hemptyStep | hpopStep
    · unfold emptyStepProductionsForRule at hemptyStep
      cases hpop : transitionRule.pop with
      | nil =>
          simp [hpop, List.mem_flatMap] at hemptyStep
          rcases hemptyStep with ⟨s, chainRhs, hendpoint, q, hqrule⟩
          rcases hqrule with ⟨_hq, hrule⟩
          rw [← hlhs, ← hrhs, ← hrule]
          change M.ToCFGProduces (ToCFGNonterminal.empty transitionRule.source q)
            (inputPrefix transitionRule.input? ++
              (chainRhs ++
                [Symbol.nonterminal (ToCFGNonterminal.empty s q)]))
          have htransition' :
              M.transition transitionRule.source transitionRule.input? []
                transitionRule.target transitionRule.push :=
            (presentation.transition_complete
              transitionRule.source transitionRule.input? []
              transitionRule.target transitionRule.push).mpr
              ⟨transitionRule, htransitionRule, by
                simp [TransitionRule.Applies, hpop]⟩
          have hprod :
              M.ToCFGProduces (ToCFGNonterminal.empty transitionRule.source q)
                ((inputPrefix transitionRule.input? ++ chainRhs) ++
                  [Symbol.nonterminal (ToCFGNonterminal.empty s q)]) :=
            ToCFGProduces.emptyStep htransition'
              (chainEndpointForms_sound hendpoint)
          simpa [List.append_assoc] using hprod
      | cons head tail =>
          simp [hpop] at hemptyStep
    · unfold popStepProductionsForRule at hpopStep
      cases hpop : transitionRule.pop with
      | nil =>
          simp [hpop] at hpopStep
      | cons A popTail =>
          cases popTail with
          | nil =>
              simp [hpop] at hpopStep
              rcases hpopStep with ⟨q, chainRhs, hendpoint, hrule⟩
              rw [← hlhs, ← hrhs, ← hrule]
              change M.ToCFGProduces
                (ToCFGNonterminal.between transitionRule.source A q)
                (inputPrefix transitionRule.input? ++ chainRhs)
              apply ToCFGProduces.popStep
              · exact (presentation.transition_complete
                  transitionRule.source transitionRule.input? [A]
                  transitionRule.target transitionRule.push).mpr
                  ⟨transitionRule, htransitionRule, by
                    simp [TransitionRule.Applies, hpop]⟩
              · exact chainEndpointForms_sound hendpoint
          | cons B rest =>
              simp [hpop] at hpopStep
    · unfold emptyBeforeTopProductionsForRule at hbefore
      cases hpop : transitionRule.pop with
      | nil =>
          simp [hpop, List.mem_flatMap] at hbefore
          rcases hbefore with
            ⟨s, chainRhs, hendpoint, A, _hA, q, hqrule⟩
          rcases hqrule with ⟨_hq, hrule⟩
          rw [← hlhs, ← hrhs, ← hrule]
          change M.ToCFGProduces
            (ToCFGNonterminal.between transitionRule.source A q)
            (inputPrefix transitionRule.input? ++
              (chainRhs ++
                [Symbol.nonterminal (ToCFGNonterminal.between s A q)]))
          have htransition' :
              M.transition transitionRule.source transitionRule.input? []
                transitionRule.target transitionRule.push :=
            (presentation.transition_complete
              transitionRule.source transitionRule.input? []
              transitionRule.target transitionRule.push).mpr
              ⟨transitionRule, htransitionRule, by
                simp [TransitionRule.Applies, hpop]⟩
          have hprod :
              M.ToCFGProduces
                (ToCFGNonterminal.between transitionRule.source A q)
                ((inputPrefix transitionRule.input? ++ chainRhs) ++
                  [Symbol.nonterminal
                    (ToCFGNonterminal.between s A q)]) :=
            ToCFGProduces.emptyBeforeTop htransition'
              (chainEndpointForms_sound hendpoint)
          simpa [List.append_assoc] using hprod
      | cons head tail =>
          simp [hpop] at hbefore

/-!
Completeness for the finite list runs the previous theorem in reverse. Each
abstract production constructor is matched with the exact list entry emitted by
the production-list generator, using the finite presentation to recover the
recorded transition rule.
-/

theorem toCFG_producesFromList_complete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {A : ToCFGNonterminal stack state}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    (hprod : ToCFGProduces M A rhs) :
    ToCFGProducesFromList M presentation A rhs := by
  cases hprod with
  | start haccept =>
      rename_i q
      refine
        ⟨{ lhs := ToCFGNonterminal.start,
           rhs := [Symbol.nonterminal (ToCFGNonterminal.empty M.start q)] },
          ?_, rfl, rfl⟩
      have hq : q ∈ presentation.acceptingStates :=
        (presentation.accept_complete q).mp haccept
      simp [productionList, startProductions]
      left
      exact ⟨q, hq, rfl⟩
  | emptyRefl =>
      rename_i q
      refine
        ⟨{ lhs := ToCFGNonterminal.empty q q, rhs := [] },
          ?_, rfl, rfl⟩
      simp [productionList, emptyReflProductions]
      right
      left
      exact ⟨q, M.statesFinite.complete q, rfl⟩
  | emptyStep htransition hchain =>
      rename_i p r s q a? push chainRhs
      rcases (presentation.transition_complete p a? [] r push).mp htransition with
        ⟨rule, hrule, hApplies⟩
      rcases hApplies with
        ⟨hsource, hinput, hpop, htarget, hpush⟩
      have hendpoint :
          (s, chainRhs) ∈
            chainEndpointForms (input := input) M.statesFinite.elems
              rule.target rule.push := by
        rw [htarget, hpush]
        exact chainEndpointForms_complete M.statesFinite.complete hchain
      let produced : CFG.Production input (ToCFGNonterminal stack state) :=
        { lhs := ToCFGNonterminal.empty rule.source q,
          rhs := inputPrefix rule.input? ++ chainRhs ++
            [Symbol.nonterminal (ToCFGNonterminal.empty s q)] }
      have hcase : produced ∈ emptyStepProductionsForRule M rule := by
        unfold produced emptyStepProductionsForRule
        rw [hpop]
        simp
        exact ⟨s, chainRhs, hendpoint, q, M.statesFinite.complete q,
          rfl, rfl, rfl⟩
      have htransitionProductions :
          produced ∈ transitionProductions M presentation := by
        unfold transitionProductions
        apply List.mem_flatMap.mpr
        refine ⟨rule, hrule, ?_⟩
        simp [hcase]
      refine ⟨produced, ?_, ?_, ?_⟩
      · simp [productionList, htransitionProductions]
      · simp [produced, hsource]
      · simp [produced, hinput]
  | popStep htransition hchain =>
      rename_i p r q A a? push chainRhs
      rcases (presentation.transition_complete p a? [A] r push).mp htransition with
        ⟨rule, hrule, hApplies⟩
      rcases hApplies with
        ⟨hsource, hinput, hpop, htarget, hpush⟩
      have hendpoint :
          (q, chainRhs) ∈
            chainEndpointForms (input := input) M.statesFinite.elems
              rule.target rule.push := by
        rw [htarget, hpush]
        exact chainEndpointForms_complete M.statesFinite.complete hchain
      let produced : CFG.Production input (ToCFGNonterminal stack state) :=
        { lhs := ToCFGNonterminal.between rule.source A q,
          rhs := inputPrefix rule.input? ++ chainRhs }
      have hcase : produced ∈ popStepProductionsForRule M rule := by
        unfold produced popStepProductionsForRule
        rw [hpop]
        simp
        exact ⟨q, hendpoint, rfl⟩
      have htransitionProductions :
          produced ∈ transitionProductions M presentation := by
        unfold transitionProductions
        apply List.mem_flatMap.mpr
        refine ⟨rule, hrule, ?_⟩
        simp [hcase]
      refine ⟨produced, ?_, ?_, ?_⟩
      · simp [productionList, htransitionProductions]
      · simp [produced, hsource]
      · simp [produced, hinput]
  | emptyBeforeTop htransition hchain =>
      rename_i p r s q A a? push chainRhs
      rcases (presentation.transition_complete p a? [] r push).mp htransition with
        ⟨rule, hrule, hApplies⟩
      rcases hApplies with
        ⟨hsource, hinput, hpop, htarget, hpush⟩
      have hendpoint :
          (s, chainRhs) ∈
            chainEndpointForms (input := input) M.statesFinite.elems
              rule.target rule.push := by
        rw [htarget, hpush]
        exact chainEndpointForms_complete M.statesFinite.complete hchain
      let produced : CFG.Production input (ToCFGNonterminal stack state) :=
        { lhs := ToCFGNonterminal.between rule.source A q,
          rhs := inputPrefix rule.input? ++ chainRhs ++
            [Symbol.nonterminal (ToCFGNonterminal.between s A q)] }
      have hcase :
          produced ∈ emptyBeforeTopProductionsForRule M presentation rule := by
        unfold produced emptyBeforeTopProductionsForRule
        rw [hpop]
        simp
        exact ⟨s, chainRhs, hendpoint, A,
          presentation.stackFinite.complete A, q,
          M.statesFinite.complete q, rfl, rfl, rfl⟩
      have htransitionProductions :
          produced ∈ transitionProductions M presentation := by
        unfold transitionProductions
        apply List.mem_flatMap.mpr
        refine ⟨rule, hrule, ?_⟩
        simp [hcase]
      refine ⟨produced, ?_, ?_, ?_⟩
      · simp [productionList, htransitionProductions]
      · simp [produced, hsource]
      · simp [produced, hinput]

theorem toCFG_producesFromList_iff
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {A : ToCFGNonterminal stack state}
    {rhs : SententialForm input (ToCFGNonterminal stack state)} :
    ToCFGProducesFromList M presentation A rhs <->
      ToCFGProduces M A rhs := by
  constructor
  · exact toCFG_producesFromList_sound
  · exact toCFG_producesFromList_complete

/-!
The next helpers move from one production to derivations of terminal words.
They introduce chain derivations, which mirror the stack word that a PDA
transition pushes and let the grammar derive the input consumed while later
summaries discharge each pushed symbol.
-/

theorem toCFG_derives_of_production
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {A : ToCFGNonterminal stack state}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    (hprod : ToCFGProduces M A rhs) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal A] rhs := by
  apply CFG.Derives.step
  · refine ⟨[], [], A, rhs, ?_, ?_, ?_⟩
    · exact toCFG_producesFromList_complete hprod
    · rfl
    · rfl
  · simpa using CFG.Derives.refl (G := ToCFG M presentation) rhs

theorem formLanguage_append_mem
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    {x y : SententialForm terminal nonterminal}
    {wx wy : Word terminal}
    (hx : wx ∈ CFG.FormLanguage symbolLanguage x)
    (hy : wy ∈ CFG.FormLanguage symbolLanguage y) :
    Word.Concat wx wy ∈ CFG.FormLanguage symbolLanguage (x ++ y) := by
  exact (CFG.formLanguage_append symbolLanguage x y
    (Word.Concat wx wy)).mpr ⟨wx, wy, hx, hy, rfl⟩

theorem formLanguage_single_nonterminal_derives
    {G : CFG terminal nonterminal}
    {A : nonterminal} {w : Word terminal}
    (h : CFG.Derives G [Symbol.nonterminal A]
      (SententialForm.terminalWord w)) :
    w ∈ CFG.FormLanguage (CFG.DerivationSymbolLanguage G)
      [Symbol.nonterminal A] := by
  exact ⟨w, Word.Empty, h, rfl, by simp [Word.Concat, Word.Empty]⟩

theorem inputPrefix_none_mem_derivationSymbolLanguage
    (G : CFG input nonterminal) :
    Word.Empty ∈ CFG.FormLanguage (CFG.DerivationSymbolLanguage G)
      (inputPrefix (input := input) (nonterminal := nonterminal) none) :=
  rfl

theorem inputPrefix_some_mem_derivationSymbolLanguage
    (G : CFG input nonterminal) (a : input) :
    Word.Symbol a ∈ CFG.FormLanguage (CFG.DerivationSymbolLanguage G)
      (inputPrefix (nonterminal := nonterminal) (some a)) := by
  exact ⟨Word.Symbol a, Word.Empty, rfl, rfl, by simp [Word.Concat, Word.Empty]⟩

inductive ToCFGChainDerives (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    state -> Word stack -> state -> Word input -> Prop where
  | nil (q : state) :
      ToCFGChainDerives M presentation q [] q Word.Empty
  | cons {p q r : state} {A : stack} {rest : Word stack}
      {first tail : Word input} :
      CFG.Derives (ToCFG M presentation)
        [Symbol.nonterminal (ToCFGNonterminal.between p A r)]
        (SententialForm.terminalWord first) ->
      ToCFGChainDerives M presentation r rest q tail ->
        ToCFGChainDerives M presentation p (A :: rest) q
          (Word.Concat first tail)

theorem toCFGChainDerives_formLanguage
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {push : Word stack} {w : Word input}
    (h : ToCFGChainDerives M presentation p push q w) :
    exists rhs : SententialForm input (ToCFGNonterminal stack state),
      ToCFGChain p push q rhs ∧
        w ∈ CFG.FormLanguage
          (CFG.DerivationSymbolLanguage (ToCFG M presentation)) rhs := by
  induction h with
  | nil q =>
      exact ⟨[], ToCFGChain.nil q, rfl⟩
  | cons hbetween _ ih =>
      rcases ih with ⟨rhs, hchain, hform⟩
      refine ⟨_, ToCFGChain.cons hchain, ?_⟩
      exact formLanguage_append_mem
        (CFG.DerivationSymbolLanguage (ToCFG M presentation))
        (formLanguage_single_nonterminal_derives hbetween) hform

theorem toCFGChainDerives_of_formLanguage
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {push : Word stack}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    (hchain : ToCFGChain p push q rhs)
    {w : Word input}
    (hw : w ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) rhs) :
    ToCFGChainDerives M presentation p push q w := by
  induction hchain with
  | nil q =>
      cases hw
      simpa [Word.Empty] using
        ToCFGChainDerives.nil (M := M) (presentation := presentation) q
  | cons hrest ih =>
      rename_i p q r A rest rhs
      rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
      rw [hwEq]
      exact ToCFGChainDerives.cons hfirst (ih htail)

theorem toCFGChainDerives_formLanguage_iff
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {push : Word stack} {w : Word input} :
    ToCFGChainDerives M presentation p push q w <->
      exists rhs : SententialForm input (ToCFGNonterminal stack state),
        ToCFGChain p push q rhs ∧
          w ∈ CFG.FormLanguage
            (CFG.DerivationSymbolLanguage (ToCFG M presentation)) rhs := by
  constructor
  · exact toCFGChainDerives_formLanguage
  · intro h
    rcases h with ⟨rhs, hchain, hform⟩
    exact toCFGChainDerives_of_formLanguage hchain hform

theorem toCFGChainDerives_append
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {left right : Word stack} {x y : Word input}
    (hleft : ToCFGChainDerives M presentation p left r x)
    (hright : ToCFGChainDerives M presentation r right q y) :
    ToCFGChainDerives M presentation p (Word.Concat left right) q
      (Word.Concat x y) := by
  induction hleft generalizing right q y with
  | nil r =>
      simpa [Word.Concat, Word.Empty] using hright
  | cons hbetween htail ih =>
      simpa [Word.Concat, List.append_assoc] using
        ToCFGChainDerives.cons hbetween (ih hright)


end PDA

end Grammars
end FoC
