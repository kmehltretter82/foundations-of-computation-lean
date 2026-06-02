import FoC.Grammars.CFG
import FoC.Grammars.PDA

namespace FoC
namespace Grammars

/-!
The standard PDA-to-CFG construction for PDAs in top-pop normal form.

The construction is factored around two summary nonterminal forms:

* `empty p q` generates words for computations that preserve the stack tail
  while moving from state `p` to state `q`.
* `between p A q` generates words for computations that remove one stack
  symbol `A`, leaving the stack tail unchanged, while moving from `p` to `q`.

The production rules are stated for PDAs whose transitions pop either no stack
symbol or exactly the current top stack symbol.  This is the grammar-friendly
normal form targeted by Chapter 4's PDA-to-CFG theorem.
-/

open Foundation
open Languages

namespace PDA

abbrev ToCFGNonterminal (stack : Type v) (state : Type w) :=
  Unit ⊕ (state × state) ⊕ ((state × stack) × state)

namespace ToCFGNonterminal

def start : ToCFGNonterminal stack state :=
  Sum.inl ()

def empty (p q : state) : ToCFGNonterminal stack state :=
  Sum.inr (Sum.inl (p, q))

def between (p : state) (A : stack) (q : state) :
    ToCFGNonterminal stack state :=
  Sum.inr (Sum.inr ((p, A), q))

def finite (stackFinite : FiniteType stack) (stateFinite : FiniteType state) :
    FiniteType (ToCFGNonterminal stack state) :=
  FiniteType.sum FiniteType.unit
    (FiniteType.sum
      (FiniteType.product stateFinite stateFinite)
      (FiniteType.product
        (FiniteType.product stateFinite stackFinite)
        stateFinite))

end ToCFGNonterminal

def inputPrefix (a? : Option input) :
    SententialForm input nonterminal :=
  match a? with
  | none => []
  | some a => [Symbol.terminal a]

inductive ToCFGChain :
    state -> Word stack -> state ->
      SententialForm input (ToCFGNonterminal stack state) -> Prop where
  | nil (q : state) :
      ToCFGChain q [] q []
  | cons {p q r : state} {A : stack} {rest : Word stack}
      {rhs : SententialForm input (ToCFGNonterminal stack state)} :
      ToCFGChain r rest q rhs ->
        ToCFGChain p (A :: rest) q
          (Symbol.nonterminal (ToCFGNonterminal.between p A r) :: rhs)

inductive ToCFGProduces (M : PDA input stack state) :
    ToCFGNonterminal stack state ->
      SententialForm input (ToCFGNonterminal stack state) -> Prop where
  | start {q : state} :
      M.accept q ->
        ToCFGProduces M ToCFGNonterminal.start
          [Symbol.nonterminal (ToCFGNonterminal.empty M.start q)]
  | emptyRefl {q : state} :
      ToCFGProduces M (ToCFGNonterminal.empty q q) []
  | emptyStep {p r s q : state} {a? : Option input}
      {push : Word stack}
      {chainRhs : SententialForm input (ToCFGNonterminal stack state)} :
      M.transition p a? [] r push ->
        ToCFGChain r push s chainRhs ->
          ToCFGProduces M (ToCFGNonterminal.empty p q)
            (inputPrefix a? ++ chainRhs ++
              [Symbol.nonterminal (ToCFGNonterminal.empty s q)])
  | popStep {p r q : state} {A : stack} {a? : Option input}
      {push : Word stack}
      {chainRhs : SententialForm input (ToCFGNonterminal stack state)} :
      M.transition p a? [A] r push ->
        ToCFGChain r push q chainRhs ->
          ToCFGProduces M (ToCFGNonterminal.between p A q)
            (inputPrefix a? ++ chainRhs)
  | emptyBeforeTop {p r s q : state} {A : stack} {a? : Option input}
      {push : Word stack}
      {chainRhs : SententialForm input (ToCFGNonterminal stack state)} :
      M.transition p a? [] r push ->
        ToCFGChain r push s chainRhs ->
        ToCFGProduces M (ToCFGNonterminal.between p A q)
          (inputPrefix a? ++ chainRhs ++
            [Symbol.nonterminal (ToCFGNonterminal.between s A q)])

def chainEndpointForms (states : List state) (p : state) :
    Word stack ->
      List (state × SententialForm input (ToCFGNonterminal stack state))
  | [] => [(p, [])]
  | A :: rest =>
      states.flatMap fun r =>
        (chainEndpointForms states r rest).map
          (fun endpoint =>
            (endpoint.1,
              Symbol.nonterminal (ToCFGNonterminal.between p A r) ::
                endpoint.2))

def startProductions (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    List (CFG.Production input (ToCFGNonterminal stack state)) :=
  presentation.acceptingStates.map
    (fun q =>
      { lhs := ToCFGNonterminal.start,
        rhs := [Symbol.nonterminal (ToCFGNonterminal.empty M.start q)] })

def emptyReflProductions (M : PDA input stack state) :
    List (CFG.Production input (ToCFGNonterminal stack state)) :=
  M.statesFinite.elems.map
    (fun q =>
      { lhs := ToCFGNonterminal.empty q q,
        rhs := [] })

def emptyStepProductionsForRule (M : PDA input stack state)
    (rule : TransitionRule input stack state) :
    List (CFG.Production input (ToCFGNonterminal stack state)) :=
  match rule.pop with
  | [] =>
      (chainEndpointForms (input := input) M.statesFinite.elems
          rule.target rule.push).flatMap
        (fun endpoint =>
          M.statesFinite.elems.map
            (fun q =>
              { lhs := ToCFGNonterminal.empty rule.source q,
                rhs := inputPrefix rule.input? ++ endpoint.2 ++
                  [Symbol.nonterminal
                    (ToCFGNonterminal.empty endpoint.1 q)] }))
  | _ => []

def popStepProductionsForRule (M : PDA input stack state)
    (rule : TransitionRule input stack state) :
    List (CFG.Production input (ToCFGNonterminal stack state)) :=
  match rule.pop with
  | A :: [] =>
      (chainEndpointForms (input := input) M.statesFinite.elems
          rule.target rule.push).map
        (fun endpoint =>
          { lhs := ToCFGNonterminal.between rule.source A endpoint.1,
            rhs := inputPrefix rule.input? ++ endpoint.2 })
  | _ => []

def emptyBeforeTopProductionsForRule (M : PDA input stack state)
    (presentation : FinitePresentation M)
    (rule : TransitionRule input stack state) :
    List (CFG.Production input (ToCFGNonterminal stack state)) :=
  match rule.pop with
  | [] =>
      (chainEndpointForms (input := input) M.statesFinite.elems
          rule.target rule.push).flatMap
        (fun endpoint =>
          presentation.stackFinite.elems.flatMap
            (fun A =>
              M.statesFinite.elems.map
                (fun q =>
                  { lhs := ToCFGNonterminal.between rule.source A q,
                    rhs := inputPrefix rule.input? ++ endpoint.2 ++
                      [Symbol.nonterminal
                        (ToCFGNonterminal.between endpoint.1 A q)] })))
  | _ => []

def transitionProductions (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    List (CFG.Production input (ToCFGNonterminal stack state)) :=
  presentation.transitionRules.flatMap
    (fun rule =>
      emptyStepProductionsForRule M rule ++
        popStepProductionsForRule M rule ++
        emptyBeforeTopProductionsForRule M presentation rule)

def productionList (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    List (CFG.Production input (ToCFGNonterminal stack state)) :=
  startProductions M presentation ++
    emptyReflProductions M ++
    transitionProductions M presentation

def ToCFGProducesFromList (M : PDA input stack state)
    (presentation : FinitePresentation M)
    (A : ToCFGNonterminal stack state)
    (rhs : SententialForm input (ToCFGNonterminal stack state)) : Prop :=
  exists rule, rule ∈ productionList M presentation ∧
    rule.lhs = A ∧ rule.rhs = rhs

def ToCFG (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    CFG input (ToCFGNonterminal stack state) where
  start := ToCFGNonterminal.start
  produces := ToCFGProducesFromList M presentation
  nonterminalsFinite :=
    ToCFGNonterminal.finite presentation.stackFinite M.statesFinite

theorem toCFG_hasFiniteProductions
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    CFG.HasFiniteProductions (ToCFG M presentation) := by
  exists productionList M presentation
  intro A rhs
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem chainEndpointForms_sound
    {states : List state} {p q : state} {push : Word stack}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    (h : (q, rhs) ∈ chainEndpointForms (input := input) states p push) :
    ToCFGChain p push q rhs := by
  induction push generalizing p q rhs with
  | nil =>
      simp [chainEndpointForms] at h
      rcases h with ⟨hq, hrhs⟩
      cases hq
      cases hrhs
      exact ToCFGChain.nil p
  | cons A rest ih =>
      simp [chainEndpointForms] at h
      rcases h with ⟨r, _hr, endpoint, hendpoint, hpair⟩
      have hchain := ih hpair.left
      cases hpair.right.left
      cases hpair.right.right
      exact ToCFGChain.cons hchain

theorem chainEndpointForms_complete
    {states : List state}
    (hstates : forall q : state, q ∈ states)
    {p q : state} {push : Word stack}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    (h : ToCFGChain p push q rhs) :
    (q, rhs) ∈ chainEndpointForms (input := input) states p push := by
  induction h with
  | nil q =>
      simp [chainEndpointForms]
  | cons hchain ih =>
      rename_i p q r A rest rhs
      simp [chainEndpointForms]
      exists r
      constructor
      · exact hstates r
      · exists q
        exists rhs
        constructor
        · exact ih hstates
        constructor
        · rfl
        constructor
        · rfl
        · rfl

def EmptySummary (M : PDA input stack state) (p q : state) :
    Language input :=
  fun w =>
    forall restInput tail,
      Computes M
        { state := p, unread := Word.Concat w restInput, stack := tail }
        { state := q, unread := restInput, stack := tail }

def BetweenSummary (M : PDA input stack state) (p : state) (A : stack)
    (q : state) : Language input :=
  fun w =>
    forall restInput tail,
      Computes M
        { state := p, unread := Word.Concat w restInput, stack := A :: tail }
        { state := q, unread := restInput, stack := tail }

def ToCFGSymbolLanguage (M : PDA input stack state) :
    Symbol input (ToCFGNonterminal stack state) -> Language input
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal (Sum.inl ()) => AcceptedLanguage M
  | Symbol.nonterminal (Sum.inr (Sum.inl (p, q))) =>
      EmptySummary M p q
  | Symbol.nonterminal (Sum.inr (Sum.inr ((p, A), q))) =>
      BetweenSummary M p A q

theorem toCFGChain_formLanguage_computes
    {M : PDA input stack state}
    {p q : state} {push : Word stack}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    (hchain : ToCFGChain p push q rhs)
    {w : Word input}
    (hw : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) rhs) :
    forall restInput tail,
      Computes M
        { state := p, unread := Word.Concat w restInput,
          stack := Word.Concat push tail }
        { state := q, unread := restInput, stack := tail } := by
  induction hchain with
  | nil q =>
      intro restInput tail
      cases hw
      simpa [Word.Concat] using
        Computes.refl
          ({ state := q, unread := restInput, stack := tail } :
            Configuration _ _ _)
  | cons hrest ih =>
      rename_i p q r A rest rhs
      intro restInput tail
      rcases hw with ⟨first, tailWord, hfirst, htail, hwEq⟩
      have hfirstComp :=
        hfirst (Word.Concat tailWord restInput) (Word.Concat rest tail)
      have hrestComp := ih htail restInput tail
      have hfirstComp' : Computes M
          { state := p,
            unread := Word.Concat (Word.Concat first tailWord) restInput,
            stack := Word.Concat (A :: rest) tail }
          { state := r,
            unread := Word.Concat tailWord restInput,
            stack := Word.Concat rest tail } := by
        simpa [Word.Concat, List.append_assoc] using hfirstComp
      rw [hwEq]
      exact computes_trans hfirstComp' hrestComp

theorem inputPrefix_formLanguage_step
    {M : PDA input stack state}
    {p r : state} {a? : Option input} {pop push : Word stack}
    (htransition : M.transition p a? pop r push)
    {pref : Word input}
    (hprefix :
      pref ∈ CFG.FormLanguage (ToCFGSymbolLanguage M)
        (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?)) :
    forall restInput tail,
      Computes M
        { state := p, unread := Word.Concat pref restInput,
          stack := Word.Concat pop tail }
        { state := r, unread := restInput,
          stack := Word.Concat push tail } := by
  cases a? with
  | none =>
      intro restInput tail
      cases hprefix
      simpa [inputPrefix, Word.Concat] using
        computes_of_step
          (Step.epsilon (M := M) (unread := restInput)
            (restStack := tail) htransition)
  | some a =>
      intro restInput tail
      rcases hprefix with ⟨first, tailWord, hfirst, htail, hprefixEq⟩
      cases hfirst
      cases htail
      rw [hprefixEq]
      simpa [inputPrefix, Word.Concat] using
        computes_of_step
          (Step.read (M := M) (unread := restInput)
            (restStack := tail) htransition)

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

theorem toCFG_yields_sound
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {x y : SententialForm input (ToCFGNonterminal stack state)}
    {w : Word input}
    (h : CFG.Yields (ToCFG M presentation) x y)
    (hw : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) y) :
    w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) x := by
  rcases h with ⟨u, v, A, rhs, hprod, hx, hy⟩
  rw [hy] at hw
  rw [hx]
  exact CFG.formLanguage_replace_sound
    (ToCFGSymbolLanguage M)
    (toCFG_production_sound (toCFG_producesFromList_sound hprod))
    hw

theorem toCFG_derives_sound
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {x y : SententialForm input (ToCFGNonterminal stack state)}
    {w : Word input}
    (h : CFG.Derives (ToCFG M presentation) x y)
    (hw : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) y) :
    w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) x := by
  induction h with
  | refl _ =>
      exact hw
  | step hstep _ ih =>
      exact toCFG_yields_sound hstep (ih hw)

theorem toCFG_accepts_of_generates
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input}
    (h : w ∈ CFG.GeneratedLanguage (ToCFG M presentation)) :
    Accepts M w := by
  have hterminal : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M)
      (SententialForm.terminalWord
        (nt := ToCFGNonterminal stack state) w) :=
    CFG.terminalWord_mem_formLanguage (ToCFGSymbolLanguage M)
      (by intro a; rfl) w
  have hsound := toCFG_derives_sound h hterminal
  rcases hsound with ⟨first, tailWord, hfirst, htail, hwEq⟩
  cases htail
  rw [hwEq, Word.concat_empty_right]
  exact hfirst

def ToCFGTopPopExact (M : PDA input stack state)
    (presentation : FinitePresentation M) : Prop :=
  Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
    (PDA.AcceptedLanguage M)

theorem toCFG_nonterminals_finite
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    (ToCFG M presentation).nonterminalsFinite =
      ToCFGNonterminal.finite presentation.stackFinite M.statesFinite :=
  rfl

end PDA

end Grammars
end FoC
