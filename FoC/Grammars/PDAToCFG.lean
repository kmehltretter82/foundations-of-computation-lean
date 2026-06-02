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

theorem toCFG_derives_of_production_word
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {A : ToCFGNonterminal stack state}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    {w : Word input}
    (hprod : ToCFGProduces M A rhs)
    (hw : w ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) rhs) :
    CFG.Derives (ToCFG M presentation) [Symbol.nonterminal A]
      (SententialForm.terminalWord w) := by
  exact CFG.derives_trans (toCFG_derives_of_production hprod)
    (CFG.formLanguage_derives hw)

theorem toCFG_start_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {q : state} {w : Word input}
    (haccept : M.accept q)
    (hbody : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty M.start q)]
      (SententialForm.terminalWord w)) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  apply toCFG_derives_of_production_word
    (M := M) (presentation := presentation)
    (ToCFGProduces.start haccept)
  exact formLanguage_single_nonterminal_derives hbody

theorem toCFG_emptyRefl_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {q : state} :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty q q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) := by
  simpa [SententialForm.terminalWord, Word.Empty] using
    toCFG_derives_of_production
      (M := M) (presentation := presentation)
      (ToCFGProduces.emptyRefl (q := q))

theorem toCFG_popStep_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (ToCFGNonterminal stack state)}
    {pref chainWord : Word input}
    (htransition : M.transition p a? [A] r push)
    (hchain : ToCFGChain r push q chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) chainRhs) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Concat pref chainWord)) := by
  apply toCFG_derives_of_production_word
    (M := M) (presentation := presentation)
    (ToCFGProduces.popStep htransition hchain)
  exact formLanguage_append_mem
    (CFG.DerivationSymbolLanguage (ToCFG M presentation)) hpref hchainWord

theorem toCFG_emptyStep_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (ToCFGNonterminal stack state)}
    {pref chainWord emptyWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : ToCFGChain r push s chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) chainRhs)
    (hempty : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord emptyWord))) := by
  apply toCFG_derives_of_production_word
    (M := M) (presentation := presentation)
    (ToCFGProduces.emptyStep htransition hchain)
  have htail : Word.Concat chainWord emptyWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (chainRhs ++
        [Symbol.nonterminal (ToCFGNonterminal.empty s q)]) := by
    exact formLanguage_append_mem
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      hchainWord
      (formLanguage_single_nonterminal_derives hempty)
  simpa [List.append_assoc] using
    formLanguage_append_mem
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) hpref htail

theorem toCFG_emptyBeforeTop_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (ToCFGNonterminal stack state)}
    {pref chainWord topWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : ToCFGChain r push s chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) chainRhs)
    (htop : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord topWord))) := by
  apply toCFG_derives_of_production_word
    (M := M) (presentation := presentation)
    (ToCFGProduces.emptyBeforeTop htransition hchain)
  have htail : Word.Concat chainWord topWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (chainRhs ++
        [Symbol.nonterminal (ToCFGNonterminal.between s A q)]) := by
    exact formLanguage_append_mem
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      hchainWord
      (formLanguage_single_nonterminal_derives htop)
  simpa [List.append_assoc] using
    formLanguage_append_mem
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) hpref htail

theorem toCFG_popStep_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {pref chainWord : Word input}
    (htransition : M.transition p a? [A] r push)
    (hchain : ToCFGChainDerives M presentation r push q chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Concat pref chainWord)) := by
  rcases toCFGChainDerives_formLanguage hchain with
    ⟨chainRhs, hchainRhs, hchainWord⟩
  exact toCFG_popStep_derives htransition hchainRhs hpref hchainWord

theorem toCFG_emptyStep_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {a? : Option input}
    {push : Word stack}
    {pref chainWord emptyWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (hempty : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord emptyWord))) := by
  rcases toCFGChainDerives_formLanguage hchain with
    ⟨chainRhs, hchainRhs, hchainWord⟩
  exact toCFG_emptyStep_derives htransition hchainRhs hpref
    hchainWord hempty

theorem toCFG_emptyBeforeTop_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {pref chainWord topWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (htop : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord topWord))) := by
  rcases toCFGChainDerives_formLanguage hchain with
    ⟨chainRhs, hchainRhs, hchainWord⟩
  exact toCFG_emptyBeforeTop_derives htransition hchainRhs hpref
    hchainWord htop

theorem toCFG_popRead_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {A : stack} {a : input}
    {push : Word stack} {chainWord : Word input}
    (htransition : M.transition p (some a) [A] r push)
    (hchain : ToCFGChainDerives M presentation r push q chainWord) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a) chainWord)) := by
  exact toCFG_popStep_of_chainDerives htransition hchain
    (inputPrefix_some_mem_derivationSymbolLanguage
      (ToCFG M presentation) a)

theorem toCFG_popEpsilon_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {A : stack}
    {push : Word stack} {chainWord : Word input}
    (htransition : M.transition p none [A] r push)
    (hchain : ToCFGChainDerives M presentation r push q chainWord) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord chainWord) := by
  simpa [Word.Concat, Word.Empty] using
    toCFG_popStep_of_chainDerives htransition hchain
      (inputPrefix_none_mem_derivationSymbolLanguage
        (ToCFG M presentation))

theorem toCFG_emptyRead_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {a : input}
    {push : Word stack}
    {chainWord emptyWord : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (hempty : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a)
          (Word.Concat chainWord emptyWord))) := by
  exact toCFG_emptyStep_of_chainDerives htransition hchain
    (inputPrefix_some_mem_derivationSymbolLanguage
      (ToCFG M presentation) a)
    hempty

theorem toCFG_emptyEpsilon_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state}
    {push : Word stack}
    {chainWord emptyWord : Word input}
    (htransition : M.transition p none [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (hempty : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat chainWord emptyWord)) := by
  simpa [Word.Concat, Word.Empty] using
    toCFG_emptyStep_of_chainDerives htransition hchain
      (inputPrefix_none_mem_derivationSymbolLanguage
        (ToCFG M presentation))
      hempty

theorem toCFG_emptyBeforeTopRead_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {A : stack} {a : input}
    {push : Word stack}
    {chainWord topWord : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (htop : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a)
          (Word.Concat chainWord topWord))) := by
  exact toCFG_emptyBeforeTop_of_chainDerives htransition hchain
    (inputPrefix_some_mem_derivationSymbolLanguage
      (ToCFG M presentation) a)
    htop

theorem toCFG_emptyBeforeTopEpsilon_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {A : stack}
    {push : Word stack}
    {chainWord topWord : Word input}
    (htransition : M.transition p none [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (htop : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat chainWord topWord)) := by
  simpa [Word.Concat, Word.Empty] using
    toCFG_emptyBeforeTop_of_chainDerives htransition hchain
      (inputPrefix_none_mem_derivationSymbolLanguage
        (ToCFG M presentation))
      htop

theorem toCFG_emptyRead_of_step_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {a : input} {restInput : Word input}
    (hstep : Step M
      { state := p, unread := a :: restInput, stack := [] }
      { state := q, unread := restInput, stack := [] }) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord (Word.Symbol a)) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hunreadSource : a :: restInput = a' :: unread := by
      exact congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have ha : a = a' := (List.cons.inj hunreadSource).1
    have hunread : restInput = unread := (List.cons.inj hunreadSource).2
    have hpop : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have hpush : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpop
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpop
      simp [Word.Concat] at hlen
      omega
    have hpushNil : push = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpush
      simp [Word.Concat, hrestNil] at hlen
      omega
    have htransition' : M.transition p (some a) [] q [] := by
      simpa [hp, hq, ha, hunread, hpopNil, hpushNil] using htransition
    have hbody :=
      toCFG_emptyRead_of_chainDerives
        (M := M) (presentation := presentation)
        (p := p) (r := q) (s := q) (q := q)
        (a := a) (push := ([] : Word stack))
        (chainWord := (Word.Empty : Word input))
        (emptyWord := (Word.Empty : Word input))
        htransition'
        (ToCFGChainDerives.nil (M := M) (presentation := presentation) q)
        (toCFG_emptyRefl_derives
          (M := M) (presentation := presentation) (q := q))
    simpa [Word.Concat, Word.Empty] using hbody
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        _htransition, hc, hd⟩
    have hunreadSource : a :: restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hunreadTarget : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hbad : a :: restInput = restInput := by
      exact hunreadSource.trans hunreadTarget.symm
    have hlen := congrArg List.length hbad
    simp at hlen

theorem toCFG_emptyEpsilon_of_step_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {restInput : Word input}
    (hstep : Step M
      { state := p, unread := restInput, stack := [] }
      { state := q, unread := restInput, stack := [] }) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    have hunreadSource : restInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hunreadTarget : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hbad : a :: unread = unread := by
      exact hunreadSource.symm.trans hunreadTarget
    have hlen := congrArg List.length hbad
    simp at hlen
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hunread : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hpop : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have hpush : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpop
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpop
      simp [Word.Concat] at hlen
      omega
    have hpushNil : push = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpush
      simp [Word.Concat, hrestNil] at hlen
      omega
    have htransition' : M.transition p none [] q [] := by
      simpa [hp, hq, hunread, hpopNil, hpushNil] using htransition
    have hbody :=
      toCFG_emptyEpsilon_of_chainDerives
        (M := M) (presentation := presentation)
        (p := p) (r := q) (s := q) (q := q)
        (push := ([] : Word stack))
        (chainWord := (Word.Empty : Word input))
        (emptyWord := (Word.Empty : Word input))
        htransition'
        (ToCFGChainDerives.nil (M := M) (presentation := presentation) q)
        (toCFG_emptyRefl_derives
          (M := M) (presentation := presentation) (q := q))
    simpa [Word.Concat, Word.Empty] using hbody

theorem toCFG_betweenRead_of_step_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack} {a : input}
    {restInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := a :: restInput, stack := A :: tail }
      { state := q, unread := restInput, stack := tail }) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Symbol a)) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hunreadSource : a :: restInput = a' :: unread := by
      exact congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have ha : a = a' := (List.cons.inj hunreadSource).1
    have hunread : restInput = unread := (List.cons.inj hunreadSource).2
    have hsourceStack : A :: tail = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have htargetStack : tail = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    rcases hnorm p' (some a') pop q' push htransition with
      hpopEmpty | hpopSingle
    · have hsourceLen := congrArg List.length hsourceStack
      have htargetLen := congrArg List.length htargetStack
      simp [Word.Concat, hpopEmpty] at hsourceLen htargetLen
      omega
    · rcases hpopSingle with ⟨B, hpopSingle⟩
      have hsourceCons : A :: tail = B :: restStack := by
        simpa [Word.Concat, hpopSingle] using hsourceStack
      have hA : A = B := (List.cons.inj hsourceCons).1
      have hrest : tail = restStack := (List.cons.inj hsourceCons).2
      have hpushNil : push = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hrestLen := congrArg List.length hrest
        have hlen := congrArg List.length htargetStack
        simp [Word.Concat] at hrestLen hlen
        omega
      have htransition' : M.transition p (some a) [A] q [] := by
        simpa [hp, hq, ha, hunread, hpopSingle, hA, hpushNil] using
          htransition
      have hbody :=
        toCFG_popRead_of_chainDerives
          (M := M) (presentation := presentation)
          (p := p) (r := q) (q := q)
          (A := A) (a := a) (push := ([] : Word stack))
          (chainWord := (Word.Empty : Word input))
          htransition'
          (ToCFGChainDerives.nil (M := M)
            (presentation := presentation) q)
      simpa [Word.Concat, Word.Empty] using hbody
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        _htransition, hc, hd⟩
    have hunreadSource : a :: restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hunreadTarget : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hbad : a :: restInput = restInput := by
      exact hunreadSource.trans hunreadTarget.symm
    have hlen := congrArg List.length hbad
    simp at hlen

theorem toCFG_betweenEpsilon_of_step_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack}
    {restInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := restInput, stack := A :: tail }
      { state := q, unread := restInput, stack := tail }) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    have hunreadSource : restInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hunreadTarget : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hbad : a :: unread = unread := by
      exact hunreadSource.symm.trans hunreadTarget
    have hlen := congrArg List.length hbad
    simp at hlen
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hunread : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hsourceStack : A :: tail = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have htargetStack : tail = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    rcases hnorm p' none pop q' push htransition with
      hpopEmpty | hpopSingle
    · have hsourceLen := congrArg List.length hsourceStack
      have htargetLen := congrArg List.length htargetStack
      simp [Word.Concat, hpopEmpty] at hsourceLen htargetLen
      omega
    · rcases hpopSingle with ⟨B, hpopSingle⟩
      have hsourceCons : A :: tail = B :: restStack := by
        simpa [Word.Concat, hpopSingle] using hsourceStack
      have hA : A = B := (List.cons.inj hsourceCons).1
      have hrest : tail = restStack := (List.cons.inj hsourceCons).2
      have hpushNil : push = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hrestLen := congrArg List.length hrest
        have hlen := congrArg List.length htargetStack
        simp [Word.Concat] at hrestLen hlen
        omega
      have htransition' : M.transition p none [A] q [] := by
        simpa [hp, hq, hunread, hpopSingle, hA, hpushNil] using
          htransition
      have hbody :=
        toCFG_popEpsilon_of_chainDerives
          (M := M) (presentation := presentation)
          (p := p) (r := q) (q := q)
          (A := A) (push := ([] : Word stack))
          (chainWord := (Word.Empty : Word input))
          htransition'
          (ToCFGChainDerives.nil (M := M)
            (presentation := presentation) q)
      simpa [Word.Concat, Word.Empty] using hbody

theorem toCFG_generates_of_acceptsIn_zero
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : ComputesIn M 0 (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  have hend := computesIn_zero_eq hcomp
  have hstate : M.start = qf := by
    simpa [initial] using congrArg
      (fun c : Configuration input stack state => c.state) hend
  have hunread : w = [] := by
    simpa [initial] using congrArg
      (fun c : Configuration input stack state => c.unread) hend
  have hbody : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty M.start qf)]
      (SententialForm.terminalWord (Word.Empty : Word input)) := by
    simpa [hstate] using
      toCFG_emptyRefl_derives
        (M := M) (presentation := presentation) (q := M.start)
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := Word.Empty) haccept hbody
  simpa [hunread] using hgen

theorem toCFG_generates_of_acceptsIn_one
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : ComputesIn M 1 (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  have hstep := computesIn_one_inv hcomp
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨q, r, a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    simp [initial, Word.Concat] at hc hd
    rcases hc with ⟨hstart, hw, hpop⟩
    rcases hd with ⟨hr, hunread, hpush⟩
    have hpopNil : pop = [] := by
      cases pop with
      | nil => rfl
      | cons _ _ => cases hpop
    have hpushNil : push = [] := by
      cases push with
      | nil => rfl
      | cons _ _ => cases hpush
    have htransition' :
        M.transition M.start (some a) [] qf [] := by
      simpa [hstart, hr, hpopNil, hpushNil] using htransition
    have hbody : CFG.Derives (ToCFG M presentation)
        [Symbol.nonterminal (ToCFGNonterminal.empty M.start qf)]
        (SententialForm.terminalWord (Word.Symbol a)) := by
      simpa [Word.Concat, Word.Empty] using
        toCFG_emptyRead_of_chainDerives
          (M := M) (presentation := presentation)
          (p := M.start) (r := qf) (s := qf) (q := qf)
          (a := a) (push := ([] : Word stack))
          (chainWord := (Word.Empty : Word input))
          (emptyWord := (Word.Empty : Word input))
          htransition'
          (ToCFGChainDerives.nil (M := M)
            (presentation := presentation) qf)
          (toCFG_emptyRefl_derives
            (M := M) (presentation := presentation) (q := qf))
    have hgen := toCFG_start_derives
      (M := M) (presentation := presentation)
      (q := qf) (w := Word.Symbol a) haccept hbody
    simpa [hw, hunread, Word.Symbol] using hgen
  · rcases heps with
      ⟨q, r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    simp [initial, Word.Concat] at hc hd
    rcases hc with ⟨hstart, hw, hpop⟩
    rcases hd with ⟨hr, hunread, hpush⟩
    have hpopNil : pop = [] := by
      cases pop with
      | nil => rfl
      | cons _ _ => cases hpop
    have hpushNil : push = [] := by
      cases push with
      | nil => rfl
      | cons _ _ => cases hpush
    have htransition' :
        M.transition M.start none [] qf [] := by
      simpa [hstart, hr, hpopNil, hpushNil] using htransition
    have hbody : CFG.Derives (ToCFG M presentation)
        [Symbol.nonterminal (ToCFGNonterminal.empty M.start qf)]
        (SententialForm.terminalWord (Word.Empty : Word input)) := by
      simpa [Word.Concat, Word.Empty] using
        toCFG_emptyEpsilon_of_chainDerives
          (M := M) (presentation := presentation)
          (p := M.start) (r := qf) (s := qf) (q := qf)
          (push := ([] : Word stack))
          (chainWord := (Word.Empty : Word input))
          (emptyWord := (Word.Empty : Word input))
          htransition'
          (ToCFGChainDerives.nil (M := M)
            (presentation := presentation) qf)
          (toCFG_emptyRefl_derives
            (M := M) (presentation := presentation) (q := qf))
    have hgen := toCFG_start_derives
      (M := M) (presentation := presentation)
      (q := qf) (w := Word.Empty) haccept hbody
    simpa [hw, hunread, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_atMostOne
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hn : n <= 1)
    (haccept : M.accept qf)
    (hcomp : ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  cases n with
  | zero =>
      exact toCFG_generates_of_acceptsIn_zero
        (M := M) (presentation := presentation)
        (w := w) (qf := qf) haccept hcomp
  | succ n =>
      cases n with
      | zero =>
          exact toCFG_generates_of_acceptsIn_one
            (M := M) (presentation := presentation)
            (w := w) (qf := qf) haccept hcomp
      | succ n =>
          omega

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
  PopsAtMostOne M ->
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
