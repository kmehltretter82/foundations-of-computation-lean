import FoC.Grammars.CFG
import FoC.Grammars.PDANormalize

set_option doc.verso true

/-!
# From PDAs to CFGs

## Summary nonterminals

The construction is factored around two summary nonterminal forms:

* {lit}`empty p q` generates words for computations that preserve the stack tail
  while moving from state {lit}`p` to state {lit}`q`.
* {lit}`between p A q` generates words for computations that remove one stack
  symbol {lit}`A`, leaving the stack tail unchanged, while moving from {lit}`p`
  to {lit}`q`.

The production rules are stated for PDAs whose transitions pop either no stack
symbol or exactly the current top stack symbol.  This is the grammar-friendly
normal form targeted by Chapter 4's PDA-to-CFG theorem.
-/

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace PDA

/-!
# Summary nonterminal syntax

The nonterminal type contains a start symbol plus the two summary forms used to
describe empty-stack and single-stack-symbol computations.
-/

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

/-!
# Summary productions

The production relation mirrors normalized PDA steps: start productions choose
an accepting state, empty summaries preserve stack tails, and between summaries
remove one stack symbol.
-/

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

/-!
# Finite production list

For a finite PDA presentation, the abstract production relation is compiled
into an explicit finite CFG production list.
-/

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

/-!
# Production-list correctness

These lemmas prove that the finite list presents exactly the abstract summary
production relation.
-/

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

/-!
The next derivation helpers erase form-language bookkeeping. They convert
production-level evidence into derivations of concrete terminal words, which is
the shape needed by the later PDA-step simulations.
-/

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

/-!
The preceding derivation lemmas work with an explicit right-hand-side chain.
The following variants package that chain as a derivation object and split the
read and epsilon cases, matching the way PDA steps are analyzed later.
-/

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

/-!
Now the proof turns one concrete PDA step into the corresponding CFG
derivation. There are separate empty-stack and top-pop cases because the summary
nonterminals describe those two stack effects directly.
-/

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

/-!
The top-pop step cases are the stack-sensitive analogue of the empty-stack
cases. The PDA step consumes a top symbol, the chain derivation handles whatever
the transition pushes, and the generated word records the input consumed by the
step plus the input consumed while discharging the pushed stack.
-/

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

/-!
After the individual read and epsilon cases, the next lemmas package them into
case splitters. They are convenient interfaces for induction on computations:
the caller supplies a PDA step, and the lemma returns the consumed prefix plus
the matching summary derivation.
-/

theorem toCFG_emptyDerives_cases_of_step_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hstep : Step M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    (sourceInput = targetInput ∧
      CFG.Derives (ToCFG M presentation)
        [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
        (SententialForm.terminalWord (Word.Empty : Word input))) ∨
    (exists a : input,
      sourceInput = a :: targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord (Word.Symbol a))) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    right
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hinput : sourceInput = a :: targetInput := by
      simpa [htarget] using hsource
    refine ⟨a, hinput, ?_⟩
    have hstep' : Step M
        { state := p, unread := a :: targetInput, stack := [] }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [hinput] using hstep
    exact toCFG_emptyRead_of_step_emptyStack
      (M := M) (presentation := presentation) hstep'
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        _htransition, hc, hd⟩
    left
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hinput : sourceInput = targetInput := hsource.trans htarget.symm
    refine ⟨hinput, ?_⟩
    have hstep' : Step M
        { state := p, unread := targetInput, stack := [] }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [hinput] using hstep
    exact toCFG_emptyEpsilon_of_step_emptyStack
      (M := M) (presentation := presentation) hstep'

theorem toCFG_betweenDerives_cases_of_step_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    (sourceInput = targetInput ∧
      CFG.Derives (ToCFG M presentation)
        [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
        (SententialForm.terminalWord (Word.Empty : Word input))) ∨
    (exists a : input,
      sourceInput = a :: targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord (Word.Symbol a))) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    right
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hinput : sourceInput = a :: targetInput := by
      simpa [htarget] using hsource
    refine ⟨a, hinput, ?_⟩
    have hstep' : Step M
        { state := p, unread := a :: targetInput, stack := A :: tail }
        { state := q, unread := targetInput, stack := tail } := by
      simpa [hinput] using hstep
    exact toCFG_betweenRead_of_step_topPop
      (M := M) (presentation := presentation) hnorm hstep'
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        _htransition, hc, hd⟩
    left
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hinput : sourceInput = targetInput := hsource.trans htarget.symm
    refine ⟨hinput, ?_⟩
    have hstep' : Step M
        { state := p, unread := targetInput, stack := A :: tail }
        { state := q, unread := targetInput, stack := tail } := by
      simpa [hinput] using hstep
    exact toCFG_betweenEpsilon_of_step_topPop
      (M := M) (presentation := presentation) hnorm hstep'

/-!
For short computations, the proof can reason by explicit step count. These
bounded lemmas are the base cases for the later summary-computation induction:
zero, one, and two normalized PDA steps are converted into CFG derivations.
-/

theorem step_sourceStack_empty_or_single_of_step_to_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    {sourceStack : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := sourceStack }
      { state := q, unread := targetInput, stack := [] }) :
    sourceStack = [] ∨ exists A : stack, sourceStack = [A] := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hsourceStack : sourceStack = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have htargetStack : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length htargetStack
      simp [Word.Concat] at hlen
      omega
    rcases hnorm p' (some a) pop q' push htransition with
      hpopNil | hpopSingle
    · left
      simpa [Word.Concat, hpopNil, hrestNil] using hsourceStack
    · rcases hpopSingle with ⟨A, hpopSingle⟩
      right
      refine ⟨A, ?_⟩
      simpa [Word.Concat, hpopSingle, hrestNil] using hsourceStack
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hsourceStack : sourceStack = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have htargetStack : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length htargetStack
      simp [Word.Concat] at hlen
      omega
    rcases hnorm p' none pop q' push htransition with
      hpopNil | hpopSingle
    · left
      simpa [Word.Concat, hpopNil, hrestNil] using hsourceStack
    · rcases hpopSingle with ⟨A, hpopSingle⟩
      right
      refine ⟨A, ?_⟩
      simpa [Word.Concat, hpopSingle, hrestNil] using hsourceStack

theorem toCFG_emptyDerives_of_computesIn_zero_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : ComputesIn M 0
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  have hend := computesIn_zero_eq hcomp
  have hstate : p = q := by
    simpa using congrArg
      (fun c : Configuration input stack state => c.state) hend
  have hunread : sourceInput = targetInput := by
    simpa using congrArg
      (fun c : Configuration input stack state => c.unread) hend
  refine ⟨Word.Empty, ?_, ?_⟩
  · simpa [Word.Concat, Word.Empty] using hunread
  · simpa [hstate, SententialForm.terminalWord, Word.Empty] using
      toCFG_emptyRefl_derives
        (M := M) (presentation := presentation) (q := p)

/-!
For one-step empty-stack computations, the zero-step base case above is joined
with the step case splitter. This is the first bounded-computation theorem that
turns a concrete PDA run into a CFG derivation.
-/

theorem toCFG_emptyDerives_of_computesIn_one_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : ComputesIn M 1
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  have hstep := computesIn_one_inv hcomp
  rcases toCFG_emptyDerives_cases_of_step_emptyStack
      (M := M) (presentation := presentation) hstep with
    hempty | hread
  · rcases hempty with ⟨hinput, hderive⟩
    refine ⟨Word.Empty, ?_, ?_⟩
    · simpa [Word.Concat, Word.Empty] using hinput
    · simpa [Word.Empty] using hderive
  · rcases hread with ⟨a, hinput, hderive⟩
    refine ⟨Word.Symbol a, ?_, ?_⟩
    · simpa [Word.Concat, Word.Symbol] using hinput
    · exact hderive

theorem toCFG_emptyDerives_of_computesIn_atMostOne_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hn : n <= 1)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  cases n with
  | zero =>
      exact toCFG_emptyDerives_of_computesIn_zero_emptyStack
        (M := M) (presentation := presentation) hcomp
  | succ n =>
      cases n with
      | zero =>
          exact toCFG_emptyDerives_of_computesIn_one_emptyStack
            (M := M) (presentation := presentation) hcomp
      | succ n =>
          omega

theorem toCFG_betweenDerives_of_computesIn_one_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M 1
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) := by
  have hstep := computesIn_one_inv hcomp
  rcases toCFG_betweenDerives_cases_of_step_topPop
      (M := M) (presentation := presentation) hnorm hstep with
    hempty | hread
  · rcases hempty with ⟨hinput, hderive⟩
    refine ⟨Word.Empty, ?_, ?_⟩
    · simpa [Word.Concat, Word.Empty] using hinput
    · simpa [Word.Empty] using hderive
  · rcases hread with ⟨a, hinput, hderive⟩
    refine ⟨Word.Symbol a, ?_, ?_⟩
    · simpa [Word.Concat, Word.Symbol] using hinput
    · exact hderive

/-!
Two-step empty-stack computations are the first place where normalization
matters. The first step may expose a temporary stack symbol; the proof handles
that by deriving a between-summary for the top symbol and then closing the
remaining empty-stack suffix.
-/

theorem toCFG_emptyDerives_of_computesIn_two_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M 2
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  rcases computesIn_succ_inv (M := M) (n := 1) hcomp with
    ⟨mid, hfirst, htail⟩
  have hsecond0 : Step M mid
      { state := q, unread := targetInput, stack := [] } :=
    computesIn_one_inv htail
  rcases step_cases hfirst with hread | heps
  · rcases hread with
      ⟨p', r, a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' :
        M.transition p (some a) [] r push := by
      simpa [hp, hpopNil] using htransition
    cases hd
    have hsecond : Step M
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [Word.Concat, hrestNil] using hsecond0
    rcases step_sourceStack_empty_or_single_of_step_to_emptyStack
        (M := M) hnorm hsecond with hpushNil | hpushSingle
    · have htransitionEmpty :
          M.transition p (some a) [] r [] := by
        simpa [hpushNil] using htransition'
      have hsecondEmpty : Step M
          { state := r, unread := unread, stack := [] }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushNil] using hsecond
      rcases toCFG_emptyDerives_of_computesIn_one_emptyStack
          (M := M) (presentation := presentation)
          (computesIn_of_step hsecondEmpty) with
        ⟨restWord, hrestInput, hrestDerive⟩
      let consumed := Word.Concat (Word.Symbol a) restWord
      have hsourceConsumed :
          sourceInput = Word.Concat consumed targetInput := by
        rw [hsource, hrestInput]
        simp [consumed, Word.Concat, Word.Symbol]
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed, Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyRead_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p) (r := r) (s := r) (q := q)
            (a := a) (push := ([] : Word stack))
            (chainWord := (Word.Empty : Word input))
            (emptyWord := restWord)
            htransitionEmpty
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) r)
            hrestDerive
      exact ⟨consumed, hsourceConsumed, hbody⟩
    · rcases hpushSingle with ⟨A, hpushSingle⟩
      have htransitionSingle :
          M.transition p (some a) [] r [A] := by
        simpa [hpushSingle] using htransition'
      have hsecondTop : Step M
          { state := r, unread := unread, stack := A :: ([] : Word stack) }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushSingle] using hsecond
      rcases toCFG_betweenDerives_of_computesIn_one_topPop
          (M := M) (presentation := presentation) hnorm
          (computesIn_of_step hsecondTop) with
        ⟨topWord, htopInput, htopDerive⟩
      let consumed := Word.Concat (Word.Symbol a) topWord
      have hsourceConsumed :
          sourceInput = Word.Concat consumed targetInput := by
        rw [hsource, htopInput]
        simp [consumed, Word.Concat, Word.Symbol]
      have hchain : ToCFGChainDerives M presentation r [A] q topWord := by
        simpa [Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons htopDerive
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed, Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyRead_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p) (r := r) (s := q) (q := q)
            (a := a) (push := [A])
            (chainWord := topWord)
            (emptyWord := (Word.Empty : Word input))
            htransitionSingle hchain
            (toCFG_emptyRefl_derives
              (M := M) (presentation := presentation) (q := q))
      exact ⟨consumed, hsourceConsumed, hbody⟩
  · rcases heps with
      ⟨p', r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' :
        M.transition p none [] r push := by
      simpa [hp, hpopNil] using htransition
    cases hd
    have hsecond : Step M
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [Word.Concat, hrestNil] using hsecond0
    rcases step_sourceStack_empty_or_single_of_step_to_emptyStack
        (M := M) hnorm hsecond with hpushNil | hpushSingle
    · have htransitionEmpty :
          M.transition p none [] r [] := by
        simpa [hpushNil] using htransition'
      have hsecondEmpty : Step M
          { state := r, unread := unread, stack := [] }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushNil] using hsecond
      rcases toCFG_emptyDerives_of_computesIn_one_emptyStack
          (M := M) (presentation := presentation)
          (computesIn_of_step hsecondEmpty) with
        ⟨restWord, hrestInput, hrestDerive⟩
      have hsourceConsumed :
          sourceInput = Word.Concat restWord targetInput := by
        rw [hsource, hrestInput]
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord restWord) := by
        simpa [Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p) (r := r) (s := r) (q := q)
            (push := ([] : Word stack))
            (chainWord := (Word.Empty : Word input))
            (emptyWord := restWord)
            htransitionEmpty
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) r)
            hrestDerive
      exact ⟨restWord, hsourceConsumed, hbody⟩
    · rcases hpushSingle with ⟨A, hpushSingle⟩
      have htransitionSingle :
          M.transition p none [] r [A] := by
        simpa [hpushSingle] using htransition'
      have hsecondTop : Step M
          { state := r, unread := unread, stack := A :: ([] : Word stack) }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushSingle] using hsecond
      rcases toCFG_betweenDerives_of_computesIn_one_topPop
          (M := M) (presentation := presentation) hnorm
          (computesIn_of_step hsecondTop) with
        ⟨topWord, htopInput, htopDerive⟩
      have hsourceConsumed :
          sourceInput = Word.Concat topWord targetInput := by
        rw [hsource, htopInput]
      have hchain : ToCFGChainDerives M presentation r [A] q topWord := by
        simpa [Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons htopDerive
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord topWord) := by
        simpa [Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p) (r := r) (s := q) (q := q)
            (push := [A])
            (chainWord := topWord)
            (emptyWord := (Word.Empty : Word input))
            htransitionSingle hchain
            (toCFG_emptyRefl_derives
              (M := M) (presentation := presentation) (q := q))
      exact ⟨topWord, hsourceConsumed, hbody⟩

/-!
The at-most-two wrapper keeps the small-computation interface uniform. It
dispatches to the zero-, one-, or two-step theorem and hides the arithmetic case
split from downstream conversion lemmas.
-/

theorem toCFG_emptyDerives_of_computesIn_atMostTwo_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  cases n with
  | zero =>
      exact toCFG_emptyDerives_of_computesIn_zero_emptyStack
        (M := M) (presentation := presentation) hcomp
  | succ n =>
      cases n with
      | zero =>
          exact toCFG_emptyDerives_of_computesIn_one_emptyStack
            (M := M) (presentation := presentation) hcomp
      | succ n =>
          cases n with
          | zero =>
              exact toCFG_emptyDerives_of_computesIn_two_emptyStack
                (M := M) (presentation := presentation) hnorm hcomp
          | succ n =>
              omega

/-!
The summary-computation predicates are custom induction principles for the
conversion proof. Instead of inducting over arbitrary PDA computations, they
classify runs by the stack effect that the matching CFG nonterminal is meant to
summarize.
-/

/-!
The summary predicates below are a more scalable replacement for the explicit
zero/one/two-step lemmas. They record just the stack effect that matters to the
CFG construction: empty-stack paths and paths that remove a specified stack word.
-/

inductive EmptyStackComputesIn (M : PDA input stack state) :
    Nat -> state -> Word input -> state -> Word input -> Prop where
  | zero (q : state) (unread : Word input) :
      EmptyStackComputesIn M 0 q unread q unread
  | read {n : Nat} {p r q : state} {a : input}
      {midInput targetInput : Word input} :
      M.transition p (some a) [] r [] ->
        EmptyStackComputesIn M n r midInput q targetInput ->
          EmptyStackComputesIn M (n + 1) p (a :: midInput) q targetInput
  | epsilon {n : Nat} {p r q : state}
      {midInput targetInput : Word input} :
      M.transition p none [] r [] ->
        EmptyStackComputesIn M n r midInput q targetInput ->
          EmptyStackComputesIn M (n + 1) p midInput q targetInput

theorem emptyStackComputesIn_computesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackComputesIn M n p sourceInput q targetInput) :
    ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } := by
  induction h with
  | zero q unread =>
      exact ComputesIn.zero _
  | read htransition htail ih =>
      rename_i p0 r0 q0 a0 midInput0 targetInput0
      have hstep : Step M
          { state := p0, unread := a0 :: midInput0, stack := [] }
          { state := r0, unread := midInput0, stack := [] } := by
        simpa [Word.Concat] using
          Step.read (M := M) (unread := midInput0)
            (restStack := ([] : Word stack)) htransition
      exact ComputesIn.succ hstep ih
  | epsilon htransition htail ih =>
      rename_i p0 r0 q0 midInput0 targetInput0
      have hstep : Step M
          { state := p0, unread := midInput0, stack := [] }
          { state := r0, unread := midInput0, stack := [] } := by
        simpa [Word.Concat] using
          Step.epsilon (M := M) (unread := midInput0)
            (restStack := ([] : Word stack)) htransition
      exact ComputesIn.succ hstep ih

theorem emptyStackComputesIn_computes
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackComputesIn M n p sourceInput q targetInput) :
    Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  computesIn_computes (emptyStackComputesIn_computesIn h)

theorem toCFG_emptyDerives_of_emptyStackComputesIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackComputesIn M n p sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  induction h with
  | zero q unread =>
      refine ⟨Word.Empty, ?_, ?_⟩
      · simp [Word.Concat, Word.Empty]
      · simpa [SententialForm.terminalWord, Word.Empty] using
          toCFG_emptyRefl_derives
            (M := M) (presentation := presentation) (q := q)
  | read htransition htail ih =>
      rename_i p0 r0 q0 a0 midInput0 targetInput0
      rcases ih with ⟨tailWord, htailInput, htailDerive⟩
      refine ⟨Word.Concat (Word.Symbol a0) tailWord, ?_, ?_⟩
      · rw [htailInput]
        simp [Word.Concat, Word.Symbol]
      · simpa [Word.Concat, Word.Symbol, Word.Empty, List.append_assoc] using
          toCFG_emptyRead_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p0) (r := r0) (s := r0) (q := q0)
            (a := a0) (push := ([] : Word stack))
            (chainWord := (Word.Empty : Word input))
            (emptyWord := tailWord)
            htransition
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) r0)
            htailDerive
  | epsilon htransition htail ih =>
      rename_i p0 r0 q0 midInput0 targetInput0
      rcases ih with ⟨tailWord, htailInput, htailDerive⟩
      refine ⟨tailWord, ?_, ?_⟩
      · exact htailInput
      · simpa [Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p0) (r := r0) (s := r0) (q := q0)
            (push := ([] : Word stack))
            (chainWord := (Word.Empty : Word input))
            (emptyWord := tailWord)
            htransition
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) r0)
            htailDerive

theorem toCFG_generates_of_emptyStackAcceptsIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptyStackComputesIn M n M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_emptyStackComputesIn
      (M := M) (presentation := presentation) hcomp with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

/-!
Stack summaries generalize the empty-stack predicate. They describe the input
consumed while removing an entire pushed stack word, and the combined
stack-then-empty predicate links that removal to the remaining computation to an
accepting empty stack.
-/

inductive StackSummaryComputesIn (M : PDA input stack state) :
    Nat -> state -> Word stack -> Word input -> state -> Word input -> Prop where
  | nil (q : state) (unread : Word input) :
      StackSummaryComputesIn M 0 q [] unread q unread
  | cons {m n : Nat} {p r q : state} {A : stack}
      {rest : Word stack} {sourceInput midInput targetInput : Word input} :
      StackSummaryComputesIn M m p [A] sourceInput r midInput ->
        StackSummaryComputesIn M n r rest midInput q targetInput ->
          StackSummaryComputesIn M (m + n) p (A :: rest)
            sourceInput q targetInput
  | popRead {n : Nat} {p r q : state} {A : stack} {a : input}
      {push : Word stack} {midInput targetInput : Word input} :
      M.transition p (some a) [A] r push ->
        StackSummaryComputesIn M n r push midInput q targetInput ->
          StackSummaryComputesIn M (n + 1) p [A]
            (a :: midInput) q targetInput
  | popEpsilon {n : Nat} {p r q : state} {A : stack}
      {push : Word stack} {midInput targetInput : Word input} :
      M.transition p none [A] r push ->
        StackSummaryComputesIn M n r push midInput q targetInput ->
          StackSummaryComputesIn M (n + 1) p [A]
            midInput q targetInput
  | emptyBeforeTopRead {m n : Nat} {p r s q : state}
      {A : stack} {a : input} {push : Word stack}
      {midInput topInput targetInput : Word input} :
      M.transition p (some a) [] r push ->
        StackSummaryComputesIn M m r push midInput s topInput ->
          StackSummaryComputesIn M n s [A] topInput q targetInput ->
            StackSummaryComputesIn M (m + n + 1) p [A]
              (a :: midInput) q targetInput
  | emptyBeforeTopEpsilon {m n : Nat} {p r s q : state}
      {A : stack} {push : Word stack}
      {midInput topInput targetInput : Word input} :
      M.transition p none [] r push ->
        StackSummaryComputesIn M m r push midInput s topInput ->
          StackSummaryComputesIn M n s [A] topInput q targetInput ->
            StackSummaryComputesIn M (m + n + 1) p [A]
              midInput q targetInput

inductive EmptySummaryComputesIn (M : PDA input stack state) :
    Nat -> state -> Word input -> state -> Word input -> Prop where
  | zero (q : state) (unread : Word input) :
      EmptySummaryComputesIn M 0 q unread q unread
  | read {m n : Nat} {p r s q : state} {a : input}
      {push : Word stack}
      {midInput emptyInput targetInput : Word input} :
      M.transition p (some a) [] r push ->
        StackSummaryComputesIn M m r push midInput s emptyInput ->
          EmptySummaryComputesIn M n s emptyInput q targetInput ->
            EmptySummaryComputesIn M (m + n + 1) p
              (a :: midInput) q targetInput
  | epsilon {m n : Nat} {p r s q : state}
      {push : Word stack}
      {midInput emptyInput targetInput : Word input} :
      M.transition p none [] r push ->
        StackSummaryComputesIn M m r push midInput s emptyInput ->
          EmptySummaryComputesIn M n s emptyInput q targetInput ->
            EmptySummaryComputesIn M (m + n + 1) p
              midInput q targetInput

def StackSummaryComputes (M : PDA input stack state)
    (p : state) (stackWord : Word stack) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  exists n, StackSummaryComputesIn M n p stackWord sourceInput q targetInput

def EmptySummaryComputes (M : PDA input stack state)
    (p : state) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  exists n, EmptySummaryComputesIn M n p sourceInput q targetInput

def StackThenEmptySummaryComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (stackWord : Word stack)
    (sourceInput : Word input) (q : state)
    (targetInput : Word input) : Prop :=
  exists stackSteps : Nat, exists emptySteps : Nat,
    exists middleState : state, exists middleInput : Word input,
      n = stackSteps + emptySteps ∧
        StackSummaryComputesIn M stackSteps p stackWord sourceInput
          middleState middleInput ∧
        EmptySummaryComputesIn M emptySteps middleState middleInput
          q targetInput

def StackThenEmptySummaryComputes (M : PDA input stack state)
    (p : state) (stackWord : Word stack) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  exists n, StackThenEmptySummaryComputesIn M n p stackWord sourceInput
    q targetInput

/-!
Soundness of the summary predicates says that their inductive structure really
does describe PDA computations. The proofs thread an arbitrary stack tail through
the path, because summaries are meant to compose inside larger stack contexts.
-/

theorem stackSummaryComputesIn_computesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput) :
    forall tail : Word stack,
      ComputesIn M n
        { state := p, unread := sourceInput,
          stack := Word.Concat stackWord tail }
        { state := q, unread := targetInput, stack := tail } := by
  induction h with
  | nil q unread =>
      intro tail
      simpa [Word.Concat, Word.Empty] using
        ComputesIn.zero
          ({ state := q, unread := unread, stack := tail } :
            Configuration input stack state)
  | cons htop hrest ihtop ihrest =>
      rename_i m n p r q A rest sourceInput midInput targetInput
      intro tail
      have hfirst := ihtop (Word.Concat rest tail)
      have htail := ihrest tail
      simpa [Word.Concat, List.append_assoc] using
        computesIn_trans hfirst htail
  | popRead htransition htail ih =>
      rename_i n p r q A a push midInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := a :: midInput, stack := A :: tail }
          { state := r, unread := midInput,
            stack := Word.Concat push tail } := by
        simpa [Word.Concat] using
          Step.read (M := M) (unread := midInput)
            (restStack := tail) htransition
      simpa [Word.Concat] using
        ComputesIn.succ hstep (ih tail)
  | popEpsilon htransition htail ih =>
      rename_i n p r q A push midInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := midInput, stack := A :: tail }
          { state := r, unread := midInput,
            stack := Word.Concat push tail } := by
        simpa [Word.Concat] using
          Step.epsilon (M := M) (unread := midInput)
            (restStack := tail) htransition
      simpa [Word.Concat] using
        ComputesIn.succ hstep (ih tail)
  | emptyBeforeTopRead htransition hpush htop ihpush ihtop =>
      rename_i m n p r s q A a push midInput topInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := a :: midInput, stack := A :: tail }
          { state := r, unread := midInput,
            stack := Word.Concat push (A :: tail) } := by
        simpa [Word.Concat] using
          Step.read (M := M) (unread := midInput)
            (restStack := A :: tail) htransition
      have hpushComp := ihpush (A :: tail)
      have htopComp := ihtop tail
      have hrest := computesIn_trans hpushComp htopComp
      simpa [Word.Concat, List.append_assoc] using
        ComputesIn.succ hstep hrest
  | emptyBeforeTopEpsilon htransition hpush htop ihpush ihtop =>
      rename_i m n p r s q A push midInput topInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := midInput, stack := A :: tail }
          { state := r, unread := midInput,
            stack := Word.Concat push (A :: tail) } := by
        simpa [Word.Concat] using
          Step.epsilon (M := M) (unread := midInput)
            (restStack := A :: tail) htransition
      have hpushComp := ihpush (A :: tail)
      have htopComp := ihtop tail
      have hrest := computesIn_trans hpushComp htopComp
      simpa [Word.Concat, List.append_assoc] using
        ComputesIn.succ hstep hrest

theorem stackSummaryComputes_computes
    {M : PDA input stack state}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputes M p stackWord sourceInput q targetInput) :
    forall tail : Word stack,
      Computes M
        { state := p, unread := sourceInput,
          stack := Word.Concat stackWord tail }
        { state := q, unread := targetInput, stack := tail } := by
  rcases h with ⟨n, hn⟩
  intro tail
  exact computesIn_computes (stackSummaryComputesIn_computesIn hn tail)

theorem stackSummaryComputesIn_computes
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput) :
    forall tail : Word stack,
      Computes M
        { state := p, unread := sourceInput,
          stack := Word.Concat stackWord tail }
        { state := q, unread := targetInput, stack := tail } := by
  intro tail
  exact computesIn_computes (stackSummaryComputesIn_computesIn h tail)

/-!
Empty summaries are also interpreted in an arbitrary tail context. This tail
version is the workhorse for composing an empty-stack summary after another
summary has exposed the rest of the stack.
-/

theorem emptySummaryComputesIn_computesIn_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    forall tail : Word stack,
      ComputesIn M n
        { state := p, unread := sourceInput, stack := tail }
        { state := q, unread := targetInput, stack := tail } := by
  induction h with
  | zero q unread =>
      intro tail
      exact ComputesIn.zero _
  | read htransition hpush hempty ihempty =>
      rename_i m n p r s q a push midInput emptyInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := a :: midInput, stack := tail }
          { state := r, unread := midInput,
            stack := Word.Concat push tail } := by
        simpa [Word.Concat] using
          Step.read (M := M) (unread := midInput)
            (restStack := tail) htransition
      have hpushComp := stackSummaryComputesIn_computesIn hpush tail
      have hemptyComp := ihempty tail
      have hrest := computesIn_trans hpushComp hemptyComp
      simpa [Word.Concat, List.append_assoc] using
        ComputesIn.succ hstep hrest
  | epsilon htransition hpush hempty ihempty =>
      rename_i m n p r s q push midInput emptyInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := midInput, stack := tail }
          { state := r, unread := midInput,
            stack := Word.Concat push tail } := by
        simpa [Word.Concat] using
          Step.epsilon (M := M) (unread := midInput)
            (restStack := tail) htransition
      have hpushComp := stackSummaryComputesIn_computesIn hpush tail
      have hemptyComp := ihempty tail
      have hrest := computesIn_trans hpushComp hemptyComp
      simpa [Word.Concat, List.append_assoc] using
        ComputesIn.succ hstep hrest

theorem emptySummaryComputesIn_computesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  emptySummaryComputesIn_computesIn_tail h ([] : Word stack)

theorem emptySummaryComputesIn_computes
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  computesIn_computes (emptySummaryComputesIn_computesIn h)

theorem emptySummaryComputesIn_computes_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput)
    (tail : Word stack) :
    Computes M
      { state := p, unread := sourceInput, stack := tail }
      { state := q, unread := targetInput, stack := tail } :=
  computesIn_computes (emptySummaryComputesIn_computesIn_tail h tail)

theorem emptySummaryComputes_computes
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputes M p sourceInput q targetInput) :
    Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } := by
  rcases h with ⟨n, hn⟩
  exact emptySummaryComputesIn_computes hn

theorem emptySummaryComputes_computes_tail
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputes M p sourceInput q targetInput)
    (tail : Word stack) :
    Computes M
      { state := p, unread := sourceInput, stack := tail }
      { state := q, unread := targetInput, stack := tail } := by
  rcases h with ⟨n, hn⟩
  exact emptySummaryComputesIn_computes_tail hn tail

theorem stackSummaryComputes_of_stackSummaryComputesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput) :
    StackSummaryComputes M p stackWord sourceInput q targetInput :=
  ⟨n, h⟩

theorem emptySummaryComputes_of_emptySummaryComputesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    EmptySummaryComputes M p sourceInput q targetInput :=
  ⟨n, h⟩

/-!
The combined stack-then-empty summary represents the common shape of a
transition that first discharges a pushed stack word and then continues with an
empty-stack computation. These lemmas connect the combined predicate back to
ordinary PDA computations with a tail stack.
-/

theorem stackThenEmptySummaryComputesIn_computesIn_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput) :
    forall tail : Word stack,
      ComputesIn M n
        { state := p, unread := sourceInput,
          stack := Word.Concat stackWord tail }
        { state := q, unread := targetInput, stack := tail } := by
  rcases h with
    ⟨stackSteps, emptySteps, middleState, middleInput,
      hlen, hstack, hempty⟩
  intro tail
  have hstackComp := stackSummaryComputesIn_computesIn hstack tail
  have hemptyComp := emptySummaryComputesIn_computesIn_tail hempty tail
  have hcomp := computesIn_trans hstackComp hemptyComp
  simpa [hlen] using hcomp

theorem stackThenEmptySummaryComputesIn_computesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput) :
    ComputesIn M n
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] } := by
  simpa [Word.Concat, Word.Empty] using
    stackThenEmptySummaryComputesIn_computesIn_tail h ([] : Word stack)

theorem stackThenEmptySummaryComputesIn_computes_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput)
    (tail : Word stack) :
    Computes M
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } :=
  computesIn_computes
    (stackThenEmptySummaryComputesIn_computesIn_tail h tail)

theorem stackThenEmptySummaryComputes_computes_tail
    {M : PDA input stack state}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputes M p stackWord sourceInput
      q targetInput)
    (tail : Word stack) :
    Computes M
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } := by
  rcases h with ⟨n, hn⟩
  exact stackThenEmptySummaryComputesIn_computes_tail hn tail

theorem stackThenEmptySummaryComputesIn_of_stack_and_empty
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hstack : StackSummaryComputesIn M m p stackWord sourceInput
      r midInput)
    (hempty : EmptySummaryComputesIn M n r midInput q targetInput) :
    StackThenEmptySummaryComputesIn M (m + n) p stackWord sourceInput
      q targetInput :=
  ⟨m, n, r, midInput, rfl, hstack, hempty⟩

theorem stackThenEmptySummaryComputesIn_of_stack
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (hstack : StackSummaryComputesIn M n p stackWord sourceInput
      q targetInput) :
    StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput := by
  refine ⟨n, 0, q, targetInput, ?_, hstack, ?_⟩
  · simp
  · exact EmptySummaryComputesIn.zero q targetInput

theorem stackThenEmptySummaryComputesIn_of_empty
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hempty : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    StackThenEmptySummaryComputesIn M n p ([] : Word stack) sourceInput
      q targetInput := by
  refine ⟨0, n, p, sourceInput, ?_, ?_, hempty⟩
  · simp
  · exact StackSummaryComputesIn.nil p sourceInput

theorem stackThenEmptySummaryComputes_of_stack_and_empty
    {M : PDA input stack state}
    {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hstack : StackSummaryComputes M p stackWord sourceInput r midInput)
    (hempty : EmptySummaryComputes M r midInput q targetInput) :
    StackThenEmptySummaryComputes M p stackWord sourceInput
      q targetInput := by
  rcases hstack with ⟨m, hm⟩
  rcases hempty with ⟨n, hn⟩
  exact ⟨m + n, stackThenEmptySummaryComputesIn_of_stack_and_empty hm hn⟩

theorem stackThenEmptySummaryComputes_of_stack
    {M : PDA input stack state}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (hstack : StackSummaryComputes M p stackWord sourceInput
      q targetInput) :
    StackThenEmptySummaryComputes M p stackWord sourceInput
      q targetInput := by
  rcases hstack with ⟨n, hn⟩
  exact ⟨n, stackThenEmptySummaryComputesIn_of_stack hn⟩

theorem stackThenEmptySummaryComputes_of_empty
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hempty : EmptySummaryComputes M p sourceInput q targetInput) :
    StackThenEmptySummaryComputes M p ([] : Word stack) sourceInput
      q targetInput := by
  rcases hempty with ⟨n, hn⟩
  exact ⟨n, stackThenEmptySummaryComputesIn_of_empty hn⟩

/-!
Transitivity is what makes summaries usable as proof objects rather than just
descriptions of individual steps. Once a computation has been split into
summary-sized pieces, these lemmas put the pieces back together.
-/

theorem emptySummaryComputesIn_trans
    {M : PDA input stack state}
    {m n : Nat} {p r q : state}
    {sourceInput midInput targetInput : Word input}
    (hleft : EmptySummaryComputesIn M m p sourceInput r midInput)
    (hright : EmptySummaryComputesIn M n r midInput q targetInput) :
    EmptySummaryComputesIn M (m + n) p sourceInput q targetInput := by
  induction hleft generalizing q targetInput n with
  | zero r midInput =>
      simpa using hright
  | read htransition hpush hempty ih =>
      rename_i m0 n0 p0 r0 s0 r1 a push mid0 empty0 mid1
      have htail := ih hright
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EmptySummaryComputesIn.read htransition hpush htail
  | epsilon htransition hpush hempty ih =>
      rename_i m0 n0 p0 r0 s0 r1 push mid0 empty0 mid1
      have htail := ih hright
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EmptySummaryComputesIn.epsilon htransition hpush htail

theorem emptySummaryComputes_trans
    {M : PDA input stack state}
    {p r q : state}
    {sourceInput midInput targetInput : Word input}
    (hleft : EmptySummaryComputes M p sourceInput r midInput)
    (hright : EmptySummaryComputes M r midInput q targetInput) :
    EmptySummaryComputes M p sourceInput q targetInput := by
  rcases hleft with ⟨m, hm⟩
  rcases hright with ⟨n, hn⟩
  exact ⟨m + n, emptySummaryComputesIn_trans hm hn⟩

theorem stackSummaryComputesIn_of_emptySummary_prefix_single
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {A : stack}
    {sourceInput midInput targetInput : Word input}
    (hempty : EmptySummaryComputesIn M m p sourceInput r midInput)
    (htop : StackSummaryComputesIn M n r [A] midInput q targetInput) :
    StackSummaryComputesIn M (m + n) p [A] sourceInput q targetInput := by
  induction hempty generalizing q targetInput n A with
  | zero r midInput =>
      simpa using htop
  | read htransition hpush hempty ih =>
      rename_i m0 n0 p0 r0 s0 r1 a push mid0 empty0 mid1
      have htail := ih htop
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StackSummaryComputesIn.emptyBeforeTopRead htransition hpush htail
  | epsilon htransition hpush hempty ih =>
      rename_i m0 n0 p0 r0 s0 r1 push mid0 empty0 mid1
      have htail := ih htop
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StackSummaryComputesIn.emptyBeforeTopEpsilon htransition hpush htail

theorem stackSummaryComputes_of_emptySummary_prefix_single
    {M : PDA input stack state}
    {p r q : state} {A : stack}
    {sourceInput midInput targetInput : Word input}
    (hempty : EmptySummaryComputes M p sourceInput r midInput)
    (htop : StackSummaryComputes M r [A] midInput q targetInput) :
    StackSummaryComputes M p [A] sourceInput q targetInput := by
  rcases hempty with ⟨m, hm⟩
  rcases htop with ⟨n, hn⟩
  exact ⟨m + n, stackSummaryComputesIn_of_emptySummary_prefix_single hm hn⟩

theorem stackSummaryComputesIn_cons_prefix
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {A : stack}
    {rest : Word stack}
    {sourceInput midInput targetInput : Word input}
    (htop : StackSummaryComputesIn M m p [A] sourceInput r midInput)
    (hrest : StackSummaryComputesIn M n r rest midInput q targetInput) :
    StackSummaryComputesIn M (m + n) p (A :: rest)
      sourceInput q targetInput :=
  StackSummaryComputesIn.cons htop hrest

theorem stackSummaryComputes_cons_prefix
    {M : PDA input stack state}
    {p r q : state} {A : stack} {rest : Word stack}
    {sourceInput midInput targetInput : Word input}
    (htop : StackSummaryComputes M p [A] sourceInput r midInput)
    (hrest : StackSummaryComputes M r rest midInput q targetInput) :
    StackSummaryComputes M p (A :: rest) sourceInput q targetInput := by
  rcases htop with ⟨m, hm⟩
  rcases hrest with ⟨n, hn⟩
  exact ⟨m + n, stackSummaryComputesIn_cons_prefix hm hn⟩

/-!
Splitting a stack summary is the main structural lemma for the induction: a run
that removes an appended stack word can be decomposed into the part that removes
the prefix and the part that removes the suffix. This mirrors how the generated
CFG chain is split into adjacent nonterminal summaries.
-/

/-!
Splitting a stack summary at a concatenation boundary is the key algebraic fact
for pushed stack words. The equality-indexed version performs the induction; the
plain append version below specializes it to an explicit prefix and suffix.
-/

theorem stackSummaryComputesIn_split_append_of_eq
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord left right : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput)
    (heq : stackWord = Word.Concat left right) :
    exists leftSteps : Nat, exists rightSteps : Nat,
      exists middleState : state, exists middleInput : Word input,
        n = leftSteps + rightSteps ∧
          StackSummaryComputesIn M leftSteps p left sourceInput
            middleState middleInput ∧
          StackSummaryComputesIn M rightSteps middleState right middleInput
            q targetInput := by
  induction h generalizing left right with
  | nil q unread =>
      have hleft : left = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlen := congrArg List.length heq
        simp [Word.Concat] at hlen
        omega
      have hright : right = [] := by
        simpa [Word.Concat, hleft] using heq.symm
      refine ⟨0, 0, q, unread, ?_, ?_, ?_⟩
      · simp
      · simpa [hleft] using StackSummaryComputesIn.nil (M := M) q unread
      · simpa [hright] using StackSummaryComputesIn.nil (M := M) q unread
  | cons htop hrest ihtop ihrest =>
      rename_i topSteps restSteps p r q A rest sourceInput midInput targetInput
      cases left with
      | nil =>
          have hright : right = A :: rest := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, topSteps + restSteps, p, sourceInput,
            ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p sourceInput
          · simpa [hright] using StackSummaryComputesIn.cons htop hrest
      | cons B leftTail =>
          have heqCons : A :: rest = B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hrestEq : rest = Word.Concat leftTail right :=
            (List.cons.inj heqCons).2
          rcases ihrest hrestEq with
            ⟨leftSteps, rightSteps, middleState, middleInput,
              hlen, hleft, hright⟩
          refine ⟨topSteps + leftSteps, rightSteps,
            middleState, middleInput, ?_, ?_, hright⟩
          · simp [hlen, Nat.add_comm, Nat.add_left_comm]
          · simpa [hA] using StackSummaryComputesIn.cons htop hleft
  | popRead htransition hpush ih =>
      rename_i tailSteps p r q A a push midInput targetInput
      cases left with
      | nil =>
          have hright : right = [A] := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, tailSteps + 1, p, (a :: midInput), ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p (a :: midInput)
          · simpa [hright] using
              StackSummaryComputesIn.popRead htransition hpush
      | cons B leftTail =>
          have heqCons : A :: ([] : Word stack) =
              B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hsuffix : Word.Concat leftTail right = [] :=
            (List.cons.inj heqCons).2.symm
          have hleftTail : leftTail = [] := by
            cases leftTail with
            | nil => rfl
            | cons C tail =>
                have hbad := hsuffix
                simp [Word.Concat] at hbad
          have hright : right = [] := by
            simpa [Word.Concat, hleftTail] using hsuffix
          refine ⟨tailSteps + 1, 0, q, targetInput, ?_, ?_, ?_⟩
          · simp
          · simpa [hA, hleftTail] using
              StackSummaryComputesIn.popRead htransition hpush
          · simpa [hright] using
              StackSummaryComputesIn.nil (M := M) q targetInput
  | popEpsilon htransition hpush ih =>
      rename_i tailSteps p r q A push midInput targetInput
      cases left with
      | nil =>
          have hright : right = [A] := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, tailSteps + 1, p, midInput, ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p midInput
          · simpa [hright] using
              StackSummaryComputesIn.popEpsilon htransition hpush
      | cons B leftTail =>
          have heqCons : A :: ([] : Word stack) =
              B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hsuffix : Word.Concat leftTail right = [] :=
            (List.cons.inj heqCons).2.symm
          have hleftTail : leftTail = [] := by
            cases leftTail with
            | nil => rfl
            | cons C tail =>
                have hbad := hsuffix
                simp [Word.Concat] at hbad
          have hright : right = [] := by
            simpa [Word.Concat, hleftTail] using hsuffix
          refine ⟨tailSteps + 1, 0, q, targetInput, ?_, ?_, ?_⟩
          · simp
          · simpa [hA, hleftTail] using
              StackSummaryComputesIn.popEpsilon htransition hpush
          · simpa [hright] using
              StackSummaryComputesIn.nil (M := M) q targetInput
  | emptyBeforeTopRead htransition hpush htop ihpush ihtop =>
      rename_i pushSteps topSteps p r s q A a push midInput topInput targetInput
      cases left with
      | nil =>
          have hright : right = [A] := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, pushSteps + topSteps + 1, p, (a :: midInput),
            ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p (a :: midInput)
          · simpa [hright] using
              StackSummaryComputesIn.emptyBeforeTopRead
                htransition hpush htop
      | cons B leftTail =>
          have heqCons : A :: ([] : Word stack) =
              B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hsuffix : Word.Concat leftTail right = [] :=
            (List.cons.inj heqCons).2.symm
          have hleftTail : leftTail = [] := by
            cases leftTail with
            | nil => rfl
            | cons C tail =>
                have hbad := hsuffix
                simp [Word.Concat] at hbad
          have hright : right = [] := by
            simpa [Word.Concat, hleftTail] using hsuffix
          refine ⟨pushSteps + topSteps + 1, 0, q, targetInput,
            ?_, ?_, ?_⟩
          · simp
          · simpa [hA, hleftTail] using
              StackSummaryComputesIn.emptyBeforeTopRead
                htransition hpush htop
          · simpa [hright] using
              StackSummaryComputesIn.nil (M := M) q targetInput
  | emptyBeforeTopEpsilon htransition hpush htop ihpush ihtop =>
      rename_i pushSteps topSteps p r s q A push midInput topInput targetInput
      cases left with
      | nil =>
          have hright : right = [A] := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, pushSteps + topSteps + 1, p, midInput, ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p midInput
          · simpa [hright] using
              StackSummaryComputesIn.emptyBeforeTopEpsilon
                htransition hpush htop
      | cons B leftTail =>
          have heqCons : A :: ([] : Word stack) =
              B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hsuffix : Word.Concat leftTail right = [] :=
            (List.cons.inj heqCons).2.symm
          have hleftTail : leftTail = [] := by
            cases leftTail with
            | nil => rfl
            | cons C tail =>
                have hbad := hsuffix
                simp [Word.Concat] at hbad
          have hright : right = [] := by
            simpa [Word.Concat, hleftTail] using hsuffix
          refine ⟨pushSteps + topSteps + 1, 0, q, targetInput,
            ?_, ?_, ?_⟩
          · simp
          · simpa [hA, hleftTail] using
              StackSummaryComputesIn.emptyBeforeTopEpsilon
                htransition hpush htop
          · simpa [hright] using
              StackSummaryComputesIn.nil (M := M) q targetInput

/-!
The append-facing split theorem is the version used by callers. It removes the
explicit equality parameter from the induction lemma and exposes the midpoint
input where the prefix summary ends and the suffix summary begins.
-/

theorem stackSummaryComputesIn_split_append
    {M : PDA input stack state}
    {n : Nat} {p q : state} {left right : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p (Word.Concat left right)
      sourceInput q targetInput) :
    exists leftSteps : Nat, exists rightSteps : Nat,
      exists middleState : state, exists middleInput : Word input,
        n = leftSteps + rightSteps ∧
          StackSummaryComputesIn M leftSteps p left sourceInput
            middleState middleInput ∧
          StackSummaryComputesIn M rightSteps middleState right middleInput
            q targetInput :=
  stackSummaryComputesIn_split_append_of_eq h rfl

theorem stackSummaryComputes_split_append
    {M : PDA input stack state}
    {p q : state} {left right : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputes M p (Word.Concat left right)
      sourceInput q targetInput) :
    exists middleState : state, exists middleInput : Word input,
      StackSummaryComputes M p left sourceInput middleState middleInput ∧
        StackSummaryComputes M middleState right middleInput
          q targetInput := by
  rcases h with ⟨n, hn⟩
  rcases stackSummaryComputesIn_split_append hn with
    ⟨leftSteps, rightSteps, middleState, middleInput,
      _hlen, hleft, hright⟩
  exact ⟨middleState, middleInput, ⟨leftSteps, hleft⟩,
    ⟨rightSteps, hright⟩⟩

/-!
Stack-then-empty summaries can also be split at a stack prefix. The result keeps
the empty-stack continuation attached to the suffix part, so prefix processing
can be peeled off without losing the final empty-stack goal.
-/

theorem stackThenEmptySummaryComputesIn_split_stack_prefix
    {M : PDA input stack state}
    {n : Nat} {p q : state} {pref suff : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p
      (Word.Concat pref suff) sourceInput q targetInput) :
    exists prefixSteps : Nat, exists suffixSteps : Nat,
      exists middleState : state, exists middleInput : Word input,
        n = prefixSteps + suffixSteps ∧
          StackSummaryComputesIn M prefixSteps p pref sourceInput
            middleState middleInput ∧
          StackThenEmptySummaryComputesIn M suffixSteps middleState suff
            middleInput q targetInput := by
  rcases h with
    ⟨stackSteps, emptySteps, emptyState, emptyInput,
      hlen, hstack, hempty⟩
  rcases stackSummaryComputesIn_split_append hstack with
    ⟨prefixSteps, suffixStackSteps, middleState, middleInput,
      hstackLen, hprefix, hsuffix⟩
  refine ⟨prefixSteps, suffixStackSteps + emptySteps, middleState,
    middleInput, ?_, hprefix, ?_⟩
  · simp [hlen, hstackLen, Nat.add_comm, Nat.add_left_comm]
  · exact stackThenEmptySummaryComputesIn_of_stack_and_empty hsuffix hempty

theorem stackThenEmptySummaryComputes_split_stack_prefix
    {M : PDA input stack state}
    {p q : state} {pref suff : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputes M p
      (Word.Concat pref suff) sourceInput q targetInput) :
    exists middleState : state, exists middleInput : Word input,
      StackSummaryComputes M p pref sourceInput middleState middleInput ∧
        StackThenEmptySummaryComputes M middleState suff
          middleInput q targetInput := by
  rcases h with ⟨n, hn⟩
  rcases stackThenEmptySummaryComputesIn_split_stack_prefix hn with
    ⟨prefixSteps, suffixSteps, middleState, middleInput,
      _hlen, hprefix, hsuffix⟩
  exact ⟨middleState, middleInput, ⟨prefixSteps, hprefix⟩,
    ⟨suffixSteps, hsuffix⟩⟩

/-!
After a split, a stack-then-empty summary can be extended by one leading stack
symbol. This is the composition step used when a PDA transition pushes several
symbols and the CFG chain has to account for them one at a time.
-/

theorem stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {A : stack} {rest : Word stack}
    {sourceInput midInput targetInput : Word input}
    (htop : StackSummaryComputesIn M m p [A] sourceInput r midInput)
    (htail : StackThenEmptySummaryComputesIn M n r rest midInput
      q targetInput) :
    StackThenEmptySummaryComputesIn M (m + n) p (A :: rest)
      sourceInput q targetInput := by
  rcases htail with
    ⟨restSteps, emptySteps, emptyState, emptyInput,
      hlen, hrest, hempty⟩
  refine ⟨m + restSteps, emptySteps, emptyState, emptyInput,
    ?_, ?_, hempty⟩
  · simp [hlen, Nat.add_comm, Nat.add_left_comm]
  · exact StackSummaryComputesIn.cons htop hrest

theorem stackThenEmptySummaryComputes_cons_of_stack_and_stackThenEmpty
    {M : PDA input stack state}
    {p r q : state} {A : stack} {rest : Word stack}
    {sourceInput midInput targetInput : Word input}
    (htop : StackSummaryComputes M p [A] sourceInput r midInput)
    (htail : StackThenEmptySummaryComputes M r rest midInput
      q targetInput) :
    StackThenEmptySummaryComputes M p (A :: rest)
      sourceInput q targetInput := by
  rcases htop with ⟨m, hm⟩
  rcases htail with ⟨n, hn⟩
  exact ⟨m + n,
    stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
      hm hn⟩

/-!
Here the proof consumes the first concrete PDA step and reconstructs the matching
summary predicate. The top-pop normal form keeps the case analysis manageable:
the first step either pops one top symbol or preserves the top symbol while a
pushed prefix is handled first.
-/

/-!
The next reconstruction lemmas turn a real top-pop PDA step into a
stack-then-empty summary. They inspect whether the step consumed input, then
attach the summary for the pushed stack word to the summary for the remaining
empty-stack computation.
-/

theorem stackThenEmptySummaryComputesIn_of_step_of_stackThenEmpty_topPop
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    {mid : Configuration input stack state}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := stackWord } mid)
    (hrest : StackThenEmptySummaryComputesIn M n mid.state mid.stack
      mid.unread q targetInput) :
    StackThenEmptySummaryComputesIn M (n + 1) p stackWord
      sourceInput q targetInput := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', r, a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : stackWord = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hrest' :
        StackThenEmptySummaryComputesIn M n r
          (Word.Concat push restStack) unread q targetInput := by
      simpa [hd] using hrest
    rcases hnorm p' (some a) pop r push htransition with
      hpopNil | hpopSingle
    · have htransition' : M.transition p (some a) [] r push := by
        simpa [hp, hpopNil] using htransition
      have hstackRest : stackWord = restStack := by
        simpa [Word.Concat, hpopNil] using hstack
      cases restStack with
      | nil =>
          have hrestPush :
              StackThenEmptySummaryComputesIn M n r push unread
                q targetInput := by
            simpa [Word.Concat] using hrest'
          rcases hrestPush with
            ⟨pushSteps, emptySteps, emptyState, emptyInput,
              hrestLen, hpush, hemptyTail⟩
          have hempty :
              EmptySummaryComputesIn M (n + 1) p (a :: unread)
                q targetInput := by
            simpa [hrestLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using EmptySummaryComputesIn.read htransition' hpush hemptyTail
          have hsummary :=
            stackThenEmptySummaryComputesIn_of_empty hempty
          simpa [hsource, hstackRest] using hsummary
      | cons A tail =>
          rcases stackThenEmptySummaryComputesIn_split_stack_prefix
              (M := M) (pref := push) (suff := A :: tail)
              hrest' with
            ⟨pushSteps, suffixSteps, afterPush, afterPushInput,
              hrestLen, hpush, hsuffix⟩
          have hsuffix' :
              StackThenEmptySummaryComputesIn M suffixSteps afterPush
                (Word.Concat [A] tail) afterPushInput q targetInput := by
            simpa [Word.Concat] using hsuffix
          rcases stackThenEmptySummaryComputesIn_split_stack_prefix
              (M := M) (pref := [A]) (suff := tail)
              hsuffix' with
            ⟨topSteps, tailSteps, afterTop, afterTopInput,
              hsuffixLen, htop, htail⟩
          have htop' :
              StackSummaryComputesIn M (pushSteps + topSteps + 1)
                p [A] (a :: unread) afterTop afterTopInput :=
            StackSummaryComputesIn.emptyBeforeTopRead
              htransition' hpush htop
          have hsummary :=
            stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
              htop' htail
          simpa [hsource, hstackRest, hrestLen, hsuffixLen,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsummary
    · rcases hpopSingle with ⟨A, hpopSingle⟩
      have htransition' : M.transition p (some a) [A] r push := by
        simpa [hp, hpopSingle] using htransition
      have hstackRest : stackWord = A :: restStack := by
        simpa [Word.Concat, hpopSingle] using hstack
      rcases stackThenEmptySummaryComputesIn_split_stack_prefix
          (M := M) (pref := push) (suff := restStack)
          hrest' with
        ⟨pushSteps, restSteps, afterPush, afterPushInput,
          hrestLen, hpush, htail⟩
      have htop :
          StackSummaryComputesIn M (pushSteps + 1) p [A]
            (a :: unread) afterPush afterPushInput :=
        StackSummaryComputesIn.popRead htransition' hpush
      have hsummary :=
        stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
          htop htail
      simpa [hsource, hstackRest, hrestLen,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsummary
  · rcases heps with
      ⟨p', r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : stackWord = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hrest' :
        StackThenEmptySummaryComputesIn M n r
          (Word.Concat push restStack) unread q targetInput := by
      simpa [hd] using hrest
    rcases hnorm p' none pop r push htransition with
      hpopNil | hpopSingle
    · have htransition' : M.transition p none [] r push := by
        simpa [hp, hpopNil] using htransition
      have hstackRest : stackWord = restStack := by
        simpa [Word.Concat, hpopNil] using hstack
      cases restStack with
      | nil =>
          have hrestPush :
              StackThenEmptySummaryComputesIn M n r push unread
                q targetInput := by
            simpa [Word.Concat] using hrest'
          rcases hrestPush with
            ⟨pushSteps, emptySteps, emptyState, emptyInput,
              hrestLen, hpush, hemptyTail⟩
          have hempty :
              EmptySummaryComputesIn M (n + 1) p unread
                q targetInput := by
            simpa [hrestLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using EmptySummaryComputesIn.epsilon htransition' hpush hemptyTail
          have hsummary :=
            stackThenEmptySummaryComputesIn_of_empty hempty
          simpa [hsource, hstackRest] using hsummary
      | cons A tail =>
          rcases stackThenEmptySummaryComputesIn_split_stack_prefix
              (M := M) (pref := push) (suff := A :: tail)
              hrest' with
            ⟨pushSteps, suffixSteps, afterPush, afterPushInput,
              hrestLen, hpush, hsuffix⟩
          have hsuffix' :
              StackThenEmptySummaryComputesIn M suffixSteps afterPush
                (Word.Concat [A] tail) afterPushInput q targetInput := by
            simpa [Word.Concat] using hsuffix
          rcases stackThenEmptySummaryComputesIn_split_stack_prefix
              (M := M) (pref := [A]) (suff := tail)
              hsuffix' with
            ⟨topSteps, tailSteps, afterTop, afterTopInput,
              hsuffixLen, htop, htail⟩
          have htop' :
              StackSummaryComputesIn M (pushSteps + topSteps + 1)
                p [A] unread afterTop afterTopInput :=
            StackSummaryComputesIn.emptyBeforeTopEpsilon
              htransition' hpush htop
          have hsummary :=
            stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
              htop' htail
          simpa [hsource, hstackRest, hrestLen, hsuffixLen,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsummary
    · rcases hpopSingle with ⟨A, hpopSingle⟩
      have htransition' : M.transition p none [A] r push := by
        simpa [hp, hpopSingle] using htransition
      have hstackRest : stackWord = A :: restStack := by
        simpa [Word.Concat, hpopSingle] using hstack
      rcases stackThenEmptySummaryComputesIn_split_stack_prefix
          (M := M) (pref := push) (suff := restStack)
          hrest' with
        ⟨pushSteps, restSteps, afterPush, afterPushInput,
          hrestLen, hpush, htail⟩
      have htop :
          StackSummaryComputesIn M (pushSteps + 1) p [A]
            unread afterPush afterPushInput :=
        StackSummaryComputesIn.popEpsilon htransition' hpush
      have hsummary :=
        stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
          htop htail
      simpa [hsource, hstackRest, hrestLen,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsummary

/-!
This theorem is the general first-step reconstruction for top-pop computations.
It finds the first PDA step, turns that step into a stack-then-empty summary, and
uses the remaining computation as the continuation.
-/

theorem stackThenEmptySummaryComputesIn_of_computesIn_topPop
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] }) :
    StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput := by
  induction n generalizing p q stackWord sourceInput targetInput with
  | zero =>
      have hend := computesIn_zero_eq hcomp
      have hstate : p = q := by
        simpa using congrArg
          (fun c : Configuration input stack state => c.state) hend
      have hinput : sourceInput = targetInput := by
        simpa using congrArg
          (fun c : Configuration input stack state => c.unread) hend
      have hstack : stackWord = [] := by
        simpa using congrArg
          (fun c : Configuration input stack state => c.stack) hend
      have hempty :
          EmptySummaryComputesIn M 0 p sourceInput p sourceInput :=
        EmptySummaryComputesIn.zero p sourceInput
      have hsummary :=
        stackThenEmptySummaryComputesIn_of_empty hempty
      simpa [hstate, hinput, hstack] using hsummary
  | succ n ih =>
      rcases computesIn_succ_inv (M := M) (n := n) hcomp with
        ⟨mid, hstep, hrest⟩
      have htail :
          StackThenEmptySummaryComputesIn M n mid.state mid.stack
            mid.unread q targetInput :=
        ih (p := mid.state) (q := q) (stackWord := mid.stack)
          (sourceInput := mid.unread) (targetInput := targetInput) hrest
      exact stackThenEmptySummaryComputesIn_of_step_of_stackThenEmpty_topPop
        hnorm hstep htail

theorem stackThenEmptySummaryComputesIn_trans_empty
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hleft : StackThenEmptySummaryComputesIn M m p stackWord
      sourceInput r midInput)
    (hright : EmptySummaryComputesIn M n r midInput q targetInput) :
    StackThenEmptySummaryComputesIn M (m + n) p stackWord
      sourceInput q targetInput := by
  rcases hleft with
    ⟨stackSteps, emptySteps, middleState, middleInput,
      hlen, hstack, hempty⟩
  have hempty' := emptySummaryComputesIn_trans hempty hright
  refine ⟨stackSteps, emptySteps + n, middleState, middleInput,
    ?_, hstack, hempty'⟩
  simp [hlen, Nat.add_comm, Nat.add_left_comm]

theorem stackThenEmptySummaryComputes_trans_empty
    {M : PDA input stack state}
    {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hleft : StackThenEmptySummaryComputes M p stackWord
      sourceInput r midInput)
    (hright : EmptySummaryComputes M r midInput q targetInput) :
    StackThenEmptySummaryComputes M p stackWord
      sourceInput q targetInput := by
  rcases hleft with ⟨m, hm⟩
  rcases hright with ⟨n, hn⟩
  exact ⟨m + n, stackThenEmptySummaryComputesIn_trans_empty hm hn⟩

theorem emptySummaryComputesIn_of_stackThenEmptySummaryComputesIn_nil
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p ([] : Word stack)
      sourceInput q targetInput) :
    EmptySummaryComputesIn M n p sourceInput q targetInput := by
  rcases h with
    ⟨stackSteps, emptySteps, middleState, middleInput,
      hlen, hstack, hempty⟩
  cases hstack with
  | nil p0 unread0 =>
      simpa [hlen] using hempty

theorem emptySummaryComputes_of_stackThenEmptySummaryComputes_nil
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputes M p ([] : Word stack)
      sourceInput q targetInput) :
    EmptySummaryComputes M p sourceInput q targetInput := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, emptySummaryComputesIn_of_stackThenEmptySummaryComputesIn_nil hn⟩

/-!
When a transition starts from an empty stack and later returns to an empty stack,
the intermediate pushed stack can be hidden inside an empty-summary witness. The
read and epsilon variants below package that first-step pattern.
-/

theorem emptySummaryComputesIn_read_of_stackThenEmptySummary
    {M : PDA input stack state}
    {n : Nat} {p r q : state} {a : input}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hrest : StackThenEmptySummaryComputesIn M n r push midInput
      q targetInput) :
    EmptySummaryComputesIn M (n + 1) p (a :: midInput)
      q targetInput := by
  rcases hrest with
    ⟨stackSteps, emptySteps, middleState, emptyInput,
      hlen, hstack, hempty⟩
  simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    EmptySummaryComputesIn.read htransition hstack hempty

theorem emptySummaryComputesIn_epsilon_of_stackThenEmptySummary
    {M : PDA input stack state}
    {n : Nat} {p r q : state}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p none [] r push)
    (hrest : StackThenEmptySummaryComputesIn M n r push midInput
      q targetInput) :
    EmptySummaryComputesIn M (n + 1) p midInput q targetInput := by
  rcases hrest with
    ⟨stackSteps, emptySteps, middleState, emptyInput,
      hlen, hstack, hempty⟩
  simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    EmptySummaryComputesIn.epsilon htransition hstack hempty

/-!
The following lemmas connect ordinary bounded PDA computations back to the
summary predicates. They are the reverse-direction counterpart of the earlier
soundness lemmas that interpreted CFG summaries as real computations.
-/

theorem emptySummaryComputesIn_of_emptyStackComputesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackComputesIn M n p sourceInput q targetInput) :
    EmptySummaryComputesIn M n p sourceInput q targetInput := by
  induction h with
  | zero q unread =>
      exact EmptySummaryComputesIn.zero q unread
  | read htransition htail ih =>
      rename_i p r q a midInput targetInput
      have hpush :
          StackSummaryComputesIn M 0 r ([] : Word stack) midInput r midInput :=
        StackSummaryComputesIn.nil r midInput
      simpa using
        EmptySummaryComputesIn.read htransition hpush ih
  | epsilon htransition htail ih =>
      rename_i p r q midInput targetInput
      have hpush :
          StackSummaryComputesIn M 0 r ([] : Word stack) midInput r midInput :=
        StackSummaryComputesIn.nil r midInput
      simpa using
        EmptySummaryComputesIn.epsilon htransition hpush ih

theorem emptySummaryComputesIn_of_step_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hstep : Step M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M 1 p sourceInput q targetInput := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have hpushStack : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hpushNil : push = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpushStack
      simp [Word.Concat, hrestNil] at hlen
      omega
    have htransition' : M.transition p (some a) [] q [] := by
      simpa [hp, hq, hpopNil, hpushNil] using htransition
    have hsummary : EmptySummaryComputesIn M 1 p (a :: unread) q unread := by
      have hpushSummary :
          StackSummaryComputesIn M 0 q ([] : Word stack) unread q unread :=
        StackSummaryComputesIn.nil q unread
      have hempty :
          EmptySummaryComputesIn M 0 q unread q unread :=
        EmptySummaryComputesIn.zero q unread
      simpa using
        EmptySummaryComputesIn.read htransition' hpushSummary hempty
    simpa [hsource, htarget] using hsummary
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have hpushStack : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hpushNil : push = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpushStack
      simp [Word.Concat, hrestNil] at hlen
      omega
    have htransition' : M.transition p none [] q [] := by
      simpa [hp, hq, hpopNil, hpushNil] using htransition
    have hsummary : EmptySummaryComputesIn M 1 p unread q unread := by
      have hpushSummary :
          StackSummaryComputesIn M 0 q ([] : Word stack) unread q unread :=
        StackSummaryComputesIn.nil q unread
      have hempty :
          EmptySummaryComputesIn M 0 q unread q unread :=
        EmptySummaryComputesIn.zero q unread
      simpa using
        EmptySummaryComputesIn.epsilon htransition' hpushSummary hempty
    simpa [hsource, htarget] using hsummary

theorem emptySummaryComputesIn_of_computesIn_zero_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : ComputesIn M 0
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M 0 p sourceInput q targetInput := by
  have hend := computesIn_zero_eq hcomp
  have hstate : p = q := by
    simpa using congrArg
      (fun c : Configuration input stack state => c.state) hend
  have hunread : sourceInput = targetInput := by
    simpa using congrArg
      (fun c : Configuration input stack state => c.unread) hend
  simpa [hstate, hunread] using
    EmptySummaryComputesIn.zero p sourceInput

theorem emptySummaryComputesIn_of_computesIn_one_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : ComputesIn M 1
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M 1 p sourceInput q targetInput :=
  emptySummaryComputesIn_of_step_emptyStack (computesIn_one_inv hcomp)

/-!
Once the first-step reconstruction exists, the one-step top-pop summary follows
by taking an empty continuation. This gives the compact bridge used by the
bounded-computation cases below.
-/

theorem stackSummaryComputesIn_of_step_topPop
    {M : PDA input stack state}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    StackSummaryComputesIn M 1 p [A] sourceInput q targetInput := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hsourceStack : A :: tail = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have htargetStack : tail = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    rcases hnorm p' (some a) pop q' push htransition with
      hpopNil | hpopSingle
    · have hsourceLen := congrArg List.length hsourceStack
      have htargetLen := congrArg List.length htargetStack
      simp [Word.Concat, hpopNil] at hsourceLen htargetLen
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
        simpa [hp, hq, hpopSingle, hA, hpushNil] using htransition
      have hsummary : StackSummaryComputesIn M 1 p [A] (a :: unread) q unread := by
        simpa using
          StackSummaryComputesIn.popRead htransition'
            (StackSummaryComputesIn.nil (M := M) q unread)
      simpa [hsource, htarget] using hsummary
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
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
      hpopNil | hpopSingle
    · have hsourceLen := congrArg List.length hsourceStack
      have htargetLen := congrArg List.length htargetStack
      simp [Word.Concat, hpopNil] at hsourceLen htargetLen
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
        simpa [hp, hq, hpopSingle, hA, hpushNil] using htransition
      have hsummary : StackSummaryComputesIn M 1 p [A] unread q unread := by
        simpa using
          StackSummaryComputesIn.popEpsilon htransition'
            (StackSummaryComputesIn.nil (M := M) q unread)
      simpa [hsource, htarget] using hsummary

theorem stackSummaryComputesIn_of_computesIn_one_topPop
    {M : PDA input stack state}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M 1
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    StackSummaryComputesIn M 1 p [A] sourceInput q targetInput :=
  stackSummaryComputesIn_of_step_topPop hnorm (computesIn_one_inv hcomp)

/-!
The two-step and at-most-two empty-stack summaries mirror the earlier direct CFG
lemmas, but now they work through summary predicates. This keeps the final CFG
generation theorem from depending on a large step-by-step case analysis.
-/

theorem emptySummaryComputesIn_of_computesIn_two_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M 2
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M 2 p sourceInput q targetInput := by
  rcases computesIn_succ_inv (M := M) (n := 1) hcomp with
    ⟨mid, hfirst, htail⟩
  have hsecond0 : Step M mid
      { state := q, unread := targetInput, stack := [] } :=
    computesIn_one_inv htail
  rcases step_cases hfirst with hread | heps
  · rcases hread with
      ⟨p', r, a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' :
        M.transition p (some a) [] r push := by
      simpa [hp, hpopNil] using htransition
    cases hd
    have hsecond : Step M
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [Word.Concat, hrestNil] using hsecond0
    rcases step_sourceStack_empty_or_single_of_step_to_emptyStack
        (M := M) hnorm hsecond with hpushNil | hpushSingle
    · have htransitionEmpty :
          M.transition p (some a) [] r [] := by
        simpa [hpushNil] using htransition'
      have hsecondEmpty : Step M
          { state := r, unread := unread, stack := [] }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushNil] using hsecond
      have hemptyTail :=
        emptySummaryComputesIn_of_step_emptyStack
          (M := M) (p := r) (q := q) hsecondEmpty
      have hpushSummary :
          StackSummaryComputesIn M 0 r ([] : Word stack) unread r unread :=
        StackSummaryComputesIn.nil r unread
      have hsummary : EmptySummaryComputesIn M 2 p (a :: unread) q targetInput := by
        simpa using
          EmptySummaryComputesIn.read htransitionEmpty hpushSummary hemptyTail
      simpa [hsource] using hsummary
    · rcases hpushSingle with ⟨A, hpushSingle⟩
      have htransitionSingle :
          M.transition p (some a) [] r [A] := by
        simpa [hpushSingle] using htransition'
      have hsecondTop : Step M
          { state := r, unread := unread, stack := A :: ([] : Word stack) }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushSingle] using hsecond
      have htopSummary :=
        stackSummaryComputesIn_of_step_topPop
          (M := M) (p := r) (q := q) (A := A)
          (tail := ([] : Word stack)) hnorm hsecondTop
      have hemptyTail :
          EmptySummaryComputesIn M 0 q targetInput q targetInput :=
        EmptySummaryComputesIn.zero q targetInput
      have hsummary : EmptySummaryComputesIn M 2 p (a :: unread) q targetInput := by
        simpa using
          EmptySummaryComputesIn.read htransitionSingle htopSummary hemptyTail
      simpa [hsource] using hsummary
  · rcases heps with
      ⟨p', r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' :
        M.transition p none [] r push := by
      simpa [hp, hpopNil] using htransition
    cases hd
    have hsecond : Step M
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [Word.Concat, hrestNil] using hsecond0
    rcases step_sourceStack_empty_or_single_of_step_to_emptyStack
        (M := M) hnorm hsecond with hpushNil | hpushSingle
    · have htransitionEmpty :
          M.transition p none [] r [] := by
        simpa [hpushNil] using htransition'
      have hsecondEmpty : Step M
          { state := r, unread := unread, stack := [] }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushNil] using hsecond
      have hemptyTail :=
        emptySummaryComputesIn_of_step_emptyStack
          (M := M) (p := r) (q := q) hsecondEmpty
      have hpushSummary :
          StackSummaryComputesIn M 0 r ([] : Word stack) unread r unread :=
        StackSummaryComputesIn.nil r unread
      have hsummary : EmptySummaryComputesIn M 2 p unread q targetInput := by
        simpa using
          EmptySummaryComputesIn.epsilon htransitionEmpty hpushSummary hemptyTail
      simpa [hsource] using hsummary
    · rcases hpushSingle with ⟨A, hpushSingle⟩
      have htransitionSingle :
          M.transition p none [] r [A] := by
        simpa [hpushSingle] using htransition'
      have hsecondTop : Step M
          { state := r, unread := unread, stack := A :: ([] : Word stack) }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushSingle] using hsecond
      have htopSummary :=
        stackSummaryComputesIn_of_step_topPop
          (M := M) (p := r) (q := q) (A := A)
          (tail := ([] : Word stack)) hnorm hsecondTop
      have hemptyTail :
          EmptySummaryComputesIn M 0 q targetInput q targetInput :=
        EmptySummaryComputesIn.zero q targetInput
      have hsummary : EmptySummaryComputesIn M 2 p unread q targetInput := by
        simpa using
          EmptySummaryComputesIn.epsilon htransitionSingle htopSummary hemptyTail
      simpa [hsource] using hsummary

theorem emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M n p sourceInput q targetInput := by
  cases n with
  | zero =>
      exact emptySummaryComputesIn_of_computesIn_zero_emptyStack hcomp
  | succ n =>
      cases n with
      | zero =>
          exact emptySummaryComputesIn_of_computesIn_one_emptyStack hcomp
      | succ n =>
          cases n with
          | zero =>
              exact emptySummaryComputesIn_of_computesIn_two_emptyStack
                hnorm hcomp
          | succ n =>
              omega

/-!
Once a summary predicate is available, the proof returns to CFG syntax. Stack
summaries become chain derivations, empty summaries become derivations from
{lit}`empty p q`, and accepting empty summaries yield generated words from the
start symbol.
-/

theorem toCFG_betweenDerives_of_singleton_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack} {w : Word input}
    (h : ToCFGChainDerives M presentation p [A] q w) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord w) := by
  cases h with
  | cons hbetween htail =>
      cases htail with
      | nil _ =>
          simpa [Word.Concat, Word.Empty] using hbetween

theorem toCFGChainDerives_of_stackSummaryComputesIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        ToCFGChainDerives M presentation p stackWord q consumed := by
  induction h with
  | nil q unread =>
      exact ⟨Word.Empty, by simp [Word.Concat, Word.Empty],
        ToCFGChainDerives.nil (M := M) (presentation := presentation) q⟩
  | cons htop hrest ihtop ihrest =>
      rename_i m n p r q A rest sourceInput midInput targetInput
      rcases ihtop with ⟨topWord, htopInput, htopChain⟩
      rcases ihrest with ⟨restWord, hrestInput, hrestChain⟩
      have hbetween :=
        toCFG_betweenDerives_of_singleton_chainDerives htopChain
      refine ⟨Word.Concat topWord restWord, ?_, ?_⟩
      · rw [htopInput, hrestInput]
        simp [Word.Concat, List.append_assoc]
      · exact ToCFGChainDerives.cons hbetween hrestChain
  | popRead htransition hpush ih =>
      rename_i n p r q A a push midInput targetInput
      rcases ih with ⟨chainWord, hchainInput, hchainDerives⟩
      let consumed := Word.Concat (Word.Symbol a) chainWord
      have hbetween : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_popRead_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives
      refine ⟨consumed, ?_, ?_⟩
      · rw [hchainInput]
        simp [consumed, Word.Concat, Word.Symbol]
      · simpa [consumed, Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons hbetween
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
  | popEpsilon htransition hpush ih =>
      rename_i n p r q A push midInput targetInput
      rcases ih with ⟨chainWord, hchainInput, hchainDerives⟩
      have hbetween : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord chainWord) :=
        toCFG_popEpsilon_of_chainDerives
          (M := M) (presentation := presentation)
          htransition hchainDerives
      refine ⟨chainWord, ?_, ?_⟩
      · exact hchainInput
      · simpa [Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons hbetween
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
  | emptyBeforeTopRead htransition hpush htop ihpush ihtop =>
      rename_i m n p r s q A a push midInput topInput targetInput
      rcases ihpush with ⟨chainWord, hchainInput, hchainDerives⟩
      rcases ihtop with ⟨topWord, htopInput, htopChain⟩
      have htopDerives :=
        toCFG_betweenDerives_of_singleton_chainDerives htopChain
      let consumed :=
        Word.Concat (Word.Symbol a) (Word.Concat chainWord topWord)
      have hbetween : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_emptyBeforeTopRead_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives htopDerives
      refine ⟨consumed, ?_, ?_⟩
      · rw [hchainInput, htopInput]
        simp [consumed, Word.Concat, Word.Symbol, List.append_assoc]
      · simpa [consumed, Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons hbetween
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
  | emptyBeforeTopEpsilon htransition hpush htop ihpush ihtop =>
      rename_i m n p r s q A push midInput topInput targetInput
      rcases ihpush with ⟨chainWord, hchainInput, hchainDerives⟩
      rcases ihtop with ⟨topWord, htopInput, htopChain⟩
      have htopDerives :=
        toCFG_betweenDerives_of_singleton_chainDerives htopChain
      let consumed := Word.Concat chainWord topWord
      have hbetween : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_emptyBeforeTopEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives htopDerives
      refine ⟨consumed, ?_, ?_⟩
      · rw [hchainInput, htopInput]
        simp [consumed, Word.Concat, List.append_assoc]
      · simpa [consumed, Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons hbetween
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)

theorem toCFGChainDerives_of_stackSummaryComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputes M p stackWord sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        ToCFGChainDerives M presentation p stackWord q consumed := by
  rcases h with ⟨n, hn⟩
  exact toCFGChainDerives_of_stackSummaryComputesIn
    (M := M) (presentation := presentation) hn

/-!
Empty-summary derivations are obtained by induction on the summary witness. The
consumed word extracted from the PDA summary becomes the terminal frontier of
the CFG derivation from the corresponding empty-stack nonterminal.
-/

theorem toCFG_emptyDerives_of_emptySummaryComputesIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  induction h with
  | zero q unread =>
      refine ⟨Word.Empty, ?_, ?_⟩
      · simp [Word.Concat, Word.Empty]
      · simpa [SententialForm.terminalWord, Word.Empty] using
          toCFG_emptyRefl_derives
            (M := M) (presentation := presentation) (q := q)
  | read htransition hpush hempty ihempty =>
      rename_i m n p r s q a push midInput emptyInput targetInput
      rcases toCFGChainDerives_of_stackSummaryComputesIn
          (M := M) (presentation := presentation) hpush with
        ⟨chainWord, hchainInput, hchainDerives⟩
      rcases ihempty with ⟨emptyWord, hemptyInput, hemptyDerives⟩
      let consumed :=
        Word.Concat (Word.Symbol a) (Word.Concat chainWord emptyWord)
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_emptyRead_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives hemptyDerives
      refine ⟨consumed, ?_, hbody⟩
      rw [hchainInput, hemptyInput]
      simp [consumed, Word.Concat, Word.Symbol, List.append_assoc]
  | epsilon htransition hpush hempty ihempty =>
      rename_i m n p r s q push midInput emptyInput targetInput
      rcases toCFGChainDerives_of_stackSummaryComputesIn
          (M := M) (presentation := presentation) hpush with
        ⟨chainWord, hchainInput, hchainDerives⟩
      rcases ihempty with ⟨emptyWord, hemptyInput, hemptyDerives⟩
      let consumed := Word.Concat chainWord emptyWord
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_emptyEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives hemptyDerives
      refine ⟨consumed, ?_, hbody⟩
      rw [hchainInput, hemptyInput]
      simp [consumed, Word.Concat, List.append_assoc]

theorem toCFG_emptyDerives_of_emptySummaryComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputes M p sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  rcases h with ⟨n, hn⟩
  exact toCFG_emptyDerives_of_emptySummaryComputesIn
    (M := M) (presentation := presentation) hn

theorem toCFG_emptyDerives_of_read_stackThenEmptySummary
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p r q : state} {a : input}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hrest : StackThenEmptySummaryComputesIn M n r push midInput
      q targetInput) :
    exists consumed : Word input,
      a :: midInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  toCFG_emptyDerives_of_emptySummaryComputesIn
    (M := M) (presentation := presentation)
    (emptySummaryComputesIn_read_of_stackThenEmptySummary
      htransition hrest)

theorem toCFG_emptyDerives_of_epsilon_stackThenEmptySummary
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p r q : state}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p none [] r push)
    (hrest : StackThenEmptySummaryComputesIn M n r push midInput
      q targetInput) :
    exists consumed : Word input,
      midInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  toCFG_emptyDerives_of_emptySummaryComputesIn
    (M := M) (presentation := presentation)
    (emptySummaryComputesIn_epsilon_of_stackThenEmptySummary
      htransition hrest)

theorem toCFG_emptyDerives_of_computesIn_atMostTwo_emptyStack_viaSummary
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  toCFG_emptyDerives_of_emptySummaryComputesIn
    (emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
      hnorm hn hcomp)

theorem toCFG_generates_of_emptySummaryAcceptsIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptySummaryComputesIn M n M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_emptySummaryComputesIn
      (M := M) (presentation := presentation) hcomp with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_emptySummaryAccepts
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptySummaryComputes M M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_emptySummaryComputes
      (M := M) (presentation := presentation) hcomp with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

/-!
The final generated-language wrappers specialize the summary bridge to accepting
computations from the initial configuration. They cover the explicit small
bounds first, then hand off to the summary-completeness assumptions later in the
file.
-/

theorem toCFG_generates_of_acceptsIn_zero
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : ComputesIn M 0 (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_computesIn_zero_emptyStack
      (M := M) (presentation := presentation)
      (p := M.start) (q := qf)
      (sourceInput := w) (targetInput := ([] : Word input))
      (by simpa [initial] using hcomp) with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_one
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : ComputesIn M 1 (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_computesIn_one_emptyStack
      (M := M) (presentation := presentation)
      (p := M.start) (q := qf)
      (sourceInput := w) (targetInput := ([] : Word input))
      (by simpa [initial] using hcomp) with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_two
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (hnorm : PopsAtMostOne M)
    (haccept : M.accept qf)
    (hcomp : ComputesIn M 2 (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_computesIn_two_emptyStack
      (M := M) (presentation := presentation)
      (p := M.start) (q := qf)
      (sourceInput := w) (targetInput := ([] : Word input))
      hnorm (by simpa [initial] using hcomp) with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_atMostOne
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hn : n <= 1)
    (haccept : M.accept qf)
    (hcomp : ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_computesIn_atMostOne_emptyStack
      (M := M) (presentation := presentation)
      (p := M.start) (q := qf)
      (sourceInput := w) (targetInput := ([] : Word input))
      hn (by simpa [initial] using hcomp) with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_atMostTwo
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hnorm : PopsAtMostOne M)
    (hn : n <= 2)
    (haccept : M.accept qf)
    (hcomp : ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  apply toCFG_generates_of_emptySummaryAcceptsIn haccept
  exact emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
    hnorm hn (by simpa [initial] using hcomp)

/-!
The final soundness step for generated CFG words goes the other direction:
derivations in the constructed grammar denote real PDA computations, so a word
generated from the start symbol is accepted by the original PDA.
-/

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

/-!
# Soundness: CFG to PDA

If the constructed grammar derives a terminal word, the original PDA accepts
that word.
-/

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

/-!
# Summary-completeness assumptions

Completeness of the reverse direction is factored through summary-completeness
predicates. Normalized top-pop PDAs satisfy these predicates.
-/

def EmptySummaryComplete (M : PDA input stack state) : Prop :=
  forall n p q sourceInput targetInput,
    _root_.FoC.Grammars.PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } ->
        EmptySummaryComputesIn M n p sourceInput q targetInput

def EmptySummaryCompleteUpTo (M : PDA input stack state)
    (bound : Nat) : Prop :=
  forall n p q sourceInput targetInput,
    n <= bound ->
      _root_.FoC.Grammars.PDA.ComputesIn M n
        { state := p, unread := sourceInput, stack := [] }
        { state := q, unread := targetInput, stack := [] } ->
          EmptySummaryComputesIn M n p sourceInput q targetInput

def EmptySummaryCompleteForComputes (M : PDA input stack state) : Prop :=
  forall p q sourceInput targetInput,
    _root_.FoC.Grammars.PDA.Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } ->
        EmptySummaryComputes M p sourceInput q targetInput

def StackThenEmptySummaryComplete (M : PDA input stack state) : Prop :=
  forall n p q stackWord sourceInput targetInput,
    _root_.FoC.Grammars.PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] } ->
        StackThenEmptySummaryComputesIn M n p stackWord sourceInput
          q targetInput

def StackThenEmptySummaryCompleteForComputes
    (M : PDA input stack state) : Prop :=
  forall p q stackWord sourceInput targetInput,
    _root_.FoC.Grammars.PDA.Computes M
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] } ->
        StackThenEmptySummaryComputes M p stackWord sourceInput
          q targetInput

def TopPopEmptySummaryComplete (M : PDA input stack state) : Prop :=
  PopsAtMostOne M -> EmptySummaryComplete M

def TopPopStackThenEmptySummaryComplete
    (M : PDA input stack state) : Prop :=
  PopsAtMostOne M -> StackThenEmptySummaryComplete M

theorem emptySummaryCompleteForComputes_of_emptySummaryComplete
    {M : PDA input stack state}
    (hcomplete : EmptySummaryComplete M) :
    EmptySummaryCompleteForComputes M := by
  intro p q sourceInput targetInput hcomp
  rcases computes_exists_length hcomp with ⟨n, hcompIn⟩
  exact ⟨n, hcomplete n p q sourceInput targetInput hcompIn⟩

theorem stackThenEmptySummaryCompleteForComputes_of_complete
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryComplete M) :
    StackThenEmptySummaryCompleteForComputes M := by
  intro p q stackWord sourceInput targetInput hcomp
  rcases computes_exists_length hcomp with ⟨n, hcompIn⟩
  exact ⟨n, hcomplete n p q stackWord sourceInput targetInput hcompIn⟩

theorem emptySummaryComplete_of_stackThenEmptySummaryComplete
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryComplete M) :
    EmptySummaryComplete M := by
  intro n p q sourceInput targetInput hcomp
  exact emptySummaryComputesIn_of_stackThenEmptySummaryComputesIn_nil
    (hcomplete n p q ([] : Word stack) sourceInput targetInput hcomp)

/-!
Completeness is proved by reducing an ordinary empty-stack computation to the
stronger stack-then-empty summary property. The first-step lemma below handles
the nonzero case by asking the completeness hypothesis to summarize the pushed
stack after that first step.
-/

theorem emptySummaryComputesIn_of_step_emptyStack_of_stackThenEmptySummaryComplete
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    {mid : Configuration input stack state}
    (hcomplete : StackThenEmptySummaryComplete M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := [] } mid)
    (hrest : ComputesIn M n mid
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M (n + 1) p sourceInput q targetInput := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', r, a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' : M.transition p (some a) [] r push := by
      simpa [hp, hpopNil] using htransition
    have hrest' : ComputesIn M n
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [hd, hrestNil, Word.Concat] using hrest
    have hpushed :
        StackThenEmptySummaryComputesIn M n r push unread q targetInput :=
      hcomplete n r q push unread targetInput hrest'
    have hsummary :=
      emptySummaryComputesIn_read_of_stackThenEmptySummary
        htransition' hpushed
    simpa [hsource] using hsummary
  · rcases heps with
      ⟨p', r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' : M.transition p none [] r push := by
      simpa [hp, hpopNil] using htransition
    have hrest' : ComputesIn M n
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [hd, hrestNil, Word.Concat] using hrest
    have hpushed :
        StackThenEmptySummaryComputesIn M n r push unread q targetInput :=
      hcomplete n r q push unread targetInput hrest'
    have hsummary :=
      emptySummaryComputesIn_epsilon_of_stackThenEmptySummary
        htransition' hpushed
    simpa [hsource] using hsummary

theorem emptySummaryComplete_of_stackThenEmptySummaryComplete_by_first_step
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryComplete M) :
    EmptySummaryComplete M := by
  intro n p q sourceInput targetInput hcomp
  cases n with
  | zero =>
      exact emptySummaryComputesIn_of_computesIn_zero_emptyStack hcomp
  | succ n =>
      rcases computesIn_succ_inv (M := M) (n := n) hcomp with
        ⟨mid, hstep, hrest⟩
      exact
        emptySummaryComputesIn_of_step_emptyStack_of_stackThenEmptySummaryComplete
          hcomplete hstep hrest

theorem emptySummaryCompleteForComputes_of_stackThenEmptySummaryCompleteForComputes
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryCompleteForComputes M) :
    EmptySummaryCompleteForComputes M := by
  intro p q sourceInput targetInput hcomp
  exact emptySummaryComputes_of_stackThenEmptySummaryComputes_nil
    (hcomplete p q ([] : Word stack) sourceInput targetInput hcomp)

theorem stackThenEmptySummaryComplete_of_topPop
    {M : PDA input stack state}
    (hnorm : PopsAtMostOne M) :
    StackThenEmptySummaryComplete M := by
  intro n p q stackWord sourceInput targetInput hcomp
  exact stackThenEmptySummaryComputesIn_of_computesIn_topPop hnorm hcomp

theorem topPopStackThenEmptySummaryComplete
    (M : PDA input stack state) :
    TopPopStackThenEmptySummaryComplete M := by
  intro hnorm
  exact stackThenEmptySummaryComplete_of_topPop hnorm

theorem emptySummaryComplete_of_topPop
    {M : PDA input stack state}
    (hnorm : PopsAtMostOne M) :
    EmptySummaryComplete M :=
  emptySummaryComplete_of_stackThenEmptySummaryComplete
    (stackThenEmptySummaryComplete_of_topPop hnorm)

theorem topPopEmptySummaryComplete
    (M : PDA input stack state) :
    TopPopEmptySummaryComplete M := by
  intro hnorm
  exact emptySummaryComplete_of_topPop hnorm

theorem emptySummaryCompleteUpTo_two_of_topPop
    {M : PDA input stack state}
    (hnorm : PopsAtMostOne M) :
    EmptySummaryCompleteUpTo M 2 := by
  intro n p q sourceInput targetInput hn hcomp
  exact emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
    hnorm hn hcomp

/-!
The final exactness statements combine both inclusions: every generated word is
accepted by soundness, and every accepted word is generated once the appropriate
summary-completeness principle is available. Top-pop normalized PDAs satisfy
that principle.
-/

theorem toCFG_generates_of_acceptsIn_of_emptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hcomplete : EmptySummaryComplete M)
    (haccept : M.accept qf)
    (hcomp : _root_.FoC.Grammars.PDA.ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  apply toCFG_generates_of_emptySummaryAcceptsIn haccept
  exact hcomplete n M.start qf w ([] : Word input)
    (by simpa [initial] using hcomp)

theorem toCFG_generates_of_acceptsIn_of_emptySummaryCompleteUpTo
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {bound n : Nat} {w : Word input} {qf : state}
    (hcomplete : EmptySummaryCompleteUpTo M bound)
    (hn : n <= bound)
    (haccept : M.accept qf)
    (hcomp : _root_.FoC.Grammars.PDA.ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  apply toCFG_generates_of_emptySummaryAcceptsIn haccept
  exact hcomplete n M.start qf w ([] : Word input) hn
    (by simpa [initial] using hcomp)

theorem toCFG_generates_of_accepts_of_emptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input}
    (hcomplete : EmptySummaryComplete M)
    (haccepts : Accepts M w) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases haccepts with ⟨qf, haccept, hcomp⟩
  rcases _root_.FoC.Grammars.PDA.computes_exists_length hcomp with
    ⟨n, hcompIn⟩
  exact toCFG_generates_of_acceptsIn_of_emptySummaryComplete
    (M := M) (presentation := presentation)
    hcomplete haccept hcompIn

theorem toCFG_generates_of_accepts_of_emptySummaryCompleteForComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input}
    (hcomplete : EmptySummaryCompleteForComputes M)
    (haccepts : Accepts M w) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases haccepts with ⟨qf, haccept, hcomp⟩
  exact toCFG_generates_of_emptySummaryAccepts
    (M := M) (presentation := presentation)
    haccept (hcomplete M.start qf w ([] : Word input) hcomp)

theorem toCFG_language_exact_of_emptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : EmptySummaryComplete M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) := by
  intro w
  constructor
  · intro h
    exact toCFG_accepts_of_generates h
  · intro h
    exact toCFG_generates_of_accepts_of_emptySummaryComplete
      (M := M) (presentation := presentation) hcomplete h

theorem toCFG_language_exact_of_emptySummaryCompleteForComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : EmptySummaryCompleteForComputes M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) := by
  intro w
  constructor
  · intro h
    exact toCFG_accepts_of_generates h
  · intro h
    exact toCFG_generates_of_accepts_of_emptySummaryCompleteForComputes
      (M := M) (presentation := presentation) hcomplete h

theorem toCFG_language_exact_of_stackThenEmptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : StackThenEmptySummaryComplete M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) :=
  toCFG_language_exact_of_emptySummaryComplete
    (M := M) (presentation := presentation)
    (emptySummaryComplete_of_stackThenEmptySummaryComplete hcomplete)

theorem toCFG_language_exact_of_stackThenEmptySummaryCompleteForComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : StackThenEmptySummaryCompleteForComputes M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) :=
  toCFG_language_exact_of_emptySummaryCompleteForComputes
    (M := M) (presentation := presentation)
    (emptySummaryCompleteForComputes_of_stackThenEmptySummaryCompleteForComputes
      hcomplete)

theorem toCFG_language_exact_of_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hnorm : PopsAtMostOne M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) :=
  toCFG_language_exact_of_stackThenEmptySummaryComplete
    (M := M) (presentation := presentation)
    (stackThenEmptySummaryComplete_of_topPop hnorm)

def ToCFGTopPopExact (M : PDA input stack state)
    (presentation : FinitePresentation M) : Prop :=
  PopsAtMostOne M ->
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (PDA.AcceptedLanguage M)

theorem toCFG_topPopExact_of_emptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : TopPopEmptySummaryComplete M) :
    ToCFGTopPopExact M presentation := by
  intro hnorm
  exact toCFG_language_exact_of_emptySummaryComplete
    (M := M) (presentation := presentation) (hcomplete hnorm)

theorem toCFG_topPopExact_of_stackThenEmptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : TopPopStackThenEmptySummaryComplete M) :
    ToCFGTopPopExact M presentation := by
  intro hnorm
  exact toCFG_language_exact_of_stackThenEmptySummaryComplete
    (M := M) (presentation := presentation) (hcomplete hnorm)

theorem toCFG_topPopExact
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    ToCFGTopPopExact M presentation := by
  intro hnorm
  exact toCFG_language_exact_of_topPop
    (M := M) (presentation := presentation) hnorm

/-!
# Normalized PDA conversion

For an arbitrary finitely presented PDA, pop normalization produces the
top-pop form needed by the exact PDA-to-CFG construction.
-/

def PopNormalizeLanguageExact
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    Prop :=
  Language.Equal (AcceptedLanguage (PopNormalize M presentation))
    (AcceptedLanguage M)

theorem popNormalizeLanguageExact
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    PopNormalizeLanguageExact M presentation :=
  popNormalize_acceptedLanguage_exact presentation

def ToCFGNormalized (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    CFG input
      (ToCFGNonterminal stack
        (PopNormalizedState (M := M) presentation)) :=
  ToCFG (PopNormalize M presentation)
    (popNormalizeFinitePresentation M presentation)

theorem toCFGNormalized_hasFiniteProductions
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    CFG.HasFiniteProductions (ToCFGNormalized M presentation) :=
  toCFG_hasFiniteProductions (PopNormalize M presentation)
    (popNormalizeFinitePresentation M presentation)

theorem toCFGNormalized_language_exact
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFGNormalized M presentation))
      (AcceptedLanguage (PopNormalize M presentation)) :=
  toCFG_language_exact_of_topPop
    (M := PopNormalize M presentation)
    (presentation := popNormalizeFinitePresentation M presentation)
    (popNormalize_popsAtMostOne M presentation)

theorem toCFGNormalized_language_exact_of_popNormalizeLanguageExact
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hexact : PopNormalizeLanguageExact M presentation) :
    Language.Equal (CFG.GeneratedLanguage (ToCFGNormalized M presentation))
      (AcceptedLanguage M) := by
  intro w
  exact Iff.trans (toCFGNormalized_language_exact M presentation w)
    (hexact w)

theorem toCFGNormalized_language_exact_original
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFGNormalized M presentation))
      (AcceptedLanguage M) :=
  toCFGNormalized_language_exact_of_popNormalizeLanguageExact
    (M := M) (presentation := presentation)
    (popNormalizeLanguageExact M presentation)

theorem acceptedLanguage_subset_popNormalizeLanguage
    {M : PDA input stack state} (presentation : FinitePresentation M) :
    Language.Subset (AcceptedLanguage M)
      (AcceptedLanguage (PopNormalize M presentation)) :=
  acceptedLanguage_subset_popNormalize presentation

theorem toCFGNormalized_generates_of_accepts
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input}
    (haccepts : w ∈ AcceptedLanguage M) :
    w ∈ CFG.GeneratedLanguage (ToCFGNormalized M presentation) :=
  (toCFGNormalized_language_exact M presentation w).mpr
    (acceptedLanguage_subset_popNormalize presentation w haccepts)

theorem acceptedLanguage_subset_toCFGNormalized
    {M : PDA input stack state} (presentation : FinitePresentation M) :
    Language.Subset (AcceptedLanguage M)
      (CFG.GeneratedLanguage (ToCFGNormalized M presentation)) := by
  intro w hw
  exact toCFGNormalized_generates_of_accepts
    (M := M) (presentation := presentation) hw

theorem toCFG_nonterminals_finite
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    (ToCFG M presentation).nonterminalsFinite =
      ToCFGNonterminal.finite presentation.stackFinite M.statesFinite :=
  rfl

end PDA

end Grammars
end FoC
