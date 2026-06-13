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


end PDA

end Grammars
end FoC
