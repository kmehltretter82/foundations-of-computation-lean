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

def ToCFG (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    CFG input (ToCFGNonterminal stack state) where
  start := ToCFGNonterminal.start
  produces := ToCFGProduces M
  nonterminalsFinite :=
    ToCFGNonterminal.finite presentation.stackFinite M.statesFinite

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
