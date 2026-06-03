import FoC.Grammars.ParseTree
import FoC.Grammars.PDA

set_option doc.verso true

/-!
# From CFGs to PDAs

## Simulating derivations with a stack

The constructed PDA starts with an empty stack, pushes the grammar start symbol,
then repeatedly expands nonterminals or matches terminals at the stack top.

This is the reusable construction behind the chapter theorem that every
context-free language is accepted by a pushdown automaton.
-/

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace CFG

/-!
# Control states and transitions

The constructed PDA has a start state and a running state. Its transitions push
the grammar start symbol, expand nonterminals, and match terminal stack symbols
against input.
-/

inductive ToPDAState where
  | start
  | run
deriving DecidableEq

namespace ToPDAState

def finite : FiniteType ToPDAState where
  elems := [start, run]
  complete := by
    intro q
    cases q <;> simp

end ToPDAState

inductive ToPDATransition (G : CFG terminal nonterminal) :
    ToPDAState -> Option terminal ->
      Word (Symbol terminal nonterminal) ->
        ToPDAState -> Word (Symbol terminal nonterminal) -> Prop where
  | start :
      ToPDATransition G ToPDAState.start none []
        ToPDAState.run [Symbol.nonterminal G.start]
  | expand {A rhs} :
      G.produces A rhs ->
        ToPDATransition G ToPDAState.run none [Symbol.nonterminal A]
          ToPDAState.run rhs
  | matchTerminal (a : terminal) :
      ToPDATransition G ToPDAState.run (some a) [Symbol.terminal a]
        ToPDAState.run []

def ToPDA (G : CFG terminal nonterminal) :
    PDA terminal (Symbol terminal nonterminal) ToPDAState where
  start := ToPDAState.start
  transition := ToPDATransition G
  accept := fun q => q = ToPDAState.run
  statesFinite := ToPDAState.finite

/-!
# Finite transition presentation

When the grammar has finite productions and finite terminal alphabet, the PDA
construction has a finite stack alphabet and finite transition-rule list.
-/

def toPDAStackFinite
    (terminalFinite : FiniteType terminal)
    (nonterminalFinite : FiniteType nonterminal) :
    FiniteType (Symbol terminal nonterminal) where
  elems := terminalFinite.elems.map Symbol.terminal ++
    nonterminalFinite.elems.map Symbol.nonterminal
  complete := by
    intro s
    cases s with
    | terminal a =>
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨a, terminalFinite.complete a, rfl⟩
    | nonterminal A =>
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨A, nonterminalFinite.complete A, rfl⟩

def toPDAStartTransitionRule (G : CFG terminal nonterminal) :
    PDA.TransitionRule terminal (Symbol terminal nonterminal) ToPDAState where
  source := ToPDAState.start
  input? := none
  pop := []
  target := ToPDAState.run
  push := [Symbol.nonterminal G.start]

def toPDAExpandTransitionRule
    (rule : Production terminal nonterminal) :
    PDA.TransitionRule terminal (Symbol terminal nonterminal) ToPDAState where
  source := ToPDAState.run
  input? := none
  pop := [Symbol.nonterminal rule.lhs]
  target := ToPDAState.run
  push := rule.rhs

def toPDAMatchTransitionRule (a : terminal) :
    PDA.TransitionRule terminal (Symbol terminal nonterminal) ToPDAState where
  source := ToPDAState.run
  input? := some a
  pop := [Symbol.terminal a]
  target := ToPDAState.run
  push := []

def toPDATransitionRules
    (G : CFG terminal nonterminal)
    (terminalFinite : FiniteType terminal)
    (rules : List (Production terminal nonterminal)) :
    List (PDA.TransitionRule terminal (Symbol terminal nonterminal)
      ToPDAState) :=
  [toPDAStartTransitionRule G] ++
    rules.map toPDAExpandTransitionRule ++
      terminalFinite.elems.map toPDAMatchTransitionRule

theorem toPDA_transition_complete
    (G : CFG terminal nonterminal)
    (terminalFinite : FiniteType terminal)
    (rules : List (Production terminal nonterminal))
    (hrules : forall A rhs,
      G.produces A rhs <->
        exists rule, rule ∈ rules ∧ rule.lhs = A ∧ rule.rhs = rhs) :
    forall q a? pop r push,
      (ToPDA G).transition q a? pop r push <->
        exists rule,
          rule ∈ toPDATransitionRules G terminalFinite rules ∧
            rule.Applies q a? pop r push := by
  intro q a? pop r push
  constructor
  · intro h
    cases h with
    | start =>
        exists toPDAStartTransitionRule G
        constructor
        · simp [toPDATransitionRules]
        · simp [PDA.TransitionRule.Applies, toPDAStartTransitionRule]
    | expand hprod =>
        rcases (hrules _ _).mp hprod with ⟨rule, hrule, hlhs, hrhs⟩
        exists toPDAExpandTransitionRule rule
        constructor
        · unfold toPDATransitionRules
          apply List.mem_append.mpr
          left
          apply List.mem_append.mpr
          right
          exact List.mem_map.mpr ⟨rule, hrule, rfl⟩
        · simp [PDA.TransitionRule.Applies, toPDAExpandTransitionRule,
            hlhs, hrhs]
    | matchTerminal a =>
        exists toPDAMatchTransitionRule a
        constructor
        · unfold toPDATransitionRules
          apply List.mem_append.mpr
          right
          exact List.mem_map.mpr ⟨a, terminalFinite.complete a, rfl⟩
        · simp [PDA.TransitionRule.Applies, toPDAMatchTransitionRule]
  · intro h
    rcases h with ⟨rule, hmem, happlies⟩
    unfold toPDATransitionRules at hmem
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hmem
    rcases happlies with ⟨hsource, hinput, hpop, htarget, hpush⟩
    rcases hmem with hleft | hmatch
    · rcases hleft with hstart | hexpand
      · subst rule
        simp [toPDAStartTransitionRule] at hsource hinput hpop htarget hpush
        subst q
        subst a?
        subst pop
        subst r
        subst push
        exact ToPDATransition.start
      · rcases hexpand with ⟨base, hbase, hruleEq⟩
        subst rule
        simp [toPDAExpandTransitionRule] at hsource hinput hpop htarget hpush
        subst q
        subst a?
        subst pop
        subst r
        subst push
        exact ToPDATransition.expand ((hrules base.lhs base.rhs).mpr
          ⟨base, hbase, rfl, rfl⟩)
    · rcases hmatch with ⟨a, _ha, hruleEq⟩
      subst rule
      simp [toPDAMatchTransitionRule] at hsource hinput hpop htarget hpush
      subst q
      subst a?
      subst pop
      subst r
      subst push
      exact ToPDATransition.matchTerminal a

theorem toPDA_accept_complete (G : CFG terminal nonterminal) :
    forall q, (ToPDA G).accept q <-> q ∈ [ToPDAState.run] := by
  intro q
  constructor
  · intro h
    simpa [ToPDA] using h
  · intro h
    simpa [ToPDA] using h

noncomputable def toPDA_finitePresentation
    (G : CFG terminal nonterminal)
    (terminalFinite : FiniteType terminal)
    (hG : HasFiniteProductions G) :
    PDA.FinitePresentation (ToPDA G) := by
  classical
  let rules := Classical.choose hG
  have hrules := Classical.choose_spec hG
  exact {
    stackFinite := toPDAStackFinite terminalFinite G.nonterminalsFinite,
    transitionRules := toPDATransitionRules G terminalFinite rules,
    transition_complete :=
      toPDA_transition_complete G terminalFinite rules hrules,
    acceptingStates := [ToPDAState.run],
    accept_complete := toPDA_accept_complete G }

theorem toPDA_hasFinitePresentation
    (G : CFG terminal nonterminal)
    (terminalFinite : FiniteType terminal)
    (hG : HasFiniteProductions G) :
    PDA.HasFinitePresentation (ToPDA G) :=
  Nonempty.intro (toPDA_finitePresentation G terminalFinite hG)

/-!
# Completeness: grammar to PDA

Parse trees and generated words produce accepting PDA computations by expanding
grammar symbols on the stack and matching terminals.
-/

theorem toPDA_start_step (G : CFG terminal nonterminal)
    (w : Word terminal) :
    PDA.Step (ToPDA G)
      { state := ToPDAState.start, unread := w, stack := [] }
      { state := ToPDAState.run, unread := w,
        stack := [Symbol.nonterminal G.start] } := by
  simpa [ToPDA, Word.Concat] using
    PDA.Step.epsilon (M := ToPDA G) (unread := w)
      (restStack := ([] : Word (Symbol terminal nonterminal)))
      ToPDATransition.start

theorem toPDA_expand_step {G : CFG terminal nonterminal}
    {A : nonterminal} {rhs : SententialForm terminal nonterminal}
    (hprod : G.produces A rhs)
    (unread : Word terminal)
    (tail : Word (Symbol terminal nonterminal)) :
    PDA.Step (ToPDA G)
      { state := ToPDAState.run, unread := unread,
        stack := Symbol.nonterminal A :: tail }
      { state := ToPDAState.run, unread := unread,
        stack := Word.Concat rhs tail } := by
  simpa [ToPDA, Word.Concat] using
    PDA.Step.epsilon (M := ToPDA G) (unread := unread)
      (restStack := tail) (ToPDATransition.expand hprod)

theorem toPDA_match_step (G : CFG terminal nonterminal)
    (a : terminal) (unread : Word terminal)
    (tail : Word (Symbol terminal nonterminal)) :
    PDA.Step (ToPDA G)
      { state := ToPDAState.run, unread := a :: unread,
        stack := Symbol.terminal a :: tail }
      { state := ToPDAState.run, unread := unread, stack := tail } := by
  simpa [ToPDA, Word.Concat] using
    PDA.Step.read (M := ToPDA G) (unread := unread)
      (restStack := tail) (ToPDATransition.matchTerminal (G := G) a)

mutual

theorem ParseTree.toPDA_computes
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    (restInput : Word terminal)
    (tail : Word (Symbol terminal nonterminal)) :
    PDA.Computes (ToPDA G)
      { state := ToPDAState.run,
        unread := Word.Concat (ParseTree.frontier tree) restInput,
        stack := s :: tail }
      { state := ToPDAState.run, unread := restInput, stack := tail } := by
  cases tree with
  | leaf a =>
      simpa [ParseTree.frontier, Word.Concat] using
        PDA.computes_of_step (toPDA_match_step G a restInput tail)
  | node A rhs hprod children =>
      have hstep :=
        toPDA_expand_step hprod
          (Word.Concat (ParseForest.frontier children) restInput) tail
      have hchildren := ParseForest.toPDA_computes children restInput tail
      exact PDA.Computes.step hstep hchildren

theorem ParseForest.toPDA_computes
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent)
    (restInput : Word terminal)
    (tail : Word (Symbol terminal nonterminal)) :
    PDA.Computes (ToPDA G)
      { state := ToPDAState.run,
        unread := Word.Concat (ParseForest.frontier forest) restInput,
        stack := Word.Concat sent tail }
      { state := ToPDAState.run, unread := restInput, stack := tail } := by
  cases forest with
  | nil =>
      simp [ParseForest.frontier, Word.Concat]
      exact PDA.Computes.refl _
  | cons s restSent tree rest =>
      have hTree :=
        ParseTree.toPDA_computes tree
          (Word.Concat (ParseForest.frontier rest) restInput)
          (Word.Concat restSent tail)
      have hRest := ParseForest.toPDA_computes rest restInput tail
      have hTree' : PDA.Computes (ToPDA G)
          { state := ToPDAState.run,
            unread :=
              Word.Concat
                (Word.Concat (ParseTree.frontier tree)
                  (ParseForest.frontier rest)) restInput,
            stack := s :: Word.Concat restSent tail }
          { state := ToPDAState.run,
            unread := Word.Concat (ParseForest.frontier rest) restInput,
            stack := Word.Concat restSent tail } := by
        simpa [Word.Concat, List.append_assoc] using hTree
      exact PDA.computes_trans
        (by
          simpa [ParseForest.frontier, Word.Concat, List.append_assoc]
            using hTree')
        hRest

end

theorem toPDA_accepts_of_parseTree
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {w : Word terminal}
    (tree : ParseTree G (Symbol.nonterminal G.start))
    (hfrontier : ParseTree.frontier tree = w) :
    PDA.Accepts (ToPDA G) w := by
  exists ToPDAState.run
  constructor
  · rfl
  · unfold PDA.initial
    have hstart := PDA.computes_of_step (toPDA_start_step G w)
    have htree :=
      ParseTree.toPDA_computes tree ([] : Word terminal)
        ([] : Word (Symbol terminal nonterminal))
    have htree' : PDA.Computes (ToPDA G)
        { state := ToPDAState.run, unread := w,
          stack := [Symbol.nonterminal G.start] }
        { state := ToPDAState.run, unread := [], stack := [] } := by
      rw [← hfrontier]
      simpa [Word.Concat] using htree
    exact PDA.computes_trans hstart htree'

theorem toPDA_accepts_of_generates
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ GeneratedLanguage G) :
    PDA.Accepts (ToPDA G) w := by
  cases ParseTree.of_generates_language h with
  | intro tree hfrontier =>
      exact toPDA_accepts_of_parseTree tree hfrontier

/-!
# Soundness: PDA to grammar

Conversely, accepting computations are read back as grammar derivations, giving
the exact language equality for the construction.
-/

theorem toPDA_running_computes_sound_config
    {G : CFG terminal nonterminal}
    {c d : PDA.Configuration terminal (Symbol terminal nonterminal) ToPDAState}
    (h : PDA.Computes (ToPDA G) c d)
    (hstate : c.state = ToPDAState.run) :
    d = { state := ToPDAState.run, unread := [], stack := [] } ->
    Derives G c.stack (SententialForm.terminalWord c.unread) := by
  induction h with
  | refl c =>
      intro hfinal
      rw [hfinal]
      simp [SententialForm.terminalWord]
      exact Derives.refl []
  | step hstep hrest ih =>
      intro hfinal
      cases hstep with
      | read htrans =>
          rename_i q r a unread pop push restStack
          cases htrans with
          | matchTerminal =>
              have htail := ih rfl hfinal
              have htail' :
                  Derives G restStack
                    (SententialForm.terminalWord unread) := by
                simpa [Word.Concat] using htail
              have hctx :
                  Derives G
                    (Word.Concat
                      ([Symbol.terminal a] :
                        Word (Symbol terminal nonterminal)) restStack)
                    (SententialForm.terminalWord (nt := nonterminal) [a] ++
                      SententialForm.terminalWord unread) := by
                simpa using derives_context htail' [Symbol.terminal a] []
              simpa [SententialForm.terminalWord] using hctx
      | epsilon htrans =>
          rename_i q r unread pop push restStack
          cases htrans with
          | start =>
              cases hstate
          | expand hprod =>
              rename_i lhs
              have htail := ih rfl hfinal
              have hstep' : Yields G
                  (Word.Concat
                    ([Symbol.nonterminal lhs] :
                      Word (Symbol terminal nonterminal)) restStack)
                  (Word.Concat push restStack) := by
                exists []
                exists restStack
                exists lhs
                exists push
              simpa [Word.Concat] using Derives.step hstep' htail

theorem toPDA_running_computes_sound
    {G : CFG terminal nonterminal}
    {w : Word terminal} {stack : Word (Symbol terminal nonterminal)}
    (h : PDA.Computes (ToPDA G)
      { state := ToPDAState.run, unread := w, stack := stack }
      { state := ToPDAState.run, unread := [], stack := [] }) :
    Derives G stack (SententialForm.terminalWord w) :=
  toPDA_running_computes_sound_config h rfl rfl

theorem toPDA_start_computes_sound_config
    {G : CFG terminal nonterminal}
    {c d : PDA.Configuration terminal (Symbol terminal nonterminal) ToPDAState}
    (h : PDA.Computes (ToPDA G) c d)
    (hstate : c.state = ToPDAState.start)
    (hstack : c.stack = ([] : Word (Symbol terminal nonterminal))) :
    d = { state := ToPDAState.run, unread := [], stack := [] } ->
    Derives G [Symbol.nonterminal G.start]
      (SententialForm.terminalWord c.unread) := by
  induction h with
  | refl c =>
      intro hfinal
      rw [hfinal] at hstate
      cases hstate
  | step hstep hrest ih =>
      intro hfinal
      cases hstep with
      | read htrans =>
          cases htrans with
          | matchTerminal _ =>
              cases hstate
      | epsilon htrans =>
          rename_i q r unread pop push restStack
          cases htrans with
          | start =>
              have hrestStack : restStack = [] := by
                simpa [Word.Concat] using hstack
              have htail :=
                toPDA_running_computes_sound_config hrest rfl hfinal
              rw [hrestStack] at htail
              simpa [Word.Concat] using htail
          | expand _ =>
              cases hstate

theorem toPDA_generates_of_accepts
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {w : Word terminal} (h : PDA.Accepts (ToPDA G) w) :
    w ∈ GeneratedLanguage G := by
  cases h with
  | intro q hq =>
      cases hq.left
      exact toPDA_start_computes_sound_config hq.right rfl rfl rfl

theorem toPDA_acceptedLanguage_exact
    {terminal nonterminal : Type} (G : CFG terminal nonterminal) :
    Language.Equal (PDA.AcceptedLanguage (ToPDA G)) (GeneratedLanguage G) := by
  intro w
  constructor
  · exact toPDA_generates_of_accepts
  · exact toPDA_accepts_of_generates

end CFG

end Grammars
end FoC
