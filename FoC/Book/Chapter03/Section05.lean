import FoC.Book.Chapter03.Section04
import FoC.Languages.NFAPath

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter03
namespace Section05

/-!
# Chapter 3, Section 3.5: Nondeterministic Finite-State Automata

Nondeterministic automata use sets of possible states rather than a single
current state. This page records epsilon-closure, reachability acceptance, the
DFA-to-NFA embedding, and the subset construction from {module}`FoC.Languages.NFA`.

The formal model does not choose one branch of the computation. Instead, after
reading a word it computes the set of all states that could be reached. The NFA
accepts if at least one reachable state is accepting.
-/

open Foundation
open Languages

/-!
## NFA Acceptance

The acceptance predicate says that some reachable state is accepting after the
whole word is read. The DFA embedding theorem states that deterministic
machines are a special case of NFAs with the same language.

Epsilon closure accounts for moves that consume no input. The acceptance
definition packages both ordinary input-consuming moves and epsilon moves into
one reachability predicate.
-/

theorem epsilon_closure_contains_start_set
    (M : NFA alpha state) (S : FSet state) {q : state} (hq : q ∈ S) :
    q ∈ NFA.EpsilonClosure M S :=
  NFA.epsilonClosure_contains hq

theorem nfa_acceptance_definition (M : NFA alpha state) (w : Word alpha) :
    NFA.Accepts M w <-> exists q, q ∈ NFA.Reach M w ∧ M.accept q :=
  Iff.rfl

theorem nfa_language_membership (M : NFA alpha state) (w : Word alpha) :
    w ∈ NFA.AcceptedLanguage M <-> NFA.Accepts M w :=
  Iff.rfl

theorem dfa_as_nfa_same_language (M : DFA alpha state) :
    Language.Equal (NFA.AcceptedLanguage (NFA.FromDFA M)) (DFA.Language M) :=
  NFA.fromDFA_language M

theorem dfa_recognizable_implies_nfa_recognizable {L : Language alpha}
    (hL : DFA.Recognizable L) : NFA.Recognizable L :=
  NFA.dfa_language_nfa_recognizable hL

/-!
## A Concrete Epsilon-NFA

This two-state NFA accepts exactly the empty word by taking one epsilon
transition from the start state to the accepting state. It is intentionally
small: the point is to expose the explicit path semantics and show how it
matches the set-of-states acceptance predicate.
-/

inductive EpsilonOnlyState where
  | start
  | accept
deriving DecidableEq

def EpsilonOnlyStateFinite : FiniteType EpsilonOnlyState where
  elems := [EpsilonOnlyState.start, EpsilonOnlyState.accept]
  complete := by
    intro q
    cases q <;> simp

def epsilonOnlyNFA : NFA Section01.AB EpsilonOnlyState where
  start := EpsilonOnlyState.start
  step := fun q input =>
    match q, input with
    | EpsilonOnlyState.start, none => FSet.Singleton EpsilonOnlyState.accept
    | _, _ => FSet.Empty
  accept := fun q => q = EpsilonOnlyState.accept
  statesFinite := EpsilonOnlyStateFinite

theorem epsilonOnlyNFA_path_accepts_empty :
    NFA.PathAccepts epsilonOnlyNFA Word.Empty := by
  exists EpsilonOnlyState.accept
  constructor
  · exact NFA.Path.eps rfl (NFA.Path.nil EpsilonOnlyState.accept)
  · rfl

theorem epsilonOnlyNFA_path_word_empty
    {q r : EpsilonOnlyState} {w : Word Section01.AB}
    (hpath : NFA.Path epsilonOnlyNFA q w r) :
    w = Word.Empty := by
  induction hpath with
  | nil _ =>
      rfl
  | eps _ _ ih =>
      exact ih
  | sym hstep _ _ =>
      cases q <;> simp [epsilonOnlyNFA] at hstep <;> cases hstep

theorem epsilonOnlyNFA_language_exact (w : Word Section01.AB) :
    w ∈ NFA.AcceptedLanguage epsilonOnlyNFA <-> w = Word.Empty := by
  constructor
  · intro hw
    have hpath := (NFA.pathAccepts_iff_accepts epsilonOnlyNFA w).mpr hw
    rcases hpath with ⟨q, hq, _haccept⟩
    exact epsilonOnlyNFA_path_word_empty hq
  · intro hw
    rw [hw]
    exact (NFA.pathAccepts_iff_accepts epsilonOnlyNFA Word.Empty).mp
      epsilonOnlyNFA_path_accepts_empty

theorem epsilonOnlyNFA_rejects_a :
    ¬ NFA.Accepts epsilonOnlyNFA [Section01.AB.a] := by
  intro h
  have hword := (epsilonOnlyNFA_language_exact [Section01.AB.a]).mp h
  cases hword

/-!
## Subset Construction

The subset construction turns an NFA into a DFA whose states are sets of NFA
states. The run invariant is stated first, then the language-equivalence
theorem comes next.

The deterministic state remembers the whole set of possible NFA states. The
run invariant says that this memory is exact after every input word, which is
why the constructed DFA recognizes the same language.
-/

theorem subset_construction_run
    (M : NFA alpha state) (subsetsFinite : FiniteType (FSet state))
    (S : FSet state) (w : Word alpha) :
    DFA.RunFrom (NFA.SubsetDFA M subsetsFinite) S w = NFA.ReachFromSet M S w :=
  NFA.subsetDFA_runFrom M subsetsFinite S w

theorem subset_construction_accepts_same_language
    {state : Type} (M : NFA alpha state) (subsetsFinite : FiniteType (FSet state)) :
    Language.Equal (DFA.Language (NFA.SubsetDFA M subsetsFinite)) (NFA.AcceptedLanguage M) :=
  NFA.subsetDFA_language M subsetsFinite

end Section05
end Chapter03
end Book
end FoC
