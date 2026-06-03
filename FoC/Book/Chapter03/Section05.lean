import FoC.Book.Chapter03.Section04
import FoC.Languages.NFA

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
-/

open Foundation
open Languages

/-!
## NFA Acceptance

The acceptance predicate says that some reachable state is accepting after the
whole word is read. The DFA embedding theorem states that deterministic
machines are a special case of NFAs with the same language.
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
## Subset Construction

The subset construction turns an NFA into a DFA whose states are sets of NFA
states. The run invariant is stated first, then the language-equivalence
theorem follows.
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
