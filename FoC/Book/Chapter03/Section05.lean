import FoC.Book.Chapter03.Section04
import FoC.Languages.NFA

namespace FoC
namespace Book
namespace Chapter03
namespace Section05

/-!
Book: Chapter 3, Section 3.5, Nondeterministic Finite-State Automata.
-/

open Foundation
open Languages

-- Book: Chapter 3, Section 3.5, Definition 3.7.
theorem epsilon_closure_contains_start_set
    (M : NFA alpha state) (S : FSet state) {q : state} (hq : q ∈ S) :
    q ∈ NFA.EpsilonClosure M S :=
  NFA.epsilonClosure_contains hq

-- Book: Chapter 3, Section 3.5, Definition 3.8.
theorem nfa_acceptance_definition (M : NFA alpha state) (w : Word alpha) :
    NFA.Accepts M w <-> exists q, q ∈ NFA.Reach M w ∧ M.accept q :=
  Iff.rfl

-- Book: Chapter 3, Section 3.5, language accepted by an NFA.
theorem nfa_language_membership (M : NFA alpha state) (w : Word alpha) :
    w ∈ NFA.AcceptedLanguage M <-> NFA.Accepts M w :=
  Iff.rfl

-- Book: Chapter 3, Section 3.5, every DFA can be viewed as an NFA.
theorem dfa_as_nfa_same_language (M : DFA alpha state) :
    Language.Equal (NFA.AcceptedLanguage (NFA.FromDFA M)) (DFA.Language M) :=
  NFA.fromDFA_language M

-- Book: Chapter 3, Section 3.5, every DFA-recognized language is NFA-recognized.
theorem dfa_recognizable_implies_nfa_recognizable {L : Language alpha}
    (hL : DFA.Recognizable L) : NFA.Recognizable L :=
  NFA.dfa_language_nfa_recognizable hL

-- Book: Chapter 3, Section 3.5, subset construction run invariant.
theorem subset_construction_run
    (M : NFA alpha state) (subsetsFinite : FiniteType (FSet state))
    (S : FSet state) (w : Word alpha) :
    DFA.RunFrom (NFA.SubsetDFA M subsetsFinite) S w = NFA.ReachFromSet M S w :=
  NFA.subsetDFA_runFrom M subsetsFinite S w

-- Book: Chapter 3, Section 3.5, Theorem 3.2, subset construction equivalence
-- for NFAs whose powerset state space is explicitly enumerated.
theorem subset_construction_accepts_same_language
    {state : Type} (M : NFA alpha state) (subsetsFinite : FiniteType (FSet state)) :
    Language.Equal (DFA.Language (NFA.SubsetDFA M subsetsFinite)) (NFA.AcceptedLanguage M) :=
  NFA.subsetDFA_language M subsetsFinite

end Section05
end Chapter03
end Book
end FoC
