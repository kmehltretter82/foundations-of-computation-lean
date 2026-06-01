import FoC.Book.Chapter03.Section05
import FoC.Languages.Regular

namespace FoC
namespace Book
namespace Chapter03
namespace Section06

/-!
Book: Chapter 3, Section 3.6, Finite-State Automata and Regular Languages.
-/

open Foundation
open Languages

-- Book: Chapter 3, Section 3.6, regular-expression closure under union.
theorem regular_languages_closed_under_union {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Union L M) :=
  RegularLanguage.union_regular hL hM

-- Book: Chapter 3, Section 3.6, regular-expression closure under concatenation.
theorem regular_languages_closed_under_concatenation {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Concat L M) :=
  RegularLanguage.concat_regular hL hM

-- Book: Chapter 3, Section 3.6, regular-expression closure under Kleene star.
theorem regular_languages_closed_under_kleene_star {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.Regular (Language.Star L) :=
  RegularLanguage.star_regular hL

-- Book: Chapter 3, Section 3.6, finite languages are regular.
theorem finite_language_regular (ws : List (Word alpha)) :
    RegularLanguage.Regular (fun w => w ∈ ws) :=
  RegularLanguage.finite_list_regular ws

-- Book: Chapter 3, Section 3.6, Theorem 3.3.
theorem regular_expression_language_is_nfa_recognizable (r : RegExp alpha) :
    RegularLanguage.NFARecognizable (RegExp.Denote r) :=
  RegularLanguage.regular_expression_nfa_recognizable r

-- Book: Chapter 3, Section 3.6, every regular language is NFA-recognized.
theorem regular_language_is_nfa_recognizable {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.NFARecognizable L :=
  RegularLanguage.regular_is_nfa_recognizable hL

-- Book: Chapter 3, Section 3.6, DFA-recognizable languages are closed under complement.
theorem dfa_recognizable_closed_under_complement {L : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.DFARecognizable (Language.Compl L) :=
  RegularLanguage.dfa_recognizable_complement hL

-- Book: Chapter 3, Section 3.6, DFA-recognizable languages are closed under union.
theorem dfa_recognizable_closed_under_union {L M : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) (hM : RegularLanguage.DFARecognizable M) :
    RegularLanguage.DFARecognizable (Language.Union L M) :=
  RegularLanguage.dfa_recognizable_union hL hM

-- Book: Chapter 3, Section 3.6, DFA-recognizable languages are closed under intersection.
theorem dfa_recognizable_closed_under_intersection {L M : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) (hM : RegularLanguage.DFARecognizable M) :
    RegularLanguage.DFARecognizable (Language.Inter L M) :=
  RegularLanguage.dfa_recognizable_intersection hL hM

-- Book: Chapter 3, Section 3.6, every DFA-recognized language is NFA-recognized.
theorem dfa_recognizable_is_nfa_recognizable {L : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.NFARecognizable L :=
  RegularLanguage.dfa_recognizable_is_nfa_recognizable hL

-- Book: Chapter 3, Section 3.6, NFA-to-DFA subset construction.
theorem nfa_subset_construction {state : Type} (M : NFA alpha state)
    (subsetsFinite : FiniteType (FSet state)) :
    RegularLanguage.DFARecognizable (NFA.AcceptedLanguage M) :=
  RegularLanguage.nfa_subset_construction M subsetsFinite

/-!
Theorem 3.4, the state-elimination direction from DFA/NFA-recognized languages
to regular expressions, is not asserted as a global premise.  The formal core
currently contains the Thompson construction, subset construction, and
regular-expression closure laws that feed that theorem.
-/

end Section06
end Chapter03
end Book
end FoC
