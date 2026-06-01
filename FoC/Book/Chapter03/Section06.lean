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

-- Book: Chapter 3, Section 3.6, finite-alphabet universal language.
theorem finite_alphabet_universal_language_regular
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet) :
    RegularLanguage.Regular (Language.Universal : Language alpha) :=
  RegularLanguage.finite_alphabet_universal_regular alphabet halphabet

-- Book: Chapter 3, Section 3.6, Theorem 3.3.
theorem regular_expression_language_is_nfa_recognizable (r : RegExp alpha) :
    RegularLanguage.NFARecognizable (RegExp.Denote r) :=
  RegularLanguage.regular_expression_nfa_recognizable r

-- Book: Chapter 3, Section 3.6, every regular language is NFA-recognized.
theorem regular_language_is_nfa_recognizable {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.NFARecognizable L :=
  RegularLanguage.regular_is_nfa_recognizable hL

-- Book: Chapter 3, Section 3.6, every regular language is DFA-recognized.
theorem regular_language_is_dfa_recognizable {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.DFARecognizable L :=
  RegularLanguage.regular_is_dfa_recognizable hL

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

-- Book: Chapter 3, Section 3.6, NFA-to-DFA subset construction
-- with the powerset state space generated from the finite NFA state list.
theorem nfa_subset_construction_auto {state : Type} (M : NFA alpha state) :
    RegularLanguage.DFARecognizable (NFA.AcceptedLanguage M) :=
  RegularLanguage.nfa_subset_construction_auto M

-- Book: Chapter 3, Section 3.6, Theorem 3.4, state-elimination regex soundness.
theorem dfa_state_elimination_regex_sound
    (alphabet : List alpha) (M : DFA alpha state) {w : Word alpha}
    (hw : w ∈ RegExp.Denote (RegularLanguage.DFARegex alphabet M)) :
    DFA.Accepts M w :=
  RegularLanguage.dfaRegex_sound alphabet M hw

-- Book: Chapter 3, Section 3.6, Theorem 3.4, state-elimination regex completeness.
theorem dfa_state_elimination_regex_complete
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    (M : DFA alpha state) {w : Word alpha}
    (hw : DFA.Accepts M w) :
    w ∈ RegExp.Denote (RegularLanguage.DFARegex alphabet M) :=
  RegularLanguage.dfaRegex_complete alphabet M halphabet hw

-- Book: Chapter 3, Section 3.6, Theorem 3.4, DFA-recognizable languages are regular.
theorem dfa_recognizable_language_is_regular
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.Regular L :=
  RegularLanguage.dfa_recognizable_regular alphabet halphabet hL

-- Book: Chapter 3, Section 3.6, Theorem 3.4, NFA languages are regular.
theorem nfa_language_is_regular
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {state : Type} (M : NFA alpha state) :
    RegularLanguage.Regular (NFA.AcceptedLanguage M) :=
  RegularLanguage.nfa_language_regular alphabet halphabet M

-- Book: Chapter 3, Section 3.6, Theorem 3.4, NFA-recognizable languages are regular.
theorem nfa_recognizable_language_is_regular
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.NFARecognizable L) :
    RegularLanguage.Regular L :=
  RegularLanguage.nfa_recognizable_regular alphabet halphabet hL

-- Book: Chapter 3, Section 3.6, Theorem 3.5, complement regularity
-- for languages already equipped with DFA recognizers.
theorem dfa_backed_regular_languages_closed_under_complement
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.Regular (Language.Compl L) :=
  RegularLanguage.dfa_recognizable_complement_regular alphabet halphabet hL

-- Book: Chapter 3, Section 3.6, Theorem 3.5, intersection regularity
-- for languages already equipped with DFA recognizers.
theorem dfa_backed_regular_languages_closed_under_intersection
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L M : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) (hM : RegularLanguage.DFARecognizable M) :
    RegularLanguage.Regular (Language.Inter L M) :=
  RegularLanguage.dfa_recognizable_intersection_regular alphabet halphabet hL hM

-- Book: Chapter 3, Section 3.6, Theorem 3.5, complement closure over a finite alphabet.
theorem regular_languages_closed_under_complement
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.Regular L) :
    RegularLanguage.Regular (Language.Compl L) :=
  RegularLanguage.complement_regular alphabet halphabet hL

-- Book: Chapter 3, Section 3.6, Theorem 3.5, intersection closure over a finite alphabet.
theorem regular_languages_closed_under_intersection
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Inter L M) :=
  RegularLanguage.intersection_regular alphabet halphabet hL hM

/-!
Theorem 3.4, the state-elimination direction from DFA/NFA-recognized languages
to regular expressions, is now proved for DFA-recognizable languages over an
explicit finite alphabet list.  The NFA direction uses an automatic finite
powerset-state witness generated from the NFA's finite state list.
-/

end Section06
end Chapter03
end Book
end FoC
