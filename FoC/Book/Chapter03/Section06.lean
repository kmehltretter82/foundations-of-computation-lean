import FoC.Book.Chapter03.Section05
import FoC.Languages.Regular

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter03
namespace Section06

/-!
# Chapter 3, Section 3.6: Finite-State Automata and Regular Languages

This section connects the two presentations of regular languages: regular
expressions and finite automata. The statements use the reusable equivalence
machinery in {module}`FoC.Languages.Regular`, together with the DFA and NFA
constructions from the previous sections.

The section proves both directions of the equivalence. Regular expressions can
be compiled to automata, and automata can be converted back to regular
expressions. Closure theorems can then be proved using whichever representation
is more convenient.
-/

open Foundation
open Languages

/-!
## Closure by Regular Expressions

Union, concatenation, Kleene star, finite languages, and the universal finite
alphabet language are regular because the corresponding regular expressions
can be built directly.

This block uses the expression view of regularity. It shows how to construct a
regular expression for the new language once regular expressions for the input
languages are known.
-/

theorem regular_languages_closed_under_union {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Union L M) :=
  RegularLanguage.union_regular hL hM

theorem regular_languages_closed_under_concatenation {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Concat L M) :=
  RegularLanguage.concat_regular hL hM

theorem regular_languages_closed_under_kleene_star {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.Regular (Language.Star L) :=
  RegularLanguage.star_regular hL

theorem finite_language_regular (ws : List (Word alpha)) :
    RegularLanguage.Regular (fun w => w ∈ ws) :=
  RegularLanguage.finite_list_regular ws

theorem finite_alphabet_universal_language_regular
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet) :
    RegularLanguage.Regular (Language.Universal : Language alpha) :=
  RegularLanguage.finite_alphabet_universal_regular alphabet halphabet

theorem regular_languages_closed_under_reversal {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.Regular (Language.Reverse L) :=
  RegularLanguage.reverse_regular hL

/-!
## From Expressions to Automata

Theorem 3.3 is represented by the NFA-recognizability of every regular
expression language. The subset construction then gives DFA recognizers.

This is the compiler direction: parse a regular expression into an NFA, then
determinize the NFA when a deterministic machine is needed.
-/

theorem regular_expression_language_is_nfa_recognizable (r : RegExp alpha) :
    RegularLanguage.NFARecognizable (RegExp.Denote r) :=
  RegularLanguage.regular_expression_nfa_recognizable r

theorem regular_language_is_nfa_recognizable {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.NFARecognizable L :=
  RegularLanguage.regular_is_nfa_recognizable hL

theorem regular_language_is_dfa_recognizable {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.DFARecognizable L :=
  RegularLanguage.regular_is_dfa_recognizable hL

theorem theorem_regex_to_nfa (r : RegExp alpha) :
    RegularLanguage.NFARecognizable (RegExp.Denote r) :=
  regular_expression_language_is_nfa_recognizable r

theorem theorem_regular_to_dfa {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    RegularLanguage.DFARecognizable L :=
  regular_language_is_dfa_recognizable hL

theorem aStarBStar_nfa_recognizable :
    RegularLanguage.NFARecognizable (RegExp.Denote Section02.aStarBStar) :=
  theorem_regex_to_nfa Section02.aStarBStar

theorem oneToThreeAsThenEvenBs_nfa_recognizable :
    RegularLanguage.NFARecognizable
      (RegExp.Denote Section02.oneToThreeAsThenEvenBs) :=
  theorem_regex_to_nfa Section02.oneToThreeAsThenEvenBs

theorem dfa_recognizable_closed_under_complement {L : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.DFARecognizable (Language.Compl L) :=
  RegularLanguage.dfa_recognizable_complement hL

theorem dfa_recognizable_closed_under_union {L M : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) (hM : RegularLanguage.DFARecognizable M) :
    RegularLanguage.DFARecognizable (Language.Union L M) :=
  RegularLanguage.dfa_recognizable_union hL hM

theorem dfa_recognizable_closed_under_intersection {L M : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) (hM : RegularLanguage.DFARecognizable M) :
    RegularLanguage.DFARecognizable (Language.Inter L M) :=
  RegularLanguage.dfa_recognizable_intersection hL hM

theorem dfa_recognizable_closed_under_difference {L M : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) (hM : RegularLanguage.DFARecognizable M) :
    RegularLanguage.DFARecognizable (Language.Diff L M) :=
  RegularLanguage.dfa_recognizable_difference hL hM

theorem dfa_recognizable_is_nfa_recognizable {L : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.NFARecognizable L :=
  RegularLanguage.dfa_recognizable_is_nfa_recognizable hL

theorem nfa_subset_construction {state : Type} (M : NFA alpha state)
    (subsetsFinite : FiniteType (FSet state)) :
    RegularLanguage.DFARecognizable (NFA.AcceptedLanguage M) :=
  RegularLanguage.nfa_subset_construction M subsetsFinite

theorem nfa_subset_construction_auto {state : Type} (M : NFA alpha state) :
    RegularLanguage.DFARecognizable (NFA.AcceptedLanguage M) :=
  RegularLanguage.nfa_subset_construction_auto M

/-!
## From Automata to Expressions

State elimination supplies a regular expression for every DFA language over an
explicit finite alphabet list. This completes the equivalence between regular
languages and finite automata.

The finite alphabet list is an explicit hypothesis because the construction
must build expressions that account for every symbol a transition may read.
-/

theorem dfa_state_elimination_regex_sound
    (alphabet : List alpha) (M : DFA alpha state) {w : Word alpha}
    (hw : w ∈ RegExp.Denote (RegularLanguage.DFARegex alphabet M)) :
    DFA.Accepts M w :=
  RegularLanguage.dfaRegex_sound alphabet M hw

theorem dfa_state_elimination_regex_complete
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    (M : DFA alpha state) {w : Word alpha}
    (hw : DFA.Accepts M w) :
    w ∈ RegExp.Denote (RegularLanguage.DFARegex alphabet M) :=
  RegularLanguage.dfaRegex_complete alphabet M halphabet hw

theorem dfa_recognizable_language_is_regular
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.Regular L :=
  RegularLanguage.dfa_recognizable_regular alphabet halphabet hL

theorem nfa_language_is_regular
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {state : Type} (M : NFA alpha state) :
    RegularLanguage.Regular (NFA.AcceptedLanguage M) :=
  RegularLanguage.nfa_language_regular alphabet halphabet M

theorem nfa_recognizable_language_is_regular
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.NFARecognizable L) :
    RegularLanguage.Regular L :=
  RegularLanguage.nfa_recognizable_regular alphabet halphabet hL

theorem theorem_dfa_to_regex
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.Regular L :=
  dfa_recognizable_language_is_regular alphabet halphabet hL

theorem theorem_nfa_to_regex
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.NFARecognizable L) :
    RegularLanguage.Regular L :=
  nfa_recognizable_language_is_regular alphabet halphabet hL

theorem regular_iff_dfa_recognizable_over_finite_alphabet
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    (L : Language alpha) :
    RegularLanguage.Regular L <-> RegularLanguage.DFARecognizable L := by
  constructor
  · exact regular_language_is_dfa_recognizable
  · exact dfa_recognizable_language_is_regular alphabet halphabet

theorem regular_iff_nfa_recognizable_over_finite_alphabet
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    (L : Language alpha) :
    RegularLanguage.Regular L <-> RegularLanguage.NFARecognizable L := by
  constructor
  · exact regular_language_is_nfa_recognizable
  · exact nfa_recognizable_language_is_regular alphabet halphabet

/-!
## Complement and Intersection

Theorem 3.5 is formalized through DFA-backed closure first, then transported
back to regular languages using the automata-expression equivalence.

Complement and intersection are easiest at the automaton level: flip accepting
states for complement, and run machines in parallel for intersection. The final
regular-language theorems transfer those constructions back to the expression
definition of regularity.
-/

theorem dfa_backed_regular_languages_closed_under_complement
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.DFARecognizable L) :
    RegularLanguage.Regular (Language.Compl L) :=
  RegularLanguage.dfa_recognizable_complement_regular alphabet halphabet hL

theorem dfa_backed_regular_languages_closed_under_intersection
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L M : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) (hM : RegularLanguage.DFARecognizable M) :
    RegularLanguage.Regular (Language.Inter L M) :=
  RegularLanguage.dfa_recognizable_intersection_regular alphabet halphabet hL hM

theorem dfa_backed_regular_languages_closed_under_difference
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L M : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) (hM : RegularLanguage.DFARecognizable M) :
    RegularLanguage.Regular (Language.Diff L M) :=
  RegularLanguage.dfa_recognizable_difference_regular alphabet halphabet hL hM

theorem regular_languages_closed_under_complement
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L : Language alpha} (hL : RegularLanguage.Regular L) :
    RegularLanguage.Regular (Language.Compl L) :=
  RegularLanguage.complement_regular alphabet halphabet hL

theorem regular_languages_closed_under_intersection
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Inter L M) :=
  RegularLanguage.intersection_regular alphabet halphabet hL hM

theorem regular_languages_closed_under_difference
    (alphabet : List alpha) (halphabet : forall a, a ∈ alphabet)
    {L M : Language alpha}
    (hL : RegularLanguage.Regular L) (hM : RegularLanguage.Regular M) :
    RegularLanguage.Regular (Language.Diff L M) :=
  RegularLanguage.difference_regular alphabet halphabet hL hM

end Section06
end Chapter03
end Book
end FoC
