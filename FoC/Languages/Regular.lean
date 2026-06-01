import FoC.Languages.RegularExpression
import FoC.Languages.NFA
import FoC.Languages.Thompson

namespace FoC
namespace Languages

/-!
Regular-language vocabulary and closure theorems.

Used by:
- Chapter 3, Section 3.2: definition of regular language
- Chapter 3, Section 3.6: closure properties and automata comparison
-/

namespace RegularLanguage

def Regular (L : Language alpha) : Prop :=
  RegExp.Regular L

def DFARecognizable (L : Language alpha) : Prop :=
  DFA.Recognizable L

def NFARecognizable (L : Language alpha) : Prop :=
  NFA.Recognizable L

theorem empty_regular : Regular (Language.Empty : Language alpha) :=
  RegExp.regular_empty

theorem epsilon_regular : Regular (Language.Singleton (Word.Empty : Word alpha)) :=
  RegExp.regular_epsilon

theorem symbol_regular (a : alpha) : Regular (Language.Singleton (Word.Symbol a)) :=
  RegExp.regular_symbol a

theorem union_regular {L M : Language alpha}
    (hL : Regular L) (hM : Regular M) : Regular (Language.Union L M) :=
  RegExp.regular_union hL hM

theorem concat_regular {L M : Language alpha}
    (hL : Regular L) (hM : Regular M) : Regular (Language.Concat L M) :=
  RegExp.regular_concat hL hM

theorem star_regular {L : Language alpha} (hL : Regular L) : Regular (Language.Star L) :=
  RegExp.regular_star hL

theorem finite_list_regular (ws : List (Word alpha)) :
    Regular (fun w => w ∈ ws) :=
  RegExp.finite_language_regular ws

theorem dfa_recognizable_is_nfa_recognizable {L : Language alpha}
    (hL : DFARecognizable L) : NFARecognizable L :=
  NFA.dfa_language_nfa_recognizable hL

theorem regular_expression_nfa_recognizable (r : RegExp alpha) :
    NFARecognizable (RegExp.Denote r) :=
  Thompson.regularExpression_nfa r

theorem regular_is_nfa_recognizable {L : Language alpha}
    (hL : Regular L) : NFARecognizable L := by
  cases hL with
  | intro r hr =>
      cases regular_expression_nfa_recognizable r with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              exists state
              exists M
              exact Language.equal_trans hM hr

theorem dfa_recognizable_complement {L : Language alpha}
    (hL : DFARecognizable L) : DFARecognizable (Language.Compl L) :=
  DFA.recognizable_complement hL

theorem dfa_recognizable_union {L M : Language alpha}
    (hL : DFARecognizable L) (hM : DFARecognizable M) :
    DFARecognizable (Language.Union L M) :=
  DFA.recognizable_union hL hM

theorem dfa_recognizable_intersection {L M : Language alpha}
    (hL : DFARecognizable L) (hM : DFARecognizable M) :
    DFARecognizable (Language.Inter L M) :=
  DFA.recognizable_intersection hL hM

theorem nfa_subset_construction {state : Type} (M : NFA alpha state)
    (subsetsFinite : Foundation.FiniteType (Foundation.FSet state)) :
    DFARecognizable (NFA.AcceptedLanguage M) :=
  NFA.nfa_language_dfa_recognizable M subsetsFinite

/-!
The book's full theorem that every DFA- or NFA-recognized language is generated
by a regular expression requires the state-elimination construction.  The
standalone development has the vocabulary and finite-state subset construction
in place; the state-elimination proof is intentionally not represented here as
an unproved global premise.
-/

end RegularLanguage
end Languages
end FoC
