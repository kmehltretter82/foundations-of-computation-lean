import FoC.Grammars.RightRegular

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section01

open Foundation
open Languages
open Grammars

/-!
# Context-Free Grammar Laws and Language Classes

This module records the chapter-facing derivation laws, context-free and regular grammar language predicates, reversal construction, and the regular-language boundary inclusions.
-/

/-!
## Derivations

One-step yields generate multi-step derivations, derivations compose, and both
notions are stable under adding sentential-form context around the rewritten
substring.

A one-step yield applies one production in one surrounding context. A
derivation is any finite chain of such steps. The context lemmas are what let a
local production be used inside a longer sentential form.
-/

theorem yields_implies_derives {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : CFG.Yields G x y) :
    CFG.Derives G x y :=
  CFG.yields_derives h

theorem derives_transitive {G : CFG terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : CFG.Derives G x y) (hyz : CFG.Derives G y z) :
    CFG.Derives G x z :=
  CFG.derives_trans hxy hyz

theorem yields_inside_context {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Yields G x y) (s t : SententialForm terminal nonterminal) :
    CFG.Yields G (s ++ x ++ t) (s ++ y ++ t) :=
  CFG.yields_context h s t

theorem derives_inside_context {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Derives G x y) (s t : SententialForm terminal nonterminal) :
    CFG.Derives G (s ++ x ++ t) (s ++ y ++ t) :=
  CFG.derives_context h s t

/-!
## Language Classes

The next definitions name the book-facing classes: context-free languages,
right-regular languages, and left-regular languages. These are thin wrappers
over the reusable grammar definitions.

These wrappers keep the section close to the book's terminology while the
implementation lives in the reusable grammar library.
-/

def ContextFreeLanguage (L : Language terminal) : Prop :=
  CFL.ContextFreeLanguage L

def RightRegularLanguage (L : Language terminal) : Prop :=
  CFG.RightRegularLanguage L

def LeftRegularLanguage (L : Language terminal) : Prop :=
  CFG.LeftRegularLanguage L

def ReverseGrammar (G : CFG terminal nonterminal) : CFG terminal nonterminal :=
  CFG.ReverseGrammar G

/-!
## Reversal and Regular Grammars

Reversing productions reverses the generated language. This relates left- and
right-regular grammars, and connects both regular-grammar forms with regular
languages over an explicit finite alphabet list.

The explicit alphabet hypothesis appears when a regular grammar is converted
back into a regular expression or automaton-style regular-language statement.
-/

theorem reverse_grammar_language_exact (G : CFG terminal nonterminal) :
    Language.Equal (CFG.GeneratedLanguage (ReverseGrammar G))
      (Language.Reverse (CFG.GeneratedLanguage G)) :=
  CFG.reverseGrammar_language_exact G

theorem reverse_grammar_has_finite_productions
    {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    CFG.HasFiniteProductions (ReverseGrammar G) :=
  CFG.reverseGrammar_hasFiniteProductions hG

theorem context_free_languages_closed_under_reversal {L : Language terminal}
    (hL : ContextFreeLanguage L) :
    ContextFreeLanguage (Language.Reverse L) :=
  CFL.reverse_context_free hL

theorem left_regular_reverse_right_regular {L : Language terminal}
    (hL : LeftRegularLanguage L) :
    RightRegularLanguage (Language.Reverse L) :=
  CFG.leftRegularLanguage_reverse_rightRegular hL

theorem right_regular_reverse_left_regular {L : Language terminal}
    (hL : RightRegularLanguage L) :
    LeftRegularLanguage (Language.Reverse L) :=
  CFG.rightRegularLanguage_reverse_leftRegular hL

theorem left_regular_iff_reverse_right_regular {L : Language terminal} :
    LeftRegularLanguage L <-> RightRegularLanguage (Language.Reverse L) :=
  CFG.leftRegularLanguage_iff_reverse_rightRegular

theorem regular_languages_are_left_regular {L : Language terminal}
    (hL : RegularLanguage.Regular L) :
    LeftRegularLanguage L :=
  CFG.regular_leftRegularLanguage hL

theorem left_regular_languages_are_regular
    (alphabet : List terminal) (halphabet : forall a, a ∈ alphabet)
    {L : Language terminal} (hL : LeftRegularLanguage L) :
    RegularLanguage.Regular L :=
  CFG.leftRegularLanguage_regular alphabet halphabet hL

theorem regular_iff_left_regular_language
    (alphabet : List terminal) (halphabet : forall a, a ∈ alphabet)
    {L : Language terminal} :
    RegularLanguage.Regular L <-> LeftRegularLanguage L :=
  CFG.regular_iff_leftRegularLanguage alphabet halphabet

theorem nfa_right_regular_grammar_language_exact {state : Type}
    (M : NFA terminal state) :
    Language.Equal (CFG.GeneratedLanguage (CFG.NFARightRegularGrammar M))
      (NFA.AcceptedLanguage M) :=
  CFG.nfaRightRegularGrammar_language_exact M

theorem regular_languages_are_right_regular {L : Language terminal}
    (hL : RegularLanguage.Regular L) :
    RightRegularLanguage L :=
  CFG.regular_rightRegularLanguage hL

theorem right_regular_languages_are_regular
    (alphabet : List terminal) (halphabet : forall a, a ∈ alphabet)
    {L : Language terminal} (hL : RightRegularLanguage L) :
    RegularLanguage.Regular L :=
  CFG.rightRegularLanguage_regular alphabet halphabet hL

theorem regular_iff_right_regular_language
    (alphabet : List terminal) (halphabet : forall a, a ∈ alphabet)
    {L : Language terminal} :
    RegularLanguage.Regular L <-> RightRegularLanguage L :=
  CFG.regular_iff_rightRegularLanguage alphabet halphabet

/-!
## Regular Languages are Context-Free

Theorem 4.4's punchline needs one more ingredient beyond exactness of the
NFA-to-grammar construction: the constructed grammar must have finitely many
productions, because the book-facing {lit}`ContextFreeLanguage` predicate
carries a finite-production witness. Over a covering alphabet list, the
finite NFA presentation supplies that witness, and every regular language is
context-free.
-/

theorem nfa_right_regular_grammar_has_finite_productions {state : Type}
    (alphabet : List terminal) (halphabet : forall a, a ∈ alphabet)
    (M : NFA terminal state) :
    CFG.HasFiniteProductions (CFG.NFARightRegularGrammar M) :=
  CFG.nfaRightRegularGrammar_hasFiniteProductions alphabet halphabet M

theorem regular_languages_are_context_free
    (alphabet : List terminal) (halphabet : forall a, a ∈ alphabet)
    {L : Language terminal} (hL : RegularLanguage.Regular L) :
    ContextFreeLanguage L :=
  CFG.regular_contextFreeLanguage alphabet halphabet hL

end Section01
end Chapter04
end Book
end FoC
