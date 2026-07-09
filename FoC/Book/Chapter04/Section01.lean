import FoC.Grammars.RightRegular

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section01

/-!
# Chapter 4, Section 4.1: Context-Free Grammars

This section introduces context-free grammars, derivations, context-free
languages, and the regular-grammar boundary. The reusable grammar API is in
{module}`FoC.Grammars.CFG`, {module}`FoC.Grammars.CFL`, and
{module}`FoC.Grammars.RightRegular`.

The central idea is that a grammar generates a language by repeatedly
rewriting nonterminals until only terminals remain. The early declarations name
the derivation relation; the later ones show how grammar constructions produce
language closure theorems and concrete examples.
-/

open Foundation
open Languages
open Grammars

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

/-!
## Closure of CFLs

The closure theorems for union, concatenation, and Kleene star are proved by
constructing new grammars and then showing their generated languages are exact.

Each construction has two kinds of theorem: generation lemmas saying how to
build words in the new grammar, and inverse lemmas saying every generated word
has the expected language-theoretic shape.
-/

theorem union_grammar_generates_left (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage G) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFG.union_generates_left G H hw

theorem union_grammar_generates_right (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage H) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFG.union_generates_right G H hw

theorem union_grammar_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H)) :
    w ∈ Language.Union (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.union_generates_inv G H h

theorem union_grammar_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) <->
      w ∈ Language.Union (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.union_generated_language_exact G H w

theorem context_free_languages_closed_under_union {L M : Language terminal}
    (hL : ContextFreeLanguage L) (hM : ContextFreeLanguage M) :
    ContextFreeLanguage (Language.Union L M) :=
  CFL.union_context_free hL hM

theorem concat_grammar_generates (G : CFG terminal left) (H : CFG terminal right)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G) (hy : y ∈ CFG.GeneratedLanguage H) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) :=
  CFG.concat_generates G H hx hy

theorem concat_grammar_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H)) :
    w ∈ Language.Concat (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.concat_generates_inv G H h

theorem concat_grammar_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) <->
      w ∈ Language.Concat (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.concat_generated_language_exact G H w

theorem context_free_languages_closed_under_concatenation {L M : Language terminal}
    (hL : ContextFreeLanguage L) (hM : ContextFreeLanguage M) :
    ContextFreeLanguage (Language.Concat L M) :=
  CFL.concat_context_free hL hM

theorem star_grammar_generates_empty (G : CFG terminal nt) :
    ([] : Word terminal) ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFG.star_generates_empty G

theorem star_grammar_generates_cons (G : CFG terminal nt)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G)
    (hy : y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFG.star_generates_cons G hx hy

theorem star_grammar_generates_inv (G : CFG terminal nt) {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    w ∈ Language.Star (CFG.GeneratedLanguage G) :=
  CFG.star_generates_inv G h

theorem star_grammar_language_exact (G : CFG terminal nt) (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) <->
      w ∈ Language.Star (CFG.GeneratedLanguage G) :=
  CFG.star_generated_language_exact G w

theorem context_free_languages_closed_under_kleene_star {L : Language terminal}
    (hL : ContextFreeLanguage L) :
    ContextFreeLanguage (Language.Star L) :=
  CFL.star_context_free hL

/-!
## Concrete Grammar Examples

The remaining code in this section builds exact grammar examples, beginning
with balanced parentheses. The helper soundness principles let a grammar proof
be checked by giving a semantic interpretation to each symbol.

For examples, the formalization often proves exactness by assigning a language
meaning to each nonterminal. Every production must be sound for that meaning,
and derivation soundness then follows for the generated language.
-/

theorem form_language_yields_sound_of_productions
    {G : CFG terminal nonterminal}
    {symbolLanguage : Symbol terminal nonterminal -> Language terminal}
    (hprod : forall A rhs,
      G.produces A rhs ->
        forall w, w ∈ CFG.FormLanguage symbolLanguage rhs ->
          w ∈ symbolLanguage (Symbol.nonterminal A))
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Yields G x y)
    (hw : w ∈ CFG.FormLanguage symbolLanguage y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  rcases h with ⟨u, v, A, rhs, hA, hx, hy⟩
  rw [hy] at hw
  rw [hx]
  exact CFG.formLanguage_replace_sound symbolLanguage (hprod A rhs hA) hw

theorem form_language_derives_sound_of_productions
    {G : CFG terminal nonterminal}
    {symbolLanguage : Symbol terminal nonterminal -> Language terminal}
    (hprod : forall A rhs,
      G.produces A rhs ->
        forall w, w ∈ CFG.FormLanguage symbolLanguage rhs ->
          w ∈ symbolLanguage (Symbol.nonterminal A))
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Derives G x y)
    (hw : w ∈ CFG.FormLanguage symbolLanguage y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  induction h with
  | refl _ =>
      exact hw
  | step hstep _ ih =>
      exact form_language_yields_sound_of_productions hprod hstep (ih hw)

/-!
The first concrete grammar example is balanced parentheses with one bracket
kind. The proof shows both directions: each production preserves the inductive
balanced-parentheses language, and every inductively balanced word is generated
by the grammar.
-/

inductive Paren where
  | left : Paren
  | right : Paren
deriving DecidableEq

inductive BalancedParensNT where
  | S : BalancedParensNT
deriving DecidableEq

def Paren.finite : FiniteType Paren where
  elems := [Paren.left, Paren.right]
  complete := by
    intro x
    cases x <;> simp

def BalancedParensNT.finite : FiniteType BalancedParensNT where
  elems := [BalancedParensNT.S]
  complete := by
    intro x
    cases x
    simp

inductive BalancedParensProduces :
    BalancedParensNT -> SententialForm Paren BalancedParensNT -> Prop where
  | empty :
      BalancedParensProduces BalancedParensNT.S []
  | pair :
      BalancedParensProduces BalancedParensNT.S
        [Symbol.terminal Paren.left,
          Symbol.nonterminal BalancedParensNT.S,
          Symbol.terminal Paren.right,
          Symbol.nonterminal BalancedParensNT.S]

def BalancedParensGrammar : CFG Paren BalancedParensNT where
  start := BalancedParensNT.S
  produces := BalancedParensProduces
  nonterminalsFinite := BalancedParensNT.finite

inductive BalancedParens : Word Paren -> Prop where
  | empty : BalancedParens []
  | pair {inside rest : Word Paren} :
      BalancedParens inside ->
        BalancedParens rest ->
          BalancedParens
            (Paren.left :: Word.Concat inside (Paren.right :: rest))

def BalancedParensSymbolLanguage :
    Symbol Paren BalancedParensNT -> Language Paren
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal BalancedParensNT.S => BalancedParens

def balancedParensEmptyProduction :
    CFG.Production Paren BalancedParensNT where
  lhs := BalancedParensNT.S
  rhs := []

def balancedParensPairProduction :
    CFG.Production Paren BalancedParensNT where
  lhs := BalancedParensNT.S
  rhs :=
    [Symbol.terminal Paren.left,
      Symbol.nonterminal BalancedParensNT.S,
      Symbol.terminal Paren.right,
      Symbol.nonterminal BalancedParensNT.S]

theorem balanced_parens_has_finite_productions :
    CFG.HasFiniteProductions BalancedParensGrammar := by
  exists [balancedParensEmptyProduction, balancedParensPairProduction]
  intro A rhs
  constructor
  · intro h
    cases h with
    | empty =>
        exact ⟨balancedParensEmptyProduction, by simp [balancedParensEmptyProduction],
          rfl, rfl⟩
    | pair =>
        exact ⟨balancedParensPairProduction,
          by simp [balancedParensPairProduction], rfl, rfl⟩
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [balancedParensEmptyProduction, balancedParensPairProduction] at hmem
    rcases hmem with hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact BalancedParensProduces.empty
    · subst rule
      cases hlhs
      cases hrhs
      exact BalancedParensProduces.pair

/-!
For soundness, the pair production is the only nontrivial case. Membership in
the form language splits the generated word into the left terminal, the inside
word, the right terminal, and the remaining balanced suffix.
-/

theorem balanced_parens_pair_form_language
    {w : Word Paren}
    (hw : w ∈ CFG.FormLanguage BalancedParensSymbolLanguage
      [Symbol.terminal Paren.left,
        Symbol.nonterminal BalancedParensNT.S,
        Symbol.terminal Paren.right,
        Symbol.nonterminal BalancedParensNT.S]) :
    BalancedParens w := by
  rcases hw with ⟨leftWord, tail1, hleft, htail1, hwEq⟩
  cases hleft
  rcases htail1 with ⟨inside, tail2, hinside, htail2, htail1Eq⟩
  rcases htail2 with ⟨rightWord, tail3, hright, htail3, htail2Eq⟩
  cases hright
  rcases htail3 with ⟨rest, tail4, hrest, htail4, htail3Eq⟩
  cases htail4
  rw [hwEq, htail1Eq, htail2Eq, htail3Eq]
  simpa [Word.Concat, Word.Symbol, Word.Empty, List.append_assoc] using
    BalancedParens.pair hinside hrest

theorem balanced_parens_production_sound
    (A : BalancedParensNT) (rhs : SententialForm Paren BalancedParensNT)
    (hprod : BalancedParensGrammar.produces A rhs) :
    forall w, w ∈ CFG.FormLanguage BalancedParensSymbolLanguage rhs ->
      w ∈ BalancedParensSymbolLanguage (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | empty =>
      cases hw
      exact BalancedParens.empty
  | pair =>
      exact balanced_parens_pair_form_language hw

theorem balanced_parens_start_form_language
    {w : Word Paren}
    (h : w ∈ CFG.FormLanguage BalancedParensSymbolLanguage
      [Symbol.nonterminal BalancedParensNT.S]) :
    BalancedParens w := by
  rcases h with ⟨balanced, tail, hbalanced, htail, hwEq⟩
  cases htail
  rw [hwEq]
  simpa [Word.Concat, Word.Empty] using hbalanced

theorem balanced_parens_generated_only_balanced {w : Word Paren}
    (h : w ∈ CFG.GeneratedLanguage BalancedParensGrammar) :
    BalancedParens w := by
  have hterminal : w ∈ CFG.FormLanguage BalancedParensSymbolLanguage
      (SententialForm.terminalWord
        (nt := BalancedParensNT) w) :=
    CFG.terminalWord_mem_formLanguage BalancedParensSymbolLanguage
      (by intro a; rfl) w
  exact balanced_parens_start_form_language
    (form_language_derives_sound_of_productions
      balanced_parens_production_sound h hterminal)

theorem balanced_parens_empty_generated :
    ([] : Word Paren) ∈ CFG.GeneratedLanguage BalancedParensGrammar := by
  apply CFG.yields_derives
  exists []
  exists []
  exists BalancedParensNT.S
  exists ([] : SententialForm Paren BalancedParensNT)
  constructor
  · exact BalancedParensProduces.empty
  constructor <;> rfl

/-!
Completeness goes in the constructive direction. Each inductive balanced word is
turned into a derivation by first using the grammar's pair production and then
placing the recursively generated inside and suffix in the two nonterminal
slots.
-/

theorem balanced_parens_pair_generated {inside rest : Word Paren}
    (hinside : inside ∈ CFG.GeneratedLanguage BalancedParensGrammar)
    (hrest : rest ∈ CFG.GeneratedLanguage BalancedParensGrammar) :
    Paren.left :: Word.Concat inside (Paren.right :: rest) ∈
      CFG.GeneratedLanguage BalancedParensGrammar := by
  have hStart : CFG.Yields BalancedParensGrammar
      [Symbol.nonterminal BalancedParensNT.S]
      [Symbol.terminal Paren.left,
        Symbol.nonterminal BalancedParensNT.S,
        Symbol.terminal Paren.right,
        Symbol.nonterminal BalancedParensNT.S] := by
    exists []
    exists []
    exists BalancedParensNT.S
    exists [Symbol.terminal Paren.left,
      Symbol.nonterminal BalancedParensNT.S,
      Symbol.terminal Paren.right,
      Symbol.nonterminal BalancedParensNT.S]
    constructor
    · exact BalancedParensProduces.pair
    constructor <;> rfl
  have hform :
      Paren.left :: Word.Concat inside (Paren.right :: rest) ∈
        CFG.FormLanguage (CFG.DerivationSymbolLanguage BalancedParensGrammar)
          [Symbol.terminal Paren.left,
            Symbol.nonterminal BalancedParensNT.S,
            Symbol.terminal Paren.right,
            Symbol.nonterminal BalancedParensNT.S] := by
    exists [Paren.left]
    exists Word.Concat inside (Paren.right :: rest)
    constructor
    · rfl
    constructor
    · exists inside
      exists Paren.right :: rest
      constructor
      · exact hinside
      constructor
      · exists [Paren.right]
        exists rest
        constructor
        · rfl
        constructor
        · exists rest
          exists ([] : Word Paren)
          constructor
          · exact hrest
          constructor
          · rfl
          · exact (Word.concat_empty_right rest).symm
        · rfl
      · rfl
    · rfl
  have hAll := CFG.Derives.step hStart (CFG.formLanguage_derives hform)
  change CFG.Derives BalancedParensGrammar
    [Symbol.nonterminal BalancedParensNT.S]
    (SententialForm.terminalWord
      (Paren.left :: Word.Concat inside (Paren.right :: rest)))
  simpa [SententialForm.terminalWord, Word.Concat, List.append_assoc] using hAll

theorem balanced_parens_words_generated {w : Word Paren}
    (h : BalancedParens w) :
    w ∈ CFG.GeneratedLanguage BalancedParensGrammar := by
  induction h with
  | empty =>
      exact balanced_parens_empty_generated
  | pair hinside hrest ihinside ihrest =>
      exact balanced_parens_pair_generated ihinside ihrest

theorem balanced_parens_generated_language_exact (w : Word Paren) :
    w ∈ CFG.GeneratedLanguage BalancedParensGrammar <-> BalancedParens w := by
  constructor
  · exact balanced_parens_generated_only_balanced
  · exact balanced_parens_words_generated

theorem balanced_parens_context_free :
    ContextFreeLanguage BalancedParens := by
  exists BalancedParensNT
  exists BalancedParensGrammar
  constructor
  · exact balanced_parens_has_finite_productions
  · exact balanced_parens_generated_language_exact

/-!
The book defines balanced parenthesis strings independently of any grammar:
writing {lit}`r_i` for the number of left parentheses minus the number of
right parentheses among the first {lit}`i` symbols, the string is balanced
when every {lit}`r_i` is nonnegative and the final value {lit}`r_n` is zero.
The predicate below phrases the same condition through prefix decompositions:
every prefix has at least as many left as right parentheses, and the whole
word has equally many of each. The bridge theorems prove this counting
characterization equivalent to the inductive predicate targeted by the
grammar exactness theorem, so the grammar is connected to the book's
independent definition instead of only to a production-for-production mirror
of itself.
-/

def BalancedParensCount (w : Word Paren) : Prop :=
  (forall x y : Word Paren, w = Word.Concat x y ->
    Word.Count Paren.right x <= Word.Count Paren.left x) ∧
  Word.Count Paren.left w = Word.Count Paren.right w

theorem balanced_parens_count_empty : BalancedParensCount [] := by
  constructor
  · intro x y hxy
    cases x with
    | nil =>
        simp [Word.Count]
    | cons c t =>
        simp [Word.Concat] at hxy
  · rfl

/-!
Each pair production preserves the counting characterization. The prefix case
analysis follows the shape of the word: a prefix is empty, stops inside the
wrapped word, stops at the matching right parenthesis, or continues into the
remaining suffix.
-/

theorem balanced_parens_count_pair {inside rest : Word Paren}
    (hinside : BalancedParensCount inside) (hrest : BalancedParensCount rest) :
    BalancedParensCount
      (Paren.left :: Word.Concat inside (Paren.right :: rest)) := by
  constructor
  · intro x y hxy
    cases x with
    | nil =>
        simp [Word.Count]
    | cons c t =>
        have hxy2 : Paren.left :: Word.Concat inside (Paren.right :: rest)
            = c :: Word.Concat t y := hxy
        injection hxy2 with hc htail
        subst hc
        rcases List.append_eq_append_iff.mp htail with
          ⟨m, hm1, hm2⟩ | ⟨m, hm1, hm2⟩
        · cases m with
          | nil =>
              have ht : t = inside := by simpa using hm1
              subst ht
              have hcount := hinside.right
              simp [Word.Count]
              lia
          | cons m0 m1 =>
              have hm0 : Paren.right :: rest = m0 :: Word.Concat m1 y := hm2
              injection hm0 with hm0h hm0t
              subst hm0h
              have hrest_prefix := hrest.left m1 y hm0t
              have ht : t = Word.Concat inside (Paren.right :: m1) := hm1
              subst ht
              have hcount := hinside.right
              simp [Word.Count, Word.count_concat]
              lia
        · have hin : inside = Word.Concat t m := hm1
          have hpre := hinside.left t m hin
          simp [Word.Count]
          lia
  · have hcount_inside := hinside.right
    have hcount_rest := hrest.right
    simp [Word.Count, Word.count_concat]
    lia

theorem balanced_parens_count_of_balanced {w : Word Paren}
    (h : BalancedParens w) : BalancedParensCount w := by
  induction h with
  | empty =>
      exact balanced_parens_count_empty
  | pair hinside hrest ihinside ihrest =>
      exact balanced_parens_count_pair ihinside ihrest

/-!
For the converse, the auxiliary chain predicate describes words consisting of
{lit}`n + 1` balanced segments separated by {lit}`n` unmatched right
parentheses. Reading a word left to right, a leading left parenthesis lowers
the number of unmatched right parentheses by pairing with the first chain
separator, and a leading right parenthesis raises it. This avoids any search
for the first prefix where the running count returns to zero.
-/

private inductive ParenRightChain : Word Paren -> Nat -> Prop where
  | base {u : Word Paren} :
      BalancedParens u -> ParenRightChain u 0
  | cons {u rest : Word Paren} {n : Nat} :
      BalancedParens u -> ParenRightChain rest n ->
      ParenRightChain (Word.Concat u (Paren.right :: rest)) (n + 1)

private theorem parenRightChain_cons_left {t : Word Paren} {n : Nat}
    (h : ParenRightChain t (n + 1)) :
    ParenRightChain (Paren.left :: t) n := by
  cases h with
  | cons hu hrest =>
      rename_i u rest
      cases hrest with
      | base hbal =>
          exact ParenRightChain.base (BalancedParens.pair hu hbal)
      | cons hu2 hrest2 =>
          rename_i u2 rest2 m
          have heq : Paren.left :: Word.Concat u
              (Paren.right :: Word.Concat u2 (Paren.right :: rest2))
              = Word.Concat
                  (Paren.left :: Word.Concat u (Paren.right :: u2))
                  (Paren.right :: rest2) := by
            simp [Word.Concat, List.append_assoc]
          rw [heq]
          exact ParenRightChain.cons (BalancedParens.pair hu hu2) hrest2

private theorem parenRightChain_of_counts (w : Word Paren) :
    forall n : Nat,
      (forall x y : Word Paren, w = Word.Concat x y ->
        Word.Count Paren.right x <= Word.Count Paren.left x + n) ->
      Word.Count Paren.right w = Word.Count Paren.left w + n ->
      ParenRightChain w n := by
  induction w with
  | nil =>
      intro n _hpre htot
      have hn : n = 0 := by simpa [Word.Count] using htot.symm
      subst hn
      exact ParenRightChain.base BalancedParens.empty
  | cons c t ih =>
      intro n hpre htot
      cases c with
      | left =>
          have hpre' : forall x y : Word Paren, t = Word.Concat x y ->
              Word.Count Paren.right x <= Word.Count Paren.left x + (n + 1) := by
            intro x y hxy
            have h := hpre (Paren.left :: x) y (by rw [hxy]; rfl)
            simp [Word.Count] at h
            lia
          have htot' : Word.Count Paren.right t
              = Word.Count Paren.left t + (n + 1) := by
            simp [Word.Count] at htot
            lia
          exact parenRightChain_cons_left (ih (n + 1) hpre' htot')
      | right =>
          cases n with
          | zero =>
              have h := hpre [Paren.right] t rfl
              simp [Word.Count] at h
          | succ m =>
              have hpre' : forall x y : Word Paren, t = Word.Concat x y ->
                  Word.Count Paren.right x <= Word.Count Paren.left x + m := by
                intro x y hxy
                have h := hpre (Paren.right :: x) y (by rw [hxy]; rfl)
                simp [Word.Count] at h
                lia
              have htot' : Word.Count Paren.right t
                  = Word.Count Paren.left t + m := by
                simp [Word.Count] at htot
                lia
              exact ParenRightChain.cons BalancedParens.empty (ih m hpre' htot')

theorem balanced_parens_of_count {w : Word Paren}
    (h : BalancedParensCount w) : BalancedParens w := by
  have hchain := parenRightChain_of_counts w 0
    (fun x y hxy => by
      have hpre := h.left x y hxy
      lia)
    (by
      have htot := h.right
      lia)
  cases hchain with
  | base hbal => exact hbal

theorem balanced_parens_iff_count (w : Word Paren) :
    BalancedParens w <-> BalancedParensCount w :=
  Iff.intro balanced_parens_count_of_balanced balanced_parens_of_count

theorem balanced_parens_generated_iff_count (w : Word Paren) :
    w ∈ CFG.GeneratedLanguage BalancedParensGrammar <->
      BalancedParensCount w :=
  Iff.trans (balanced_parens_generated_language_exact w)
    (balanced_parens_iff_count w)

theorem balanced_parens_count_context_free :
    ContextFreeLanguage BalancedParensCount := by
  exists BalancedParensNT
  exists BalancedParensGrammar
  constructor
  · exact balanced_parens_has_finite_productions
  · exact balanced_parens_generated_iff_count

/-!
Balanced brackets are the same proof pattern with two bracket kinds. The
round-pair and square-pair productions each get their own generation theorem,
then the induction over balanced words dispatches to the matching constructor.

Unlike the one-kind parenthesis language above, the two-kind language is
formalized here only through its inductive predicate. Counting each bracket
kind separately would not capture proper nesting of mixed brackets, so the
counting bridge proved for parentheses has no direct analogue here and no
independent characterization is formalized for this example.
-/

inductive Bracket where
  | roundLeft : Bracket
  | roundRight : Bracket
  | squareLeft : Bracket
  | squareRight : Bracket
deriving DecidableEq

inductive BalancedBracketsNT where
  | S : BalancedBracketsNT
deriving DecidableEq

def Bracket.finite : FiniteType Bracket where
  elems := [Bracket.roundLeft, Bracket.roundRight,
    Bracket.squareLeft, Bracket.squareRight]
  complete := by
    intro x
    cases x <;> simp

def BalancedBracketsNT.finite : FiniteType BalancedBracketsNT where
  elems := [BalancedBracketsNT.S]
  complete := by
    intro x
    cases x
    simp

inductive BalancedBracketsProduces :
    BalancedBracketsNT -> SententialForm Bracket BalancedBracketsNT -> Prop where
  | empty :
      BalancedBracketsProduces BalancedBracketsNT.S []
  | roundPair :
      BalancedBracketsProduces BalancedBracketsNT.S
        [Symbol.terminal Bracket.roundLeft,
          Symbol.nonterminal BalancedBracketsNT.S,
          Symbol.terminal Bracket.roundRight,
          Symbol.nonterminal BalancedBracketsNT.S]
  | squarePair :
      BalancedBracketsProduces BalancedBracketsNT.S
        [Symbol.terminal Bracket.squareLeft,
          Symbol.nonterminal BalancedBracketsNT.S,
          Symbol.terminal Bracket.squareRight,
          Symbol.nonterminal BalancedBracketsNT.S]

def BalancedBracketsGrammar : CFG Bracket BalancedBracketsNT where
  start := BalancedBracketsNT.S
  produces := BalancedBracketsProduces
  nonterminalsFinite := BalancedBracketsNT.finite

inductive BalancedBrackets : Word Bracket -> Prop where
  | empty : BalancedBrackets []
  | roundPair {inside rest : Word Bracket} :
      BalancedBrackets inside ->
        BalancedBrackets rest ->
          BalancedBrackets
            (Bracket.roundLeft :: Word.Concat inside (Bracket.roundRight :: rest))
  | squarePair {inside rest : Word Bracket} :
      BalancedBrackets inside ->
        BalancedBrackets rest ->
          BalancedBrackets
            (Bracket.squareLeft :: Word.Concat inside (Bracket.squareRight :: rest))

def BalancedBracketsSymbolLanguage :
    Symbol Bracket BalancedBracketsNT -> Language Bracket
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal BalancedBracketsNT.S => BalancedBrackets

def balancedBracketsEmptyProduction :
    CFG.Production Bracket BalancedBracketsNT where
  lhs := BalancedBracketsNT.S
  rhs := []

def balancedBracketsRoundPairProduction :
    CFG.Production Bracket BalancedBracketsNT where
  lhs := BalancedBracketsNT.S
  rhs :=
    [Symbol.terminal Bracket.roundLeft,
      Symbol.nonterminal BalancedBracketsNT.S,
      Symbol.terminal Bracket.roundRight,
      Symbol.nonterminal BalancedBracketsNT.S]

def balancedBracketsSquarePairProduction :
    CFG.Production Bracket BalancedBracketsNT where
  lhs := BalancedBracketsNT.S
  rhs :=
    [Symbol.terminal Bracket.squareLeft,
      Symbol.nonterminal BalancedBracketsNT.S,
      Symbol.terminal Bracket.squareRight,
      Symbol.nonterminal BalancedBracketsNT.S]

theorem balanced_brackets_has_finite_productions :
    CFG.HasFiniteProductions BalancedBracketsGrammar := by
  exists [balancedBracketsEmptyProduction, balancedBracketsRoundPairProduction,
    balancedBracketsSquarePairProduction]
  intro A rhs
  constructor
  · intro h
    cases h with
    | empty =>
        exact ⟨balancedBracketsEmptyProduction,
          by simp [balancedBracketsEmptyProduction], rfl, rfl⟩
    | roundPair =>
        exact ⟨balancedBracketsRoundPairProduction,
          by simp [balancedBracketsRoundPairProduction], rfl, rfl⟩
    | squarePair =>
        exact ⟨balancedBracketsSquarePairProduction,
          by simp [balancedBracketsSquarePairProduction], rfl, rfl⟩
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [balancedBracketsEmptyProduction, balancedBracketsRoundPairProduction,
      balancedBracketsSquarePairProduction] at hmem
    rcases hmem with hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact BalancedBracketsProduces.empty
    · subst rule
      cases hlhs
      cases hrhs
      exact BalancedBracketsProduces.roundPair
    · subst rule
      cases hlhs
      cases hrhs
      exact BalancedBracketsProduces.squarePair

/-!
The two-bracket grammar repeats the parenthesis soundness argument twice. Each
case has the same form-language split, but the terminal symbols determine which
inductive constructor is available.
-/

theorem balanced_brackets_round_pair_form_language
    {w : Word Bracket}
    (hw : w ∈ CFG.FormLanguage BalancedBracketsSymbolLanguage
      [Symbol.terminal Bracket.roundLeft,
        Symbol.nonterminal BalancedBracketsNT.S,
        Symbol.terminal Bracket.roundRight,
        Symbol.nonterminal BalancedBracketsNT.S]) :
    BalancedBrackets w := by
  rcases hw with ⟨leftWord, tail1, hleft, htail1, hwEq⟩
  cases hleft
  rcases htail1 with ⟨inside, tail2, hinside, htail2, htail1Eq⟩
  rcases htail2 with ⟨rightWord, tail3, hright, htail3, htail2Eq⟩
  cases hright
  rcases htail3 with ⟨rest, tail4, hrest, htail4, htail3Eq⟩
  cases htail4
  rw [hwEq, htail1Eq, htail2Eq, htail3Eq]
  simpa [Word.Concat, Word.Symbol, Word.Empty, List.append_assoc] using
    BalancedBrackets.roundPair hinside hrest

theorem balanced_brackets_square_pair_form_language
    {w : Word Bracket}
    (hw : w ∈ CFG.FormLanguage BalancedBracketsSymbolLanguage
      [Symbol.terminal Bracket.squareLeft,
        Symbol.nonterminal BalancedBracketsNT.S,
        Symbol.terminal Bracket.squareRight,
        Symbol.nonterminal BalancedBracketsNT.S]) :
    BalancedBrackets w := by
  rcases hw with ⟨leftWord, tail1, hleft, htail1, hwEq⟩
  cases hleft
  rcases htail1 with ⟨inside, tail2, hinside, htail2, htail1Eq⟩
  rcases htail2 with ⟨rightWord, tail3, hright, htail3, htail2Eq⟩
  cases hright
  rcases htail3 with ⟨rest, tail4, hrest, htail4, htail3Eq⟩
  cases htail4
  rw [hwEq, htail1Eq, htail2Eq, htail3Eq]
  simpa [Word.Concat, Word.Symbol, Word.Empty, List.append_assoc] using
    BalancedBrackets.squarePair hinside hrest

theorem balanced_brackets_production_sound
    (A : BalancedBracketsNT) (rhs : SententialForm Bracket BalancedBracketsNT)
    (hprod : BalancedBracketsGrammar.produces A rhs) :
    forall w, w ∈ CFG.FormLanguage BalancedBracketsSymbolLanguage rhs ->
      w ∈ BalancedBracketsSymbolLanguage (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | empty =>
      cases hw
      exact BalancedBrackets.empty
  | roundPair =>
      exact balanced_brackets_round_pair_form_language hw
  | squarePair =>
      exact balanced_brackets_square_pair_form_language hw

theorem balanced_brackets_start_form_language
    {w : Word Bracket}
    (h : w ∈ CFG.FormLanguage BalancedBracketsSymbolLanguage
      [Symbol.nonterminal BalancedBracketsNT.S]) :
    BalancedBrackets w := by
  rcases h with ⟨balanced, tail, hbalanced, htail, hwEq⟩
  cases htail
  rw [hwEq]
  simpa [Word.Concat, Word.Empty] using hbalanced

theorem balanced_brackets_generated_only_balanced {w : Word Bracket}
    (h : w ∈ CFG.GeneratedLanguage BalancedBracketsGrammar) :
    BalancedBrackets w := by
  have hterminal : w ∈ CFG.FormLanguage BalancedBracketsSymbolLanguage
      (SententialForm.terminalWord
        (nt := BalancedBracketsNT) w) :=
    CFG.terminalWord_mem_formLanguage BalancedBracketsSymbolLanguage
      (by intro a; rfl) w
  exact balanced_brackets_start_form_language
    (form_language_derives_sound_of_productions
      balanced_brackets_production_sound h hterminal)

theorem balanced_brackets_empty_generated :
    ([] : Word Bracket) ∈ CFG.GeneratedLanguage BalancedBracketsGrammar := by
  apply CFG.yields_derives
  exists []
  exists []
  exists BalancedBracketsNT.S
  exists ([] : SententialForm Bracket BalancedBracketsNT)
  constructor
  · exact BalancedBracketsProduces.empty
  constructor <;> rfl

/-!
The generation proofs for brackets mirror the two wrapping productions. They are
kept separate so the final induction over balanced bracket words can dispatch to
the round or square constructor without hiding either derivation shape.
-/

theorem balanced_brackets_round_pair_generated {inside rest : Word Bracket}
    (hinside : inside ∈ CFG.GeneratedLanguage BalancedBracketsGrammar)
    (hrest : rest ∈ CFG.GeneratedLanguage BalancedBracketsGrammar) :
    Bracket.roundLeft :: Word.Concat inside (Bracket.roundRight :: rest) ∈
      CFG.GeneratedLanguage BalancedBracketsGrammar := by
  have hStart : CFG.Yields BalancedBracketsGrammar
      [Symbol.nonterminal BalancedBracketsNT.S]
      [Symbol.terminal Bracket.roundLeft,
        Symbol.nonterminal BalancedBracketsNT.S,
        Symbol.terminal Bracket.roundRight,
        Symbol.nonterminal BalancedBracketsNT.S] := by
    exists []
    exists []
    exists BalancedBracketsNT.S
    exists [Symbol.terminal Bracket.roundLeft,
      Symbol.nonterminal BalancedBracketsNT.S,
      Symbol.terminal Bracket.roundRight,
      Symbol.nonterminal BalancedBracketsNT.S]
    constructor
    · exact BalancedBracketsProduces.roundPair
    constructor <;> rfl
  have hform :
      Bracket.roundLeft :: Word.Concat inside (Bracket.roundRight :: rest) ∈
        CFG.FormLanguage (CFG.DerivationSymbolLanguage BalancedBracketsGrammar)
          [Symbol.terminal Bracket.roundLeft,
            Symbol.nonterminal BalancedBracketsNT.S,
            Symbol.terminal Bracket.roundRight,
            Symbol.nonterminal BalancedBracketsNT.S] := by
    exists [Bracket.roundLeft]
    exists Word.Concat inside (Bracket.roundRight :: rest)
    constructor
    · rfl
    constructor
    · exists inside
      exists Bracket.roundRight :: rest
      constructor
      · exact hinside
      constructor
      · exists [Bracket.roundRight]
        exists rest
        constructor
        · rfl
        constructor
        · exists rest
          exists ([] : Word Bracket)
          constructor
          · exact hrest
          constructor
          · rfl
          · exact (Word.concat_empty_right rest).symm
        · rfl
      · rfl
    · rfl
  have hAll := CFG.Derives.step hStart (CFG.formLanguage_derives hform)
  change CFG.Derives BalancedBracketsGrammar
    [Symbol.nonterminal BalancedBracketsNT.S]
    (SententialForm.terminalWord
      (Bracket.roundLeft :: Word.Concat inside (Bracket.roundRight :: rest)))
  simpa [SententialForm.terminalWord, Word.Concat, List.append_assoc] using hAll

theorem balanced_brackets_square_pair_generated {inside rest : Word Bracket}
    (hinside : inside ∈ CFG.GeneratedLanguage BalancedBracketsGrammar)
    (hrest : rest ∈ CFG.GeneratedLanguage BalancedBracketsGrammar) :
    Bracket.squareLeft :: Word.Concat inside (Bracket.squareRight :: rest) ∈
      CFG.GeneratedLanguage BalancedBracketsGrammar := by
  have hStart : CFG.Yields BalancedBracketsGrammar
      [Symbol.nonterminal BalancedBracketsNT.S]
      [Symbol.terminal Bracket.squareLeft,
        Symbol.nonterminal BalancedBracketsNT.S,
        Symbol.terminal Bracket.squareRight,
        Symbol.nonterminal BalancedBracketsNT.S] := by
    exists []
    exists []
    exists BalancedBracketsNT.S
    exists [Symbol.terminal Bracket.squareLeft,
      Symbol.nonterminal BalancedBracketsNT.S,
      Symbol.terminal Bracket.squareRight,
      Symbol.nonterminal BalancedBracketsNT.S]
    constructor
    · exact BalancedBracketsProduces.squarePair
    constructor <;> rfl
  have hform :
      Bracket.squareLeft :: Word.Concat inside (Bracket.squareRight :: rest) ∈
        CFG.FormLanguage (CFG.DerivationSymbolLanguage BalancedBracketsGrammar)
          [Symbol.terminal Bracket.squareLeft,
            Symbol.nonterminal BalancedBracketsNT.S,
            Symbol.terminal Bracket.squareRight,
            Symbol.nonterminal BalancedBracketsNT.S] := by
    exists [Bracket.squareLeft]
    exists Word.Concat inside (Bracket.squareRight :: rest)
    constructor
    · rfl
    constructor
    · exists inside
      exists Bracket.squareRight :: rest
      constructor
      · exact hinside
      constructor
      · exists [Bracket.squareRight]
        exists rest
        constructor
        · rfl
        constructor
        · exists rest
          exists ([] : Word Bracket)
          constructor
          · exact hrest
          constructor
          · rfl
          · exact (Word.concat_empty_right rest).symm
        · rfl
      · rfl
    · rfl
  have hAll := CFG.Derives.step hStart (CFG.formLanguage_derives hform)
  change CFG.Derives BalancedBracketsGrammar
    [Symbol.nonterminal BalancedBracketsNT.S]
    (SententialForm.terminalWord
      (Bracket.squareLeft :: Word.Concat inside (Bracket.squareRight :: rest)))
  simpa [SententialForm.terminalWord, Word.Concat, List.append_assoc] using hAll

theorem balanced_brackets_words_generated {w : Word Bracket}
    (h : BalancedBrackets w) :
    w ∈ CFG.GeneratedLanguage BalancedBracketsGrammar := by
  induction h with
  | empty =>
      exact balanced_brackets_empty_generated
  | roundPair hinside hrest ihinside ihrest =>
      exact balanced_brackets_round_pair_generated ihinside ihrest
  | squarePair hinside hrest ihinside ihrest =>
      exact balanced_brackets_square_pair_generated ihinside ihrest

theorem balanced_brackets_generated_language_exact (w : Word Bracket) :
    w ∈ CFG.GeneratedLanguage BalancedBracketsGrammar <-> BalancedBrackets w := by
  constructor
  · exact balanced_brackets_generated_only_balanced
  · exact balanced_brackets_words_generated

theorem balanced_brackets_context_free :
    ContextFreeLanguage BalancedBrackets := by
  exists BalancedBracketsNT
  exists BalancedBracketsGrammar
  constructor
  · exact balanced_brackets_has_finite_productions
  · exact balanced_brackets_generated_language_exact

/-!
The {lit}`a^n b^n` example is more arithmetic than the bracket grammars. The
support lemmas track the open sentential form with one remaining nonterminal and
show that any terminal derivation has exactly the matched prefix/suffix shape.
-/

inductive AB where
  | a : AB
  | b : AB
deriving DecidableEq

inductive AnBnNT where
  | S : AnBnNT
deriving DecidableEq

def AB.finite : FiniteType AB where
  elems := [AB.a, AB.b]
  complete := by
    intro x
    cases x <;> simp

def AnBnNT.finite : FiniteType AnBnNT where
  elems := [AnBnNT.S]
  complete := by
    intro x
    cases x
    simp

inductive AnBnProduces :
    AnBnNT -> SententialForm AB AnBnNT -> Prop where
  | wrap :
      AnBnProduces AnBnNT.S
        [Symbol.terminal AB.a, Symbol.nonterminal AnBnNT.S, Symbol.terminal AB.b]
  | stop :
      AnBnProduces AnBnNT.S []

def AnBnGrammar : CFG AB AnBnNT where
  start := AnBnNT.S
  produces := AnBnProduces
  nonterminalsFinite := AnBnNT.finite

def AnBnWrap (w : Word AB) : Word AB :=
  AB.a :: Word.Concat w [AB.b]

def AnBnWord (n : Nat) : Word AB :=
  Word.Concat (Word.RepeatSymbol AB.a n) (Word.RepeatSymbol AB.b n)

def AnBnPrefix (n : Nat) : SententialForm AB AnBnNT :=
  SententialForm.terminalWord (Word.RepeatSymbol AB.a n)

def AnBnSuffix (n : Nat) : SententialForm AB AnBnNT :=
  SententialForm.terminalWord (Word.RepeatSymbol AB.b n)

def AnBnOpenForm (n : Nat) : SententialForm AB AnBnNT :=
  AnBnPrefix n ++ [Symbol.nonterminal AnBnNT.S] ++ AnBnSuffix n

def AnBnClosedForm (n : Nat) : SententialForm AB AnBnNT :=
  SententialForm.terminalWord (AnBnWord n)

/-!
The {lit}`a^n b^n` proof needs a little list algebra because the grammar keeps
one central nonterminal between terminal prefixes and suffixes. The split lemma
below says that this distinguished nonterminal can be recovered uniquely from
the surrounding terminal-only lists.
-/

theorem list_append_cons_inj_of_not_mem {alpha : Type u}
    {xs ys zs ws : List alpha} {a b : alpha}
    (hxs : ¬ b ∈ xs) (hzs : ¬ b ∈ zs)
    (h : xs ++ a :: zs = ys ++ b :: ws) :
    xs = ys ∧ a = b ∧ zs = ws := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          simp at h
          exact And.intro rfl (And.intro h.left h.right)
      | cons y ys =>
          simp at h
          have hb : b ∈ zs := by
            rw [h.right]
            simp
          exact False.elim (hzs hb)
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at h
          have hb : b ∈ x :: xs := by
            rw [h.left]
            exact List.Mem.head xs
          exact False.elim (hxs hb)
      | cons y ys =>
          simp at h
          have hxsTail : ¬ b ∈ xs := by
            intro hb
            exact hxs (List.Mem.tail x hb)
          have htail := ih hxsTail h.right
          exact And.intro (by rw [h.left, htail.left])
            (And.intro htail.right.left htail.right.right)

theorem nonterminal_not_mem_terminalWord (A : AnBnNT) (w : Word AB) :
    ¬ Symbol.nonterminal A ∈ SententialForm.terminalWord (nt := AnBnNT) w := by
  induction w with
  | nil =>
      intro h
      cases h
  | cons t rest ih =>
      intro h
      cases h with
      | tail _ htail =>
          exact ih htail

theorem replicate_succ_eq_append (x : alpha) (n : Nat) :
    List.replicate (n + 1) x = List.replicate n x ++ [x] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change x :: List.replicate (n + 1) x =
        x :: (List.replicate n x ++ [x])
      rw [ih]

theorem replicate_succ_eq_cons (x : alpha) (n : Nat) :
    List.replicate (n + 1) x = x :: List.replicate n x :=
  rfl

theorem anbn_wrap_word (n : Nat) :
    AnBnWrap (AnBnWord n) = AnBnWord (n + 1) := by
  simp [AnBnWrap, AnBnWord, Word.Concat, Word.RepeatSymbol,
    replicate_succ_eq_cons AB.a n,
    replicate_succ_eq_append AB.b n, List.append_assoc]

theorem anbn_yields_open_cases (n : Nat) {y : SententialForm AB AnBnNT}
    (h : CFG.Yields AnBnGrammar (AnBnOpenForm n) y) :
    y = AnBnOpenForm (n + 1) ∨ y = AnBnClosedForm n := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          unfold AnBnOpenForm at hx
                          simp only [List.append_assoc, List.singleton_append] at hx
                          have hsplit := list_append_cons_inj_of_not_mem
                            (nonterminal_not_mem_terminalWord A
                              (Word.RepeatSymbol AB.a n))
                            (nonterminal_not_mem_terminalWord A
                              (Word.RepeatSymbol AB.b n))
                            hx
                          subst y
                          rw [← hsplit.left, ← hsplit.right.right]
                          cases hsplit.right.left
                          cases hprod with
                          | wrap =>
                              left
                              simp [AnBnOpenForm, AnBnPrefix, AnBnSuffix,
                                Word.RepeatSymbol, SententialForm.terminalWord,
                                replicate_succ_eq_append (Symbol.terminal AB.a) n,
                                replicate_succ_eq_cons (Symbol.terminal AB.b) n,
                                List.append_assoc]
                          | stop =>
                              right
                              simp [AnBnClosedForm, AnBnWord, Word.Concat,
                                SententialForm.terminalWord]

theorem anbn_terminalWord_no_yields {w : Word AB}
    {y : SententialForm AB AnBnNT} :
    ¬ CFG.Yields AnBnGrammar (SententialForm.terminalWord w) y := by
  intro h
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro _hprod hrest =>
                      cases hrest with
                      | intro hx _hy =>
                          have hmem : Symbol.nonterminal A ∈
                              SententialForm.terminalWord (nt := AnBnNT) w := by
                            rw [hx]
                            simp
                          exact nonterminal_not_mem_terminalWord A w hmem

theorem terminalWord_injective {x y : Word AB}
    (h : SententialForm.terminalWord (nt := AnBnNT) x =
      SententialForm.terminalWord (nt := AnBnNT) y) :
    x = y := by
  have hopt := congrArg (SententialForm.toWord? (term := AB) (nt := AnBnNT)) h
  rw [SententialForm.terminalWord_toWord, SententialForm.terminalWord_toWord] at hopt
  cases hopt
  rfl

private theorem anbn_terminal_derives_eq_aux
    {xform yform : SententialForm AB AnBnNT} {x y : Word AB}
    (hxform : xform = SententialForm.terminalWord (nt := AnBnNT) x)
    (hyform : yform = SententialForm.terminalWord (nt := AnBnNT) y)
    (h : CFG.Derives AnBnGrammar xform yform) :
    x = y := by
  induction h generalizing x y with
  | refl z =>
      apply terminalWord_injective
      rw [← hxform, ← hyform]
  | step hstep _hrest _ih =>
      rw [hxform] at hstep
      exact False.elim (anbn_terminalWord_no_yields hstep)

theorem anbn_terminal_derives_eq {x y : Word AB}
    (h : CFG.Derives AnBnGrammar
      (SententialForm.terminalWord (nt := AnBnNT) x)
      (SententialForm.terminalWord (nt := AnBnNT) y)) :
    x = y :=
  anbn_terminal_derives_eq_aux rfl rfl h

theorem anbn_open_not_terminal (n : Nat) (w : Word AB) :
    AnBnOpenForm n ≠ SententialForm.terminalWord (nt := AnBnNT) w := by
  intro h
  have hmem : Symbol.nonterminal AnBnNT.S ∈ AnBnOpenForm n := by
    simp [AnBnOpenForm]
  rw [h] at hmem
  exact nonterminal_not_mem_terminalWord AnBnNT.S w hmem

/-!
This is the main invariant for the grammar: starting from an open form, any
terminal derivation either keeps wrapping and eventually stops, or is impossible.
The result extracts the number of wraps and therefore the matching word
{lit}`a^n b^n`.
-/

private theorem anbn_open_derives_terminal_exact_aux
    {xform yform : SententialForm AB AnBnNT} {w : Word AB}
    (hopen : exists n, xform = AnBnOpenForm n)
    (hyform : yform = SententialForm.terminalWord (nt := AnBnNT) w)
    (h : CFG.Derives AnBnGrammar xform yform) :
    exists n, w = AnBnWord n := by
  induction h with
  | refl z =>
      cases hopen with
      | intro n hn =>
          exact False.elim (anbn_open_not_terminal n w (by rw [← hn, hyform]))
  | step hstep hrest ih =>
      cases hopen with
      | intro n hn =>
          rw [hn] at hstep
          cases anbn_yields_open_cases n hstep with
          | inl hopenNext =>
              exact ih (Exists.intro (n + 1) hopenNext) hyform
          | inr hclosed =>
              have hword : AnBnWord n = w := by
                exact anbn_terminal_derives_eq_aux
                  (x := AnBnWord n) (y := w)
                  (by rw [hclosed]; rfl)
                  hyform hrest
              exists n
              exact hword.symm

theorem anbn_generated_only_anbn_words {w : Word AB}
    (h : w ∈ CFG.GeneratedLanguage AnBnGrammar) :
    exists n, w = AnBnWord n :=
  anbn_open_derives_terminal_exact_aux
    (Exists.intro 0 (by rfl))
    rfl h

theorem anbn_empty_generated :
    AnBnWord 0 ∈ CFG.GeneratedLanguage AnBnGrammar := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AnBnNT.S
  exists ([] : SententialForm AB AnBnNT)
  constructor
  · exact AnBnProduces.stop
  constructor <;> rfl

theorem anbn_wrap_generated {w : Word AB}
    (h : w ∈ CFG.GeneratedLanguage AnBnGrammar) :
    AnBnWrap w ∈ CFG.GeneratedLanguage AnBnGrammar := by
  have hStart : CFG.Yields AnBnGrammar
      [Symbol.nonterminal AnBnNT.S]
      [Symbol.terminal AB.a, Symbol.nonterminal AnBnNT.S, Symbol.terminal AB.b] := by
    exists []
    exists []
    exists AnBnNT.S
    exists [Symbol.terminal AB.a, Symbol.nonterminal AnBnNT.S, Symbol.terminal AB.b]
    constructor
    · exact AnBnProduces.wrap
    constructor <;> rfl
  have hContext :
      CFG.Derives AnBnGrammar
        [Symbol.terminal AB.a, Symbol.nonterminal AnBnNT.S, Symbol.terminal AB.b]
        (Symbol.terminal AB.a ::
          SententialForm.terminalWord w ++ [Symbol.terminal AB.b]) := by
    simpa using CFG.derives_context h [Symbol.terminal AB.a] [Symbol.terminal AB.b]
  have hAll := CFG.Derives.step hStart hContext
  change CFG.Derives AnBnGrammar [Symbol.nonterminal AnBnNT.S]
    (SententialForm.terminalWord (AB.a :: Word.Concat w [AB.b]))
  simpa [SententialForm.terminalWord, Word.Concat] using hAll

theorem anbn_words_generated (n : Nat) :
    AnBnWord n ∈ CFG.GeneratedLanguage AnBnGrammar := by
  induction n with
  | zero => exact anbn_empty_generated
  | succ n ih =>
      simpa [anbn_wrap_word n] using anbn_wrap_generated ih

theorem anbn_generated_language_exact (w : Word AB) :
    w ∈ CFG.GeneratedLanguage AnBnGrammar <-> exists n, w = AnBnWord n := by
  constructor
  · exact anbn_generated_only_anbn_words
  · intro h
    cases h with
    | intro n hn =>
        rw [hn]
        exact anbn_words_generated n

/-!
The {lit}`a^n b^n` grammar has exactly two productions, so the language it
generates is context-free in the book's finite-production sense. The named
language definition below is reused by the boundary corollary that separates
context-free languages from regular languages.
-/

def anbnWrapProduction : CFG.Production AB AnBnNT where
  lhs := AnBnNT.S
  rhs :=
    [Symbol.terminal AB.a, Symbol.nonterminal AnBnNT.S, Symbol.terminal AB.b]

def anbnStopProduction : CFG.Production AB AnBnNT where
  lhs := AnBnNT.S
  rhs := []

theorem anbn_has_finite_productions :
    CFG.HasFiniteProductions AnBnGrammar := by
  exists [anbnWrapProduction, anbnStopProduction]
  intro A rhs
  constructor
  · intro h
    cases h with
    | wrap =>
        exact ⟨anbnWrapProduction, by simp [anbnWrapProduction], rfl, rfl⟩
    | stop =>
        exact ⟨anbnStopProduction, by simp [anbnStopProduction], rfl, rfl⟩
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [anbnWrapProduction, anbnStopProduction] at hmem
    rcases hmem with hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact AnBnProduces.wrap
    · subst rule
      cases hlhs
      cases hrhs
      exact AnBnProduces.stop

def AnBnLanguage : Language AB :=
  fun w => exists n, w = AnBnWord n

theorem anbn_context_free : ContextFreeLanguage AnBnLanguage := by
  exists AnBnNT
  exists AnBnGrammar
  constructor
  · exact anbn_has_finite_productions
  · exact anbn_generated_language_exact

/-!
The palindrome grammar is the final example. Its soundness proof separates
single-letter productions from the two wrapping productions; completeness then
follows by induction over the inductive palindrome predicate.
-/

inductive PalindromeNT where
  | S : PalindromeNT
deriving DecidableEq

def PalindromeNT.finite : FiniteType PalindromeNT where
  elems := [PalindromeNT.S]
  complete := by
    intro x
    cases x
    simp

inductive PalindromeProduces :
    PalindromeNT -> SententialForm AB PalindromeNT -> Prop where
  | empty :
      PalindromeProduces PalindromeNT.S []
  | singleA :
      PalindromeProduces PalindromeNT.S [Symbol.terminal AB.a]
  | singleB :
      PalindromeProduces PalindromeNT.S [Symbol.terminal AB.b]
  | wrapA :
      PalindromeProduces PalindromeNT.S
        [Symbol.terminal AB.a,
          Symbol.nonterminal PalindromeNT.S,
          Symbol.terminal AB.a]
  | wrapB :
      PalindromeProduces PalindromeNT.S
        [Symbol.terminal AB.b,
          Symbol.nonterminal PalindromeNT.S,
          Symbol.terminal AB.b]

def PalindromeGrammar : CFG AB PalindromeNT where
  start := PalindromeNT.S
  produces := PalindromeProduces
  nonterminalsFinite := PalindromeNT.finite

inductive PalindromeAB : Word AB -> Prop where
  | empty : PalindromeAB []
  | singleA : PalindromeAB [AB.a]
  | singleB : PalindromeAB [AB.b]
  | wrapA {w : Word AB} :
      PalindromeAB w -> PalindromeAB (AB.a :: Word.Concat w [AB.a])
  | wrapB {w : Word AB} :
      PalindromeAB w -> PalindromeAB (AB.b :: Word.Concat w [AB.b])

def PalindromeSymbolLanguage : Symbol AB PalindromeNT -> Language AB
  | Symbol.terminal sym => Language.Singleton (Word.Symbol sym)
  | Symbol.nonterminal PalindromeNT.S => PalindromeAB

def palindromeEmptyProduction : CFG.Production AB PalindromeNT where
  lhs := PalindromeNT.S
  rhs := []

def palindromeSingleAProduction : CFG.Production AB PalindromeNT where
  lhs := PalindromeNT.S
  rhs := [Symbol.terminal AB.a]

def palindromeSingleBProduction : CFG.Production AB PalindromeNT where
  lhs := PalindromeNT.S
  rhs := [Symbol.terminal AB.b]

def palindromeWrapAProduction : CFG.Production AB PalindromeNT where
  lhs := PalindromeNT.S
  rhs :=
    [Symbol.terminal AB.a,
      Symbol.nonterminal PalindromeNT.S,
      Symbol.terminal AB.a]

def palindromeWrapBProduction : CFG.Production AB PalindromeNT where
  lhs := PalindromeNT.S
  rhs :=
    [Symbol.terminal AB.b,
      Symbol.nonterminal PalindromeNT.S,
      Symbol.terminal AB.b]

/-!
For palindromes, finite production bookkeeping has five cases: the empty word,
the two one-letter words, and the two symmetric wrappers. Naming each production
keeps the generated-language proof readable later.
-/

theorem palindrome_has_finite_productions :
    CFG.HasFiniteProductions PalindromeGrammar := by
  exists [palindromeEmptyProduction, palindromeSingleAProduction,
    palindromeSingleBProduction, palindromeWrapAProduction,
    palindromeWrapBProduction]
  intro A rhs
  constructor
  · intro h
    cases h with
    | empty =>
        exact ⟨palindromeEmptyProduction, by simp [palindromeEmptyProduction],
          rfl, rfl⟩
    | singleA =>
        exact ⟨palindromeSingleAProduction,
          by simp [palindromeSingleAProduction], rfl, rfl⟩
    | singleB =>
        exact ⟨palindromeSingleBProduction,
          by simp [palindromeSingleBProduction], rfl, rfl⟩
    | wrapA =>
        exact ⟨palindromeWrapAProduction,
          by simp [palindromeWrapAProduction], rfl, rfl⟩
    | wrapB =>
        exact ⟨palindromeWrapBProduction,
          by simp [palindromeWrapBProduction], rfl, rfl⟩
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [palindromeEmptyProduction, palindromeSingleAProduction,
      palindromeSingleBProduction, palindromeWrapAProduction,
      palindromeWrapBProduction] at hmem
    rcases hmem with hrule | hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact PalindromeProduces.empty
    · subst rule
      cases hlhs
      cases hrhs
      exact PalindromeProduces.singleA
    · subst rule
      cases hlhs
      cases hrhs
      exact PalindromeProduces.singleB
    · subst rule
      cases hlhs
      cases hrhs
      exact PalindromeProduces.wrapA
    · subst rule
      cases hlhs
      cases hrhs
      exact PalindromeProduces.wrapB

theorem palindrome_single_a_form_language {w : Word AB}
    (hw : w ∈ CFG.FormLanguage PalindromeSymbolLanguage
      [Symbol.terminal AB.a]) :
    PalindromeAB w := by
  rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
  cases hfirst
  cases htail
  rw [hwEq]
  simpa [Word.Concat, Word.Symbol, Word.Empty] using PalindromeAB.singleA

theorem palindrome_single_b_form_language {w : Word AB}
    (hw : w ∈ CFG.FormLanguage PalindromeSymbolLanguage
      [Symbol.terminal AB.b]) :
    PalindromeAB w := by
  rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
  cases hfirst
  cases htail
  rw [hwEq]
  simpa [Word.Concat, Word.Symbol, Word.Empty] using PalindromeAB.singleB

theorem palindrome_wrap_a_form_language {w : Word AB}
    (hw : w ∈ CFG.FormLanguage PalindromeSymbolLanguage
      [Symbol.terminal AB.a,
        Symbol.nonterminal PalindromeNT.S,
        Symbol.terminal AB.a]) :
    PalindromeAB w := by
  rcases hw with ⟨leftWord, tail1, hleft, htail1, hwEq⟩
  cases hleft
  rcases htail1 with ⟨middle, tail2, hmiddle, htail2, htail1Eq⟩
  rcases htail2 with ⟨rightWord, tail3, hright, htail3, htail2Eq⟩
  cases hright
  cases htail3
  rw [hwEq, htail1Eq, htail2Eq]
  simpa [Word.Concat, Word.Symbol, Word.Empty, List.append_assoc] using
    PalindromeAB.wrapA hmiddle

theorem palindrome_wrap_b_form_language {w : Word AB}
    (hw : w ∈ CFG.FormLanguage PalindromeSymbolLanguage
      [Symbol.terminal AB.b,
        Symbol.nonterminal PalindromeNT.S,
        Symbol.terminal AB.b]) :
    PalindromeAB w := by
  rcases hw with ⟨leftWord, tail1, hleft, htail1, hwEq⟩
  cases hleft
  rcases htail1 with ⟨middle, tail2, hmiddle, htail2, htail1Eq⟩
  rcases htail2 with ⟨rightWord, tail3, hright, htail3, htail2Eq⟩
  cases hright
  cases htail3
  rw [hwEq, htail1Eq, htail2Eq]
  simpa [Word.Concat, Word.Symbol, Word.Empty, List.append_assoc] using
    PalindromeAB.wrapB hmiddle

theorem palindrome_production_sound
    (A : PalindromeNT) (rhs : SententialForm AB PalindromeNT)
    (hprod : PalindromeGrammar.produces A rhs) :
    forall w, w ∈ CFG.FormLanguage PalindromeSymbolLanguage rhs ->
      w ∈ PalindromeSymbolLanguage (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | empty =>
      cases hw
      exact PalindromeAB.empty
  | singleA =>
      exact palindrome_single_a_form_language hw
  | singleB =>
      exact palindrome_single_b_form_language hw
  | wrapA =>
      exact palindrome_wrap_a_form_language hw
  | wrapB =>
      exact palindrome_wrap_b_form_language hw

theorem palindrome_start_form_language {w : Word AB}
    (h : w ∈ CFG.FormLanguage PalindromeSymbolLanguage
      [Symbol.nonterminal PalindromeNT.S]) :
    PalindromeAB w := by
  rcases h with ⟨pal, tail, hpal, htail, hwEq⟩
  cases htail
  rw [hwEq]
  simpa [Word.Concat, Word.Empty] using hpal

theorem palindrome_generated_only_palindrome {w : Word AB}
    (h : w ∈ CFG.GeneratedLanguage PalindromeGrammar) :
    PalindromeAB w := by
  have hterminal : w ∈ CFG.FormLanguage PalindromeSymbolLanguage
      (SententialForm.terminalWord (nt := PalindromeNT) w) :=
    CFG.terminalWord_mem_formLanguage PalindromeSymbolLanguage
      (by intro sym; rfl) w
  exact palindrome_start_form_language
    (form_language_derives_sound_of_productions
      palindrome_production_sound h hterminal)

theorem palindrome_empty_generated :
    ([] : Word AB) ∈ CFG.GeneratedLanguage PalindromeGrammar := by
  apply CFG.yields_derives
  exists []
  exists []
  exists PalindromeNT.S
  exists ([] : SententialForm AB PalindromeNT)
  constructor
  · exact PalindromeProduces.empty
  constructor <;> rfl

theorem palindrome_single_a_generated :
    [AB.a] ∈ CFG.GeneratedLanguage PalindromeGrammar := by
  apply CFG.yields_derives
  exists []
  exists []
  exists PalindromeNT.S
  exists [Symbol.terminal AB.a]
  constructor
  · exact PalindromeProduces.singleA
  constructor <;> rfl

theorem palindrome_single_b_generated :
    [AB.b] ∈ CFG.GeneratedLanguage PalindromeGrammar := by
  apply CFG.yields_derives
  exists []
  exists []
  exists PalindromeNT.S
  exists [Symbol.terminal AB.b]
  constructor
  · exact PalindromeProduces.singleB
  constructor <;> rfl

/-!
The palindrome completeness proof is again constructive. The base productions
generate empty and singleton palindromes directly; the wrapper productions embed
an already generated palindrome in matching terminal symbols.
-/

theorem palindrome_wrap_a_generated {w : Word AB}
    (h : w ∈ CFG.GeneratedLanguage PalindromeGrammar) :
    AB.a :: Word.Concat w [AB.a] ∈
      CFG.GeneratedLanguage PalindromeGrammar := by
  have hStart : CFG.Yields PalindromeGrammar
      [Symbol.nonterminal PalindromeNT.S]
      [Symbol.terminal AB.a,
        Symbol.nonterminal PalindromeNT.S,
        Symbol.terminal AB.a] := by
    exists []
    exists []
    exists PalindromeNT.S
    exists [Symbol.terminal AB.a,
      Symbol.nonterminal PalindromeNT.S,
      Symbol.terminal AB.a]
    constructor
    · exact PalindromeProduces.wrapA
    constructor <;> rfl
  have hform :
      AB.a :: Word.Concat w [AB.a] ∈
        CFG.FormLanguage (CFG.DerivationSymbolLanguage PalindromeGrammar)
          [Symbol.terminal AB.a,
            Symbol.nonterminal PalindromeNT.S,
            Symbol.terminal AB.a] := by
    exists [AB.a]
    exists Word.Concat w [AB.a]
    constructor
    · rfl
    constructor
    · exists w
      exists [AB.a]
      constructor
      · exact h
      constructor
      · exact CFG.terminalWord_mem_formLanguage
          (CFG.DerivationSymbolLanguage PalindromeGrammar)
          (by intro sym; rfl) [AB.a]
      · rfl
    · rfl
  have hAll := CFG.Derives.step hStart (CFG.formLanguage_derives hform)
  change CFG.Derives PalindromeGrammar [Symbol.nonterminal PalindromeNT.S]
    (SententialForm.terminalWord (AB.a :: Word.Concat w [AB.a]))
  simpa [SententialForm.terminalWord, Word.Concat, List.append_assoc] using hAll

theorem palindrome_wrap_b_generated {w : Word AB}
    (h : w ∈ CFG.GeneratedLanguage PalindromeGrammar) :
    AB.b :: Word.Concat w [AB.b] ∈
      CFG.GeneratedLanguage PalindromeGrammar := by
  have hStart : CFG.Yields PalindromeGrammar
      [Symbol.nonterminal PalindromeNT.S]
      [Symbol.terminal AB.b,
        Symbol.nonterminal PalindromeNT.S,
        Symbol.terminal AB.b] := by
    exists []
    exists []
    exists PalindromeNT.S
    exists [Symbol.terminal AB.b,
      Symbol.nonterminal PalindromeNT.S,
      Symbol.terminal AB.b]
    constructor
    · exact PalindromeProduces.wrapB
    constructor <;> rfl
  have hform :
      AB.b :: Word.Concat w [AB.b] ∈
        CFG.FormLanguage (CFG.DerivationSymbolLanguage PalindromeGrammar)
          [Symbol.terminal AB.b,
            Symbol.nonterminal PalindromeNT.S,
            Symbol.terminal AB.b] := by
    exists [AB.b]
    exists Word.Concat w [AB.b]
    constructor
    · rfl
    constructor
    · exists w
      exists [AB.b]
      constructor
      · exact h
      constructor
      · exact CFG.terminalWord_mem_formLanguage
          (CFG.DerivationSymbolLanguage PalindromeGrammar)
          (by intro sym; rfl) [AB.b]
      · rfl
    · rfl
  have hAll := CFG.Derives.step hStart (CFG.formLanguage_derives hform)
  change CFG.Derives PalindromeGrammar [Symbol.nonterminal PalindromeNT.S]
    (SententialForm.terminalWord (AB.b :: Word.Concat w [AB.b]))
  simpa [SententialForm.terminalWord, Word.Concat, List.append_assoc] using hAll

theorem palindrome_words_generated {w : Word AB}
    (h : PalindromeAB w) :
    w ∈ CFG.GeneratedLanguage PalindromeGrammar := by
  induction h with
  | empty =>
      exact palindrome_empty_generated
  | singleA =>
      exact palindrome_single_a_generated
  | singleB =>
      exact palindrome_single_b_generated
  | wrapA hpal ih =>
      exact palindrome_wrap_a_generated ih
  | wrapB hpal ih =>
      exact palindrome_wrap_b_generated ih

theorem palindrome_generated_language_exact (w : Word AB) :
    w ∈ CFG.GeneratedLanguage PalindromeGrammar <-> PalindromeAB w := by
  constructor
  · exact palindrome_generated_only_palindrome
  · exact palindrome_words_generated

theorem palindrome_context_free :
    ContextFreeLanguage PalindromeAB := by
  exists PalindromeNT
  exists PalindromeGrammar
  constructor
  · exact palindrome_has_finite_productions
  · exact palindrome_generated_language_exact

/-!
The book defines a palindrome independently of any grammar: {lit}`w` is a
palindrome exactly when {lit}`w` equals its own reversal. The bridge below
proves that the inductive predicate targeted by the grammar exactness theorem
coincides with that reversal equation, so the palindrome grammar is connected
to the book's definition instead of only to a production-for-production mirror
of itself. The formalized alphabet is the two-letter {lit}`AB` alphabet,
whereas the book's exercise uses a three-letter example alphabet.
-/

theorem palindrome_reverse_eq {w : Word AB} (h : PalindromeAB w) :
    w = Word.Reverse w := by
  induction h with
  | empty => rfl
  | singleA => rfl
  | singleB => rfl
  | wrapA hw ih =>
      simp only [Word.Reverse, Word.Concat] at ih ⊢
      simp [List.reverse_append, ← ih]
  | wrapB hw ih =>
      simp only [Word.Reverse, Word.Concat] at ih ⊢
      simp [List.reverse_append, ← ih]

/-!
The converse peels one matching symbol off each end. Bounding the induction by
word length makes the middle word available to the induction hypothesis after
both ends are removed.
-/

private theorem palindrome_of_reverse_bounded :
    forall (n : Nat) (w : Word AB), Word.Length w <= n ->
      w = Word.Reverse w -> PalindromeAB w := by
  intro n
  induction n with
  | zero =>
      intro w hlen _hrev
      cases w with
      | nil => exact PalindromeAB.empty
      | cons c t => simp [Word.Length] at hlen
  | succ n ih =>
      intro w hlen hrev
      cases w with
      | nil => exact PalindromeAB.empty
      | cons c t =>
          rcases List.eq_nil_or_concat t with hnil | ⟨t', last, hconcat⟩
          · subst hnil
            cases c with
            | a => exact PalindromeAB.singleA
            | b => exact PalindromeAB.singleB
          · subst hconcat
            have h := hrev
            simp only [List.concat_eq_append, Word.Reverse, List.reverse_cons,
              List.reverse_append, List.reverse_nil, List.nil_append,
              List.cons_append] at h
            injection h with hcb htail
            subst hcb
            have hlen' : t'.length = t'.reverse.length :=
              List.length_reverse.symm
            have hinj := List.append_inj htail hlen'
            have hpal : t' = Word.Reverse t' := hinj.left
            have hlent : Word.Length t' <= n := by
              simp [Word.Length, List.concat_eq_append] at hlen ⊢
              lia
            have hmid := ih t' hlent hpal
            rw [List.concat_eq_append]
            cases c with
            | a => exact PalindromeAB.wrapA hmid
            | b => exact PalindromeAB.wrapB hmid

theorem palindrome_iff_reverse (w : Word AB) :
    PalindromeAB w <-> w = Word.Reverse w :=
  Iff.intro palindrome_reverse_eq
    (fun h => palindrome_of_reverse_bounded (Word.Length w) w (Nat.le_refl _) h)

theorem palindrome_generated_iff_reverse (w : Word AB) :
    w ∈ CFG.GeneratedLanguage PalindromeGrammar <-> w = Word.Reverse w :=
  Iff.trans (palindrome_generated_language_exact w) (palindrome_iff_reverse w)

theorem palindrome_reverse_language_context_free :
    ContextFreeLanguage (fun w : Word AB => w = Word.Reverse w) := by
  exists PalindromeNT
  exists PalindromeGrammar
  constructor
  · exact palindrome_has_finite_productions
  · exact palindrome_generated_iff_reverse

end Section01
end Chapter04
end Book
end FoC
