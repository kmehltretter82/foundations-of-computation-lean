import FoC.Book.Chapter04.Section01.Common

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section01

open Foundation
open Languages
open Grammars

/-!
# Balanced Parentheses

A one-bracket grammar is proved exactly equivalent both to an inductive balanced-word language and to the standard nonnegative-prefix counting characterization.
-/

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
  simpa [Word.Concat, Word.Empty] using! hbalanced

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
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      balanced_parens_has_finite_productions
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
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      balanced_parens_has_finite_productions
  · exact balanced_parens_generated_iff_count

end Section01
end Chapter04
end Book
end FoC
