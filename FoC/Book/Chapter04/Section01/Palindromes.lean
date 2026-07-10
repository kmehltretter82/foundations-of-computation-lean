import FoC.Book.Chapter04.Section01.AnBn

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section01

open Foundation
open Languages
open Grammars

/-!
# Binary Palindromes

A finite CFG is proved exactly equivalent to the inductive binary-palindrome language and to equality with word reversal.
-/

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
  simpa [Word.Concat, Word.Empty] using! hpal

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
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      palindrome_has_finite_productions
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
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      palindrome_has_finite_productions
  · exact palindrome_generated_iff_reverse

end Section01
end Chapter04
end Book
end FoC
