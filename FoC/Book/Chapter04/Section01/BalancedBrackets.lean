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
# Balanced Brackets

The two-bracket grammar tracks matching round and square delimiters and is proved exactly equivalent to its inductive balanced-word language.
-/

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

def balancedBracketsProductionList :
    List (CFG.Production Bracket BalancedBracketsNT) :=
  [balancedBracketsEmptyProduction, balancedBracketsRoundPairProduction,
    balancedBracketsSquarePairProduction]

def BalancedBracketsGrammar : CFG Bracket BalancedBracketsNT :=
  CFG.ProductionList.toCFG BalancedBracketsNT.S BalancedBracketsNT.finite
    balancedBracketsProductionList

def balancedBracketsPresentation : CFG.Presentation BalancedBracketsGrammar :=
  CFG.ProductionList.presentation BalancedBracketsNT.S
    BalancedBracketsNT.finite balancedBracketsProductionList

theorem balanced_brackets_produces_iff
    (A : BalancedBracketsNT)
    (rhs : SententialForm Bracket BalancedBracketsNT) :
    BalancedBracketsGrammar.produces A rhs <->
      (A = BalancedBracketsNT.S ∧ rhs = []) ∨
      (A = BalancedBracketsNT.S ∧
        [Symbol.terminal Bracket.roundLeft,
          Symbol.nonterminal BalancedBracketsNT.S,
          Symbol.terminal Bracket.roundRight,
          Symbol.nonterminal BalancedBracketsNT.S] = rhs) ∨
      (A = BalancedBracketsNT.S ∧
        [Symbol.terminal Bracket.squareLeft,
          Symbol.nonterminal BalancedBracketsNT.S,
          Symbol.terminal Bracket.squareRight,
          Symbol.nonterminal BalancedBracketsNT.S] = rhs) := by
  simp [BalancedBracketsGrammar, CFG.ProductionList.toCFG,
    balancedBracketsProductionList, balancedBracketsEmptyProduction,
    balancedBracketsRoundPairProduction,
    balancedBracketsSquarePairProduction]

theorem balanced_brackets_empty_produces :
    BalancedBracketsGrammar.produces BalancedBracketsNT.S [] := by
  exact (balanced_brackets_produces_iff _ _).mpr (Or.inl ⟨rfl, rfl⟩)

theorem balanced_brackets_round_pair_produces :
    BalancedBracketsGrammar.produces BalancedBracketsNT.S
      [Symbol.terminal Bracket.roundLeft,
        Symbol.nonterminal BalancedBracketsNT.S,
        Symbol.terminal Bracket.roundRight,
        Symbol.nonterminal BalancedBracketsNT.S] := by
  exact (balanced_brackets_produces_iff _ _).mpr
    (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem balanced_brackets_square_pair_produces :
    BalancedBracketsGrammar.produces BalancedBracketsNT.S
      [Symbol.terminal Bracket.squareLeft,
        Symbol.nonterminal BalancedBracketsNT.S,
        Symbol.terminal Bracket.squareRight,
        Symbol.nonterminal BalancedBracketsNT.S] := by
  exact (balanced_brackets_produces_iff _ _).mpr
    (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem balanced_brackets_has_finite_productions :
    CFG.HasFiniteProductions BalancedBracketsGrammar :=
  CFG.hasFiniteProductions_of_hasFinitePresentation
    ⟨balancedBracketsPresentation⟩

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
  rcases (balanced_brackets_produces_iff A rhs).mp hprod with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
      cases hw
      exact BalancedBrackets.empty
  ·
      exact balanced_brackets_round_pair_form_language hw
  ·
      exact balanced_brackets_square_pair_form_language hw

theorem balanced_brackets_start_form_language
    {w : Word Bracket}
    (h : w ∈ CFG.FormLanguage BalancedBracketsSymbolLanguage
      [Symbol.nonterminal BalancedBracketsNT.S]) :
    BalancedBrackets w := by
  rcases h with ⟨balanced, tail, hbalanced, htail, hwEq⟩
  cases htail
  rw [hwEq]
  simpa [Word.Concat, Word.Empty] using! hbalanced

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
  · exact balanced_brackets_empty_produces
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
    · exact balanced_brackets_round_pair_produces
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
    · exact balanced_brackets_square_pair_produces
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
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      balanced_brackets_has_finite_productions
  · exact balanced_brackets_generated_language_exact

end Section01
end Chapter04
end Book
end FoC
