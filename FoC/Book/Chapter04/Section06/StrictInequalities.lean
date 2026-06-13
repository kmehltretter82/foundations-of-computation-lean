import FoC.Book.Chapter04.Section06.OrderedABCD

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Section 4.6 strict block inequalities
-/

open Languages
open Grammars

/-!
# Strict Block Inequalities

The strict-more-{lit}`b` grammar generates ordered block words with more {lit}`b`s than
{lit}`a`s. The proof uses a tail phase that adds at least one extra {lit}`b` after all
balanced {lit}`a`/{lit}`b` pairs have been produced.
-/

inductive StrictMoreBNT where
  | start
  | tail
deriving DecidableEq

namespace StrictMoreBNT

def finite : Foundation.FiniteType StrictMoreBNT where
  elems := [start, tail]
  complete := by
    intro A
    cases A <;> simp

end StrictMoreBNT

def moreBN (A : StrictMoreBNT) :
    Symbol EqualCountTerminal StrictMoreBNT :=
  ggNonterminal A

def moreBT (tok : EqualCountTerminal) :
    Symbol EqualCountTerminal StrictMoreBNT :=
  ggTerminal tok

inductive StrictMoreBProduces :
    SententialForm EqualCountTerminal StrictMoreBNT ->
      SententialForm EqualCountTerminal StrictMoreBNT -> Prop where
  | wrapPair :
      StrictMoreBProduces [moreBN StrictMoreBNT.start]
        [moreBT EqualCountTerminal.a, moreBN StrictMoreBNT.start,
          moreBT EqualCountTerminal.b]
  | toTail :
      StrictMoreBProduces [moreBN StrictMoreBNT.start]
        [moreBN StrictMoreBNT.tail]
  | tailMore :
      StrictMoreBProduces [moreBN StrictMoreBNT.tail]
        [moreBT EqualCountTerminal.b, moreBN StrictMoreBNT.tail]
  | tailOne :
      StrictMoreBProduces [moreBN StrictMoreBNT.tail]
        [moreBT EqualCountTerminal.b]

def StrictMoreBGrammar :
    GeneralGrammar EqualCountTerminal StrictMoreBNT where
  start := StrictMoreBNT.start
  produces := StrictMoreBProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, moreBN,
      ggNonterminal]
  nonterminalsFinite := StrictMoreBNT.finite

def StrictMoreBProductionList :
    List (GeneralGrammar.Production EqualCountTerminal StrictMoreBNT) :=
  [{ lhs := [moreBN StrictMoreBNT.start],
     rhs := [moreBT EqualCountTerminal.a, moreBN StrictMoreBNT.start,
       moreBT EqualCountTerminal.b] },
   { lhs := [moreBN StrictMoreBNT.start],
     rhs := [moreBN StrictMoreBNT.tail] },
   { lhs := [moreBN StrictMoreBNT.tail],
     rhs := [moreBT EqualCountTerminal.b, moreBN StrictMoreBNT.tail] },
   { lhs := [moreBN StrictMoreBNT.tail],
     rhs := [moreBT EqualCountTerminal.b] }]

theorem strictMoreBGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions StrictMoreBGrammar := by
  exists StrictMoreBProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [StrictMoreBProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [StrictMoreBProductionList] at hmem
    rcases hmem with hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictMoreBProduces.wrapPair
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictMoreBProduces.toTail
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictMoreBProduces.tailMore
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictMoreBProduces.tailOne

theorem strictMoreBGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage StrictMoreBGrammar) := by
  exists StrictMoreBNT
  exists StrictMoreBGrammar
  constructor
  · exact strictMoreBGrammar_has_finite_productions
  · intro word
    rfl

def strictMoreBCountA
    (sf : SententialForm EqualCountTerminal StrictMoreBNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.a sf

def strictMoreBCountBWithCredits
    (sf : SententialForm EqualCountTerminal StrictMoreBNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.b sf +
    SententialCountNonterminal StrictMoreBNT.start sf +
    SententialCountNonterminal StrictMoreBNT.tail sf

def strictMoreBMargin
    (sf : SententialForm EqualCountTerminal StrictMoreBNT) : Prop :=
  strictMoreBCountA sf < strictMoreBCountBWithCredits sf

theorem strictMoreB_start_margin :
    strictMoreBMargin [moreBN StrictMoreBNT.start] := by
  simp [strictMoreBMargin, strictMoreBCountA,
    strictMoreBCountBWithCredits, SententialCountTerminal,
    SententialCountNonterminal, moreBN, ggNonterminal]

theorem strictMoreB_yields_preserves_margin
    {x y : SententialForm EqualCountTerminal StrictMoreBNT}
    (h : GeneralGrammar.Yields StrictMoreBGrammar x y) :
    strictMoreBMargin x -> strictMoreBMargin y := by
  intro hmargin
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro lhs hlhs =>
              cases hlhs with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hx] at hmargin
                          rw [hy]
                          cases hprod <;>
                            simp [strictMoreBMargin, strictMoreBCountA,
                              strictMoreBCountBWithCredits,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, moreBN, moreBT,
                              ggNonterminal, ggTerminal] at hmargin ⊢ <;>
                            omega

theorem strictMoreB_derives_preserves_margin
    {x y : SententialForm EqualCountTerminal StrictMoreBNT}
    (h : GeneralGrammar.Derives StrictMoreBGrammar x y) :
    strictMoreBMargin x -> strictMoreBMargin y := by
  induction h with
  | refl _ =>
      intro hmargin
      exact hmargin
  | step hstep _ ih =>
      intro hmargin
      exact ih (strictMoreB_yields_preserves_margin hstep hmargin)

theorem strictMoreBGrammar_generated_has_fewer_as_than_bs
    {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage StrictMoreBGrammar) :
    Word.Count EqualCountTerminal.a word <
      Word.Count EqualCountTerminal.b word := by
  have hderives :
      GeneralGrammar.Derives StrictMoreBGrammar
        [moreBN StrictMoreBNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
      ggNonterminal] using h
  have hmargin :=
    strictMoreB_derives_preserves_margin hderives
      strictMoreB_start_margin
  simpa [strictMoreBMargin, strictMoreBCountA,
    strictMoreBCountBWithCredits, sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hmargin

def strictMoreBWord (n extra : Nat) : Word EqualCountTerminal :=
  Word.Concat (Word.RepeatSymbol EqualCountTerminal.a n)
    (Word.RepeatSymbol EqualCountTerminal.b (n + extra + 1))

def strictMoreBTailWord (extra : Nat) : Word EqualCountTerminal :=
  Word.RepeatSymbol EqualCountTerminal.b (extra + 1)

def strictMoreBLanguage : Language EqualCountTerminal :=
  fun word => exists n extra, word = strictMoreBWord n extra

def strictMoreBTailLanguage : Language EqualCountTerminal :=
  fun word => exists extra, word = strictMoreBTailWord extra

/-!
Generation and soundness split cleanly here. Generation wraps balanced
{lit}`a`/{lit}`b` pairs around a tail with at least one extra {lit}`b`; soundness
uses the two nonterminal meanings below to prove no other shape can be
generated.
-/

theorem strictMoreB_word_zero (extra : Nat) :
    strictMoreBWord 0 extra = strictMoreBTailWord extra := by
  simp [strictMoreBWord, strictMoreBTailWord, Word.Concat,
    Word.RepeatSymbol]

theorem strictMoreB_tail_more_word (extra : Nat) :
    EqualCountTerminal.b :: strictMoreBTailWord extra =
      strictMoreBTailWord (extra + 1) := by
  unfold strictMoreBTailWord
  rw [show extra + 1 + 1 = (extra + 1) + 1 by omega]
  rfl

theorem strictMoreB_wrap_word (n extra : Nat) :
    EqualCountTerminal.a ::
        Word.Concat (strictMoreBWord n extra) [EqualCountTerminal.b] =
      strictMoreBWord (n + 1) extra := by
  unfold strictMoreBWord
  rw [show Word.RepeatSymbol EqualCountTerminal.a (n + 1) =
    EqualCountTerminal.a :: Word.RepeatSymbol EqualCountTerminal.a n by rfl]
  have hb :
      Word.RepeatSymbol EqualCountTerminal.b (n + 1 + extra + 1) =
        Word.Concat
          (Word.RepeatSymbol EqualCountTerminal.b (n + extra + 1))
          [EqualCountTerminal.b] := by
    have hnat : n + 1 + extra + 1 = (n + extra + 1) + 1 := by
      omega
    rw [hnat, repeatSymbol_succ_eq_append]
  rw [hb]
  simp [Word.Concat, List.append_assoc]

def strictMoreBSymbolLanguage :
    Symbol EqualCountTerminal StrictMoreBNT -> Language EqualCountTerminal
  | Symbol.terminal token => Language.Singleton (Word.Symbol token)
  | Symbol.nonterminal StrictMoreBNT.start => strictMoreBLanguage
  | Symbol.nonterminal StrictMoreBNT.tail => strictMoreBTailLanguage

theorem strictMoreB_tail_one_derives :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
      (SententialForm.terminalWord (strictMoreBTailWord 0)) := by
  have hstep :
      GeneralGrammar.Yields StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
        [moreBT EqualCountTerminal.b] := by
    simpa [moreBN, moreBT] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.tailOne [] []
  simpa [strictMoreBTailWord, SententialForm.terminalWord,
    Word.RepeatSymbol, moreBT] using
    GeneralGrammar.yields_derives hstep

theorem strictMoreB_tail_more_derives {word : Word EqualCountTerminal}
    (h : GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
      (SententialForm.terminalWord word)) :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
      (SententialForm.terminalWord (EqualCountTerminal.b :: word)) := by
  have hstep :
      GeneralGrammar.Yields StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
        [moreBT EqualCountTerminal.b, moreBN StrictMoreBNT.tail] := by
    simpa [moreBN, moreBT] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.tailMore [] []
  have hcontext :
      GeneralGrammar.Derives StrictMoreBGrammar
        [moreBT EqualCountTerminal.b, moreBN StrictMoreBNT.tail]
        (moreBT EqualCountTerminal.b :: SententialForm.terminalWord word) := by
    simpa [moreBT] using
      general_derives_context h [moreBT EqualCountTerminal.b] []
  exact GeneralGrammar.Derives.step hstep (by
    simpa [SententialForm.terminalWord, moreBT] using hcontext)

theorem strictMoreB_tail_words_derives (extra : Nat) :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
      (SententialForm.terminalWord (strictMoreBTailWord extra)) := by
  induction extra with
  | zero =>
      exact strictMoreB_tail_one_derives
  | succ extra ih =>
      simpa [strictMoreB_tail_more_word extra] using
        strictMoreB_tail_more_derives ih

theorem strictMoreB_zero_words_derives (extra : Nat) :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.start]
      (SententialForm.terminalWord (strictMoreBWord 0 extra)) := by
  have hstep :
      GeneralGrammar.Yields StrictMoreBGrammar [moreBN StrictMoreBNT.start]
        [moreBN StrictMoreBNT.tail] := by
    simpa [moreBN] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.toTail [] []
  have htail := strictMoreB_tail_words_derives extra
  have hall := GeneralGrammar.Derives.step hstep htail
  simpa [strictMoreB_word_zero] using hall

theorem strictMoreB_wrap_derives {word : Word EqualCountTerminal}
    (h : GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.start]
      (SententialForm.terminalWord word)) :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.start]
      (SententialForm.terminalWord
        (EqualCountTerminal.a :: Word.Concat word [EqualCountTerminal.b])) := by
  have hstep :
      GeneralGrammar.Yields StrictMoreBGrammar [moreBN StrictMoreBNT.start]
        [moreBT EqualCountTerminal.a, moreBN StrictMoreBNT.start,
          moreBT EqualCountTerminal.b] := by
    simpa [moreBN, moreBT] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.wrapPair [] []
  have hcontext :
      GeneralGrammar.Derives StrictMoreBGrammar
        [moreBT EqualCountTerminal.a, moreBN StrictMoreBNT.start,
          moreBT EqualCountTerminal.b]
        (moreBT EqualCountTerminal.a ::
          SententialForm.terminalWord word ++ [moreBT EqualCountTerminal.b]) := by
    simpa [moreBT] using
      general_derives_context h [moreBT EqualCountTerminal.a]
        [moreBT EqualCountTerminal.b]
  have hall := GeneralGrammar.Derives.step hstep hcontext
  change GeneralGrammar.Derives StrictMoreBGrammar
    [moreBN StrictMoreBNT.start]
    (SententialForm.terminalWord
      (EqualCountTerminal.a :: Word.Concat word [EqualCountTerminal.b]))
  simpa [SententialForm.terminalWord, Word.Concat, moreBT] using hall

theorem strictMoreB_words_generated (n extra : Nat) :
    strictMoreBWord n extra ∈
      GeneralGrammar.GeneratedLanguage StrictMoreBGrammar := by
  induction n with
  | zero =>
      simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
        ggNonterminal] using strictMoreB_zero_words_derives extra
  | succ n ih =>
      have hderives :
          GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.start]
            (SententialForm.terminalWord
              (EqualCountTerminal.a ::
                Word.Concat (strictMoreBWord n extra)
                  [EqualCountTerminal.b])) := by
        exact strictMoreB_wrap_derives (by
          simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
            ggNonterminal] using ih)
      simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
        ggNonterminal, strictMoreB_wrap_word n extra] using hderives

/-!
The strict-more-b grammar uses a margin invariant instead of equality. Its
soundness proof shows that every production preserves a positive surplus of
b-symbol credit over a-symbol demand.
-/

theorem strictMoreB_production_sound
    (lhs rhs : SententialForm EqualCountTerminal StrictMoreBNT)
    (hprod : StrictMoreBGrammar.produces lhs rhs) :
    forall word,
      word ∈ CFG.FormLanguage strictMoreBSymbolLanguage rhs ->
        word ∈ CFG.FormLanguage strictMoreBSymbolLanguage lhs := by
  intro word hword
  cases hprod with
  | wrapPair =>
      simp [CFG.FormLanguage, strictMoreBSymbolLanguage,
        moreBN, moreBT, ggNonterminal, ggTerminal] at hword
      rcases hword with
        ⟨first, tail, hfirst, htail, hwordEq⟩
      rcases htail with
        ⟨middle, lastPart, hmiddle, hlastPart, htailEq⟩
      rcases hmiddle with ⟨n, extra, hmiddleEq⟩
      rcases hlastPart with
        ⟨last, empty, hlast, hempty, hlastPartEq⟩
      refine ⟨strictMoreBWord (n + 1) extra, Word.Empty,
        ⟨n + 1, extra, rfl⟩, rfl, ?_⟩
      rw [hwordEq, hfirst, htailEq, hmiddleEq, hlastPartEq, hlast,
        hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using
        strictMoreB_wrap_word n extra
  | toTail =>
      simp [CFG.FormLanguage, strictMoreBSymbolLanguage,
        moreBN, ggNonterminal] at hword
      rcases hword with ⟨tailWord, empty, htailWord, hempty, hwordEq⟩
      rcases htailWord with ⟨extra, htailWordEq⟩
      refine ⟨strictMoreBWord 0 extra, Word.Empty,
        ⟨0, extra, rfl⟩, rfl, ?_⟩
      rw [hwordEq, htailWordEq, hempty]
      simp [Word.Concat, Word.Empty, strictMoreB_word_zero extra]
  | tailMore =>
      simp [CFG.FormLanguage, strictMoreBSymbolLanguage,
        moreBN, moreBT, ggNonterminal, ggTerminal] at hword
      rcases hword with
        ⟨first, tail, hfirst, htail, hwordEq⟩
      rcases htail with
        ⟨middle, empty, hmiddle, hempty, htailEq⟩
      rcases hmiddle with ⟨extra, hmiddleEq⟩
      refine ⟨strictMoreBTailWord (extra + 1), Word.Empty,
        ⟨extra + 1, rfl⟩, rfl, ?_⟩
      rw [hwordEq, hfirst, htailEq, hmiddleEq, hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using
        strictMoreB_tail_more_word extra
  | tailOne =>
      simp [CFG.FormLanguage, strictMoreBSymbolLanguage,
        moreBT, ggTerminal] at hword
      rcases hword with ⟨first, empty, hfirst, hempty, hwordEq⟩
      refine ⟨strictMoreBTailWord 0, Word.Empty, ⟨0, rfl⟩, rfl, ?_⟩
      rw [hwordEq, hfirst, hempty]
      simp [strictMoreBTailWord, Word.Symbol, Word.Concat, Word.Empty,
        Word.RepeatSymbol]

theorem strictMoreB_generated_only_language {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage StrictMoreBGrammar) :
    word ∈ strictMoreBLanguage := by
  have hderives :
      GeneralGrammar.Derives StrictMoreBGrammar
        [moreBN StrictMoreBNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
      ggNonterminal] using h
  have hs := general_derives_sound_for_symbol_language
    strictMoreBSymbolLanguage (by intro token; rfl)
    strictMoreB_production_sound hderives
  simp [CFG.FormLanguage, strictMoreBSymbolLanguage] at hs
  rcases hs with ⟨startWord, empty, hstartWord, hempty, hwordEq⟩
  rw [hwordEq]
  have hemptyEq : empty = Word.Empty := hempty
  rw [hemptyEq, Word.concat_empty_right]
  exact hstartWord

theorem strictMoreB_generated_language_exact (word : Word EqualCountTerminal) :
    word ∈ GeneralGrammar.GeneratedLanguage StrictMoreBGrammar <->
      word ∈ strictMoreBLanguage := by
  constructor
  · exact strictMoreB_generated_only_language
  · intro h
    rcases h with ⟨n, extra, hword⟩
    rw [hword]
    exact strictMoreB_words_generated n extra

theorem strictMoreBLanguage_finite_production_generated :
    FiniteProductionGeneralLanguage strictMoreBLanguage := by
  exists StrictMoreBNT
  exists StrictMoreBGrammar
  constructor
  · exact strictMoreBGrammar_has_finite_productions
  · intro word
    exact strictMoreB_generated_language_exact word

def aabbbWord : Word EqualCountTerminal :=
  [EqualCountTerminal.a, EqualCountTerminal.a, EqualCountTerminal.b,
    EqualCountTerminal.b, EqualCountTerminal.b]

theorem strictMoreBGrammar_generates_aabbb :
    aabbbWord ∈ GeneralGrammar.GeneratedLanguage StrictMoreBGrammar := by
  let S := moreBN StrictMoreBNT.start
  let T := moreBN StrictMoreBNT.tail
  let a := moreBT EqualCountTerminal.a
  let b := moreBT EqualCountTerminal.b
  have h1 :
      GeneralGrammar.Yields StrictMoreBGrammar [S] [a, S, b] := by
    simpa [S, a, b] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.wrapPair [] []
  have h2 :
      GeneralGrammar.Yields StrictMoreBGrammar [a, S, b]
        [a, a, S, b, b] := by
    simpa [S, a, b] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.wrapPair [a] [b]
  have h3 :
      GeneralGrammar.Yields StrictMoreBGrammar [a, a, S, b, b]
        [a, a, T, b, b] := by
    simpa [S, T, a, b] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.toTail [a, a] [b, b]
  have h4 :
      GeneralGrammar.Yields StrictMoreBGrammar [a, a, T, b, b]
        [a, a, b, b, b] := by
    simpa [T, a, b] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.tailOne [a, a] [b, b]
  have hderives :
      GeneralGrammar.Derives StrictMoreBGrammar [S]
        [a, a, b, b, b] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.refl [a, a, b, b, b]))))
  simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, aabbbWord,
    SententialForm.terminalWord, S, a, b] using hderives

/-!
# Strict Three-Way Counts

This grammar targets strict count inequalities among {lit}`a`, {lit}`b`, and {lit}`c`
symbols. The invariant records count margins so each production can be checked
locally against the intended strict ordering.
-/

inductive StrictABCGreaterNT where
  | start
  | pair
  | extraA
  | done
  | markA
  | markB
  | markC
deriving DecidableEq

namespace StrictABCGreaterNT

def finite : Foundation.FiniteType StrictABCGreaterNT where
  elems := [start, pair, extraA, done, markA, markB, markC]
  complete := by
    intro A
    cases A <;> simp

end StrictABCGreaterNT

def strictABCGreaterN (A : StrictABCGreaterNT) :
    Symbol EqualCountTerminal StrictABCGreaterNT :=
  ggNonterminal A

def strictABCGreaterT (tok : EqualCountTerminal) :
    Symbol EqualCountTerminal StrictABCGreaterNT :=
  ggTerminal tok

inductive StrictABCGreaterProduces :
    SententialForm EqualCountTerminal StrictABCGreaterNT ->
      SententialForm EqualCountTerminal StrictABCGreaterNT -> Prop where
  | growTriple :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.start]
        [strictABCGreaterN StrictABCGreaterNT.start,
          strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markC]
  | toPair :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.start]
        [strictABCGreaterN StrictABCGreaterNT.pair]
  | growPair :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.pair]
        [strictABCGreaterN StrictABCGreaterNT.pair,
          strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB]
  | endPair :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.pair]
        [strictABCGreaterN StrictABCGreaterNT.extraA,
          strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB]
  | growExtraA :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.extraA]
        [strictABCGreaterN StrictABCGreaterNT.extraA,
          strictABCGreaterN StrictABCGreaterNT.markA]
  | endExtraA :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.extraA]
        [strictABCGreaterN StrictABCGreaterNT.done,
          strictABCGreaterN StrictABCGreaterNT.markA]
  | finish :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.done] []
  | swapAB :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB]
        [strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markA]
  | swapBA :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markA]
        [strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB]
  | swapAC :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markC]
        [strictABCGreaterN StrictABCGreaterNT.markC,
          strictABCGreaterN StrictABCGreaterNT.markA]
  | swapCA :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markC,
          strictABCGreaterN StrictABCGreaterNT.markA]
        [strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markC]
  | swapBC :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markC]
        [strictABCGreaterN StrictABCGreaterNT.markC,
          strictABCGreaterN StrictABCGreaterNT.markB]
  | swapCB :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markC,
          strictABCGreaterN StrictABCGreaterNT.markB]
        [strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markC]
  | emitA :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.markA]
        [strictABCGreaterT EqualCountTerminal.a]
  | emitB :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.markB]
        [strictABCGreaterT EqualCountTerminal.b]
  | emitC :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.markC]
        [strictABCGreaterT EqualCountTerminal.c]

def StrictABCGreaterGrammar :
    GeneralGrammar EqualCountTerminal StrictABCGreaterNT where
  start := StrictABCGreaterNT.start
  produces := StrictABCGreaterProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal,
      strictABCGreaterN, ggNonterminal]
  nonterminalsFinite := StrictABCGreaterNT.finite

def StrictABCGreaterProductionList :
    List (GeneralGrammar.Production EqualCountTerminal StrictABCGreaterNT) :=
  [{ lhs := [strictABCGreaterN StrictABCGreaterNT.start],
     rhs := [strictABCGreaterN StrictABCGreaterNT.start,
       strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markC] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.start],
     rhs := [strictABCGreaterN StrictABCGreaterNT.pair] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.pair],
     rhs := [strictABCGreaterN StrictABCGreaterNT.pair,
       strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.pair],
     rhs := [strictABCGreaterN StrictABCGreaterNT.extraA,
       strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.extraA],
     rhs := [strictABCGreaterN StrictABCGreaterNT.extraA,
       strictABCGreaterN StrictABCGreaterNT.markA] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.extraA],
     rhs := [strictABCGreaterN StrictABCGreaterNT.done,
       strictABCGreaterN StrictABCGreaterNT.markA] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.done],
     rhs := [] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markA] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markA],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markC],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markC,
       strictABCGreaterN StrictABCGreaterNT.markA] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markC,
       strictABCGreaterN StrictABCGreaterNT.markA],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markC] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markC],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markC,
       strictABCGreaterN StrictABCGreaterNT.markB] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markC,
       strictABCGreaterN StrictABCGreaterNT.markB],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markC] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markA],
     rhs := [strictABCGreaterT EqualCountTerminal.a] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markB],
     rhs := [strictABCGreaterT EqualCountTerminal.b] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markC],
     rhs := [strictABCGreaterT EqualCountTerminal.c] }]

/-!
The strict-count grammar records inequalities rather than equalities. Its
production list and margin invariant are separated so the non-context-free
witnesses can reuse the generated-language facts without reopening the grammar.
-/

theorem strictABCGreaterGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions StrictABCGreaterGrammar := by
  exists StrictABCGreaterProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [StrictABCGreaterProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [StrictABCGreaterProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.growTriple
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.toPair
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.growPair
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.endPair
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.growExtraA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.endExtraA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.finish
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapAB
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapAC
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapBC
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.emitA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.emitB
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.emitC

/-!
After finite production bookkeeping, the strict grammar proves that every
generated terminal word has the required margin property. This is the semantic
half used by the closure counterexamples.
-/

theorem strictABCGreaterGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage StrictABCGreaterGrammar) := by
  exists StrictABCGreaterNT
  exists StrictABCGreaterGrammar
  constructor
  · exact strictABCGreaterGrammar_has_finite_productions
  · intro word
    rfl

def strictABCGreaterTotalA
    (sf : SententialForm EqualCountTerminal StrictABCGreaterNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.a sf +
    SententialCountNonterminal StrictABCGreaterNT.markA sf +
    2 * SententialCountNonterminal StrictABCGreaterNT.start sf +
    2 * SententialCountNonterminal StrictABCGreaterNT.pair sf +
    SententialCountNonterminal StrictABCGreaterNT.extraA sf

def strictABCGreaterTotalB
    (sf : SententialForm EqualCountTerminal StrictABCGreaterNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.b sf +
    SententialCountNonterminal StrictABCGreaterNT.markB sf +
    SententialCountNonterminal StrictABCGreaterNT.start sf +
    SententialCountNonterminal StrictABCGreaterNT.pair sf

def strictABCGreaterTotalC
    (sf : SententialForm EqualCountTerminal StrictABCGreaterNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.c sf +
    SententialCountNonterminal StrictABCGreaterNT.markC sf

def strictABCGreaterMargin
    (sf : SententialForm EqualCountTerminal StrictABCGreaterNT) : Prop :=
  strictABCGreaterTotalA sf > strictABCGreaterTotalB sf ∧
    strictABCGreaterTotalB sf > strictABCGreaterTotalC sf

theorem strictABCGreater_start_margin :
    strictABCGreaterMargin
      [strictABCGreaterN StrictABCGreaterNT.start] := by
  simp [strictABCGreaterMargin, strictABCGreaterTotalA,
    strictABCGreaterTotalB, strictABCGreaterTotalC,
    SententialCountTerminal, SententialCountNonterminal,
    strictABCGreaterN, ggNonterminal]

theorem strictABCGreater_yields_preserves_margin
    {x y : SententialForm EqualCountTerminal StrictABCGreaterNT}
    (h : GeneralGrammar.Yields StrictABCGreaterGrammar x y) :
    strictABCGreaterMargin x -> strictABCGreaterMargin y := by
  intro hmargin
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro lhs hlhs =>
              cases hlhs with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hx] at hmargin
                          rw [hy]
                          cases hprod <;>
                            simp [strictABCGreaterMargin,
                              strictABCGreaterTotalA,
                              strictABCGreaterTotalB,
                              strictABCGreaterTotalC,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal,
                              strictABCGreaterN, strictABCGreaterT,
                              ggNonterminal, ggTerminal] at hmargin ⊢ <;>
                            omega

theorem strictABCGreater_derives_preserves_margin
    {x y : SententialForm EqualCountTerminal StrictABCGreaterNT}
    (h : GeneralGrammar.Derives StrictABCGreaterGrammar x y) :
    strictABCGreaterMargin x -> strictABCGreaterMargin y := by
  induction h with
  | refl _ =>
      intro hmargin
      exact hmargin
  | step hstep _ ih =>
      intro hmargin
      exact ih (strictABCGreater_yields_preserves_margin hstep hmargin)

theorem strictABCGreaterGrammar_generated_has_strict_counts
    {word : Word EqualCountTerminal}
    (h : word ∈
      GeneralGrammar.GeneratedLanguage StrictABCGreaterGrammar) :
    Word.Count EqualCountTerminal.a word >
        Word.Count EqualCountTerminal.b word ∧
      Word.Count EqualCountTerminal.b word >
        Word.Count EqualCountTerminal.c word := by
  have hderives :
      GeneralGrammar.Derives StrictABCGreaterGrammar
        [strictABCGreaterN StrictABCGreaterNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, StrictABCGreaterGrammar,
      strictABCGreaterN, ggNonterminal] using h
  have hmargin :=
    strictABCGreater_derives_preserves_margin hderives
      strictABCGreater_start_margin
  simpa [strictABCGreaterMargin, strictABCGreaterTotalA,
    strictABCGreaterTotalB, strictABCGreaterTotalC,
    sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hmargin

/-!
The strict three-way grammar is used mainly as a count-invariant example. It
guarantees a strict inequality among the three terminal counts, and the concrete
derivation below witnesses a small generated word.
-/

def strictABCGreaterAABWord : Word EqualCountTerminal :=
  [EqualCountTerminal.a, EqualCountTerminal.a, EqualCountTerminal.b]

theorem strictABCGreaterGrammar_generates_aab :
    strictABCGreaterAABWord ∈
      GeneralGrammar.GeneratedLanguage StrictABCGreaterGrammar := by
  let S := strictABCGreaterN StrictABCGreaterNT.start
  let P := strictABCGreaterN StrictABCGreaterNT.pair
  let X := strictABCGreaterN StrictABCGreaterNT.extraA
  let R := strictABCGreaterN StrictABCGreaterNT.done
  let A := strictABCGreaterN StrictABCGreaterNT.markA
  let B := strictABCGreaterN StrictABCGreaterNT.markB
  let a := strictABCGreaterT EqualCountTerminal.a
  let b := strictABCGreaterT EqualCountTerminal.b
  have h1 : GeneralGrammar.Yields StrictABCGreaterGrammar [S] [P] := by
    simpa [S, P] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.toPair [] []
  have h2 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [P] [X, A, B] := by
    simpa [P, X, A, B] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.endPair [] []
  have h3 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [X, A, B]
        [R, A, A, B] := by
    simpa [X, R, A, B] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.endExtraA [] [A, B]
  have h4 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [R, A, A, B]
        [A, A, B] := by
    simpa [R, A, B] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.finish [] [A, A, B]
  have h5 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [A, A, B]
        [a, A, B] := by
    simpa [A, B, a] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.emitA [] [A, B]
  have h6 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [a, A, B]
        [a, a, B] := by
    simpa [A, B, a] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.emitA [a] [B]
  have h7 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [a, a, B]
        [a, a, b] := by
    simpa [A, B, a, b] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.emitB [a, a] []
  have hderives :
      GeneralGrammar.Derives StrictABCGreaterGrammar [S] [a, a, b] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.step h6
                (GeneralGrammar.Derives.step h7
                  (GeneralGrammar.Derives.refl [a, a, b])))))))
  simpa [GeneralGrammar.GeneratedLanguage, StrictABCGreaterGrammar,
    strictABCGreaterAABWord, SententialForm.terminalWord, S, a, b] using
    hderives


end Section06
end Chapter04
end Book
end FoC
