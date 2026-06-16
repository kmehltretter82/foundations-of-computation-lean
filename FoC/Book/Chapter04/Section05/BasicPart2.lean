import FoC.Book.Chapter04.Section05.BasicPart1

namespace FoC
namespace Book
namespace Chapter04
namespace Section05
open Languages
open Grammars

theorem anbnCstar_production_sound
    (A : AnBnCstarNT) (rhs : SententialForm ABC AnBnCstarNT)
    (hprod : AnBnCstarGrammar.produces A rhs) :
    forall w, w ∈ CFG.FormLanguage anbnCstarSymbolLanguage rhs ->
      w ∈ anbnCstarSymbolLanguage (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | startRule =>
      simp [CFG.FormLanguage, anbnCstarSymbolLanguage] at hw
      rcases hw with ⟨pairWord, tail, hpair, htail, _hwEq⟩
      rcases hpair with ⟨n, hn⟩
      rcases htail with ⟨cWord, empty, hcWord, _hempty, _htailEq⟩
      rcases hcWord with ⟨k, hk⟩
      exists n
      exists k
      subst pairWord
      subst cWord
      subst empty
      subst tail
      subst w
      simp [anbnCstarWord, Word.Concat, Word.Empty]
  | pairWrap =>
      simp [CFG.FormLanguage, anbnCstarSymbolLanguage] at hw
      rcases hw with ⟨first, tail, _hfirst, htail, _hwEq⟩
      rcases htail with ⟨middle, last, hmiddle, hlast, _htailEq⟩
      rcases hmiddle with ⟨n, hn⟩
      rcases hlast with ⟨bword, empty, _hbword, _hempty, hlastEq⟩
      exists n + 1
      subst first
      subst tail
      subst middle
      subst bword
      subst empty
      subst w
      rw [hlastEq]
      exact abcAnBn_wrap_word n
  | pairStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0
  | cMore =>
      simp [CFG.FormLanguage, anbnCstarSymbolLanguage] at hw
      rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
      rcases htail with ⟨middle, empty, hmiddle, hempty, htailEq⟩
      rcases hmiddle with ⟨k, hk⟩
      exists k + 1
      rw [hwEq, hfirst, htailEq, hk, hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using abcCstar_cons_word k
  | cStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0

theorem anbnCstar_generated_only_language {w : Word ABC}
    (h : w ∈ CFG.GeneratedLanguage AnBnCstarGrammar) :
    w ∈ anbnCstarLanguage := by
  have hs := cfg_derives_sound_for_symbol_language anbnCstarSymbolLanguage
    (by intro t; rfl) anbnCstar_production_sound h
  simp [CFG.FormLanguage, anbnCstarSymbolLanguage] at hs
  rcases hs with ⟨first, empty, hfirst, hempty, hEq⟩
  rw [hEq]
  have hemptyEq : empty = Word.Empty := hempty
  rw [hemptyEq, Word.concat_empty_right]
  exact hfirst

theorem anbnCstar_generated_language_exact (w : Word ABC) :
    w ∈ CFG.GeneratedLanguage AnBnCstarGrammar <->
      w ∈ anbnCstarLanguage := by
  constructor
  · exact anbnCstar_generated_only_language
  · intro h
    rcases h with ⟨n, k, hw⟩
    rw [hw]
    exact anbnCstar_words_generated n k

theorem anbnCstar_hasFiniteProductions :
    CFG.HasFiniteProductions AnBnCstarGrammar := by
  exists [
    { lhs := AnBnCstarNT.start,
      rhs := [Symbol.nonterminal AnBnCstarNT.pair,
        Symbol.nonterminal AnBnCstarNT.ctail] },
    { lhs := AnBnCstarNT.pair,
      rhs := [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
        Symbol.terminal ABC.b] },
    { lhs := AnBnCstarNT.pair,
      rhs := [] },
    { lhs := AnBnCstarNT.ctail,
      rhs := [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail] },
    { lhs := AnBnCstarNT.ctail,
      rhs := [] }]
  intro A rhs
  constructor
  · intro h
    cases h <;> simp
  · intro h
    simp at h
    rcases h with h | h | h | h | h
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.startRule
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.pairWrap
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.pairStop
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.cMore
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.cStop

theorem anbnCstar_finite_production_context_free :
    CFL.FiniteProductionContextFreeLanguage anbnCstarLanguage := by
  exists AnBnCstarNT
  exists AnBnCstarGrammar
  constructor
  · exact anbnCstar_hasFiniteProductions
  · exact anbnCstar_generated_language_exact

/-!
The second witness grammar is symmetric: it generates an arbitrary prefix of
{lit}`a`s followed by a matched {lit}`b`/{lit}`c` block. Intersecting this
language with the previous one forces all three counts to agree.
-/

inductive AstarBnCnNT where
  | start
  | ahead
  | pair
deriving DecidableEq

namespace AstarBnCnNT

def finite : Foundation.FiniteType AstarBnCnNT where
  elems := [start, ahead, pair]
  complete := by
    intro x
    cases x <;> simp

end AstarBnCnNT

inductive AstarBnCnProduces :
    AstarBnCnNT -> SententialForm ABC AstarBnCnNT -> Prop where
  | startRule :
      AstarBnCnProduces AstarBnCnNT.start
        [Symbol.nonterminal AstarBnCnNT.ahead,
         Symbol.nonterminal AstarBnCnNT.pair]
  | aMore :
      AstarBnCnProduces AstarBnCnNT.ahead
        [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead]
  | aStop :
      AstarBnCnProduces AstarBnCnNT.ahead []
  | pairWrap :
      AstarBnCnProduces AstarBnCnNT.pair
        [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
         Symbol.terminal ABC.c]
  | pairStop :
      AstarBnCnProduces AstarBnCnNT.pair []

def AstarBnCnGrammar : CFG ABC AstarBnCnNT where
  start := AstarBnCnNT.start
  produces := AstarBnCnProduces
  nonterminalsFinite := AstarBnCnNT.finite

def astarBnCnSymbolLanguage : Symbol ABC AstarBnCnNT -> Language ABC
  | Symbol.terminal t => Language.Singleton (Word.Symbol t)
  | Symbol.nonterminal AstarBnCnNT.start => astarBnCnLanguage
  | Symbol.nonterminal AstarBnCnNT.ahead => abcAstarLanguage
  | Symbol.nonterminal AstarBnCnNT.pair => abcBnCnLanguage

theorem astarBnCn_a_stop_generated :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.ahead]
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.a 0)) := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AstarBnCnNT.ahead
  exists ([] : SententialForm ABC AstarBnCnNT)
  constructor
  · exact AstarBnCnProduces.aStop
  constructor
  · rfl
  · simp [Word.RepeatSymbol, SententialForm.terminalWord]

/-!
The {lit}`a^* b^n c^n` grammar reuses the same proof pattern with the free
prefix and matched suffix swapped. The next block builds the generated words
before proving that no other terminal shapes are generated.
-/

theorem astarBnCn_a_more_generated {w : Word ABC}
    (h : CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.ahead]
      (SententialForm.terminalWord w)) :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.ahead]
      (SententialForm.terminalWord (ABC.a :: w)) := by
  have hStart : CFG.Yields AstarBnCnGrammar
      [Symbol.nonterminal AstarBnCnNT.ahead]
      [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead] := by
    exists []
    exists []
    exists AstarBnCnNT.ahead
    exists [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead]
    constructor
    · exact AstarBnCnProduces.aMore
    constructor <;> rfl
  have hContext :
      CFG.Derives AstarBnCnGrammar
        [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead]
        (Symbol.terminal ABC.a :: SententialForm.terminalWord w) := by
    simpa using CFG.derives_context h [Symbol.terminal ABC.a] []
  have hAll := CFG.Derives.step hStart hContext
  simpa [SententialForm.terminalWord] using hAll

theorem astarBnCn_a_words_generated (k : Nat) :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.ahead]
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k)) := by
  induction k with
  | zero => exact astarBnCn_a_stop_generated
  | succ k ih =>
      simpa [abcAstar_cons_word k] using astarBnCn_a_more_generated ih

theorem astarBnCn_pair_stop_generated :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
      (SententialForm.terminalWord (abcBnCnWord 0)) := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AstarBnCnNT.pair
  exists ([] : SententialForm ABC AstarBnCnNT)
  constructor
  · exact AstarBnCnProduces.pairStop
  constructor
  · rfl
  · simp [abcBnCnWord, Word.Concat, Word.RepeatSymbol, SententialForm.terminalWord]

theorem astarBnCn_pair_wrap_generated {w : Word ABC}
    (h : CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
      (SententialForm.terminalWord w)) :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
      (SententialForm.terminalWord (ABC.b :: Word.Concat w [ABC.c])) := by
  have hStart : CFG.Yields AstarBnCnGrammar
      [Symbol.nonterminal AstarBnCnNT.pair]
      [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
       Symbol.terminal ABC.c] := by
    exists []
    exists []
    exists AstarBnCnNT.pair
    exists [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
      Symbol.terminal ABC.c]
    constructor
    · exact AstarBnCnProduces.pairWrap
    constructor <;> rfl
  have hContext :
      CFG.Derives AstarBnCnGrammar
        [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
         Symbol.terminal ABC.c]
        (Symbol.terminal ABC.b ::
          SententialForm.terminalWord w ++ [Symbol.terminal ABC.c]) := by
    simpa using CFG.derives_context h [Symbol.terminal ABC.b]
      [Symbol.terminal ABC.c]
  have hAll := CFG.Derives.step hStart hContext
  change CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
    (SententialForm.terminalWord (ABC.b :: Word.Concat w [ABC.c]))
  simpa [SententialForm.terminalWord, Word.Concat] using hAll

theorem astarBnCn_pair_words_generated (n : Nat) :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
      (SententialForm.terminalWord (abcBnCnWord n)) := by
  induction n with
  | zero => exact astarBnCn_pair_stop_generated
  | succ n ih =>
      simpa [abcBnCn_wrap_word n] using astarBnCn_pair_wrap_generated ih

/-!
The full generated-word theorem combines the free a-prefix derivation with the
matched b/c suffix derivation under the grammar's start production.
-/

theorem astarBnCn_words_generated (k n : Nat) :
    astarBnCnWord k n ∈ CFG.GeneratedLanguage AstarBnCnGrammar := by
  have hStart : CFG.Yields AstarBnCnGrammar
      [Symbol.nonterminal AstarBnCnNT.start]
      [Symbol.nonterminal AstarBnCnNT.ahead,
       Symbol.nonterminal AstarBnCnNT.pair] := by
    exists []
    exists []
    exists AstarBnCnNT.start
    exists [Symbol.nonterminal AstarBnCnNT.ahead,
      Symbol.nonterminal AstarBnCnNT.pair]
    constructor
    · exact AstarBnCnProduces.startRule
    constructor <;> rfl
  have hAhead :=
    astarBnCn_a_words_generated k
  have hPair :=
    astarBnCn_pair_words_generated n
  have hAheadContext :
      CFG.Derives AstarBnCnGrammar
        [Symbol.nonterminal AstarBnCnNT.ahead,
         Symbol.nonterminal AstarBnCnNT.pair]
        (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k) ++
          [Symbol.nonterminal AstarBnCnNT.pair]) := by
    simpa using CFG.derives_context hAhead []
      [Symbol.nonterminal AstarBnCnNT.pair]
  have hPairContext :
      CFG.Derives AstarBnCnGrammar
        (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k) ++
          [Symbol.nonterminal AstarBnCnNT.pair])
        (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k) ++
          SententialForm.terminalWord (abcBnCnWord n)) := by
    simpa using CFG.derives_context hPair
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k)) []
  have hAll := CFG.Derives.step hStart
    (CFG.derives_trans hAheadContext hPairContext)
  change CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.start]
    (SententialForm.terminalWord (astarBnCnWord k n))
  rw [astarBnCnWord, SententialForm.terminalWord_append]
  exact hAll

theorem astarBnCn_production_sound
    (A : AstarBnCnNT) (rhs : SententialForm ABC AstarBnCnNT)
    (hprod : AstarBnCnGrammar.produces A rhs) :
    forall w, w ∈ CFG.FormLanguage astarBnCnSymbolLanguage rhs ->
      w ∈ astarBnCnSymbolLanguage (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | startRule =>
      simp [CFG.FormLanguage, astarBnCnSymbolLanguage] at hw
      rcases hw with ⟨aWord, tail, haWord, htail, _hwEq⟩
      rcases haWord with ⟨k, hk⟩
      rcases htail with ⟨pairWord, empty, hpairWord, _hempty, _htailEq⟩
      rcases hpairWord with ⟨n, hn⟩
      exists k
      exists n
      subst aWord
      subst pairWord
      subst empty
      subst tail
      subst w
      simp [astarBnCnWord, Word.Concat, Word.Empty]
  | aMore =>
      simp [CFG.FormLanguage, astarBnCnSymbolLanguage] at hw
      rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
      rcases htail with ⟨middle, empty, hmiddle, hempty, htailEq⟩
      rcases hmiddle with ⟨k, hk⟩
      exists k + 1
      rw [hwEq, hfirst, htailEq, hk, hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using abcAstar_cons_word k
  | aStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0
  | pairWrap =>
      simp [CFG.FormLanguage, astarBnCnSymbolLanguage] at hw
      rcases hw with ⟨first, tail, _hfirst, htail, _hwEq⟩
      rcases htail with ⟨middle, last, hmiddle, hlast, _htailEq⟩
      rcases hmiddle with ⟨n, hn⟩
      rcases hlast with ⟨cword, empty, _hcword, _hempty, hlastEq⟩
      exists n + 1
      subst first
      subst tail
      subst middle
      subst cword
      subst empty
      subst w
      rw [hlastEq]
      exact abcBnCn_wrap_word n
  | pairStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0

theorem astarBnCn_generated_only_language {w : Word ABC}
    (h : w ∈ CFG.GeneratedLanguage AstarBnCnGrammar) :
    w ∈ astarBnCnLanguage := by
  have hs := cfg_derives_sound_for_symbol_language astarBnCnSymbolLanguage
    (by intro t; rfl) astarBnCn_production_sound h
  simp [CFG.FormLanguage, astarBnCnSymbolLanguage] at hs
  rcases hs with ⟨first, empty, hfirst, hempty, hEq⟩
  rw [hEq]
  have hemptyEq : empty = Word.Empty := hempty
  rw [hemptyEq, Word.concat_empty_right]
  exact hfirst

theorem astarBnCn_generated_language_exact (w : Word ABC) :
    w ∈ CFG.GeneratedLanguage AstarBnCnGrammar <->
      w ∈ astarBnCnLanguage := by
  constructor
  · exact astarBnCn_generated_only_language
  · intro h
    rcases h with ⟨k, n, hw⟩
    rw [hw]
    exact astarBnCn_words_generated k n

theorem astarBnCn_hasFiniteProductions :
    CFG.HasFiniteProductions AstarBnCnGrammar := by
  exists [
    { lhs := AstarBnCnNT.start,
      rhs := [Symbol.nonterminal AstarBnCnNT.ahead,
        Symbol.nonterminal AstarBnCnNT.pair] },
    { lhs := AstarBnCnNT.ahead,
      rhs := [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead] },
    { lhs := AstarBnCnNT.ahead,
      rhs := [] },
    { lhs := AstarBnCnNT.pair,
      rhs := [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
        Symbol.terminal ABC.c] },
    { lhs := AstarBnCnNT.pair,
      rhs := [] }]
  intro A rhs
  constructor
  · intro h
    cases h <;> simp
  · intro h
    simp at h
    rcases h with h | h | h | h | h
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.startRule
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.aMore
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.aStop
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.pairWrap
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.pairStop

theorem astarBnCn_finite_production_context_free :
    CFL.FiniteProductionContextFreeLanguage astarBnCnLanguage := by
  exists AstarBnCnNT
  exists AstarBnCnGrammar
  constructor
  · exact astarBnCn_hasFiniteProductions
  · exact astarBnCn_generated_language_exact

/-!
The intersection proof is arithmetic on symbol counts. Membership in the first
language gives equal {lit}`a` and {lit}`b` counts; membership in the second gives
equal {lit}`b` and {lit}`c` counts. Together they identify a word of the exact
form {lit}`a^n b^n c^n`.
-/

theorem anbnCstar_word_count_a (n k : Nat) :
    Word.Count ABC.a (anbnCstarWord n k) = n := by
  unfold anbnCstarWord abcAnBnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.b)]
  rw [Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbnCstar_word_count_b (n k : Nat) :
    Word.Count ABC.b (anbnCstarWord n k) = n := by
  unfold anbnCstarWord abcAnBnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.a)]
  rw [Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbnCstar_word_count_c (n k : Nat) :
    Word.Count ABC.c (anbnCstarWord n k) = k := by
  unfold anbnCstarWord abcAnBnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
  rw [Word.count_repeatSymbol_same]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem astarBnCn_word_count_a (k n : Nat) :
    Word.Count ABC.a (astarBnCnWord k n) = k := by
  unfold astarBnCnWord abcBnCnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.b)]
  rw [Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem astarBnCn_word_count_b (k n : Nat) :
    Word.Count ABC.b (astarBnCnWord k n) = n := by
  unfold astarBnCnWord abcBnCnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.a)]
  rw [Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem astarBnCn_word_count_c (k n : Nat) :
    Word.Count ABC.c (astarBnCnWord k n) = n := by
  unfold astarBnCnWord abcBnCnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
  rw [Word.count_repeatSymbol_same]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbnCstarWord_diagonal (n : Nat) :
    anbnCstarWord n n = anbncnBlockWord n := by
  simp [anbnCstarWord, abcAnBnWord, anbncnBlockWord, Word.Concat,
    List.append_assoc]

theorem astarBnCnWord_diagonal (n : Nat) :
    astarBnCnWord n n = anbncnBlockWord n := by
  simp [astarBnCnWord, abcBnCnWord, anbncnBlockWord, Word.Concat]

theorem anbnCstar_inter_astarBnCn_exact :
    Language.Equal (Language.Inter anbnCstarLanguage astarBnCnLanguage)
      anbncnLanguage := by
  intro w
  constructor
  · intro hw
    rcases hw.left with ⟨n, k, hleft⟩
    rcases hw.right with ⟨i, j, hright⟩
    have hEq : anbnCstarWord n k = astarBnCnWord i j := by
      rw [← hleft, ← hright]
    have hb : n = j := by
      have hcount := congrArg (Word.Count ABC.b) hEq
      rw [anbnCstar_word_count_b n k,
        astarBnCn_word_count_b i j] at hcount
      exact hcount
    have hc : k = j := by
      have hcount := congrArg (Word.Count ABC.c) hEq
      rw [anbnCstar_word_count_c n k,
        astarBnCn_word_count_c i j] at hcount
      exact hcount
    have hk : k = n := by omega
    exists n
    rw [hleft, hk, anbnCstarWord_diagonal]
  · intro hw
    rcases hw with ⟨n, hw⟩
    constructor
    · exists n
      exists n
      rw [hw]
      exact (anbnCstarWord_diagonal n).symm
    · exists n
      exists n

/-!
# Finite-Production CFLs and Pumping Vocabulary

The book-facing context-free predicate requires a finite production list. The
CFL Pumping Lemma uses a five-part decomposition {lit}`u x y z v`, where pumping
repeats the two outer middle pieces {lit}`x` and {lit}`z` together. At least one of
{lit}`x` or {lit}`z` is nonempty, and the combined middle region {lit}`x y z` is bounded by
the pumping length.
-/

def FiniteProductionContextFreeLanguage (L : Language terminal) : Prop :=
  CFL.FiniteProductionContextFreeLanguage L

def CFLPumpingDecomposition (L : Language terminal) (K : Nat) (w : Word terminal) :
    Prop :=
  CFL.PumpingDecomposition L K w

def CFLPumpingLength (L : Language terminal) (K : Nat) : Prop :=
  CFL.PumpingLength L K

def CFLHasPumpingProperty (L : Language terminal) : Prop :=
  CFL.HasPumpingProperty L

def LanguageClassExtensional (C : Language terminal -> Prop) : Prop :=
  forall L M, Language.Equal L M -> C L -> C M

def ClosedUnderIntersection (C : Language terminal -> Prop) : Prop :=
  forall L M, C L -> C M -> C (Language.Inter L M)

def ClosedUnderUnion (C : Language terminal -> Prop) : Prop :=
  forall L M, C L -> C M -> C (Language.Union L M)

def ClosedUnderComplement (C : Language terminal -> Prop) : Prop :=
  forall L, C L -> C (Language.Compl L)

theorem finite_production_context_free {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    CFL.ContextFreeLanguage L :=
  CFL.finiteProduction_contextFree hL

theorem finite_production_context_free_of_equal {L M : Language terminal}
    (hEq : Language.Equal L M)
    (hL : FiniteProductionContextFreeLanguage L) :
    FiniteProductionContextFreeLanguage M := by
  cases hL with
  | intro nonterminal hnt =>
      cases hnt with
      | intro G hG =>
          exists nonterminal
          exists G
          constructor
          · exact hG.left
          · exact Language.equal_trans hG.right hEq

theorem finite_production_context_free_extensional :
    LanguageClassExtensional
      (FiniteProductionContextFreeLanguage (terminal := terminal)) := by
  intro L M hEq hL
  exact finite_production_context_free_of_equal hEq hL

theorem finite_production_cfls_closed_under_union :
    ClosedUnderUnion
      (FiniteProductionContextFreeLanguage (terminal := terminal)) := by
  intro L M hL hM
  exact CFL.union_context_free hL hM

theorem finite_production_rhs_length_bound {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    exists B : Nat,
      B > 0 ∧ forall A rhs, G.produces A rhs -> rhs.length < B :=
  CFL.finiteProduction_rhs_length_bound hG

theorem finite_production_grammar_pumping_property
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    CFLHasPumpingProperty (CFG.GeneratedLanguage G) :=
  CFL.finiteProduction_generated_hasPumpingProperty hG

theorem finite_production_pumping_property {terminal : Type}
    {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    CFLHasPumpingProperty L :=
  CFL.finiteProduction_hasPumpingProperty hL

theorem pumping_decomposition_original_word_mem {L : Language terminal}
    {K : Nat} {w : Word terminal}
    (h : CFLPumpingDecomposition L K w) : w ∈ L :=
  CFL.pumping_decomposition_original_word_mem h

theorem pumping_decomposition_of_equal {L M : Language terminal} {K : Nat}
    {w : Word terminal}
    (hEq : Language.Equal L M) (h : CFLPumpingDecomposition L K w) :
    CFLPumpingDecomposition M K w :=
  CFL.pumping_decomposition_of_equal hEq h

theorem pumping_length_of_equal {L M : Language terminal} {K : Nat}
    (hEq : Language.Equal L M) (h : CFLPumpingLength L K) :
    CFLPumpingLength M K :=
  CFL.pumpingLength_of_equal hEq h

theorem pumping_property_of_equal {L M : Language terminal}
    (hEq : Language.Equal L M) (h : CFLHasPumpingProperty L) :
    CFLHasPumpingProperty M :=
  CFL.hasPumpingProperty_of_equal hEq h

theorem pumping_length_monotone {L : Language terminal} {K M : Nat}
    (hKM : K <= M) (h : CFLPumpingLength L K) :
    CFLPumpingLength L M :=
  CFL.pumpingLength_mono hKM h

theorem not_pumping_length_of_counterexample {L : Language terminal} {K : Nat}
    {w : Word terminal}
    (hw : w ∈ L) (hlen : K <= Word.Length w)
    (hbad :
      forall u x y z v : Word terminal,
        w = CFL.Concat5 u x y z v ->
        (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
        Word.Length (CFL.Concat3 x y z) < K ->
        exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L) :
    ¬ CFLPumpingLength L K :=
  CFL.not_pumpingLength_of_counterexample hw hlen hbad

theorem not_pumping_property_of_counterexamples {L : Language terminal}
    (hbad :
      forall K : Nat, K > 0 ->
        exists w : Word terminal,
          w ∈ L ∧
          K <= Word.Length w ∧
          forall u x y z v : Word terminal,
            w = CFL.Concat5 u x y z v ->
            (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
            Word.Length (CFL.Concat3 x y z) < K ->
            exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L) :
    ¬ CFLHasPumpingProperty L :=
  CFL.not_hasPumpingProperty_of_counterexamples hbad

/-!
These wrappers are the practical way to use the CFL Pumping Lemma on this page:
build a bad-word family for every proposed pumping length, then conclude that
the language is not context-free.
-/

theorem not_context_free_of_no_pumping_property {terminal : Type}
    {L : Language terminal}
    (hNoPump : ¬ CFLHasPumpingProperty L) :
    ¬ CFL.ContextFreeLanguage L :=
  CFL.not_context_free_of_no_pumping_property hNoPump

def CFLPumpingBadWordFamily (L : Language terminal) : Prop :=
  forall K : Nat, K > 0 ->
    exists w : Word terminal,
      w ∈ L ∧
      K <= Word.Length w ∧
      forall u x y z v : Word terminal,
        w = CFL.Concat5 u x y z v ->
        (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
        Word.Length (CFL.Concat3 x y z) < K ->
        exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L

theorem not_pumping_property_of_bad_word_family {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ CFLHasPumpingProperty L :=
  not_pumping_property_of_counterexamples hbad

theorem not_context_free_of_bad_word_family {terminal : Type}
    {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ CFL.ContextFreeLanguage L :=
  not_context_free_of_no_pumping_property
    (not_pumping_property_of_bad_word_family hbad)

theorem not_finite_production_context_free_of_bad_word_family
    {terminal : Type} {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ FiniteProductionContextFreeLanguage L := by
  intro hcf
  exact not_pumping_property_of_bad_word_family hbad
    (finite_production_pumping_property hcf)

theorem cfl_pumped_two_count_symbol [DecidableEq terminal]
    (s : terminal) (u x y z v : Word terminal) :
    Word.Count s (CFL.Pumped u x y z v 2) =
      Word.Count s (CFL.Concat5 u x y z v) +
        Word.Count s (Word.Concat x z) := by
  unfold CFL.Pumped CFL.Concat5
  rw [show Word.RepeatWord x 2 = Word.Concat x x by
    simp [Word.RepeatWord, Word.Concat]]
  rw [show Word.RepeatWord z 2 = Word.Concat z z by
    simp [Word.RepeatWord, Word.Concat]]
  repeat rw [Word.count_concat]
  omega

/-!
# Pumping {lit}`a^n b^n c^n`

For a proposed CFL pumping length {lit}`K`, choose {lit}`a^K b^K c^K`. The bounded
middle region {lit}`x y z` cannot cover all three block boundaries at once, so
pumping {lit}`x` and {lit}`z` with count {lit}`2` changes at most two of the three symbol
counts. The resulting word cannot still have equal numbers of {lit}`a`, {lit}`b`, and
{lit}`c`.
-/

theorem anbncn_membership (w : Word ABC) :
    w ∈ anbncnLanguage <-> exists n, w = anbncnBlockWord n :=
  Iff.rfl

theorem anbncn_block_count_a (n : Nat) :
    Word.Count ABC.a (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_concat, Word.count_repeatSymbol_different,
    Word.count_repeatSymbol_different]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_count_b (n : Nat) :
    Word.Count ABC.b (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.a)]
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_count_c (n : Nat) :
    Word.Count ABC.c (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
  rw [Word.count_repeatSymbol_same]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_length (n : Nat) :
    Word.Length (anbncnBlockWord n) = 3 * n := by
  unfold anbncnBlockWord
  simp [Word.length_concat, Word.length_repeatSymbol]
  omega

theorem anbncn_members_have_equal_counts {w : Word ABC}
    (hw : w ∈ anbncnLanguage) :
    Word.Count ABC.a w = Word.Count ABC.b w ∧
      Word.Count ABC.b w = Word.Count ABC.c w := by
  cases hw with
  | intro n hn =>
      rw [hn, anbncn_block_count_a n, anbncn_block_count_b n,
        anbncn_block_count_c n]
      exact ⟨rfl, rfl⟩

/-!
The pumping contradiction needs one combinatorial fact: because the pumpable
middle region is shorter than {lit}`K`, it cannot touch both the first
{lit}`a`-block and the final {lit}`c`-block of {lit}`a^K b^K c^K`.
-/

theorem abc_count_sum_pos_of_nonempty {w : Word ABC}
    (h : w ≠ Word.Empty) :
    0 < Word.Count ABC.a w + Word.Count ABC.b w + Word.Count ABC.c w := by
  cases w with
  | nil =>
      exact False.elim (h rfl)
  | cons head tail =>
      cases head <;> simp [Word.Count] <;> omega

theorem anbncn_drop_after_a_count_a_zero (K l : Nat) (hl : K <= l) :
    Word.Count ABC.a (List.drop l (anbncnBlockWord K)) = 0 := by
  unfold anbncnBlockWord
  change Word.Count ABC.a
      (List.drop l
        (List.append (Word.RepeatSymbol ABC.a K)
          (Word.Concat (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K)))) = 0
  simp [List.drop_append, Word.RepeatSymbol, List.drop_replicate]
  have hzero : K - l = 0 := by omega
  rw [hzero]
  change Word.Count ABC.a
      (List.drop (l - K)
        (Word.Concat (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K))) = 0
  change Word.Count ABC.a
      (List.drop (l - K)
        (List.append (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K))) = 0
  simp [List.drop_append, Word.RepeatSymbol, List.drop_replicate]
  change Word.Count ABC.a
      (Word.Concat (Word.RepeatSymbol ABC.b (K - (l - K)))
        (Word.RepeatSymbol ABC.c (K - (l - K - K)))) = 0
  have hb :
      Word.Count ABC.a (Word.RepeatSymbol ABC.b (K - (l - K))) = 0 := by
    exact Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.b)
      (by intro h; cases h) _
  have hc :
      Word.Count ABC.a (Word.RepeatSymbol ABC.c (K - (l - K - K))) = 0 := by
    exact Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.c)
      (by intro h; cases h) _
  rw [Word.count_concat, hb, hc]

theorem anbncn_take_before_c_count_c_zero (K l : Nat)
    (hl : l <= 2 * K) :
    Word.Count ABC.c (List.take l (anbncnBlockWord K)) = 0 := by
  unfold anbncnBlockWord
  change Word.Count ABC.c
      (List.take l
        (List.append (Word.RepeatSymbol ABC.a K)
          (List.append (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K)))) = 0
  simp [List.take_append, Word.RepeatSymbol, List.take_replicate]
  have hzero : min (l - K - K) K = 0 := by omega
  rw [hzero]
  change Word.Count ABC.c
      (Word.Concat (Word.RepeatSymbol ABC.a (min l K))
        (Word.Concat (Word.RepeatSymbol ABC.b (min (l - K) K))
          (Word.RepeatSymbol ABC.c 0))) = 0
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  · rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
    · simp [Word.count_repeatSymbol_same]
    · intro h
      cases h
  · intro h
    cases h

theorem anbncn_middle_after_a_count_a_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hu : K <= Word.Length u) :
    Word.Count ABC.a middle = 0 := by
  have htail :
      Word.Concat middle v = List.drop (Word.Length u) (anbncnBlockWord K) := by
    calc
      Word.Concat middle v =
          List.drop (Word.Length u) (Word.Concat u (Word.Concat middle v)) := by
        change Word.Concat middle v =
          List.drop (List.length u) (List.append u (Word.Concat middle v))
        exact (List.drop_left (l₁ := u) (l₂ := Word.Concat middle v)).symm
      _ = List.drop (Word.Length u) (anbncnBlockWord K) := by
        rw [← hword]
  have hcountTail :
      Word.Count ABC.a (Word.Concat middle v) = 0 := by
    rw [htail]
    exact anbncn_drop_after_a_count_a_zero K (Word.Length u) hu
  rw [Word.count_concat] at hcountTail
  omega

theorem anbncn_middle_before_c_count_c_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hprefix : Word.Length (Word.Concat u middle) <= 2 * K) :
    Word.Count ABC.c middle = 0 := by
  have hprefixEq :
      Word.Concat u middle =
        List.take (Word.Length (Word.Concat u middle)) (anbncnBlockWord K) := by
    calc
      Word.Concat u middle =
          List.take (Word.Length (Word.Concat u middle))
            (Word.Concat (Word.Concat u middle) v) := by
        change Word.Concat u middle =
          List.take (List.length (Word.Concat u middle))
            (List.append (Word.Concat u middle) v)
        exact (List.take_left (l₁ := Word.Concat u middle) (l₂ := v)).symm
      _ = List.take (Word.Length (Word.Concat u middle))
            (Word.Concat u (Word.Concat middle v)) := by
        rw [Word.concat_assoc]
      _ = List.take (Word.Length (Word.Concat u middle)) (anbncnBlockWord K) := by
        rw [← hword]
  have hcountPrefix :
      Word.Count ABC.c (Word.Concat u middle) = 0 := by
    rw [hprefixEq]
    exact anbncn_take_before_c_count_c_zero K
      (Word.Length (Word.Concat u middle)) hprefix
  rw [Word.count_concat] at hcountPrefix
  omega

theorem anbncn_short_middle_count_a_or_c_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hmiddle : Word.Length middle < K) :
    Word.Count ABC.a middle = 0 ∨ Word.Count ABC.c middle = 0 := by
  by_cases hu : K <= Word.Length u
  · exact Or.inl (anbncn_middle_after_a_count_a_zero hword hu)
  · apply Or.inr
    have huLt : Word.Length u < K := by omega
    have hprefix : Word.Length (Word.Concat u middle) <= 2 * K := by
      rw [Word.length_concat]
      omega
    exact anbncn_middle_before_c_count_c_zero hword hprefix

theorem cfl_pumped_two_count (s : ABC) (u x y z v : Word ABC) :
    Word.Count s (CFL.Pumped u x y z v 2) =
      Word.Count s (CFL.Concat5 u x y z v) +
        Word.Count s (Word.Concat x z) := by
  exact cfl_pumped_two_count_symbol s u x y z v

/-!
Pumping with count {lit}`2` adds one extra copy of {lit}`x` and one extra copy
of {lit}`z`. Since {lit}`x ++ z` is nonempty but misses either all {lit}`a`s or
all {lit}`c`s, at least one of the three counts changes differently from the
others.
-/

theorem anbncn_xz_count_a_or_c_zero
    {u x y z v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = CFL.Concat5 u x y z v)
    (hshort : Word.Length (CFL.Concat3 x y z) < K) :
    Word.Count ABC.a (Word.Concat x z) = 0 ∨
      Word.Count ABC.c (Word.Concat x z) = 0 := by
  have hmiddleWord :
      anbncnBlockWord K =
        Word.Concat u (Word.Concat (CFL.Concat3 x y z) v) := by
    rw [hword]
    simp [CFL.Concat5, CFL.Concat3, Word.Concat, List.append_assoc]
  cases anbncn_short_middle_count_a_or_c_zero hmiddleWord hshort with
  | inl ha =>
      apply Or.inl
      unfold CFL.Concat3 at ha
      rw [Word.count_concat, Word.count_concat] at ha
      rw [Word.count_concat]
      omega
  | inr hc =>
      apply Or.inr
      unfold CFL.Concat3 at hc
      rw [Word.count_concat, Word.count_concat] at hc
      rw [Word.count_concat]
      omega

theorem anbncn_xz_nonempty {x z : Word ABC}
    (h : x ≠ Word.Empty ∨ z ≠ Word.Empty) :
    Word.Concat x z ≠ Word.Empty := by
  intro hxz
  cases x with
  | nil =>
      cases h with
      | inl hx =>
          exact hx rfl
      | inr hz =>
          apply hz
          simpa [Word.Concat, Word.Empty] using hxz
  | cons _ _ =>
      cases hxz

theorem anbncn_pump_two_not_mem
    {u x y z v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = CFL.Concat5 u x y z v)
    (hnonempty : x ≠ Word.Empty ∨ z ≠ Word.Empty)
    (hshort : Word.Length (CFL.Concat3 x y z) < K) :
    ¬ CFL.Pumped u x y z v 2 ∈ anbncnLanguage := by
  intro hpumped
  have hcounts := anbncn_members_have_equal_counts hpumped
  have hcountA :
      Word.Count ABC.a (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.a (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_a K]
  have hcountB :
      Word.Count ABC.b (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.b (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_b K]
  have hcountC :
      Word.Count ABC.c (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.c (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_c K]
  have hEqAB :
      K + Word.Count ABC.a (Word.Concat x z) =
        K + Word.Count ABC.b (Word.Concat x z) := by
    rw [← hcountA, ← hcountB]
    exact hcounts.left
  have hEqBC :
      K + Word.Count ABC.b (Word.Concat x z) =
        K + Word.Count ABC.c (Word.Concat x z) := by
    rw [← hcountB, ← hcountC]
    exact hcounts.right
  have hxzNonempty : Word.Concat x z ≠ Word.Empty :=
    anbncn_xz_nonempty hnonempty
  have hpos :
      0 < Word.Count ABC.a (Word.Concat x z) +
        Word.Count ABC.b (Word.Concat x z) +
        Word.Count ABC.c (Word.Concat x z) :=
    abc_count_sum_pos_of_nonempty hxzNonempty
  cases anbncn_xz_count_a_or_c_zero hword hshort with
  | inl ha0 =>
      have hb0 : Word.Count ABC.b (Word.Concat x z) = 0 := by omega
      have hc0 : Word.Count ABC.c (Word.Concat x z) = 0 := by omega
      omega
  | inr hc0 =>
      have hb0 : Word.Count ABC.b (Word.Concat x z) = 0 := by omega
      have ha0 : Word.Count ABC.a (Word.Concat x z) = 0 := by omega
      omega

theorem anbncn_bad_word_family :
    CFLPumpingBadWordFamily anbncnLanguage := by
  intro K hK
  let w : Word ABC := anbncnBlockWord K
  have hwMem : w ∈ anbncnLanguage := by
    exists K
  have hwLength : K <= Word.Length w := by
    simp [w, anbncn_block_length]
    omega
  refine ⟨w, hwMem, hwLength, ?_⟩
  intro u x y z v hword hnonempty hshort
  exact ⟨2, anbncn_pump_two_not_mem hword hnonempty hshort⟩

theorem anbncn_no_pumping_property :
    ¬ CFLHasPumpingProperty anbncnLanguage :=
  not_pumping_property_of_bad_word_family anbncn_bad_word_family

theorem anbncn_not_finite_production_context_free :
    ¬ FiniteProductionContextFreeLanguage anbncnLanguage := by
  intro hcf
  exact anbncn_no_pumping_property
    (finite_production_pumping_property hcf)

theorem anbncn_not_context_free :
    ¬ CFL.ContextFreeLanguage anbncnLanguage :=
  not_context_free_of_no_pumping_property anbncn_no_pumping_property

/-!
# The Duplicate-Word Language

The book's second pumping example is `{ w w | w in {a,b}* }`. The full
context-free pumping contradiction needs a careful position argument, but the
basic vocabulary and count facts are reusable: every duplicate word has an even
number of any fixed symbol.
-/

def duplicateWordLanguage : Language Section01.AB :=
  fun w => exists u : Word Section01.AB, w = Word.Concat u u

def duplicateSeedWord (n : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a n)
    (Word.Concat (Word.Symbol Section01.AB.b)
      (Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.Symbol Section01.AB.b)))

def duplicateBadWord (n : Nat) : Word Section01.AB :=
  Word.Concat (duplicateSeedWord n) (duplicateSeedWord n)

theorem duplicate_word_membership (w : Word Section01.AB) :
    w ∈ duplicateWordLanguage <->
      exists u : Word Section01.AB, w = Word.Concat u u :=
  Iff.rfl

theorem duplicateBadWord_mem (n : Nat) :
    duplicateBadWord n ∈ duplicateWordLanguage := by
  exists duplicateSeedWord n

theorem duplicateSeedWord_count_b (n : Nat) :
    Word.Count Section01.AB.b (duplicateSeedWord n) = 2 := by
  unfold duplicateSeedWord
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different
    (a := Section01.AB.b) (b := Section01.AB.a)]
  rw [Word.count_concat]
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different
    (a := Section01.AB.b) (b := Section01.AB.a)]
  · simp [Word.Count, Word.Symbol]
  · intro h
    cases h
  · intro h
    cases h

theorem duplicateBadWord_count_b (n : Nat) :
    Word.Count Section01.AB.b (duplicateBadWord n) = 4 := by
  unfold duplicateBadWord
  rw [Word.count_concat, duplicateSeedWord_count_b]

theorem duplicateSeedWord_length (n : Nat) :
    Word.Length (duplicateSeedWord n) = 2 * n + 2 := by
  unfold duplicateSeedWord
  simp [Word.Length, Word.Concat, Word.RepeatSymbol, Word.Symbol]
  omega

theorem duplicateBadWord_length (n : Nat) :
    Word.Length (duplicateBadWord n) = 4 * n + 4 := by
  unfold duplicateBadWord
  rw [Word.length_concat, duplicateSeedWord_length]
  omega

theorem duplicate_word_count_even
    (sym : Section01.AB) {w : Word Section01.AB}
    (hw : w ∈ duplicateWordLanguage) :
    exists n : Nat, Word.Count sym w = 2 * n := by
  rcases hw with ⟨u, hu⟩
  exists Word.Count sym u
  rw [hu, Word.count_concat]
  omega

theorem duplicate_word_not_count_b_five {w : Word Section01.AB}
    (hcount : Word.Count Section01.AB.b w = 5) :
    ¬ w ∈ duplicateWordLanguage := by
  intro hw
  rcases duplicate_word_count_even Section01.AB.b hw with ⟨n, hn⟩
  rw [hcount] at hn
  omega

theorem duplicate_pump_two_not_mem_of_xz_count_b_one
    {u x y z v : Word Section01.AB} {K : Nat}
    (hword : duplicateBadWord K = CFL.Concat5 u x y z v)
    (hcount : Word.Count Section01.AB.b (Word.Concat x z) = 1) :
    ¬ CFL.Pumped u x y z v 2 ∈ duplicateWordLanguage := by
  apply duplicate_word_not_count_b_five
  rw [cfl_pumped_two_count_symbol, ← hword, duplicateBadWord_count_b, hcount]

theorem duplicate_xz_count_b_le_middle_count_b
    (x y z : Word Section01.AB) :
    Word.Count Section01.AB.b (Word.Concat x z) <=
      Word.Count Section01.AB.b (CFL.Concat3 x y z) := by
  unfold CFL.Concat3
  repeat rw [Word.count_concat]
  omega

theorem duplicate_pump_two_not_mem_of_xz_count_b_pos_le_one
    {u x y z v : Word Section01.AB} {K : Nat}
    (hword : duplicateBadWord K = CFL.Concat5 u x y z v)
    (hpos : 0 < Word.Count Section01.AB.b (Word.Concat x z))
    (hle : Word.Count Section01.AB.b (Word.Concat x z) <= 1) :
    ¬ CFL.Pumped u x y z v 2 ∈ duplicateWordLanguage := by
  have hcount : Word.Count Section01.AB.b (Word.Concat x z) = 1 := by
    omega
  exact duplicate_pump_two_not_mem_of_xz_count_b_one hword hcount

theorem duplicate_pump_two_not_mem_of_middle_count_b_le_one
    {u x y z v : Word Section01.AB} {K : Nat}
    (hword : duplicateBadWord K = CFL.Concat5 u x y z v)
    (hpos : 0 < Word.Count Section01.AB.b (Word.Concat x z))
    (hmiddle :
      Word.Count Section01.AB.b (CFL.Concat3 x y z) <= 1) :
    ¬ CFL.Pumped u x y z v 2 ∈ duplicateWordLanguage := by
  exact duplicate_pump_two_not_mem_of_xz_count_b_pos_le_one hword hpos
    (Nat.le_trans (duplicate_xz_count_b_le_middle_count_b x y z) hmiddle)

/-!
# Nonclosure Consequences

Because `{ a^n b^n c^* }` and `{ a^* b^n c^n }` are context-free but their
intersection is {lit}`{ a^n b^n c^n }`, finite-production context-free languages
are not closed under intersection. If they were closed under complement as
well as union, De Morgan's law would give intersection closure, so complement
closure fails too.
-/

theorem finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
    {L M : Language ABC}
    (hL : FiniteProductionContextFreeLanguage L)
    (hM : FiniteProductionContextFreeLanguage M)
    (hEq : Language.Equal (Language.Inter L M) anbncnLanguage) :
    ¬ ClosedUnderIntersection
      (FiniteProductionContextFreeLanguage (terminal := ABC)) := by
  intro hClosed
  have hInter : FiniteProductionContextFreeLanguage (Language.Inter L M) :=
    hClosed L M hL hM
  exact anbncn_not_finite_production_context_free
    (finite_production_context_free_of_equal hEq hInter)

theorem finite_production_cfls_not_closed_under_intersection :
    ¬ ClosedUnderIntersection
      (FiniteProductionContextFreeLanguage (terminal := ABC)) :=
  finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
    anbnCstar_finite_production_context_free
    astarBnCn_finite_production_context_free
    anbnCstar_inter_astarBnCn_exact

theorem complement_closure_and_union_closure_imply_intersection_closure
    {C : Language terminal -> Prop}
    (hExt : LanguageClassExtensional C)
    (hUnion : ClosedUnderUnion C)
    (hCompl : ClosedUnderComplement C) :
    ClosedUnderIntersection C := by
  classical
  intro L M hL hM
  let N : Language terminal :=
    Language.Compl (Language.Union (Language.Compl L) (Language.Compl M))
  have hN : C N := by
    have hUnionCompl : C (Language.Union (Language.Compl L) (Language.Compl M)) :=
      hUnion (Language.Compl L) (Language.Compl M)
      (hCompl L hL) (hCompl M hM)
    simpa [N] using hCompl
      (Language.Union (Language.Compl L) (Language.Compl M)) hUnionCompl
  apply hExt N (Language.Inter L M)
  · intro w
    constructor
    · intro hw
      change ¬ w ∈ Language.Union (Language.Compl L) (Language.Compl M) at hw
      constructor
      · by_cases hmem : w ∈ L
        · exact hmem
        · exact False.elim (hw (Or.inl hmem))
      · by_cases hmem : w ∈ M
        · exact hmem
        · exact False.elim (hw (Or.inr hmem))
    · intro hw
      change ¬ w ∈ Language.Union (Language.Compl L) (Language.Compl M)
      intro hUnionMem
      cases hUnionMem with
      | inl hnotL => exact hnotL hw.left
      | inr hnotM => exact hnotM hw.right
  · exact hN

theorem finite_production_cfl_complement_nonclosure_from_anbncn_witnesses
    {L M : Language ABC}
    (hL : FiniteProductionContextFreeLanguage L)
    (hM : FiniteProductionContextFreeLanguage M)
    (hEq : Language.Equal (Language.Inter L M) anbncnLanguage)
    (hUnion :
      ClosedUnderUnion
        (FiniteProductionContextFreeLanguage (terminal := ABC))) :
    ¬ ClosedUnderComplement
      (FiniteProductionContextFreeLanguage (terminal := ABC)) := by
  intro hCompl
  have hInterClosed :
      ClosedUnderIntersection
        (FiniteProductionContextFreeLanguage (terminal := ABC)) :=
    complement_closure_and_union_closure_imply_intersection_closure
      finite_production_context_free_extensional hUnion hCompl
  exact
    finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
      hL hM hEq hInterClosed

theorem finite_production_cfls_not_closed_under_complement :
    ¬ ClosedUnderComplement
      (FiniteProductionContextFreeLanguage (terminal := ABC)) :=
  finite_production_cfl_complement_nonclosure_from_anbncn_witnesses
    anbnCstar_finite_production_context_free
    astarBnCn_finite_production_context_free
    anbnCstar_inter_astarBnCn_exact
    finite_production_cfls_closed_under_union

theorem anbncn_not_context_free_from_pumping_lemma
    (_pumpingLemma : CFL.PumpingLemmaConclusion anbncnLanguage) :
    ¬ CFL.ContextFreeLanguage anbncnLanguage :=
  anbncn_not_context_free

/-!
The concrete contradiction for `{ a^n b^n c^n | n >= 0 }` is now formalized:
no pumping length can satisfy the book's quantified CFL pumping property for
this language. Since the public {lean}`CFL.ContextFreeLanguage` predicate is
now the book-facing finite-production predicate, this gives the unconditional
{lean}`anbncn_not_context_free` theorem.
-/

end Section05
end Chapter04
end Book
end FoC
