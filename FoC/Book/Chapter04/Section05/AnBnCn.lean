import FoC.Book.Chapter04.Section01
import FoC.Grammars.CFL.Closure

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section05

open Languages
open Grammars

/-!
# The Three-Block Witness Languages

This module constructs finite CFG presentations for
{lit}`a^n b^n c^*` and {lit}`a^* b^n c^n`, proves their generated
languages exactly, and identifies their intersection with
{lit}`a^n b^n c^n`.
-/

/-!
## The {lit}`a^n b^n c^n` Witness Setup

The language {lit}`{ a^n b^n c^n | n >= 0 }` is the standard example that is not
context-free. The auxiliary languages {lit}`{ a^n b^n c^* }` and
{lit}`{ a^* b^n c^n }` are context-free, and their intersection is exactly
{lit}`{ a^n b^n c^n }`. This gives the closure-based nonclosure argument after the
pumping proof establishes the target language is not context-free.
-/

inductive ABC where
  | a
  | b
  | c
deriving DecidableEq

def anbncnBlockWord (n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.a n)
    (Word.Concat (Word.RepeatSymbol ABC.b n) (Word.RepeatSymbol ABC.c n))

def anbncnLanguage : Language ABC :=
  fun w => exists n, w = anbncnBlockWord n

def abcAnBnWord (n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.a n) (Word.RepeatSymbol ABC.b n)

def abcBnCnWord (n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.b n) (Word.RepeatSymbol ABC.c n)

def anbnCstarWord (n k : Nat) : Word ABC :=
  Word.Concat (abcAnBnWord n) (Word.RepeatSymbol ABC.c k)

def astarBnCnWord (k n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.a k) (abcBnCnWord n)

def abcAnBnLanguage : Language ABC :=
  fun w => exists n, w = abcAnBnWord n

def abcBnCnLanguage : Language ABC :=
  fun w => exists n, w = abcBnCnWord n

def abcAstarLanguage : Language ABC :=
  fun w => exists k, w = Word.RepeatSymbol ABC.a k

def abcCstarLanguage : Language ABC :=
  fun w => exists k, w = Word.RepeatSymbol ABC.c k

def anbnCstarLanguage : Language ABC :=
  fun w => exists n k, w = anbnCstarWord n k

def astarBnCnLanguage : Language ABC :=
  fun w => exists k n, w = astarBnCnWord k n

theorem abcAnBn_wrap_word (n : Nat) :
    ABC.a :: Word.Concat (abcAnBnWord n) [ABC.b] =
      abcAnBnWord (n + 1) := by
  unfold abcAnBnWord
  simp [Word.RepeatSymbol, Word.Concat]
  rw [show List.replicate (n + 1) ABC.a =
    ABC.a :: List.replicate n ABC.a by rfl]
  rw [Section01.replicate_succ_eq_append ABC.b n]
  simp

theorem abcBnCn_wrap_word (n : Nat) :
    ABC.b :: Word.Concat (abcBnCnWord n) [ABC.c] =
      abcBnCnWord (n + 1) := by
  unfold abcBnCnWord
  simp [Word.RepeatSymbol, Word.Concat]
  rw [show List.replicate (n + 1) ABC.b =
    ABC.b :: List.replicate n ABC.b by rfl]
  rw [Section01.replicate_succ_eq_append ABC.c n]
  simp

theorem abcCstar_cons_word (k : Nat) :
    ABC.c :: Word.RepeatSymbol ABC.c k =
      Word.RepeatSymbol ABC.c (k + 1) :=
  rfl

theorem abcAstar_cons_word (k : Nat) :
    ABC.a :: Word.RepeatSymbol ABC.a k =
      Word.RepeatSymbol ABC.a (k + 1) :=
  rfl

/-!
The witness grammars below are proved exact with a reusable soundness pattern.
Instead of inspecting a final derivation directly, we assign a language meaning
to each nonterminal and prove every production is sound for that meaning.
-/

theorem cfg_yields_sound_for_symbol_language
    {G : CFG terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hprod : forall A rhs, G.produces A rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ symbolLanguage (Symbol.nonterminal A))
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Yields G x y)
    (hw : w ∈ CFG.FormLanguage symbolLanguage y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprodA hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hy] at hw
                          rw [hx]
                          exact CFG.formLanguage_replace_sound symbolLanguage
                            (hprod A rhs hprodA) hw

private theorem cfg_derives_sound_for_symbol_language_aux
    {G : CFG terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hterminal : forall a,
      Word.Symbol a ∈ symbolLanguage (Symbol.terminal a))
    (hprod : forall A rhs, G.produces A rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ symbolLanguage (Symbol.nonterminal A))
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (hy : y = SententialForm.terminalWord w)
    (h : CFG.Derives G x y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  induction h generalizing w with
  | refl _ =>
      rw [hy]
      exact CFG.terminalWord_mem_formLanguage symbolLanguage hterminal w
  | step hstep _ ih =>
      exact cfg_yields_sound_for_symbol_language symbolLanguage hprod hstep
        (ih hy)

theorem cfg_derives_sound_for_symbol_language
    {G : CFG terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hterminal : forall a,
      Word.Symbol a ∈ symbolLanguage (Symbol.terminal a))
    (hprod : forall A rhs, G.produces A rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ symbolLanguage (Symbol.nonterminal A))
    {x : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Derives G x (SententialForm.terminalWord w)) :
    w ∈ CFG.FormLanguage symbolLanguage x :=
  cfg_derives_sound_for_symbol_language_aux symbolLanguage hterminal hprod rfl h

inductive AnBnCstarNT where
  | start
  | pair
  | ctail
deriving DecidableEq

namespace AnBnCstarNT

def finite : Foundation.FiniteType AnBnCstarNT where
  elems := [start, pair, ctail]
  complete := by
    intro x
    cases x <;> simp

end AnBnCstarNT

inductive AnBnCstarProduces :
    AnBnCstarNT -> SententialForm ABC AnBnCstarNT -> Prop where
  | startRule :
      AnBnCstarProduces AnBnCstarNT.start
        [Symbol.nonterminal AnBnCstarNT.pair,
         Symbol.nonterminal AnBnCstarNT.ctail]
  | pairWrap :
      AnBnCstarProduces AnBnCstarNT.pair
        [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
         Symbol.terminal ABC.b]
  | pairStop :
      AnBnCstarProduces AnBnCstarNT.pair []
  | cMore :
      AnBnCstarProduces AnBnCstarNT.ctail
        [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail]
  | cStop :
      AnBnCstarProduces AnBnCstarNT.ctail []

def AnBnCstarGrammar : CFG ABC AnBnCstarNT where
  start := AnBnCstarNT.start
  produces := AnBnCstarProduces
  nonterminalsFinite := AnBnCstarNT.finite

def anbnCstarSymbolLanguage : Symbol ABC AnBnCstarNT -> Language ABC
  | Symbol.terminal t => Language.Singleton (Word.Symbol t)
  | Symbol.nonterminal AnBnCstarNT.start => anbnCstarLanguage
  | Symbol.nonterminal AnBnCstarNT.pair => abcAnBnLanguage
  | Symbol.nonterminal AnBnCstarNT.ctail => abcCstarLanguage

/-!
The {lit}`a^n b^n c^*` grammar has two independent phases: one nonterminal
generates the matched {lit}`a`/{lit}`b` prefix, and the other generates the
arbitrary tail of {lit}`c`s.
-/

theorem anbnCstar_pair_stop_generated :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
      (SententialForm.terminalWord (abcAnBnWord 0)) := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AnBnCstarNT.pair
  exists ([] : SententialForm ABC AnBnCstarNT)
  constructor
  · exact AnBnCstarProduces.pairStop
  constructor
  · rfl
  · simp [abcAnBnWord, Word.Concat, Word.RepeatSymbol, SententialForm.terminalWord]

theorem anbnCstar_pair_wrap_generated {w : Word ABC}
    (h : CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
      (SententialForm.terminalWord w)) :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
      (SententialForm.terminalWord (ABC.a :: Word.Concat w [ABC.b])) := by
  have hStart : CFG.Yields AnBnCstarGrammar
      [Symbol.nonterminal AnBnCstarNT.pair]
      [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
       Symbol.terminal ABC.b] := by
    exists []
    exists []
    exists AnBnCstarNT.pair
    exists [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
      Symbol.terminal ABC.b]
    constructor
    · exact AnBnCstarProduces.pairWrap
    constructor <;> rfl
  have hContext :
      CFG.Derives AnBnCstarGrammar
        [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
         Symbol.terminal ABC.b]
        (Symbol.terminal ABC.a ::
          SententialForm.terminalWord w ++ [Symbol.terminal ABC.b]) := by
    simpa using CFG.derives_context h [Symbol.terminal ABC.a]
      [Symbol.terminal ABC.b]
  have hAll := CFG.Derives.step hStart hContext
  change CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
    (SententialForm.terminalWord (ABC.a :: Word.Concat w [ABC.b]))
  simpa [SententialForm.terminalWord, Word.Concat] using hAll

theorem anbnCstar_pair_words_generated (n : Nat) :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
      (SententialForm.terminalWord (abcAnBnWord n)) := by
  induction n with
  | zero => exact anbnCstar_pair_stop_generated
  | succ n ih =>
      simpa [abcAnBn_wrap_word n] using anbnCstar_pair_wrap_generated ih

theorem anbnCstar_c_stop_generated :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.ctail]
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.c 0)) := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AnBnCstarNT.ctail
  exists ([] : SententialForm ABC AnBnCstarNT)
  constructor
  · exact AnBnCstarProduces.cStop
  constructor
  · rfl
  · simp [Word.RepeatSymbol, SententialForm.terminalWord]

theorem anbnCstar_c_more_generated {w : Word ABC}
    (h : CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.ctail]
      (SententialForm.terminalWord w)) :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.ctail]
      (SententialForm.terminalWord (ABC.c :: w)) := by
  have hStart : CFG.Yields AnBnCstarGrammar
      [Symbol.nonterminal AnBnCstarNT.ctail]
      [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail] := by
    exists []
    exists []
    exists AnBnCstarNT.ctail
    exists [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail]
    constructor
    · exact AnBnCstarProduces.cMore
    constructor <;> rfl
  have hContext :
      CFG.Derives AnBnCstarGrammar
        [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail]
        (Symbol.terminal ABC.c :: SententialForm.terminalWord w) := by
    simpa using CFG.derives_context h [Symbol.terminal ABC.c] []
  have hAll := CFG.Derives.step hStart hContext
  simpa [SententialForm.terminalWord] using hAll

theorem anbnCstar_c_words_generated (k : Nat) :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.ctail]
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.c k)) := by
  induction k with
  | zero => exact anbnCstar_c_stop_generated
  | succ k ih =>
      simpa [abcCstar_cons_word k] using anbnCstar_c_more_generated ih

theorem anbnCstar_words_generated (n k : Nat) :
    anbnCstarWord n k ∈ CFG.GeneratedLanguage AnBnCstarGrammar := by
  have hStart : CFG.Yields AnBnCstarGrammar
      [Symbol.nonterminal AnBnCstarNT.start]
      [Symbol.nonterminal AnBnCstarNT.pair,
       Symbol.nonterminal AnBnCstarNT.ctail] := by
    exists []
    exists []
    exists AnBnCstarNT.start
    exists [Symbol.nonterminal AnBnCstarNT.pair,
      Symbol.nonterminal AnBnCstarNT.ctail]
    constructor
    · exact AnBnCstarProduces.startRule
    constructor <;> rfl
  have hPair :=
    anbnCstar_pair_words_generated n
  have hTail :=
    anbnCstar_c_words_generated k
  have hPairContext :
      CFG.Derives AnBnCstarGrammar
        [Symbol.nonterminal AnBnCstarNT.pair,
         Symbol.nonterminal AnBnCstarNT.ctail]
        (SententialForm.terminalWord (abcAnBnWord n) ++
          [Symbol.nonterminal AnBnCstarNT.ctail]) := by
    simpa using CFG.derives_context hPair []
      [Symbol.nonterminal AnBnCstarNT.ctail]
  have hTailContext :
      CFG.Derives AnBnCstarGrammar
        (SententialForm.terminalWord (abcAnBnWord n) ++
          [Symbol.nonterminal AnBnCstarNT.ctail])
        (SententialForm.terminalWord (abcAnBnWord n) ++
          SententialForm.terminalWord (Word.RepeatSymbol ABC.c k)) := by
    simpa using CFG.derives_context hTail
      (SententialForm.terminalWord (abcAnBnWord n)) []
  have hAll := CFG.Derives.step hStart
    (CFG.derives_trans hPairContext hTailContext)
  change CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.start]
    (SententialForm.terminalWord (anbnCstarWord n k))
  rw [anbnCstarWord, SententialForm.terminalWord_append]
  exact hAll

/-!
For the {lit}`a^n b^n c^*` grammar, generation is constructive first and
soundness second. The production-soundness theorem checks that each production
preserves the intended language of the current nonterminal.
-/

theorem anbnCstar_production_sound
    (A : AnBnCstarNT) (rhs : SententialForm ABC AnBnCstarNT)
    (hprod : AnBnCstarGrammar.produces A rhs) :
    forall w, w ∈ CFG.FormLanguage anbnCstarSymbolLanguage rhs ->
      w ∈ anbnCstarSymbolLanguage (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | startRule =>
      simp [CFG.FormLanguage] at hw
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
      simp [CFG.FormLanguage] at hw
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
      simp [CFG.FormLanguage] at hw
      rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
      rcases htail with ⟨middle, empty, hmiddle, hempty, htailEq⟩
      rcases hmiddle with ⟨k, hk⟩
      exists k + 1
      rw [hwEq, hfirst, htailEq, hk, hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using! abcCstar_cons_word k
  | cStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0

theorem anbnCstar_generated_only_language {w : Word ABC}
    (h : w ∈ CFG.GeneratedLanguage AnBnCstarGrammar) :
    w ∈ anbnCstarLanguage := by
  have hs := cfg_derives_sound_for_symbol_language anbnCstarSymbolLanguage
    (by intro t; rfl) anbnCstar_production_sound h
  simp [CFG.FormLanguage] at hs
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
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      anbnCstar_hasFiniteProductions
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
      simp [CFG.FormLanguage] at hw
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
      simp [CFG.FormLanguage] at hw
      rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
      rcases htail with ⟨middle, empty, hmiddle, hempty, htailEq⟩
      rcases hmiddle with ⟨k, hk⟩
      exists k + 1
      rw [hwEq, hfirst, htailEq, hk, hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using! abcAstar_cons_word k
  | aStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0
  | pairWrap =>
      simp [CFG.FormLanguage] at hw
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
  simp [CFG.FormLanguage] at hs
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
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      astarBnCn_hasFiniteProductions
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
  · lia
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
  · lia
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
  · lia
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
  · lia
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
  · lia
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
  · lia
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
    have hk : k = n := by lia
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

end Section05
end Chapter04
end Book
end FoC

