import FoC.Book.Chapter04.Section01
import FoC.Grammars.CFL.Closure

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section05

/-!
# Chapter 4, Section 4.5: Non-Context-Free Languages

This implementation module begins the chapter's concrete
{lit}`a^n b^n c^n` witness development. The reusable PDA/DFA product and
context-free closure theorems now live in
{module}`FoC.Grammars.PDA.Intersection` and
{module}`FoC.Grammars.CFL.Closure`.
-/

open Languages
open Grammars

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

end Section05
end Chapter04
end Book
end FoC
