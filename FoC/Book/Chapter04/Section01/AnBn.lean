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
# The Equal Two-Block Language

The grammar for {lit}`a^n b^n` is proved sound and complete by tracking its unique open sentential form and terminal prefix/suffix shape.
-/

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

def anbnWrapProduction : CFG.Production AB AnBnNT where
  lhs := AnBnNT.S
  rhs :=
    [Symbol.terminal AB.a, Symbol.nonterminal AnBnNT.S, Symbol.terminal AB.b]

def anbnStopProduction : CFG.Production AB AnBnNT where
  lhs := AnBnNT.S
  rhs := []

def anbnProductionList : List (CFG.Production AB AnBnNT) :=
  [anbnWrapProduction, anbnStopProduction]

def AnBnGrammar : CFG AB AnBnNT :=
  CFG.ProductionList.toCFG AnBnNT.S AnBnNT.finite anbnProductionList

def anbnPresentation : CFG.Presentation AnBnGrammar :=
  CFG.ProductionList.presentation AnBnNT.S AnBnNT.finite anbnProductionList

theorem anbn_produces_iff
    (A : AnBnNT) (rhs : SententialForm AB AnBnNT) :
    AnBnGrammar.produces A rhs <->
      (A = AnBnNT.S ∧
        [Symbol.terminal AB.a, Symbol.nonterminal AnBnNT.S,
          Symbol.terminal AB.b] = rhs) ∨
      (A = AnBnNT.S ∧ rhs = []) := by
  simp [AnBnGrammar, CFG.ProductionList.toCFG, anbnProductionList,
    anbnWrapProduction, anbnStopProduction]

theorem anbn_wrap_produces :
    AnBnGrammar.produces AnBnNT.S
      [Symbol.terminal AB.a, Symbol.nonterminal AnBnNT.S,
        Symbol.terminal AB.b] :=
  (anbn_produces_iff _ _).mpr (Or.inl ⟨rfl, rfl⟩)

theorem anbn_stop_produces : AnBnGrammar.produces AnBnNT.S [] :=
  (anbn_produces_iff _ _).mpr (Or.inr ⟨rfl, rfl⟩)

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
                          rcases (anbn_produces_iff A rhs).mp hprod with
                            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          ·
                              left
                              simp [AnBnOpenForm, AnBnPrefix, AnBnSuffix,
                                Word.RepeatSymbol, SententialForm.terminalWord,
                                replicate_succ_eq_append (Symbol.terminal AB.a) n,
                                replicate_succ_eq_cons (Symbol.terminal AB.b) n,
                                List.append_assoc]
                          ·
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
  · exact anbn_stop_produces
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
    · exact anbn_wrap_produces
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

theorem anbn_has_finite_productions :
    CFG.HasFiniteProductions AnBnGrammar :=
  CFG.hasFiniteProductions_of_hasFinitePresentation ⟨anbnPresentation⟩

def AnBnLanguage : Language AB :=
  fun w => exists n, w = AnBnWord n

theorem anbn_context_free : ContextFreeLanguage AnBnLanguage := by
  exists AnBnNT
  exists AnBnGrammar
  constructor
  · exact CFG.hasFinitePresentation_of_hasFiniteProductions
      anbn_has_finite_productions
  · exact anbn_generated_language_exact

end Section01
end Chapter04
end Book
end FoC
