import FoC.Grammars.CFL

namespace FoC
namespace Book
namespace Chapter04
namespace Section01

/-!
Book: Chapter 4, Section 4.1, Context-free Grammars.
-/

open Foundation
open Languages
open Grammars

-- Book: Chapter 4, Section 4.1, Theorem 4.1(1).
theorem yields_implies_derives {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : CFG.Yields G x y) :
    CFG.Derives G x y :=
  CFG.yields_derives h

-- Book: Chapter 4, Section 4.1, Theorem 4.1(2).
theorem derives_transitive {G : CFG terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : CFG.Derives G x y) (hyz : CFG.Derives G y z) :
    CFG.Derives G x z :=
  CFG.derives_trans hxy hyz

-- Book: Chapter 4, Section 4.1, Theorem 4.1(3).
theorem yields_inside_context {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Yields G x y) (s t : SententialForm terminal nonterminal) :
    CFG.Yields G (s ++ x ++ t) (s ++ y ++ t) :=
  CFG.yields_context h s t

-- Book: Chapter 4, Section 4.1, Theorem 4.1(4).
theorem derives_inside_context {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Derives G x y) (s t : SententialForm terminal nonterminal) :
    CFG.Derives G (s ++ x ++ t) (s ++ y ++ t) :=
  CFG.derives_context h s t

-- Book: Chapter 4, Section 4.1, definition of a context-free language.
def ContextFreeLanguage (L : Language terminal) : Prop :=
  CFL.ContextFreeLanguage L

-- Book: Chapter 4, Section 4.1, union grammar construction, forward direction.
theorem union_grammar_generates_left (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage G) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFL.unionGrammar_generates_left G H hw

-- Book: Chapter 4, Section 4.1, union grammar construction, forward direction.
theorem union_grammar_generates_right (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage H) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFL.unionGrammar_generates_right G H hw

-- Book: Chapter 4, Section 4.1, Theorem 4.3, union grammar converse.
theorem union_grammar_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H)) :
    w ∈ Language.Union (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFL.unionGrammar_generates_inv G H h

-- Book: Chapter 4, Section 4.1, Theorem 4.3, exact union grammar language.
theorem union_grammar_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) <->
      w ∈ Language.Union (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFL.unionGrammar_language_exact G H w

-- Book: Chapter 4, Section 4.1, Theorem 4.3, CFL closure under union.
theorem context_free_languages_closed_under_union {L M : Language terminal}
    (hL : ContextFreeLanguage L) (hM : ContextFreeLanguage M) :
    ContextFreeLanguage (Language.Union L M) :=
  CFL.union_context_free hL hM

-- Book: Chapter 4, Section 4.1, concatenation grammar construction.
theorem concat_grammar_generates (G : CFG terminal left) (H : CFG terminal right)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G) (hy : y ∈ CFG.GeneratedLanguage H) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) :=
  CFL.concatGrammar_generates G H hx hy

-- Book: Chapter 4, Section 4.1, Theorem 4.3, concatenation grammar converse.
theorem concat_grammar_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H)) :
    w ∈ Language.Concat (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFL.concatGrammar_generates_inv G H h

-- Book: Chapter 4, Section 4.1, Theorem 4.3, exact concatenation grammar language.
theorem concat_grammar_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) <->
      w ∈ Language.Concat (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFL.concatGrammar_language_exact G H w

-- Book: Chapter 4, Section 4.1, Theorem 4.3, CFL closure under concatenation.
theorem context_free_languages_closed_under_concatenation {L M : Language terminal}
    (hL : ContextFreeLanguage L) (hM : ContextFreeLanguage M) :
    ContextFreeLanguage (Language.Concat L M) :=
  CFL.concat_context_free hL hM

-- Book: Chapter 4, Section 4.1, Kleene-star grammar construction.
theorem star_grammar_generates_empty (G : CFG terminal nt) :
    ([] : Word terminal) ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFL.starGrammar_generates_empty G

-- Book: Chapter 4, Section 4.1, Kleene-star grammar construction.
theorem star_grammar_generates_cons (G : CFG terminal nt)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G)
    (hy : y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFL.starGrammar_generates_cons G hx hy

-- Book: Chapter 4, Section 4.1, Theorem 4.3, Kleene-star grammar converse.
theorem star_grammar_generates_inv (G : CFG terminal nt) {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    w ∈ Language.Star (CFG.GeneratedLanguage G) :=
  CFL.starGrammar_generates_inv G h

-- Book: Chapter 4, Section 4.1, Theorem 4.3, exact Kleene-star grammar language.
theorem star_grammar_language_exact (G : CFG terminal nt) (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) <->
      w ∈ Language.Star (CFG.GeneratedLanguage G) :=
  CFL.starGrammar_language_exact G w

-- Book: Chapter 4, Section 4.1, Theorem 4.3, CFL closure under Kleene star.
theorem context_free_languages_closed_under_kleene_star {L : Language terminal}
    (hL : ContextFreeLanguage L) :
    ContextFreeLanguage (Language.Star L) :=
  CFL.star_context_free hL

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

theorem anbn_terminal_derives_eq_aux
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

theorem anbn_open_derives_terminal_exact_aux
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

-- Book: Chapter 4, Section 4.1, Theorem 4.2 reverse inclusion.
theorem anbn_generated_only_anbn_words {w : Word AB}
    (h : w ∈ CFG.GeneratedLanguage AnBnGrammar) :
    exists n, w = AnBnWord n :=
  anbn_open_derives_terminal_exact_aux
    (Exists.intro 0 (by rfl))
    rfl h

-- Book: Chapter 4, Section 4.1, grammar for {a^n b^n}.
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

-- Book: Chapter 4, Section 4.1, wrapping derivations with a and b.
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

-- Book: Chapter 4, Section 4.1, every recursively described a^n b^n word is generated.
theorem anbn_words_generated (n : Nat) :
    AnBnWord n ∈ CFG.GeneratedLanguage AnBnGrammar := by
  induction n with
  | zero => exact anbn_empty_generated
  | succ n ih =>
      simpa [anbn_wrap_word n] using anbn_wrap_generated ih

-- Book: Chapter 4, Section 4.1, Theorem 4.2 exact language.
theorem anbn_generated_language_exact (w : Word AB) :
    w ∈ CFG.GeneratedLanguage AnBnGrammar <-> exists n, w = AnBnWord n := by
  constructor
  · exact anbn_generated_only_anbn_words
  · intro h
    cases h with
    | intro n hn =>
        rw [hn]
        exact anbn_words_generated n

end Section01
end Chapter04
end Book
end FoC
