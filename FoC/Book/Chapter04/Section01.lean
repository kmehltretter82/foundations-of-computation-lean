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

-- Book: Chapter 4, Section 4.1, concatenation grammar construction.
theorem concat_grammar_generates (G : CFG terminal left) (H : CFG terminal right)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G) (hy : y ∈ CFG.GeneratedLanguage H) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) :=
  CFL.concatGrammar_generates G H hx hy

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

def AnBnWord : Nat -> Word AB
  | 0 => []
  | n + 1 => AnBnWrap (AnBnWord n)

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
      exact anbn_wrap_generated ih

end Section01
end Chapter04
end Book
end FoC
