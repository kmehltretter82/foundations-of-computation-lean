import FoC.Grammars.CFG

set_option doc.verso true

/-!
# BNF notation

## BNF expressions

The textbook uses BNF conveniences such as alternatives, optional pieces, and
repetition.  This module treats those conveniences as expressions that expand
to ordinary context-free right-hand sides.

## Book coordinates

Used by:
- Chapter 4, Section 4.2: alternatives, optional items, and repeated items
  are expanded into ordinary context-free right-hand sides.
-/

namespace FoC
namespace Grammars

namespace BNF

/-!
# Expression syntax

BNF forms are syntax trees over ordinary grammar symbols: empty pieces, single
symbols, sequencing, alternatives, optional expressions, and repeated
expressions.
-/

inductive Expr (terminal : Type u) (nonterminal : Type v) where
  | empty : Expr terminal nonterminal
  | symbol : Symbol terminal nonterminal -> Expr terminal nonterminal
  | seq : Expr terminal nonterminal -> Expr terminal nonterminal -> Expr terminal nonterminal
  | alt : Expr terminal nonterminal -> Expr terminal nonterminal -> Expr terminal nonterminal
  | optional : Expr terminal nonterminal -> Expr terminal nonterminal
  | many : Expr terminal nonterminal -> Expr terminal nonterminal

namespace Expr

/-!
# Expansion relation

Expansion interprets a BNF expression as one ordinary sentential form. The
constructors are the formal counterpart of replacing BNF notation by concrete
right-hand sides.
-/

inductive Expands :
    Expr terminal nonterminal -> SententialForm terminal nonterminal -> Prop where
  | empty : Expands empty []
  | symbol (s : Symbol terminal nonterminal) : Expands (symbol s) [s]
  | seq {e f : Expr terminal nonterminal} {x y} :
      Expands e x -> Expands f y -> Expands (seq e f) (x ++ y)
  | altLeft {e f : Expr terminal nonterminal} {x} :
      Expands e x -> Expands (alt e f) x
  | altRight {e f : Expr terminal nonterminal} {y} :
      Expands f y -> Expands (alt e f) y
  | optionalNone (e : Expr terminal nonterminal) :
      Expands (optional e) []
  | optionalSome {e : Expr terminal nonterminal} {x} :
      Expands e x -> Expands (optional e) x
  | manyZero (e : Expr terminal nonterminal) :
      Expands (many e) []
  | manyMore {e : Expr terminal nonterminal} {x xs} :
      Expands e x -> Expands (many e) xs -> Expands (many e) (x ++ xs)

/-!
# BNF laws

These lemmas give the useful introduction and equivalence rules for
alternatives, optional pieces, and repetitions.
-/

theorem alt_expands {e f : Expr terminal nonterminal} {x} :
    Expands (alt e f) x <-> Expands e x ∨ Expands f x := by
  constructor
  · intro h
    cases h with
    | altLeft he => exact Or.inl he
    | altRight hf => exact Or.inr hf
  · intro h
    cases h with
    | inl he => exact Expands.altLeft he
    | inr hf => exact Expands.altRight hf

theorem optional_empty (e : Expr terminal nonterminal) :
    Expands (optional e) [] :=
  Expands.optionalNone e

theorem optional_some {e : Expr terminal nonterminal} {x}
    (h : Expands e x) : Expands (optional e) x :=
  Expands.optionalSome h

theorem repeat_empty (e : Expr terminal nonterminal) :
    Expands (many e) [] :=
  Expands.manyZero e

theorem repeat_cons {e : Expr terminal nonterminal} {x xs}
    (hx : Expands e x) (hxs : Expands (many e) xs) :
    Expands (many e) (x ++ xs) :=
  Expands.manyMore hx hxs

end Expr
end BNF

end Grammars
end FoC
