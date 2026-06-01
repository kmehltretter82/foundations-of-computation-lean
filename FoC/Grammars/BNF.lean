import FoC.Grammars.CFG

namespace FoC
namespace Grammars

/-!
Small BNF notation model.

Used by:
- Chapter 4, Section 4.2: alternatives, optional items, and repeated items
  are expanded into ordinary context-free right-hand sides.
-/

namespace BNF

inductive Expr (terminal : Type u) (nonterminal : Type v) where
  | empty : Expr terminal nonterminal
  | symbol : Symbol terminal nonterminal -> Expr terminal nonterminal
  | seq : Expr terminal nonterminal -> Expr terminal nonterminal -> Expr terminal nonterminal
  | alt : Expr terminal nonterminal -> Expr terminal nonterminal -> Expr terminal nonterminal
  | optional : Expr terminal nonterminal -> Expr terminal nonterminal
  | many : Expr terminal nonterminal -> Expr terminal nonterminal

namespace Expr

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
