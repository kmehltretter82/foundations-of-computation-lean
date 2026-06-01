import FoC.Grammars.BNF

namespace FoC
namespace Book
namespace Chapter04
namespace Section02

/-!
Book: Chapter 4, Section 4.2, Application: BNF.
-/

open Grammars

-- Book: Chapter 4, Section 4.2, a BNF symbol expands to its singleton RHS.
theorem bnf_symbol_expands (s : Symbol terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.symbol s) [s] :=
  BNF.Expr.Expands.symbol s

-- Book: Chapter 4, Section 4.2, sequencing concatenates expanded RHS lists.
theorem bnf_sequence_expands {e f : BNF.Expr terminal nonterminal} {x y}
    (hx : BNF.Expr.Expands e x) (hy : BNF.Expr.Expands f y) :
    BNF.Expr.Expands (BNF.Expr.seq e f) (x ++ y) :=
  BNF.Expr.Expands.seq hx hy

-- Book: Chapter 4, Section 4.2, BNF alternatives.
theorem bnf_alternative_expands {e f : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands (BNF.Expr.alt e f) rhs) :
    BNF.Expr.Expands e rhs ∨ BNF.Expr.Expands f rhs :=
  (BNF.Expr.alt_expands).mp h

-- Book: Chapter 4, Section 4.2, BNF alternatives.
theorem bnf_expands_alternative_left {e f : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands e rhs) :
    BNF.Expr.Expands (BNF.Expr.alt e f) rhs :=
  (BNF.Expr.alt_expands).mpr (Or.inl h)

-- Book: Chapter 4, Section 4.2, optional BNF item omitted.
theorem bnf_optional_empty (e : BNF.Expr terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.optional e) [] :=
  BNF.Expr.optional_empty e

-- Book: Chapter 4, Section 4.2, optional BNF item present.
theorem bnf_optional_some {e : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands e rhs) :
    BNF.Expr.Expands (BNF.Expr.optional e) rhs :=
  BNF.Expr.optional_some h

-- Book: Chapter 4, Section 4.2, repeated BNF item omitted.
theorem bnf_repeat_empty (e : BNF.Expr terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.many e) [] :=
  BNF.Expr.repeat_empty e

-- Book: Chapter 4, Section 4.2, repeated BNF item extended.
theorem bnf_repeat_cons {e : BNF.Expr terminal nonterminal} {first rest}
    (hfirst : BNF.Expr.Expands e first)
    (hrest : BNF.Expr.Expands (BNF.Expr.many e) rest) :
    BNF.Expr.Expands (BNF.Expr.many e) (first ++ rest) :=
  BNF.Expr.repeat_cons hfirst hrest

-- Book: Chapter 4, Section 4.2, two repeated BNF items expand by two `many` steps.
theorem bnf_repeat_two {e : BNF.Expr terminal nonterminal} {first second}
    (hfirst : BNF.Expr.Expands e first)
    (hsecond : BNF.Expr.Expands e second) :
    BNF.Expr.Expands (BNF.Expr.many e) (first ++ second) := by
  exact BNF.Expr.repeat_cons hfirst (by
    simpa [List.append_nil] using
      BNF.Expr.repeat_cons hsecond (BNF.Expr.repeat_empty e))

end Section02
end Chapter04
end Book
end FoC
