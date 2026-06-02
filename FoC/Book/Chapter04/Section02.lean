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

inductive BNFExampleTerminal where
  | zero
  | one
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine
  | plus
  | minus
  | semicolon
deriving DecidableEq

inductive BNFExampleNT where
  | digit
  | type
  | variable
deriving DecidableEq

def bnfTerminal (t : BNFExampleTerminal) :
    Symbol BNFExampleTerminal BNFExampleNT :=
  Symbol.terminal t

def bnfNonterminal (nt : BNFExampleNT) :
    Symbol BNFExampleTerminal BNFExampleNT :=
  Symbol.nonterminal nt

def bnfTerminalExpr (t : BNFExampleTerminal) :
    BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.symbol (bnfTerminal t)

def bnfNonterminalExpr (nt : BNFExampleNT) :
    BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.symbol (bnfNonterminal nt)

def digitAlternativeExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.zero)
    (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.one)
      (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.two)
        (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.three)
          (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.four)
            (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.five)
              (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.six)
                (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.seven)
                  (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.eight)
                    (bnfTerminalExpr BNFExampleTerminal.nine)))))))))

def signAlternativeExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.plus)
    (bnfTerminalExpr BNFExampleTerminal.minus)

def declarationExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.type)
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.variable)
      (BNF.Expr.optional (bnfTerminalExpr BNFExampleTerminal.semicolon)))

def integerExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.digit)
    (BNF.Expr.many (bnfNonterminalExpr BNFExampleNT.digit))

-- Book: Chapter 4, Section 4.2, a concrete digit alternative.
theorem bnf_digit_seven_expands :
    BNF.Expr.Expands digitAlternativeExpr [bnfTerminal BNFExampleTerminal.seven] := by
  unfold digitAlternativeExpr
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altLeft
  exact BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.seven)

-- Book: Chapter 4, Section 4.2, sign alternatives.
theorem bnf_sign_plus_expands :
    BNF.Expr.Expands signAlternativeExpr [bnfTerminal BNFExampleTerminal.plus] := by
  exact BNF.Expr.Expands.altLeft
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.plus))

-- Book: Chapter 4, Section 4.2, sign alternatives.
theorem bnf_sign_minus_expands :
    BNF.Expr.Expands signAlternativeExpr [bnfTerminal BNFExampleTerminal.minus] := by
  exact BNF.Expr.Expands.altRight
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.minus))

-- Book: Chapter 4, Section 4.2, optional semicolon omitted.
theorem bnf_declaration_without_semicolon_expands :
    BNF.Expr.Expands declarationExpr
      [bnfNonterminal BNFExampleNT.type, bnfNonterminal BNFExampleNT.variable] := by
  unfold declarationExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.type))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.variable))
      (BNF.Expr.Expands.optionalNone
        (bnfTerminalExpr BNFExampleTerminal.semicolon)))

-- Book: Chapter 4, Section 4.2, optional semicolon present.
theorem bnf_declaration_with_semicolon_expands :
    BNF.Expr.Expands declarationExpr
      [bnfNonterminal BNFExampleNT.type, bnfNonterminal BNFExampleNT.variable,
        bnfTerminal BNFExampleTerminal.semicolon] := by
  unfold declarationExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.type))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.variable))
      (BNF.Expr.Expands.optionalSome
        (BNF.Expr.Expands.symbol
          (bnfTerminal BNFExampleTerminal.semicolon))))

-- Book: Chapter 4, Section 4.2, integer as one digit followed by no repeats.
theorem bnf_integer_one_digit_expands :
    BNF.Expr.Expands integerExpr [bnfNonterminal BNFExampleNT.digit] := by
  unfold integerExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
    (BNF.Expr.Expands.manyZero
      (bnfNonterminalExpr BNFExampleNT.digit))

-- Book: Chapter 4, Section 4.2, integer as one digit followed by two repeats.
theorem bnf_integer_three_digits_expands :
    BNF.Expr.Expands integerExpr
      [bnfNonterminal BNFExampleNT.digit, bnfNonterminal BNFExampleNT.digit,
        bnfNonterminal BNFExampleNT.digit] := by
  unfold integerExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
    (BNF.Expr.repeat_cons
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
      (BNF.Expr.repeat_cons
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
        (BNF.Expr.repeat_empty (bnfNonterminalExpr BNFExampleNT.digit))))

end Section02
end Chapter04
end Book
end FoC
