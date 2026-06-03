set_option doc.verso true

/-!
# A small quadratic-surd model

## The Quad2 model

{lit}`Quad2` represents expressions of the form {lit}`a + b√2` with integer
coefficients.  This is not a real-number implementation; it is a small algebraic
model for the book exercise showing that the product of two irrational numbers
need not be irrational.  A future {lit}`Real` module can embed this structure by
mapping `a + b√2` to the corresponding real expression.

## Book coordinates

Used by:
- Chapter 1, Section 1.6: counterexample to "the product of two irrational
  numbers is irrational"
- Chapter 1, Section 1.7: surrogate for `√2` before full real numbers exist
-/

namespace FoC
namespace Foundation

/-!
# Algebraic surrogate

{lit}`Quad2` stores the integer coefficients of an expression of the form
{lit}`a + b√2`.
-/

structure Quad2 where
  rational : Int
  radical : Int
deriving DecidableEq

namespace Quad2

/-!
# Operations and rational-like elements

The small algebra supports addition, negation, subtraction, multiplication, and
the predicates needed for the Chapter 1 irrational-product example.
-/

def ofInt (n : Int) : Quad2 :=
  { rational := n, radical := 0 }

def sqrtTwo : Quad2 :=
  { rational := 0, radical := 1 }

def add (x y : Quad2) : Quad2 :=
  { rational := x.rational + y.rational,
    radical := x.radical + y.radical }

def neg (x : Quad2) : Quad2 :=
  { rational := -x.rational,
    radical := -x.radical }

def sub (x y : Quad2) : Quad2 :=
  add x (neg y)

def mul (x y : Quad2) : Quad2 :=
  { rational := x.rational * y.rational + 2 * x.radical * y.radical,
    radical := x.rational * y.radical + x.radical * y.rational }

def RationalLike (x : Quad2) : Prop :=
  x.radical = 0

def IrrationalLike (x : Quad2) : Prop :=
  ¬ x.RationalLike

theorem ofInt_rationalLike (n : Int) : RationalLike (ofInt n) :=
  rfl

/-!
# The square root of two example

The formal facts record that {lit}`sqrtTwo` is irrational-like while its square
is rational-like.
-/

theorem sqrtTwo_irrationalLike : IrrationalLike sqrtTwo := by
  intro h
  simp [RationalLike, sqrtTwo] at h

theorem sqrtTwo_mul_self_eq_two : mul sqrtTwo sqrtTwo = ofInt 2 :=
  rfl

theorem sqrtTwo_mul_self_rationalLike : RationalLike (mul sqrtTwo sqrtTwo) :=
  rfl

end Quad2

end Foundation
end FoC
