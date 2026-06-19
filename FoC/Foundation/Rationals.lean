set_option doc.verso true

/-!
# Rational representatives

## Raw rational representatives

The book introduces rational numbers as ratios of integers with nonzero
denominator. This module formalizes that representation directly. It does not
yet quotient different representatives such as {lit}`1/2` and {lit}`2/4`; that
quotient layer is developed separately in
{module -checked}`FoC.Foundation.QuotientRationals`.

## Book coordinates

Used by:
- Chapter 1, Section 1.6: rational-number proof examples
- Chapter 1, Section 1.7: irrationality statements, later
- Chapter 2, Section 2.6: countability of rationals, later
-/

namespace FoC
namespace Foundation

/-!
# Raw representatives

A rational number is represented by an integer numerator and a nonzero integer
denominator.  No quotienting is performed in this file.
-/

structure Rational where
  num : Int
  den : Int
  den_ne_zero : den ≠ 0

namespace Rational

/-!
# Arithmetic operations

The operations are defined by the usual representative formulas, with each
definition carrying the proof that the new denominator is nonzero.
-/

def IsRepresentation (_num den : Int) : Prop :=
  den ≠ 0

def ofInt (n : Int) : Rational where
  num := n
  den := 1
  den_ne_zero := by
    decide

def add (x y : Rational) : Rational where
  num := x.num * y.den + y.num * x.den
  den := x.den * y.den
  den_ne_zero := Int.mul_ne_zero x.den_ne_zero y.den_ne_zero

def neg (x : Rational) : Rational where
  num := -x.num
  den := x.den
  den_ne_zero := x.den_ne_zero

def sub (x y : Rational) : Rational :=
  add x (neg y)

def mul (x y : Rational) : Rational where
  num := x.num * y.num
  den := x.den * y.den
  den_ne_zero := Int.mul_ne_zero x.den_ne_zero y.den_ne_zero

def inv (x : Rational) (h : x.num ≠ 0) : Rational where
  num := x.den
  den := x.num
  den_ne_zero := h

def div (x y : Rational) (h : y.num ≠ 0) : Rational :=
  mul x (inv y h)

theorem representation_of_den_ne_zero {num den : Int}
    (hden : den ≠ 0) : IsRepresentation num den :=
  hden

theorem add_den_ne_zero (x y : Rational) :
    (add x y).den ≠ 0 :=
  (add x y).den_ne_zero

theorem mul_den_ne_zero (x y : Rational) :
    (mul x y).den ≠ 0 :=
  (mul x y).den_ne_zero

/-!
# Representability checks

The rational-addition proof checks that the usual common-denominator formula
still has a nonzero denominator.
-/
theorem add_representation {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    IsRepresentation (a * d + c * b) (b * d) :=
  Int.mul_ne_zero hb hd

/-!
The rational-multiplication exercise has the same shape: the product
denominator is nonzero when both input denominators are nonzero.
-/
theorem mul_representation {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    IsRepresentation (a * c) (b * d) :=
  Int.mul_ne_zero hb hd

end Rational

end Foundation
end FoC
