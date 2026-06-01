namespace FoC
namespace Foundation

/-!
Standalone rational-number representatives.

The book introduces rational numbers as ratios of integers with nonzero
denominator. This module formalizes that representation directly. It does not
yet quotient different representatives such as `1/2` and `2/4`.

Used by:
- Chapter 1, Section 1.6: rational-number proof examples
- Chapter 1, Section 1.7: irrationality statements, later
- Chapter 2, Section 2.6: countability of rationals, later
-/

structure Rational where
  num : Int
  den : Int
  den_ne_zero : den ≠ 0

namespace Rational

def IsRepresentation (_num den : Int) : Prop :=
  den ≠ 0

def ofInt (n : Int) : Rational where
  num := n
  den := 1
  den_ne_zero := by
    omega

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

theorem add_num (x y : Rational) :
    (add x y).num = x.num * y.den + y.num * x.den :=
  rfl

theorem add_den (x y : Rational) :
    (add x y).den = x.den * y.den :=
  rfl

theorem add_den_ne_zero (x y : Rational) :
    (add x y).den ≠ 0 :=
  (add x y).den_ne_zero

theorem neg_den (x : Rational) :
    (neg x).den = x.den :=
  rfl

theorem neg_den_ne_zero (x : Rational) :
    (neg x).den ≠ 0 :=
  (neg x).den_ne_zero

theorem sub_den_ne_zero (x y : Rational) :
    (sub x y).den ≠ 0 :=
  (sub x y).den_ne_zero

theorem mul_num (x y : Rational) :
    (mul x y).num = x.num * y.num :=
  rfl

theorem mul_den (x y : Rational) :
    (mul x y).den = x.den * y.den :=
  rfl

theorem mul_den_ne_zero (x y : Rational) :
    (mul x y).den ≠ 0 :=
  (mul x y).den_ne_zero

theorem inv_den_ne_zero (x : Rational) (h : x.num ≠ 0) :
    (inv x h).den ≠ 0 :=
  (inv x h).den_ne_zero

theorem div_den_ne_zero (x y : Rational) (h : y.num ≠ 0) :
    (div x y h).den ≠ 0 :=
  (div x y h).den_ne_zero

-- Book: Chapter 1, Section 1.6, rational addition proof.
theorem add_representation {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    IsRepresentation (a * d + c * b) (b * d) :=
  Int.mul_ne_zero hb hd

-- Book: Chapter 1, Section 1.6, rational multiplication exercise.
theorem mul_representation {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    IsRepresentation (a * c) (b * d) :=
  Int.mul_ne_zero hb hd

theorem add_representable {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    exists r : Rational, r.num = a * d + c * b ∧ r.den = b * d := by
  exact Exists.intro
    { num := a * d + c * b, den := b * d, den_ne_zero := Int.mul_ne_zero hb hd }
    (And.intro rfl rfl)

theorem mul_representable {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    exists r : Rational, r.num = a * c ∧ r.den = b * d := by
  exact Exists.intro
    { num := a * c, den := b * d, den_ne_zero := Int.mul_ne_zero hb hd }
    (And.intro rfl rfl)

end Rational

end Foundation
end FoC
