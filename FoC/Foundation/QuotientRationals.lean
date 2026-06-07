import FoC.Foundation.Countable
import FoC.Foundation.RationalCore
import FoC.Foundation.Rationals
import Init.Data.Rat.Lemmas

set_option doc.verso true

/-!
# Quotient rational numbers

## Rational representatives modulo equality

The earlier {module}`FoC.Foundation.Rationals` module keeps raw
integer-over-integer representatives.
This module introduces the quotient-rational layer needed before Dedekind cuts:
integer numerators, positive natural denominators, and equality by cross
multiplication.

## Book coordinates

Used by:
- {lit}`Real` construction: Dedekind cuts over quotient rationals
- Chapter 1 real-number examples: rational embedding and arithmetic transport
- Chapter 2 countability examples: rationals as countable data
-/

namespace FoC
namespace Foundation

/-!
# Raw rational pairs

{lit}`RatPair` stores an integer numerator and a positive natural denominator.
Equality is cross-multiplication, and raw order is the corresponding
cross-multiplied inequality.
-/

structure RatPair where
  num : Int
  den : Nat
  den_pos : 0 < den

namespace RatPair

def Rel (p q : RatPair) : Prop :=
  p.num * (q.den : Int) = q.num * (p.den : Int)

def RawLt (p q : RatPair) : Prop :=
  p.num * (q.den : Int) < q.num * (p.den : Int)

def toRat (p : RatPair) : Rat :=
  Rat.divInt p.num (p.den : Int)

theorem den_ne_zero (p : RatPair) : p.den ≠ 0 := by
  exact Nat.ne_of_gt p.den_pos

theorem den_cast_ne_zero (p : RatPair) : (p.den : Int) ≠ 0 := by
  exact Int.ofNat_ne_zero.mpr (den_ne_zero p)

theorem den_cast_pos (p : RatPair) : 0 < (p.den : Int) := by
  exact Int.natCast_pos.mpr p.den_pos

theorem toRat_eq_iff_rel (p q : RatPair) :
    p.toRat = q.toRat <-> Rel p q := by
  exact Rat.divInt_eq_divInt_iff (den_cast_ne_zero p) (den_cast_ne_zero q)

theorem rel_of_toRat_eq {p q : RatPair} (h : p.toRat = q.toRat) : Rel p q :=
  (toRat_eq_iff_rel p q).mp h

theorem toRat_eq_of_rel {p q : RatPair} (h : Rel p q) : p.toRat = q.toRat :=
  (toRat_eq_iff_rel p q).mpr h

theorem rel_refl (p : RatPair) : Rel p p := by
  unfold Rel
  rfl

theorem rel_symm {p q : RatPair} (h : Rel p q) : Rel q p := by
  unfold Rel at h ⊢
  exact h.symm

theorem rel_trans {p q r : RatPair} (hpq : Rel p q) (hqr : Rel q r) : Rel p r := by
  apply rel_of_toRat_eq
  exact Eq.trans (toRat_eq_of_rel hpq) (toRat_eq_of_rel hqr)

instance instSetoid : Setoid RatPair where
  r := Rel
  iseqv := by
    constructor
    · exact rel_refl
    · intro p q
      exact rel_symm
    · intro p q r
      exact rel_trans

/-!
# Representative arithmetic

The raw representative operations mirror the usual rational formulas and then
prove compatibility with the standard {lit}`Rat` interpretation.
-/

def ofInt (n : Int) : RatPair where
  num := n
  den := 1
  den_pos := by omega

def ofNat (n : Nat) : RatPair :=
  ofInt n

def ofPositiveRatRep (q : PositiveRatRep) : RatPair where
  num := q.num
  den := q.den
  den_pos := q.den_pos

def ofRational (q : Rational) : RatPair where
  num := q.num * q.den.sign
  den := q.den.natAbs
  den_pos := by
    exact Int.natAbs_pos.mpr q.den_ne_zero

def ofStdRat (q : Rat) : RatPair where
  num := q.num
  den := q.den
  den_pos := Nat.pos_of_ne_zero q.den_nz

def add (p q : RatPair) : RatPair where
  num := p.num * (q.den : Int) + q.num * (p.den : Int)
  den := p.den * q.den
  den_pos := Nat.mul_pos p.den_pos q.den_pos

def neg (p : RatPair) : RatPair where
  num := -p.num
  den := p.den
  den_pos := p.den_pos

def sub (p q : RatPair) : RatPair :=
  add p (neg q)

def mul (p q : RatPair) : RatPair where
  num := p.num * q.num
  den := p.den * q.den
  den_pos := Nat.mul_pos p.den_pos q.den_pos

theorem toRat_ofInt (n : Int) :
    (ofInt n).toRat = (n : Rat) := by
  change Rat.divInt n ((1 : Nat) : Int) = (n : Rat)
  rw [Rat.divInt_ofNat]
  rw [← Rat.normalize_eq_mkRat (by decide : (1 : Nat) ≠ 0)]
  simp [Rat.normalize_eq]

theorem toRat_ofNat (n : Nat) :
    (ofNat n).toRat = (n : Rat) := by
  rw [ofNat, toRat_ofInt]
  rfl

theorem toRat_ofPositiveRatRep (q : PositiveRatRep) :
    (ofPositiveRatRep q).toRat = Rat.divInt q.num (q.den : Int) := by
  rfl

theorem toRat_ofRational (q : Rational) :
    (ofRational q).toRat = Rat.divInt q.num q.den := by
  change Rat.divInt (q.num * q.den.sign) (q.den.natAbs : Int) = Rat.divInt q.num q.den
  apply (Rat.divInt_eq_divInt_iff
    (Int.ofNat_ne_zero.mpr
      (Nat.ne_of_gt (Int.natAbs_pos.mpr q.den_ne_zero)))
    q.den_ne_zero).mpr
  generalize hden : q.den = d
  cases d with
  | ofNat n =>
      cases n with
      | zero => exact False.elim (q.den_ne_zero hden)
      | succ n => simp [Int.sign, Int.natAbs]
  | negSucc n =>
      simp [Int.sign, Int.natAbs, Int.negSucc_eq, Int.neg_mul_neg]

theorem toRat_ofStdRat (q : Rat) :
    (ofStdRat q).toRat = q := by
  exact Rat.num_divInt_den q

theorem toRat_add (p q : RatPair) :
    (add p q).toRat = p.toRat + q.toRat := by
  unfold toRat add
  rw [Rat.divInt_add_divInt]
  · simp [Int.natCast_mul]
  · exact den_cast_ne_zero p
  · exact den_cast_ne_zero q

theorem toRat_neg (p : RatPair) :
    (neg p).toRat = -p.toRat := by
  unfold toRat neg
  rw [Rat.neg_divInt]

theorem toRat_sub (p q : RatPair) :
    (sub p q).toRat = p.toRat - q.toRat := by
  simp [sub, toRat_add, toRat_neg, Rat.sub_eq_add_neg]

theorem toRat_mul (p q : RatPair) :
    (mul p q).toRat = p.toRat * q.toRat := by
  unfold toRat mul
  rw [Rat.divInt_mul_divInt]
  simp [Int.natCast_mul]

theorem add_respects {p p' q q' : RatPair}
    (hp : Rel p p') (hq : Rel q q') : Rel (add p q) (add p' q') := by
  apply rel_of_toRat_eq
  rw [toRat_add, toRat_add, toRat_eq_of_rel hp, toRat_eq_of_rel hq]

theorem neg_respects {p p' : RatPair}
    (hp : Rel p p') : Rel (neg p) (neg p') := by
  apply rel_of_toRat_eq
  rw [toRat_neg, toRat_neg, toRat_eq_of_rel hp]

theorem sub_respects {p p' q q' : RatPair}
    (hp : Rel p p') (hq : Rel q q') : Rel (sub p q) (sub p' q') := by
  exact add_respects hp (neg_respects hq)

theorem mul_respects {p p' q q' : RatPair}
    (hp : Rel p p') (hq : Rel q q') : Rel (mul p q) (mul p' q') := by
  apply rel_of_toRat_eq
  rw [toRat_mul, toRat_mul, toRat_eq_of_rel hp, toRat_eq_of_rel hq]

theorem rawLt_of_rel {p p' q q' : RatPair}
    (hp : Rel p p') (hq : Rel q q') (h : RawLt p q) : RawLt p' q' := by
  unfold RawLt at h ⊢
  have hp' : p.num * (p'.den : Int) = p'.num * (p.den : Int) := hp
  have hq' : q.num * (q'.den : Int) = q'.num * (q.den : Int) := hq
  have hmul := Int.mul_lt_mul_of_pos_right h
    (Int.mul_pos (den_cast_pos p') (den_cast_pos q'))
  have hleft :
      (p.num * (q.den : Int)) * ((p'.den : Int) * (q'.den : Int)) =
        (p'.num * (q'.den : Int)) * ((p.den : Int) * (q.den : Int)) := by
    calc
      (p.num * (q.den : Int)) * ((p'.den : Int) * (q'.den : Int))
          = (p.num * (p'.den : Int)) * ((q.den : Int) * (q'.den : Int)) := by
              ac_rfl
      _ = (p'.num * (p.den : Int)) * ((q.den : Int) * (q'.den : Int)) := by
              rw [hp']
      _ = (p'.num * (q'.den : Int)) * ((p.den : Int) * (q.den : Int)) := by
              ac_rfl
  have hright :
      (q.num * (p.den : Int)) * ((p'.den : Int) * (q'.den : Int)) =
        (q'.num * (p'.den : Int)) * ((p.den : Int) * (q.den : Int)) := by
    calc
      (q.num * (p.den : Int)) * ((p'.den : Int) * (q'.den : Int))
          = (q.num * (q'.den : Int)) * ((p.den : Int) * (p'.den : Int)) := by
              ac_rfl
      _ = (q'.num * (q.den : Int)) * ((p.den : Int) * (p'.den : Int)) := by
              rw [hq']
      _ = (q'.num * (p'.den : Int)) * ((p.den : Int) * (q.den : Int)) := by
              ac_rfl
  have htarget :
      (p'.num * (q'.den : Int)) * ((p.den : Int) * (q.den : Int)) <
        (q'.num * (p'.den : Int)) * ((p.den : Int) * (q.den : Int)) := by
    simpa [hleft, hright] using hmul
  exact Int.lt_of_mul_lt_mul_right htarget
    (Int.le_of_lt (Int.mul_pos (den_cast_pos p) (den_cast_pos q)))

theorem rawLt_congr {p p' q q' : RatPair}
    (hp : Rel p p') (hq : Rel q q') :
    RawLt p q <-> RawLt p' q' := by
  constructor
  · exact rawLt_of_rel hp hq
  · exact rawLt_of_rel (rel_symm hp) (rel_symm hq)

theorem rawLt_trans {p q r : RatPair}
    (hpq : RawLt p q) (hqr : RawLt q r) : RawLt p r := by
  unfold RawLt at hpq hqr ⊢
  have hd : 0 < (q.den : Int) * (q.den : Int) :=
    Int.mul_pos (den_cast_pos q) (den_cast_pos q)
  have hleft_mul := Int.mul_lt_mul_of_pos_right hpq
    (Int.mul_pos (den_cast_pos r) (den_cast_pos q))
  have hright_mul := Int.mul_lt_mul_of_pos_right hqr
    (Int.mul_pos (den_cast_pos p) (den_cast_pos q))
  have hleft :
      (p.num * (q.den : Int)) * ((r.den : Int) * (q.den : Int)) =
        (p.num * (r.den : Int)) * ((q.den : Int) * (q.den : Int)) := by
    ac_rfl
  have hmiddle_left :
      (q.num * (p.den : Int)) * ((r.den : Int) * (q.den : Int)) =
        (q.num * (r.den : Int)) * ((p.den : Int) * (q.den : Int)) := by
    ac_rfl
  have hmiddle_right :
      (q.num * (r.den : Int)) * ((p.den : Int) * (q.den : Int)) =
        (q.num * (r.den : Int)) * ((p.den : Int) * (q.den : Int)) := by
    rfl
  have hright :
      (r.num * (q.den : Int)) * ((p.den : Int) * (q.den : Int)) =
        (r.num * (p.den : Int)) * ((q.den : Int) * (q.den : Int)) := by
    ac_rfl
  have h1 :
      (p.num * (r.den : Int)) * ((q.den : Int) * (q.den : Int)) <
        (q.num * (r.den : Int)) * ((p.den : Int) * (q.den : Int)) := by
    simpa [hleft, hmiddle_left] using hleft_mul
  have h2 :
      (q.num * (r.den : Int)) * ((p.den : Int) * (q.den : Int)) <
        (r.num * (p.den : Int)) * ((q.den : Int) * (q.den : Int)) := by
    simpa [hmiddle_right, hright] using hright_mul
  exact Int.lt_of_mul_lt_mul_right (Int.lt_trans h1 h2) (Int.le_of_lt hd)

theorem rawLt_irrefl (p : RatPair) : ¬ RawLt p p := by
  unfold RawLt
  exact Int.lt_irrefl _

theorem rawLt_asymm {p q : RatPair} (h : RawLt p q) : ¬ RawLt q p := by
  unfold RawLt at h ⊢
  exact Int.lt_asymm h

theorem den_rat_pos (p : RatPair) : 0 < ((p.den : Int) : Rat) := by
  simpa [Rat.intCast_natCast] using
    (Rat.natCast_pos.mpr p.den_pos : 0 < (p.den : Rat))

theorem rat_div_mul_eq_mul_div (a b c : Rat) :
    a / b * c = (a * c) / b := by
  rw [Rat.div_def, Rat.div_def]
  rw [Rat.mul_assoc, Rat.mul_comm b⁻¹ c, ← Rat.mul_assoc]

theorem toRat_lt_iff_rawLt (p q : RatPair) :
    p.toRat < q.toRat <-> RawLt p q := by
  unfold toRat RawLt
  rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
  rw [Rat.div_lt_iff (den_rat_pos p)]
  rw [rat_div_mul_eq_mul_div]
  rw [Rat.lt_div_iff (den_rat_pos q)]
  rw [← Rat.intCast_lt_intCast]
  simp [Rat.intCast_mul]

def midpoint (p q : RatPair) : RatPair where
  num := p.num * (q.den : Int) + q.num * (p.den : Int)
  den := 2 * p.den * q.den
  den_pos := by
    exact Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) p.den_pos) q.den_pos

theorem rawLt_left_midpoint {p q : RatPair} (h : RawLt p q) :
    RawLt p (midpoint p q) := by
  unfold RawLt at h ⊢
  simp only [midpoint]
  have hmul := Int.mul_lt_mul_of_pos_right h (den_cast_pos p)
  have hleft :
      p.num * ↑(2 * p.den * q.den) =
        (p.num * (q.den : Int)) * (p.den : Int) +
          (p.num * (q.den : Int)) * (p.den : Int) := by
    simp [Int.natCast_mul]
    rw [show (p.num * (2 * ↑p.den * ↑q.den) : Int) =
        p.num * (2 * ((p.den : Int) * (q.den : Int))) by ac_rfl]
    rw [Int.two_mul, Int.mul_add]
    ac_rfl
  have hright :
      (p.num * ↑q.den + q.num * ↑p.den) * ↑p.den =
        (p.num * (q.den : Int)) * (p.den : Int) +
          (q.num * (p.den : Int)) * (p.den : Int) := by
    rw [Int.add_mul]
  exact hleft ▸ hright ▸ Int.add_lt_add_left hmul
    ((p.num * (q.den : Int)) * (p.den : Int))

theorem rawLt_midpoint_right {p q : RatPair} (h : RawLt p q) :
    RawLt (midpoint p q) q := by
  unfold RawLt at h ⊢
  simp only [midpoint]
  have hmul := Int.mul_lt_mul_of_pos_right h (den_cast_pos q)
  have hleft :
      (p.num * ↑q.den + q.num * ↑p.den) * ↑q.den =
        (p.num * (q.den : Int)) * (q.den : Int) +
          (q.num * (p.den : Int)) * (q.den : Int) := by
    rw [Int.add_mul]
  have hright :
      q.num * ↑(2 * p.den * q.den) =
        (q.num * (p.den : Int)) * (q.den : Int) +
          (q.num * (p.den : Int)) * (q.den : Int) := by
    simp [Int.natCast_mul]
    rw [show (q.num * (2 * ↑p.den * ↑q.den) : Int) =
        q.num * (2 * ((p.den : Int) * (q.den : Int))) by ac_rfl]
    rw [Int.two_mul, Int.mul_add]
    ac_rfl
  exact hleft ▸ hright ▸ Int.add_lt_add_right hmul
    ((q.num * (p.den : Int)) * (q.den : Int))

def pred (p : RatPair) : RatPair where
  num := p.num - (p.den : Int)
  den := p.den
  den_pos := p.den_pos

def succ (p : RatPair) : RatPair where
  num := p.num + (p.den : Int)
  den := p.den
  den_pos := p.den_pos

theorem rawLt_pred_self (p : RatPair) : RawLt (pred p) p := by
  unfold RawLt pred
  exact Int.mul_lt_mul_of_pos_right
    (Int.sub_lt_self p.num (den_cast_pos p)) (den_cast_pos p)

theorem rawLt_self_succ (p : RatPair) : RawLt p (succ p) := by
  unfold RawLt succ
  exact Int.mul_lt_mul_of_pos_right
    (Int.lt_add_of_pos_right p.num (den_cast_pos p)) (den_cast_pos p)

end RatPair

/-!
# Quotient rationals

{lit}`QRat` is the quotient of raw rational pairs by cross-multiplied equality. The
API is built by transporting arithmetic and order through representatives.
-/

abbrev QRat : Type :=
  Quotient RatPair.instSetoid

namespace QRat

def mk (p : RatPair) : QRat :=
  Quotient.mk RatPair.instSetoid p

def toRat : QRat -> Rat :=
  Quotient.lift RatPair.toRat (by
    intro p q h
    exact RatPair.toRat_eq_of_rel h)

theorem toRat_mk (p : RatPair) :
    toRat (mk p) = p.toRat :=
  rfl

theorem ext {x y : QRat} (h : toRat x = toRat y) : x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  apply Quotient.sound
  exact RatPair.rel_of_toRat_eq h

theorem toRat_injective : Fn.Injective toRat := by
  intro x y h
  exact ext h

def ofInt (n : Int) : QRat :=
  mk (RatPair.ofInt n)

def ofNat (n : Nat) : QRat :=
  ofInt n

def ofPositiveRatRep (q : PositiveRatRep) : QRat :=
  mk (RatPair.ofPositiveRatRep q)

def ofRational (q : Rational) : QRat :=
  mk (RatPair.ofRational q)

def ofStdRat (q : Rat) : QRat :=
  mk (RatPair.ofStdRat q)

instance : Zero QRat where
  zero := ofInt 0

instance : One QRat where
  one := ofInt 1

instance : OfNat QRat n where
  ofNat := ofNat n

instance : IntCast QRat where
  intCast := ofInt

def add (x y : QRat) : QRat :=
  Quotient.liftOn₂ x y
    (fun p q => mk (RatPair.add p q))
    (by
      intro p p' q q' hp hq
      apply Quotient.sound
      exact RatPair.add_respects hp hq)

def neg (x : QRat) : QRat :=
  Quotient.liftOn x
    (fun p => mk (RatPair.neg p))
    (by
      intro p p' hp
      apply Quotient.sound
      exact RatPair.neg_respects hp)

def sub (x y : QRat) : QRat :=
  add x (neg y)

def mul (x y : QRat) : QRat :=
  Quotient.liftOn₂ x y
    (fun p q => mk (RatPair.mul p q))
    (by
      intro p p' q q' hp hq
      apply Quotient.sound
      exact RatPair.mul_respects hp hq)

def inv (x : QRat) : QRat :=
  ofStdRat (toRat x)⁻¹

def div (x y : QRat) : QRat :=
  mul x (inv y)

instance : Add QRat where
  add := add

instance : Neg QRat where
  neg := neg

instance : Sub QRat where
  sub := sub

instance : Mul QRat where
  mul := mul

instance : Inv QRat where
  inv := inv

instance : Div QRat where
  div := div

theorem toRat_ofInt (n : Int) :
    toRat (ofInt n) = (n : Rat) :=
  RatPair.toRat_ofInt n

theorem toRat_ofNat (n : Nat) :
    toRat (ofNat n) = (n : Rat) := by
  rw [ofNat, toRat_ofInt]
  rfl

theorem toRat_ofPositiveRatRep (q : PositiveRatRep) :
    toRat (ofPositiveRatRep q) = Rat.divInt q.num (q.den : Int) :=
  RatPair.toRat_ofPositiveRatRep q

theorem toRat_ofRational (q : Rational) :
    toRat (ofRational q) = Rat.divInt q.num q.den :=
  RatPair.toRat_ofRational q

theorem toRat_ofStdRat (q : Rat) :
    toRat (ofStdRat q) = q :=
  RatPair.toRat_ofStdRat q

@[simp] theorem toRat_zero :
    toRat (0 : QRat) = 0 := by
  exact toRat_ofInt 0

@[simp] theorem toRat_one :
    toRat (1 : QRat) = 1 := by
  exact toRat_ofInt 1

theorem toRat_add (x y : QRat) :
    toRat (x + y) = toRat x + toRat y := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  exact RatPair.toRat_add p q

theorem toRat_neg (x : QRat) :
    toRat (-x) = -toRat x := by
  refine Quotient.inductionOn x ?_
  intro p
  exact RatPair.toRat_neg p

theorem toRat_sub (x y : QRat) :
    toRat (x - y) = toRat x - toRat y := by
  calc
    toRat (x - y) = toRat (x + (-y)) := rfl
    _ = toRat x + toRat (-y) := toRat_add x (-y)
    _ = toRat x + -toRat y := by rw [toRat_neg]
    _ = toRat x - toRat y := by rw [Rat.sub_eq_add_neg]

theorem toRat_mul (x y : QRat) :
    toRat (x * y) = toRat x * toRat y := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  exact RatPair.toRat_mul p q

theorem toRat_inv (x : QRat) :
    toRat x⁻¹ = (toRat x)⁻¹ := by
  exact toRat_ofStdRat (toRat x)⁻¹

theorem toRat_div (x y : QRat) :
    toRat (x / y) = toRat x / toRat y := by
  change toRat (x * inv y) = toRat x / toRat y
  rw [show inv y = y⁻¹ by rfl, toRat_mul, toRat_inv, Rat.div_def]

theorem add_eq_of_toRat (x y : QRat) :
    toRat (x + y) = toRat x + toRat y :=
  toRat_add x y

theorem mul_eq_of_toRat (x y : QRat) :
    toRat (x * y) = toRat x * toRat y :=
  toRat_mul x y

/-!
# Order and density

Order is defined by choosing representatives and using raw order.  The density
theorems provide lower, upper, and intermediate rationals for the real-number
cut construction.
-/

def lt (x y : QRat) : Prop :=
  Quotient.liftOn₂ x y RatPair.RawLt
    (by
      intro p p' q q' hp hq
      exact propext (RatPair.rawLt_congr hp hq))

instance : LT QRat where
  lt := lt

theorem lt_mk_iff (p q : RatPair) :
    mk p < mk q <-> RatPair.RawLt p q :=
  Iff.rfl

theorem lt_mk_of_rawLt {p q : RatPair} (h : RatPair.RawLt p q) :
    mk p < mk q :=
  h

theorem rawLt_of_lt_mk {p q : RatPair} (h : mk p < mk q) :
    RatPair.RawLt p q :=
  h

theorem toRat_lt_of_lt {x y : QRat} (h : x < y) :
    toRat x < toRat y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  exact (RatPair.toRat_lt_iff_rawLt p q).mpr h

theorem lt_trans {x y z : QRat} (hxy : x < y) (hyz : y < z) : x < z := by
  revert hxy hyz
  refine Quotient.inductionOn₃ x y z ?_
  intro p q r hxy hyz
  exact RatPair.rawLt_trans hxy hyz

theorem lt_irrefl (x : QRat) : ¬ x < x := by
  refine Quotient.inductionOn x ?_
  intro p
  exact RatPair.rawLt_irrefl p

theorem lt_asymm {x y : QRat} (h : x < y) : ¬ y < x := by
  intro hyx
  exact lt_irrefl x (lt_trans h hyx)

theorem lt_trichotomy (x y : QRat) : x < y ∨ x = y ∨ y < x := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  cases Int.lt_trichotomy (p.num * (q.den : Int)) (q.num * (p.den : Int)) with
  | inl hlt =>
      exact Or.inl hlt
  | inr hrest =>
      cases hrest with
      | inl heq =>
          exact Or.inr (Or.inl (Quotient.sound heq))
      | inr hgt =>
          exact Or.inr (Or.inr hgt)

theorem lt_of_toRat_lt {x y : QRat} (h : toRat x < toRat y) :
    x < y := by
  cases lt_trichotomy x y with
  | inl hxy =>
      exact hxy
  | inr hrest =>
      cases hrest with
      | inl hxyEq =>
          rw [hxyEq] at h
          exact False.elim (Rat.lt_irrefl h)
      | inr hyx =>
          have hyxRat : toRat y < toRat x := toRat_lt_of_lt hyx
          exact False.elim ((Rat.not_le.mpr h) (Rat.le_of_lt hyxRat))

theorem ofNat_pos {n : Nat} (hn : 0 < n) : (0 : QRat) < ofNat n := by
  apply lt_of_toRat_lt
  rw [toRat_zero, toRat_ofNat]
  exact Rat.natCast_pos.mpr hn

theorem ofNat_lt_of_nat_lt {m n : Nat} (h : m < n) :
    ofNat m < ofNat n := by
  apply lt_of_toRat_lt
  rw [toRat_ofNat, toRat_ofNat]
  exact Rat.natCast_lt_natCast.mpr h

theorem ofNat_ne_zero {n : Nat} (hn : 0 < n) : ofNat n ≠ 0 := by
  intro h
  have hpos : (0 : QRat) < ofNat n := ofNat_pos hn
  rw [h] at hpos
  exact lt_irrefl 0 hpos

theorem lt_iff_toRat_lt (x y : QRat) :
    x < y <-> toRat x < toRat y := by
  constructor
  · exact toRat_lt_of_lt
  · exact lt_of_toRat_lt

theorem lt_iff_not_ge {x y : QRat} :
    x < y <-> ¬ y < x ∧ x ≠ y := by
  constructor
  · intro h
    constructor
    · exact lt_asymm h
    · intro hxy
      rw [hxy] at h
      exact lt_irrefl y h
  · intro h
    cases lt_trichotomy x y with
    | inl hlt => exact hlt
    | inr hrest =>
        cases hrest with
        | inl heq => exact False.elim (h.right heq)
        | inr hgt => exact False.elim (h.left hgt)

theorem density {x y : QRat} (h : x < y) :
    exists z : QRat, x < z ∧ z < y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  exists mk (RatPair.midpoint p q)
  exact And.intro
    (RatPair.rawLt_left_midpoint h)
    (RatPair.rawLt_midpoint_right h)

theorem exists_between {x y : QRat} (h : x < y) :
    exists z : QRat, x < z ∧ z < y :=
  density h

theorem exists_lower_upper (x : QRat) :
    exists l u : QRat, l < x ∧ x < u := by
  refine Quotient.inductionOn x ?_
  intro p
  exists mk (RatPair.pred p)
  exists mk (RatPair.succ p)
  exact And.intro (RatPair.rawLt_pred_self p) (RatPair.rawLt_self_succ p)

def le (x y : QRat) : Prop :=
  ¬ y < x

instance : LE QRat where
  le := le

theorem le_def (x y : QRat) :
    x ≤ y <-> ¬ y < x :=
  Iff.rfl

theorem le_refl (x : QRat) : x ≤ x := by
  exact lt_irrefl x

theorem le_of_lt {x y : QRat} (h : x < y) : x ≤ y := by
  exact lt_asymm h

theorem le_trans {x y z : QRat} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  intro hzx
  cases lt_trichotomy x y with
  | inl hxylt =>
      exact hyz (lt_trans hzx hxylt)
  | inr hrest =>
      cases hrest with
      | inl hxyEq =>
          rw [hxyEq] at hzx
          exact hyz hzx
      | inr hyx =>
          exact hxy hyx

theorem le_antisymm {x y : QRat} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  cases lt_trichotomy x y with
  | inl hlt => exact False.elim (hyx hlt)
  | inr hrest =>
      cases hrest with
      | inl heq => exact heq
      | inr hgt => exact False.elim (hxy hgt)

theorem eq_of_toRat_eq {x y : QRat} (h : toRat x = toRat y) : x = y :=
  toRat_injective h

/-!
# Algebraic laws

The quotient-rational operations inherit the expected additive and
multiplicative laws from their standard rational interpretation.
-/

theorem add_comm (x y : QRat) : x + y = y + x := by
  apply eq_of_toRat_eq
  rw [toRat_add, toRat_add, Rat.add_comm]

theorem add_assoc (x y z : QRat) : (x + y) + z = x + (y + z) := by
  apply eq_of_toRat_eq
  rw [toRat_add, toRat_add, toRat_add, toRat_add, Rat.add_assoc]

theorem zero_add (x : QRat) : 0 + x = x := by
  apply eq_of_toRat_eq
  rw [toRat_add, toRat_zero, Rat.zero_add]

theorem add_zero (x : QRat) : x + 0 = x := by
  apply eq_of_toRat_eq
  rw [toRat_add, toRat_zero, Rat.add_zero]

theorem neg_neg (x : QRat) : -(-x) = x := by
  apply eq_of_toRat_eq
  rw [toRat_neg, toRat_neg, Rat.neg_neg]

theorem neg_zero : -(0 : QRat) = 0 := by
  apply eq_of_toRat_eq
  rw [toRat_neg, toRat_zero, Rat.neg_zero]

theorem add_neg_cancel (x : QRat) : x + -x = 0 := by
  apply eq_of_toRat_eq
  rw [toRat_add, toRat_neg, toRat_zero, Rat.add_neg_cancel]

theorem neg_add_cancel (x : QRat) : -x + x = 0 := by
  rw [add_comm, add_neg_cancel]

theorem sub_eq_add_neg (x y : QRat) : x - y = x + -y := rfl

theorem add_lt_add_left {x y : QRat} (z : QRat) (h : x < y) :
    z + x < z + y := by
  apply lt_of_toRat_lt
  rw [toRat_add, toRat_add]
  exact (Rat.add_lt_add_left (c := toRat z)).mpr (toRat_lt_of_lt h)

theorem add_lt_add_right {x y : QRat} (z : QRat) (h : x < y) :
    x + z < y + z := by
  apply lt_of_toRat_lt
  rw [toRat_add, toRat_add]
  exact (Rat.add_lt_add_right (c := toRat z)).mpr (toRat_lt_of_lt h)

theorem add_lt_add {a b c d : QRat} (hab : a < b) (hcd : c < d) :
    a + c < b + d := by
  exact lt_trans (add_lt_add_right c hab) (add_lt_add_left b hcd)

theorem lt_of_add_lt_add_right {x y z : QRat} (h : x + z < y + z) : x < y := by
  apply lt_of_toRat_lt
  have ht := toRat_lt_of_lt h
  rw [toRat_add, toRat_add] at ht
  exact (Rat.add_lt_add_right (c := toRat z)).mp ht

theorem lt_of_add_lt_add_left {x y z : QRat} (h : z + x < z + y) : x < y := by
  apply lt_of_toRat_lt
  have ht := toRat_lt_of_lt h
  rw [toRat_add, toRat_add] at ht
  exact (Rat.add_lt_add_left (c := toRat z)).mp ht

theorem neg_lt_neg {x y : QRat} (h : x < y) : -y < -x := by
  apply lt_of_toRat_lt
  rw [toRat_neg, toRat_neg]
  exact Rat.neg_lt_neg (toRat_lt_of_lt h)

theorem neg_pos_of_neg {x : QRat} (h : x < 0) : 0 < -x := by
  have hneg := neg_lt_neg h
  rwa [neg_zero] at hneg

theorem sub_lt_iff {a b c : QRat} : a - c < b <-> a < b + c := by
  constructor
  · intro h
    apply lt_of_toRat_lt
    rw [toRat_add]
    have ht := toRat_lt_of_lt h
    rw [toRat_sub] at ht
    exact Rat.sub_lt_iff.mp ht
  · intro h
    apply lt_of_toRat_lt
    rw [toRat_sub]
    have ht := toRat_lt_of_lt h
    rw [toRat_add] at ht
    exact Rat.sub_lt_iff.mpr ht

theorem lt_sub_right_iff_add_lt {a b c : QRat} :
    a < c - b <-> a + b < c := by
  constructor
  · intro h
    apply lt_of_toRat_lt
    rw [toRat_add]
    have ht := toRat_lt_of_lt h
    rw [toRat_sub] at ht
    exact Rat.lt_sub_right_iff_add_lt.mp ht
  · intro h
    apply lt_of_toRat_lt
    rw [toRat_sub]
    have ht := toRat_lt_of_lt h
    rw [toRat_add] at ht
    exact Rat.lt_sub_right_iff_add_lt.mpr ht

theorem lt_add_iff_sub_lt {a b c : QRat} :
    a < b + c <-> a - c < b :=
  Iff.symm sub_lt_iff

theorem exists_add_split_lt {q a b : QRat} (h : q < a + b) :
    exists u v : QRat, u < a ∧ v < b ∧ q < u + v := by
  have hqa : q - b < a := sub_lt_iff.mpr h
  rcases density hqa with ⟨u, hqu, hua⟩
  have hqub : q < u + b := sub_lt_iff.mp hqu
  have hqsub : q - u < b := by
    apply sub_lt_iff.mpr
    simpa [add_comm] using hqub
  rcases density hqsub with ⟨v, hqv, hvb⟩
  refine ⟨u, v, hua, hvb, ?_⟩
  have hqvu : q < v + u := sub_lt_iff.mp hqv
  simpa [add_comm] using hqvu

theorem sub_pos_of_lt {q c : QRat} (h : q < c) : 0 < c - q := by
  apply (lt_sub_right_iff_add_lt (a := 0) (b := q) (c := c)).mpr
  rwa [zero_add]

theorem add_sub_cancel (x y : QRat) : x + y - y = x := by
  apply eq_of_toRat_eq
  rw [toRat_sub, toRat_add, Rat.add_sub_cancel]

theorem sub_add_cancel (x y : QRat) : x - y + y = x := by
  apply eq_of_toRat_eq
  rw [toRat_add, toRat_sub, Rat.sub_add_cancel]

theorem mul_comm (x y : QRat) : x * y = y * x := by
  apply eq_of_toRat_eq
  rw [toRat_mul, toRat_mul, Rat.mul_comm]

theorem mul_assoc (x y z : QRat) : (x * y) * z = x * (y * z) := by
  apply eq_of_toRat_eq
  rw [toRat_mul, toRat_mul, toRat_mul, toRat_mul, Rat.mul_assoc]

theorem ofNat_mul (m n : Nat) :
    ofNat (m * n) = ofNat m * ofNat n := by
  apply eq_of_toRat_eq
  rw [toRat_ofNat, toRat_mul, toRat_ofNat, toRat_ofNat, Rat.natCast_mul]

theorem ofNat_add (m n : Nat) :
    ofNat (m + n) = ofNat m + ofNat n := by
  apply eq_of_toRat_eq
  rw [toRat_ofNat, toRat_add, toRat_ofNat, toRat_ofNat, Rat.natCast_add]

theorem add_mul (x y z : QRat) : (x + y) * z = x * z + y * z := by
  apply eq_of_toRat_eq
  rw [toRat_mul, toRat_add, toRat_add, toRat_mul, toRat_mul, Rat.add_mul]

theorem mul_add (x y z : QRat) : x * (y + z) = x * y + x * z := by
  apply eq_of_toRat_eq
  rw [toRat_mul, toRat_add, toRat_add, toRat_mul, toRat_mul, Rat.mul_add]

theorem zero_lt_one : (0 : QRat) < 1 := by
  change RatPair.RawLt (RatPair.ofInt 0) (RatPair.ofInt 1)
  simp [RatPair.RawLt, RatPair.ofInt]

theorem one_ne_zero : (1 : QRat) ≠ 0 := by
  intro h
  have hlt : (0 : QRat) < 1 := zero_lt_one
  rw [h] at hlt
  exact lt_irrefl 0 hlt

theorem zero_mul (x : QRat) : 0 * x = 0 := by
  apply eq_of_toRat_eq
  simp [toRat_mul]

theorem mul_zero (x : QRat) : x * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem one_mul (x : QRat) : 1 * x = x := by
  apply eq_of_toRat_eq
  simp [toRat_mul]

theorem mul_one (x : QRat) : x * 1 = x := by
  rw [mul_comm, one_mul]

theorem neg_mul (x y : QRat) : (-x) * y = -(x * y) := by
  apply eq_of_toRat_eq
  rw [toRat_mul, toRat_neg, toRat_neg, toRat_mul, Rat.neg_mul]

theorem mul_neg (x y : QRat) : x * (-y) = -(x * y) := by
  apply eq_of_toRat_eq
  rw [toRat_mul, toRat_neg, toRat_neg, toRat_mul, Rat.mul_neg]

theorem neg_mul_neg (x y : QRat) : (-x) * (-y) = x * y := by
  apply eq_of_toRat_eq
  rw [toRat_mul, toRat_neg, toRat_neg, toRat_mul,
    Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem toRat_ne_zero_of_ne_zero {x : QRat} (hx : x ≠ 0) :
    toRat x ≠ 0 := by
  intro h
  apply hx
  apply eq_of_toRat_eq
  rw [h, toRat_zero]

theorem mul_pos {x y : QRat} (hx : 0 < x) (hy : 0 < y) :
    0 < x * y := by
  apply lt_of_toRat_lt
  rw [toRat_zero, toRat_mul]
  exact Rat.mul_pos (toRat_lt_of_lt hx) (toRat_lt_of_lt hy)

theorem eq_zero_of_not_lt_zero_of_not_zero_lt {x : QRat}
    (hneg : ¬ x < 0) (hpos : ¬ 0 < x) : x = 0 := by
  cases lt_trichotomy x 0 with
  | inl hx0 =>
      exact False.elim (hneg hx0)
  | inr hrest =>
      cases hrest with
      | inl hx0 =>
          exact hx0
      | inr h0x =>
          exact False.elim (hpos h0x)

theorem pos_of_not_lt_zero_of_ne_zero {x : QRat}
    (hneg : ¬ x < 0) (hne : x ≠ 0) : 0 < x := by
  cases lt_trichotomy 0 x with
  | inl hpos =>
      exact hpos
  | inr hrest =>
      cases hrest with
      | inl hzero =>
          exact False.elim (hne hzero.symm)
      | inr hx0 =>
          exact False.elim (hneg hx0)

theorem zero_lt_of_not_lt_zero_of_lt {x y : QRat}
    (hx : ¬ x < 0) (hxy : x < y) : 0 < y := by
  cases lt_trichotomy 0 y with
  | inl hpos =>
      exact hpos
  | inr hrest =>
      cases hrest with
      | inl hy0 =>
          rw [← hy0] at hxy
          exact False.elim (hx hxy)
      | inr hy0 =>
          exact False.elim (hx (lt_trans hxy hy0))

theorem lt_of_lt_zero_of_not_lt_zero {x y : QRat}
    (hx : x < 0) (hy : ¬ y < 0) : x < y := by
  cases lt_trichotomy x y with
  | inl hxy =>
      exact hxy
  | inr hrest =>
      cases hrest with
      | inl hxyEq =>
          rw [← hxyEq] at hy
          exact False.elim (hy hx)
      | inr hyx =>
          exact False.elim (hy (lt_trans hyx hx))

theorem mul_nonneg {x y : QRat}
    (hx : ¬ x < 0) (hy : ¬ y < 0) : ¬ x * y < 0 := by
  intro hxy
  cases lt_trichotomy 0 x with
  | inl hxpos =>
      cases lt_trichotomy 0 y with
      | inl hypos =>
          exact lt_asymm (mul_pos hxpos hypos) hxy
      | inr hyrest =>
          cases hyrest with
          | inl hyzero =>
              rw [← hyzero, mul_zero] at hxy
              exact lt_irrefl 0 hxy
          | inr hyneg =>
              exact hy hyneg
  | inr hxrest =>
      cases hxrest with
      | inl hxzero =>
          rw [← hxzero, zero_mul] at hxy
          exact lt_irrefl 0 hxy
      | inr hxneg =>
          exact hx hxneg

theorem pos_of_nonneg_mul_pos_left {x y : QRat}
    (hx : ¬ x < 0) (_hy : ¬ y < 0) (hxy : 0 < x * y) : 0 < x := by
  cases lt_trichotomy 0 x with
  | inl hxpos =>
      exact hxpos
  | inr hxrest =>
      cases hxrest with
      | inl hxzero =>
          rw [← hxzero, zero_mul] at hxy
          exact False.elim (lt_irrefl 0 hxy)
      | inr hxneg =>
          exact False.elim (hx hxneg)

theorem mul_lt_mul_of_pos_left {x y c : QRat}
    (hxy : x < y) (hc : 0 < c) : c * x < c * y := by
  apply lt_of_toRat_lt
  rw [toRat_mul, toRat_mul]
  exact Rat.mul_lt_mul_of_pos_left (toRat_lt_of_lt hxy) (toRat_lt_of_lt hc)

theorem mul_lt_mul_of_pos_right {x y c : QRat}
    (hxy : x < y) (hc : 0 < c) : x * c < y * c := by
  apply lt_of_toRat_lt
  rw [toRat_mul, toRat_mul]
  exact Rat.mul_lt_mul_of_pos_right (toRat_lt_of_lt hxy) (toRat_lt_of_lt hc)

theorem lt_zero_of_lt_mul_of_not_pos_left {q a b : QRat}
    (hqa : q < a * b) (ha : ¬ 0 < a) (hb : 0 < b) : q < 0 := by
  cases lt_trichotomy a 0 with
  | inl ha0 =>
      exact lt_trans hqa (by
        have hmul := mul_lt_mul_of_pos_right ha0 hb
        rwa [zero_mul] at hmul)
  | inr hrest =>
      cases hrest with
      | inl hazero =>
          rwa [hazero, zero_mul] at hqa
      | inr hapos =>
          exact False.elim (ha hapos)

theorem mul_lt_mul_of_pos {a b c d : QRat}
    (hab : a < b) (hcd : c < d) (ha : 0 < a) (hc : 0 < c) :
    a * c < b * d := by
  have hb : 0 < b := lt_trans ha hab
  exact lt_trans
    (mul_lt_mul_of_pos_right hab hc)
    (mul_lt_mul_of_pos_left hcd hb)

theorem pos_of_nonneg_mul_pos_right {x y : QRat}
    (hx : ¬ x < 0) (hy : ¬ y < 0) (hxy : 0 < x * y) : 0 < y := by
  rw [mul_comm] at hxy
  exact pos_of_nonneg_mul_pos_left hy hx hxy

theorem square_nonneg (x : QRat) : ¬ x * x < 0 := by
  intro hsq
  cases lt_trichotomy 0 x with
  | inl hxpos =>
      exact lt_asymm (mul_pos hxpos hxpos) hsq
  | inr hrest =>
      cases hrest with
      | inl hxzero =>
          rw [← hxzero, zero_mul] at hsq
          exact lt_irrefl 0 hsq
      | inr hxneg =>
          have hnegpos : 0 < -x := neg_pos_of_neg hxneg
          have hpos : 0 < (-x) * (-x) := mul_pos hnegpos hnegpos
          rw [neg_mul_neg] at hpos
          exact lt_asymm hpos hsq

theorem square_pos_of_ne_zero (x : QRat) (hx : x ≠ 0) : 0 < x * x := by
  cases lt_trichotomy 0 x with
  | inl hxpos =>
      exact mul_pos hxpos hxpos
  | inr hrest =>
      cases hrest with
      | inl hxzero =>
          exact False.elim (hx hxzero.symm)
      | inr hxneg =>
          have hnegpos : 0 < -x := neg_pos_of_neg hxneg
          have hpos : 0 < (-x) * (-x) := mul_pos hnegpos hnegpos
          rwa [neg_mul_neg] at hpos

theorem lt_of_mul_lt_mul_left {x y c : QRat}
    (hxy : c * x < c * y) (hc : 0 < c) : x < y := by
  apply lt_of_toRat_lt
  have ht := toRat_lt_of_lt hxy
  rw [toRat_mul, toRat_mul] at ht
  exact Rat.lt_of_mul_lt_mul_left ht
    (Rat.le_of_lt (toRat_lt_of_lt hc))

theorem lt_of_mul_lt_mul_right {x y c : QRat}
    (hxy : x * c < y * c) (hc : 0 < c) : x < y := by
  apply lt_of_toRat_lt
  have ht := toRat_lt_of_lt hxy
  rw [toRat_mul, toRat_mul] at ht
  exact Rat.lt_of_mul_lt_mul_right ht
    (Rat.le_of_lt (toRat_lt_of_lt hc))

theorem div_lt_iff {x y c : QRat} (hy : 0 < y) :
    x / y < c <-> x < c * y := by
  constructor
  · intro h
    apply lt_of_toRat_lt
    rw [toRat_mul]
    have ht := toRat_lt_of_lt h
    rw [toRat_div] at ht
    exact Rat.div_lt_iff (toRat_lt_of_lt hy) |>.mp ht
  · intro h
    apply lt_of_toRat_lt
    rw [toRat_div]
    have ht := toRat_lt_of_lt h
    rw [toRat_mul] at ht
    exact Rat.div_lt_iff (toRat_lt_of_lt hy) |>.mpr ht

theorem exists_neg_factor_mul_gt {q c : QRat}
    (hq : q < 0) (hc : 0 < c) :
    exists a : QRat, a < 0 ∧ q < a * c := by
  have hdiv : q / c < 0 := by
    apply (div_lt_iff (x := q) (y := c) (c := 0) hc).mpr
    rwa [zero_mul]
  rcases density hdiv with ⟨a, hqa, ha0⟩
  exact ⟨a, ha0, (div_lt_iff (x := q) (y := c) (c := a) hc).mp hqa⟩

theorem div_nonneg {x y : QRat}
    (hx : ¬ x < 0) (hy : 0 < y) : ¬ x / y < 0 := by
  intro h
  have hx0 : x < 0 * y :=
    (div_lt_iff (x := x) (y := y) (c := 0) hy).mp h
  rw [zero_mul] at hx0
  exact hx hx0

theorem div_pos {x y : QRat} (hx : 0 < x) (hy : 0 < y) :
    0 < x / y := by
  apply lt_of_toRat_lt
  rw [toRat_zero, toRat_div, Rat.div_def]
  exact Rat.mul_pos (toRat_lt_of_lt hx)
    (Rat.inv_pos.mpr (toRat_lt_of_lt hy))

theorem lt_div_iff {x y c : QRat} (hc : 0 < c) :
    x < y / c <-> x * c < y := by
  constructor
  · intro h
    apply lt_of_toRat_lt
    rw [toRat_mul]
    have ht := toRat_lt_of_lt h
    rw [toRat_div] at ht
    exact Rat.lt_div_iff (toRat_lt_of_lt hc) |>.mp ht
  · intro h
    apply lt_of_toRat_lt
    rw [toRat_div]
    have ht := toRat_lt_of_lt h
    rw [toRat_mul] at ht
    exact Rat.lt_div_iff (toRat_lt_of_lt hc) |>.mpr ht

theorem div_mul_cancel (x : QRat) {y : QRat} (hy : y ≠ 0) :
    x / y * y = x := by
  apply eq_of_toRat_eq
  rw [toRat_mul, toRat_div]
  exact Rat.div_mul_cancel (toRat_ne_zero_of_ne_zero hy)

theorem mul_div_cancel (x : QRat) {y : QRat} (hy : y ≠ 0) :
    x * y / y = x := by
  apply eq_of_toRat_eq
  rw [toRat_div, toRat_mul]
  exact Rat.mul_div_cancel (toRat_ne_zero_of_ne_zero hy)

theorem inv_mul_cancel {x : QRat} (hx : x ≠ 0) : x⁻¹ * x = 1 := by
  calc
    x⁻¹ * x = (1 * x⁻¹) * x := by rw [one_mul]
    _ = 1 / x * x := rfl
    _ = 1 := div_mul_cancel 1 hx

theorem mul_inv_cancel {x : QRat} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  rw [mul_comm]
  exact inv_mul_cancel hx

theorem div_self {x : QRat} (hx : x ≠ 0) : x / x = 1 := by
  exact mul_inv_cancel hx

theorem inv_ne_zero {x : QRat} (hx : x ≠ 0) : x⁻¹ ≠ 0 := by
  intro hinv
  have hmul := congrArg (fun t : QRat => t * x) hinv
  change x⁻¹ * x = 0 * x at hmul
  rw [inv_mul_cancel hx, zero_mul] at hmul
  exact one_ne_zero hmul

theorem exists_nat_mul_pos_gt (z : QRat) {c : QRat} (hc : 0 < c) :
    exists n : Nat, z < ofNat n * c := by
  let r : Rat := toRat z / toRat c
  let k : Int := r.floor + 1
  let n : Nat := Int.toNat k + 1
  have hkltInt : k < Int.ofNat n := by
    dsimp [n]
    have hle : k ≤ Int.ofNat (Int.toNat k) := Int.self_le_toNat k
    have hlt : Int.ofNat (Int.toNat k) < Int.ofNat (Int.toNat k + 1) :=
      Int.ofNat_lt.mpr (Nat.lt_succ_self _)
    exact Int.lt_of_le_of_lt hle hlt
  have hrk : r < (k : Rat) := by
    dsimp [k]
    exact Rat.lt_floor_add_one r
  have hkn : (k : Rat) < (n : Rat) := by
    have h :=
      (Rat.intCast_lt_intCast (a := k) (b := Int.ofNat n)).mpr hkltInt
    simpa using h
  have hrn : r < (n : Rat) := by
    grind
  have hzc : toRat z < (n : Rat) * toRat c := by
    have hcRat : 0 < toRat c := toRat_lt_of_lt hc
    exact (Rat.div_lt_iff hcRat).mp hrn
  exact Exists.intro n (lt_of_toRat_lt (by
    rw [toRat_mul, toRat_ofNat]
    exact hzc))

theorem half_pos {x : QRat} (hx : 0 < x) :
    0 < x / ofNat 2 :=
  div_pos hx (ofNat_pos (by decide : 0 < 2))

theorem half_lt_self {x : QRat} (hx : 0 < x) :
    x / ofNat 2 < x := by
  apply lt_of_toRat_lt
  rw [toRat_div, toRat_ofNat]
  have hxRat : 0 < toRat x := toRat_lt_of_lt hx
  grind

theorem half_add_half (x : QRat) : x / ofNat 2 + x / ofNat 2 = x := by
  apply eq_of_toRat_eq
  simp [toRat_add, toRat_div, toRat_ofNat]
  grind

theorem half_neg_of_neg {x : QRat} (hx : x < 0) : x / ofNat 2 < 0 := by
  apply lt_of_toRat_lt
  simp [toRat_div, toRat_zero, toRat_ofNat]
  have hxRat : toRat x < 0 := by
    simpa [toRat_zero] using toRat_lt_of_lt hx
  grind

theorem exists_neg_split_gt {q : QRat} (hq : q < 0) :
    exists a b : QRat, a < 0 ∧ b < 0 ∧ q < a + b := by
  rcases density hq with ⟨r, hqr, hr0⟩
  exists r / ofNat 2
  exists r / ofNat 2
  constructor
  · exact half_neg_of_neg hr0
  · constructor
    · exact half_neg_of_neg hr0
    · rwa [half_add_half]

/-!
# Natural rational fractions

Concrete rational fractions with natural numerators and positive natural
denominators are useful both for digit-stream real encodings and for explicit
square-root approximations.  The comparison lemmas keep those constructions in
natural-number arithmetic whenever possible.
-/

def natFrac (num den : Nat) (hden : 0 < den) : QRat :=
  QRat.mk { num := (num : Int), den := den, den_pos := hden }

theorem natFrac_lt_natFrac {a b d : Nat} (hd : 0 < d) (h : a < b) :
    natFrac a d hd < natFrac b d hd := by
  apply QRat.lt_mk_of_rawLt
  unfold RatPair.RawLt
  change (a : Int) * (d : Int) < (b : Int) * (d : Int)
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_lt.mpr ((Nat.mul_lt_mul_right hd).mpr h)

theorem natFrac_lt_of_cross {a b da db : Nat} (hda : 0 < da) (hdb : 0 < db)
    (h : a * db < b * da) :
    natFrac a da hda < natFrac b db hdb := by
  apply QRat.lt_mk_of_rawLt
  unfold RatPair.RawLt
  change (a : Int) * (db : Int) < (b : Int) * (da : Int)
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_lt.mpr h

theorem natFrac_lt_one_over_of_cross {a d e : Nat} (hd : 0 < d) (he : 0 < e)
    (h : a * d < e) :
    natFrac a e he < natFrac 1 d hd := by
  exact natFrac_lt_of_cross he hd (by simpa [Nat.mul_one] using h)

theorem exists_natFrac_one_lt {d : QRat} (hd : (0 : QRat) < d) :
    exists n : Nat, natFrac 1 (n + 1) (Nat.succ_pos n) < d := by
  revert hd
  refine Quotient.inductionOn d ?_
  intro p hd
  exists p.den
  unfold natFrac
  apply QRat.lt_mk_of_rawLt
  unfold RatPair.RawLt
  simp
  have hpnum_pos : 0 < p.num := by
    change RatPair.RawLt (RatPair.ofInt 0) p at hd
    unfold RatPair.RawLt RatPair.ofInt at hd
    simpa using hd
  have hden_lt : (p.den : Int) < (p.den : Int) + 1 := by omega
  have hle : (p.den : Int) + 1 ≤ p.num * ((p.den : Int) + 1) := by
    calc
      (p.den : Int) + 1 = 1 * ((p.den : Int) + 1) := by omega
      _ ≤ p.num * ((p.den : Int) + 1) := by
          apply Int.mul_le_mul_of_nonneg_right
          · omega
          · omega
  exact Int.lt_of_lt_of_le hden_lt hle

theorem one_gt_natFrac {a d : Nat} (hd : 0 < d) (h : a < d) :
    natFrac a d hd < (1 : QRat) := by
  change natFrac a d hd < QRat.ofNat 1
  unfold QRat.ofNat QRat.ofInt
  apply QRat.lt_mk_of_rawLt
  unfold RatPair.RawLt
  change (a : Int) * (1 : Int) < (1 : Int) * (d : Int)
  simp
  exact h

theorem natFrac_pos {a d : Nat} (ha : 0 < a) (hd : 0 < d) :
    (0 : QRat) < natFrac a d hd := by
  change QRat.ofInt 0 < natFrac a d hd
  unfold natFrac QRat.ofInt
  apply QRat.lt_mk_of_rawLt
  unfold RatPair.RawLt RatPair.ofInt
  simp
  exact ha

theorem natFrac_mul_self_lt_of_square_lt {p q c : Nat} (hq : 0 < q)
    (h : p * p < c * q * q) :
    natFrac p q hq * natFrac p q hq < QRat.ofNat c := by
  unfold natFrac QRat.ofNat QRat.ofInt
  apply QRat.lt_mk_of_rawLt
  unfold RatPair.RawLt RatPair.mul RatPair.ofInt
  simp [Int.natCast_mul]
  exact Int.ofNat_lt.mpr (by simpa [Nat.mul_assoc] using h)

theorem natFrac_square_add_gap_eq_of_num_square_add_gap {p q c gap : Nat}
    (hq : 0 < q) (h : p * p + gap = c * q * q) :
    natFrac p q hq * natFrac p q hq +
      natFrac gap (q * q) (Nat.mul_pos hq hq) = QRat.ofNat c := by
  unfold natFrac QRat.ofNat QRat.ofInt
  apply Quotient.sound
  change RatPair.Rel
    (RatPair.add (RatPair.mul { num := (p : Int), den := q, den_pos := hq }
      { num := (p : Int), den := q, den_pos := hq })
      { num := (gap : Int), den := q * q, den_pos := Nat.mul_pos hq hq })
    (RatPair.ofInt (c : Int))
  unfold RatPair.Rel RatPair.add RatPair.mul RatPair.ofInt
  simp [Int.natCast_mul]
  have hi : (p * p + gap : Int) = (c * q * q : Int) := by
    exact congrArg (fun t : Nat => (t : Int)) h
  calc
    (p : Int) * (p : Int) * ((q : Int) * (q : Int)) +
        (gap : Int) * ((q : Int) * (q : Int))
        = ((p : Int) * (p : Int) + (gap : Int)) * ((q : Int) * (q : Int)) := by
          rw [Int.add_mul]
    _ = ((c : Int) * (q : Int) * (q : Int)) * ((q : Int) * (q : Int)) := by
          rw [hi]
    _ = (c : Int) * (((q : Int) * (q : Int)) * ((q : Int) * (q : Int))) := by
          ac_rfl

theorem lt_of_square_add_gap_eq_of_gap_lt_sub {q sq gap c : QRat}
    (hgap : gap < c - q) (heq : sq + gap = c) : q < sq := by
  have hgq : gap + q < c :=
    (lt_sub_right_iff_add_lt (a := gap) (b := q) (c := c)).mp hgap
  have hqg : q + gap < sq + gap := by
    rw [heq]
    simpa [add_comm] using hgq
  exact lt_of_add_lt_add_right hqg

/-!
# Square-root approximation sequences

The concrete Dedekind-cut square roots need quotient-rational approximants from
below.  The following Pell-style recurrences give explicit unbounded-denominator
families whose squares are just below {lit}`2` and {lit}`3`; the exact gap
equalities record the quantitative error term available for the later cut
proofs.
-/

mutual
  def sqrtTwoApproxNum : Nat -> Nat
    | 0 => 1
    | n + 1 => 3 * sqrtTwoApproxNum n + 4 * sqrtTwoApproxDen n

  def sqrtTwoApproxDen : Nat -> Nat
    | 0 => 1
    | n + 1 => 2 * sqrtTwoApproxNum n + 3 * sqrtTwoApproxDen n
end

theorem sqrtTwoApprox_pell (n : Nat) :
    sqrtTwoApproxNum n * sqrtTwoApproxNum n + 1 =
      2 * sqrtTwoApproxDen n * sqrtTwoApproxDen n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [sqrtTwoApproxNum, sqrtTwoApproxDen]
      grind

theorem sqrtTwoApproxNum_pos (n : Nat) : 0 < sqrtTwoApproxNum n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [sqrtTwoApproxNum]
      omega

theorem sqrtTwoApproxDen_pos (n : Nat) : 0 < sqrtTwoApproxDen n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [sqrtTwoApproxDen]
      omega

theorem sqrtTwoApproxDen_linear_growth (n : Nat) :
    n + 1 ≤ sqrtTwoApproxDen n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [sqrtTwoApproxDen]
      omega

theorem sqrtTwoApproxDen_gt_self (n : Nat) : n < sqrtTwoApproxDen n := by
  have h := sqrtTwoApproxDen_linear_growth n
  omega

theorem exists_sqrtTwoApproxDen_gt (bound : Nat) :
    exists n : Nat, bound < sqrtTwoApproxDen n := by
  exists bound
  exact sqrtTwoApproxDen_gt_self bound

def sqrtTwoApprox (n : Nat) : QRat :=
  natFrac (sqrtTwoApproxNum n) (sqrtTwoApproxDen n) (sqrtTwoApproxDen_pos n)

def sqrtTwoApproxGap (n : Nat) : QRat :=
  natFrac 1 (sqrtTwoApproxDen n * sqrtTwoApproxDen n)
    (Nat.mul_pos (sqrtTwoApproxDen_pos n) (sqrtTwoApproxDen_pos n))

theorem sqrtTwoApprox_pos (n : Nat) : (0 : QRat) < sqrtTwoApprox n := by
  unfold sqrtTwoApprox
  exact natFrac_pos (sqrtTwoApproxNum_pos n) (sqrtTwoApproxDen_pos n)

theorem sqrtTwoApprox_num_square_lt_two_den_square (n : Nat) :
    sqrtTwoApproxNum n * sqrtTwoApproxNum n <
      2 * sqrtTwoApproxDen n * sqrtTwoApproxDen n := by
  have h := sqrtTwoApprox_pell n
  omega

theorem sqrtTwoApprox_square_lt_two (n : Nat) :
    sqrtTwoApprox n * sqrtTwoApprox n < (2 : QRat) := by
  change sqrtTwoApprox n * sqrtTwoApprox n < QRat.ofNat 2
  unfold sqrtTwoApprox
  exact natFrac_mul_self_lt_of_square_lt (sqrtTwoApproxDen_pos n)
    (sqrtTwoApprox_num_square_lt_two_den_square n)

theorem sqrtTwoApprox_square_gap_eq_two (n : Nat) :
    sqrtTwoApprox n * sqrtTwoApprox n + sqrtTwoApproxGap n = (2 : QRat) := by
  change sqrtTwoApprox n * sqrtTwoApprox n + sqrtTwoApproxGap n = QRat.ofNat 2
  unfold sqrtTwoApprox sqrtTwoApproxGap
  exact natFrac_square_add_gap_eq_of_num_square_add_gap (sqrtTwoApproxDen_pos n)
    (sqrtTwoApprox_pell n)

theorem exists_sqrtTwoApproxGap_lt_natFrac_one (bound : Nat) :
    exists n : Nat, sqrtTwoApproxGap n < natFrac 1 (bound + 1) (Nat.succ_pos bound) := by
  let n := bound + 1
  exists n
  unfold sqrtTwoApproxGap
  apply natFrac_lt_one_over_of_cross
  simp
  have hden : bound + 1 < sqrtTwoApproxDen n := by
    simpa [n] using sqrtTwoApproxDen_gt_self n
  have hle : sqrtTwoApproxDen n ≤ sqrtTwoApproxDen n * sqrtTwoApproxDen n := by
    exact Nat.le_mul_of_pos_right (sqrtTwoApproxDen n) (sqrtTwoApproxDen_pos n)
  exact Nat.lt_of_lt_of_le hden hle

theorem sqrtTwoApprox_square_cofinal {q : QRat} (hq : q < QRat.ofNat 2) :
    exists t : QRat, 0 < t ∧ q < t * t ∧ t * t < QRat.ofNat 2 := by
  have hgap_pos : 0 < QRat.ofNat 2 - q := QRat.sub_pos_of_lt hq
  cases QRat.exists_natFrac_one_lt hgap_pos with
  | intro n hn =>
      cases QRat.exists_sqrtTwoApproxGap_lt_natFrac_one n with
      | intro m hm =>
          exists QRat.sqrtTwoApprox m
          constructor
          · exact QRat.sqrtTwoApprox_pos m
          · constructor
            · apply QRat.lt_of_square_add_gap_eq_of_gap_lt_sub
              · exact QRat.lt_trans hm hn
              · exact QRat.sqrtTwoApprox_square_gap_eq_two m
            · exact QRat.sqrtTwoApprox_square_lt_two m

mutual
  def sqrtThreeApproxNum : Nat -> Nat
    | 0 => 1
    | n + 1 => 2 * sqrtThreeApproxNum n + 3 * sqrtThreeApproxDen n

  def sqrtThreeApproxDen : Nat -> Nat
    | 0 => 1
    | n + 1 => sqrtThreeApproxNum n + 2 * sqrtThreeApproxDen n
end

theorem sqrtThreeApprox_pell (n : Nat) :
    sqrtThreeApproxNum n * sqrtThreeApproxNum n + 2 =
      3 * sqrtThreeApproxDen n * sqrtThreeApproxDen n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [sqrtThreeApproxNum, sqrtThreeApproxDen]
      grind

theorem sqrtThreeApproxNum_pos (n : Nat) : 0 < sqrtThreeApproxNum n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [sqrtThreeApproxNum]
      omega

theorem sqrtThreeApproxDen_pos (n : Nat) : 0 < sqrtThreeApproxDen n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [sqrtThreeApproxDen]
      omega

theorem sqrtThreeApproxDen_linear_growth (n : Nat) :
    n + 1 ≤ sqrtThreeApproxDen n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [sqrtThreeApproxDen]
      omega

theorem sqrtThreeApproxDen_gt_self (n : Nat) : n < sqrtThreeApproxDen n := by
  have h := sqrtThreeApproxDen_linear_growth n
  omega

theorem exists_sqrtThreeApproxDen_gt (bound : Nat) :
    exists n : Nat, bound < sqrtThreeApproxDen n := by
  exists bound
  exact sqrtThreeApproxDen_gt_self bound

def sqrtThreeApprox (n : Nat) : QRat :=
  natFrac (sqrtThreeApproxNum n) (sqrtThreeApproxDen n) (sqrtThreeApproxDen_pos n)

def sqrtThreeApproxGap (n : Nat) : QRat :=
  natFrac 2 (sqrtThreeApproxDen n * sqrtThreeApproxDen n)
    (Nat.mul_pos (sqrtThreeApproxDen_pos n) (sqrtThreeApproxDen_pos n))

theorem sqrtThreeApprox_pos (n : Nat) : (0 : QRat) < sqrtThreeApprox n := by
  unfold sqrtThreeApprox
  exact natFrac_pos (sqrtThreeApproxNum_pos n) (sqrtThreeApproxDen_pos n)

theorem sqrtThreeApprox_num_square_lt_three_den_square (n : Nat) :
    sqrtThreeApproxNum n * sqrtThreeApproxNum n <
      3 * sqrtThreeApproxDen n * sqrtThreeApproxDen n := by
  have h := sqrtThreeApprox_pell n
  omega

theorem sqrtThreeApprox_square_lt_three (n : Nat) :
    sqrtThreeApprox n * sqrtThreeApprox n < (3 : QRat) := by
  change sqrtThreeApprox n * sqrtThreeApprox n < QRat.ofNat 3
  unfold sqrtThreeApprox
  exact natFrac_mul_self_lt_of_square_lt (sqrtThreeApproxDen_pos n)
    (sqrtThreeApprox_num_square_lt_three_den_square n)

theorem sqrtThreeApprox_square_gap_eq_three (n : Nat) :
    sqrtThreeApprox n * sqrtThreeApprox n + sqrtThreeApproxGap n = (3 : QRat) := by
  change sqrtThreeApprox n * sqrtThreeApprox n + sqrtThreeApproxGap n = QRat.ofNat 3
  unfold sqrtThreeApprox sqrtThreeApproxGap
  exact natFrac_square_add_gap_eq_of_num_square_add_gap (sqrtThreeApproxDen_pos n)
    (sqrtThreeApprox_pell n)

theorem exists_sqrtThreeApproxGap_lt_natFrac_one (bound : Nat) :
    exists n : Nat, sqrtThreeApproxGap n < natFrac 1 (bound + 1) (Nat.succ_pos bound) := by
  let n := 2 * (bound + 1)
  exists n
  unfold sqrtThreeApproxGap
  apply natFrac_lt_one_over_of_cross
  have hden : 2 * (bound + 1) < sqrtThreeApproxDen n := by
    simpa [n] using sqrtThreeApproxDen_gt_self n
  have hle : sqrtThreeApproxDen n ≤ sqrtThreeApproxDen n * sqrtThreeApproxDen n := by
    exact Nat.le_mul_of_pos_right (sqrtThreeApproxDen n) (sqrtThreeApproxDen_pos n)
  exact Nat.lt_of_lt_of_le hden hle

theorem sqrtThreeApprox_square_cofinal {q : QRat} (hq : q < QRat.ofNat 3) :
    exists t : QRat, 0 < t ∧ q < t * t ∧ t * t < QRat.ofNat 3 := by
  have hgap_pos : 0 < QRat.ofNat 3 - q := QRat.sub_pos_of_lt hq
  cases QRat.exists_natFrac_one_lt hgap_pos with
  | intro n hn =>
      cases QRat.exists_sqrtThreeApproxGap_lt_natFrac_one n with
      | intro m hm =>
          exists QRat.sqrtThreeApprox m
          constructor
          · exact QRat.sqrtThreeApprox_pos m
          · constructor
            · apply QRat.lt_of_square_add_gap_eq_of_gap_lt_sub
              · exact QRat.lt_trans hm hn
              · exact QRat.sqrtThreeApprox_square_gap_eq_three m
            · exact QRat.sqrtThreeApprox_square_lt_three m

/-!
# Powers and square-root obstructions

Natural powers and reduced-rational representatives connect the quotient
rationals back to the irrationality cores for square roots of two and three.
-/

def powNat (x : QRat) : Nat -> QRat
  | 0 => 1
  | n + 1 => powNat x n * x

theorem powNat_zero (x : QRat) : powNat x 0 = 1 :=
  rfl

theorem powNat_succ (x : QRat) (n : Nat) :
    powNat x (n + 1) = powNat x n * x :=
  rfl

theorem powNat_ofNat (m n : Nat) :
    powNat (ofNat m) n = ofNat (m ^ n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        powNat (ofNat m) (n + 1) = powNat (ofNat m) n * ofNat m := rfl
        _ = ofNat (m ^ n) * ofNat m := by rw [ih]
        _ = ofNat (m ^ n * m) := by rw [← ofNat_mul]
        _ = ofNat (m ^ (n + 1)) := by rw [Nat.pow_succ]

def toPositiveRatRep (q : QRat) : PositiveRatRep where
  num := (toRat q).num
  den := (toRat q).den
  den_pos := Rat.den_pos (toRat q)

theorem toPositiveRatRep_reduced (q : QRat) :
    (toPositiveRatRep q).Reduced := by
  exact (toRat q).reduced

theorem toPositiveRatRep_squareRootOfNat_of_square_eq_ofNat
    {q : QRat} {c : Nat} (h : q * q = QRat.ofNat c) :
    (toPositiveRatRep q).SquareRootOfNat c := by
  have hpow : (toRat q) ^ 2 = (c : Rat) := by
    have hRat : toRat q * toRat q = (c : Rat) := by
      have hcongr := congrArg QRat.toRat h
      simpa [QRat.toRat_mul, QRat.toRat_ofNat] using hcongr
    simpa [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] using hRat
  have hnum := congrArg Rat.num hpow
  have hden := congrArg Rat.den hpow
  simp [toPositiveRatRep, PositiveRatRep.SquareRootOfNat] at hnum hden ⊢
  rw [hden]
  simpa [Int.pow_succ, Int.pow_zero, Int.one_mul] using hnum

theorem no_square_root_two (q : QRat) :
    q * q ≠ QRat.ofNat 2 := by
  intro h
  exact PositiveRatRep.no_reduced_square_root_two (toPositiveRatRep q)
    (toPositiveRatRep_reduced q)
    (toPositiveRatRep_squareRootOfNat_of_square_eq_ofNat h)

theorem no_square_root_three (q : QRat) :
    q * q ≠ QRat.ofNat 3 := by
  intro h
  exact PositiveRatRep.no_reduced_square_root_three (toPositiveRatRep q)
    (toPositiveRatRep_reduced q)
    (toPositiveRatRep_squareRootOfNat_of_square_eq_ofNat h)

end QRat

namespace Countability

/-!
# Countability of rationals

Quotient rationals are countable by coding their standard rational
representatives injectively into natural numbers.
-/

def RatCode (r : Rat) : Nat :=
  PairCode (IntCode r.num) r.den

theorem ratCode_injective : Fn.Injective RatCode := by
  intro x y h
  have hp : (IntCode x.num, x.den) = (IntCode y.num, y.den) :=
    pairCode_injective h
  have hnumCode : IntCode x.num = IntCode y.num :=
    congrArg Prod.fst hp
  have hden : x.den = y.den :=
    congrArg Prod.snd hp
  exact Rat.ext (intCode_injective hnumCode) hden

def QRatCode (q : QRat) : Nat :=
  RatCode (QRat.toRat q)

theorem qratCode_injective : Fn.Injective QRatCode := by
  intro x y h
  exact QRat.toRat_injective (ratCode_injective h)

theorem qrat_encodable : EncodableByNat QRat := by
  exists QRatCode
  exact qratCode_injective

end Countability

namespace QRat

theorem countable_univ : FSet.Countable (FSet.Univ : FSet QRat) :=
  Countability.countable_univ_of_encodableByNat Countability.qrat_encodable

end QRat

end Foundation
end FoC
