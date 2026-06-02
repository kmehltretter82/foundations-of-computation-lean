import FoC.Foundation.Countable
import FoC.Foundation.RationalCore
import FoC.Foundation.Rationals
import Init.Data.Rat.Lemmas

namespace FoC
namespace Foundation

/-!
Quotient rational numbers.

The earlier `Rational` module keeps raw integer-over-integer representatives.
This module introduces the quotient-rational layer needed before Dedekind cuts:
integer numerators, positive natural denominators, and equality by cross
multiplication.

Used by:
- Future `Real` construction: Dedekind cuts over quotient rationals
- Chapter 1 real-number examples: rational embedding and arithmetic transport
- Chapter 2 countability examples: rationals as countable data
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

instance : Add QRat where
  add := add

instance : Neg QRat where
  neg := neg

instance : Sub QRat where
  sub := sub

instance : Mul QRat where
  mul := mul

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

theorem add_eq_of_toRat (x y : QRat) :
    toRat (x + y) = toRat x + toRat y :=
  toRat_add x y

theorem mul_eq_of_toRat (x y : QRat) :
    toRat (x * y) = toRat x * toRat y :=
  toRat_mul x y

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

end QRat

end Foundation
end FoC
