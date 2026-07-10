import FoC.Foundation.Reals.BasicPart1

set_option doc.verso true

/-!
# Dedekind-real multiplication

This module continues the nonnegative cut product from
{module}`FoC.Foundation.Reals.BasicPart1`. It defines signed multiplication,
establishes the ring laws, proves compatibility with embedded quotient
rationals and natural powers, and records rational closure under the basic
ring operations.
-/

namespace FoC
namespace Foundation
namespace Real

theorem mulNonneg_one_left (x : Real)
    (h1 : (0 : Real) ≤ qreal 1) (hx : (0 : Real) ≤ x) :
    mulNonneg (qreal 1) x h1 hx = x := by
  apply ext
  intro q
  constructor
  · intro hq
    cases hq with
    | inl hq0 =>
        exact hx q hq0
    | inr hprod =>
        rcases hprod with ⟨a, b, ha0, hb0, ha1, hb, hqab⟩
        have hab_lt_b : a * b < b := by
          have h := QRat.mul_lt_mul_of_pos_right ha1 hb0
          simpa [QRat.one_mul] using h
        exact x.downward_closed q b (QRat.lt_trans hqab hab_lt_b) hb
  · intro hxq
    by_cases hq0 : q < 0
    · exact Or.inl hq0
    · cases x.open_upward q hxq with
      | intro b hb =>
          have hbpos : 0 < b :=
            QRat.zero_lt_of_not_lt_zero_of_lt hq0 hb.left
          have hqdiv : q / b < 1 := by
            apply (QRat.div_lt_iff (x := q) (y := b) (c := 1) hbpos).mpr
            simpa [QRat.one_mul] using hb.left
          cases QRat.density hqdiv with
          | intro a ha =>
              have ha0 : 0 < a :=
                QRat.zero_lt_of_not_lt_zero_of_lt
                  (QRat.div_nonneg hq0 hbpos) ha.left
              have hqab : q < a * b :=
                (QRat.div_lt_iff (x := q) (y := b) (c := a) hbpos).mp ha.left
              exact Or.inr ⟨a, b, ha0, hbpos, ha.right, hb.right, hqab⟩

theorem mulNonneg_one_right (x : Real)
    (hx : (0 : Real) ≤ x) (h1 : (0 : Real) ≤ qreal 1) :
    mulNonneg x (qreal 1) hx h1 = x := by
  apply ext
  intro q
  constructor
  · intro hq
    cases hq with
    | inl hq0 =>
        exact hx q hq0
    | inr hprod =>
        rcases hprod with ⟨a, b, ha0, hb0, ha, hb1, hqab⟩
        have hab_lt_a : a * b < a := by
          have h := QRat.mul_lt_mul_of_pos_left hb1 ha0
          simpa [QRat.mul_one] using h
        exact x.downward_closed q a (QRat.lt_trans hqab hab_lt_a) ha
  · intro hxq
    by_cases hq0 : q < 0
    · exact Or.inl hq0
    · cases x.open_upward q hxq with
      | intro a ha =>
          have hapos : 0 < a :=
            QRat.zero_lt_of_not_lt_zero_of_lt hq0 ha.left
          have hqdiv : q / a < 1 := by
            apply (QRat.div_lt_iff (x := q) (y := a) (c := 1) hapos).mpr
            simpa [QRat.one_mul] using ha.left
          cases QRat.density hqdiv with
          | intro b hb =>
              have hb0 : 0 < b :=
                QRat.zero_lt_of_not_lt_zero_of_lt
                  (QRat.div_nonneg hq0 hapos) hb.left
              have hqab : q < a * b := by
                have hqba : q < b * a :=
                  (QRat.div_lt_iff (x := q) (y := a) (c := b) hapos).mp hb.left
                simpa [QRat.mul_comm] using hqba
              exact Or.inr ⟨a, b, hapos, hb0, ha.right, hb.right, hqab⟩

theorem mulNonneg_zero_right (x : Real)
    (hx : (0 : Real) ≤ x) (h0 : (0 : Real) ≤ qreal 0) :
    mulNonneg x (qreal 0) hx h0 = 0 := by
  apply ext
  intro q
  change (mulNonneg x (qreal 0) hx h0).lower q ↔ q < 0
  constructor
  · intro hq
    cases hq with
    | inl hq0 =>
        exact hq0
    | inr hprod =>
        rcases hprod with ⟨_a, b, _ha0, hb0, _ha, hbzero, _hqab⟩
        exact False.elim (QRat.lt_asymm hb0 hbzero)
  · intro hq0
    exact Or.inl hq0

theorem qreal_mulNonneg_neg_right {a b : QRat}
    (ha : (0 : Real) ≤ qreal a) (hb : (0 : Real) ≤ -qreal b) :
    mulNonneg (qreal a) (-qreal b) ha hb = qreal (a * -b) := by
  have hb' : (0 : Real) ≤ qreal (-b) := by
    rwa [← qreal_neg]
  calc
    mulNonneg (qreal a) (-qreal b) ha hb
        = mulNonneg (qreal a) (qreal (-b)) ha hb' :=
            mulNonneg_congr rfl (qreal_neg b) ha hb ha hb'
    _ = qreal (a * -b) :=
            qreal_mulNonneg ha hb'

theorem qreal_mulNonneg_neg_left {a b : QRat}
    (ha : (0 : Real) ≤ -qreal a) (hb : (0 : Real) ≤ qreal b) :
    mulNonneg (-qreal a) (qreal b) ha hb = qreal ((-a) * b) := by
  have ha' : (0 : Real) ≤ qreal (-a) := by
    rwa [← qreal_neg]
  calc
    mulNonneg (-qreal a) (qreal b) ha hb
        = mulNonneg (qreal (-a)) (qreal b) ha' hb :=
            mulNonneg_congr (qreal_neg a) rfl ha hb ha' hb
    _ = qreal ((-a) * b) :=
            qreal_mulNonneg ha' hb

theorem qreal_mulNonneg_neg_neg {a b : QRat}
    (ha : (0 : Real) ≤ -qreal a) (hb : (0 : Real) ≤ -qreal b) :
    mulNonneg (-qreal a) (-qreal b) ha hb = qreal ((-a) * (-b)) := by
  have ha' : (0 : Real) ≤ qreal (-a) := by
    rwa [← qreal_neg]
  have hb' : (0 : Real) ≤ qreal (-b) := by
    rwa [← qreal_neg]
  calc
    mulNonneg (-qreal a) (-qreal b) ha hb
        = mulNonneg (qreal (-a)) (qreal (-b)) ha' hb' :=
            mulNonneg_congr (qreal_neg a) (qreal_neg b) ha hb ha' hb'
    _ = qreal ((-a) * (-b)) :=
            qreal_mulNonneg ha' hb'

noncomputable def mul (x y : Real) : Real := by
  classical
  exact
    if hx : (0 : Real) ≤ x then
      if hy : (0 : Real) ≤ y then
        mulNonneg x y hx hy
      else
        -(mulNonneg x (-y) hx (nonneg_neg_of_not_nonneg hy))
    else if hy : (0 : Real) ≤ y then
      -(mulNonneg (-x) y (nonneg_neg_of_not_nonneg hx) hy)
    else
      mulNonneg (-x) (-y)
        (nonneg_neg_of_not_nonneg hx)
        (nonneg_neg_of_not_nonneg hy)

noncomputable instance : Mul Real where
  mul := mul

theorem mul_comm (x y : Real) : x * y = y * x := by
  classical
  change mul x y = mul y x
  unfold mul
  by_cases hx : (0 : Real) ≤ x
  · simp [hx]
    by_cases hy : (0 : Real) ≤ y
    · simp [hy]
      exact mulNonneg_comm x y hx hy
    · simp [hy]
      change -mulNonneg x (-y) hx (nonneg_neg_of_not_nonneg hy) =
        -mulNonneg (-y) x (nonneg_neg_of_not_nonneg hy) hx
      rw [mulNonneg_comm]
  · simp [hx]
    by_cases hy : (0 : Real) ≤ y
    · simp [hy]
      change -mulNonneg (-x) y (nonneg_neg_of_not_nonneg hx) hy =
        -mulNonneg y (-x) hy (nonneg_neg_of_not_nonneg hx)
      rw [mulNonneg_comm]
    · simp [hy]
      change mulNonneg (-x) (-y) (nonneg_neg_of_not_nonneg hx)
          (nonneg_neg_of_not_nonneg hy) =
        mulNonneg (-y) (-x) (nonneg_neg_of_not_nonneg hy)
          (nonneg_neg_of_not_nonneg hx)
      exact mulNonneg_comm (-x) (-y)
        (nonneg_neg_of_not_nonneg hx) (nonneg_neg_of_not_nonneg hy)

theorem mul_ne_zero {x y : Real} (hxne : x ≠ 0) (hyne : y ≠ 0) :
    x * y ≠ 0 := by
  classical
  change mul x y ≠ 0
  unfold mul
  by_cases hx : (0 : Real) ≤ x
  · simp [hx]
    by_cases hy : (0 : Real) ≤ y
    · simp [hy]
      exact mulNonneg_ne_zero_of_pos hx hy
        (zero_lt_of_nonneg_ne_zero hx hxne)
        (zero_lt_of_nonneg_ne_zero hy hyne)
    · simp [hy]
      apply neg_ne_zero
      have hny : (0 : Real) ≤ -y := nonneg_neg_of_not_nonneg hy
      exact mulNonneg_ne_zero_of_pos hx hny
        (zero_lt_of_nonneg_ne_zero hx hxne)
        (zero_lt_of_nonneg_ne_zero hny (neg_ne_zero hyne))
  · simp [hx]
    by_cases hy : (0 : Real) ≤ y
    · simp [hy]
      apply neg_ne_zero
      have hnx : (0 : Real) ≤ -x := nonneg_neg_of_not_nonneg hx
      exact mulNonneg_ne_zero_of_pos hnx hy
        (zero_lt_of_nonneg_ne_zero hnx (neg_ne_zero hxne))
        (zero_lt_of_nonneg_ne_zero hy hyne)
    · simp [hy]
      have hnx : (0 : Real) ≤ -x := nonneg_neg_of_not_nonneg hx
      have hny : (0 : Real) ≤ -y := nonneg_neg_of_not_nonneg hy
      exact mulNonneg_ne_zero_of_pos hnx hny
        (zero_lt_of_nonneg_ne_zero hnx (neg_ne_zero hxne))
        (zero_lt_of_nonneg_ne_zero hny (neg_ne_zero hyne))

theorem one_mul (x : Real) : 1 * x = x := by
  classical
  change mul 1 x = x
  unfold mul
  have h1 : (0 : Real) ≤ (1 : Real) := by
    change (0 : Real) ≤ qreal 1
    exact (qreal_nonneg_iff 1).mpr (QRat.lt_asymm QRat.zero_lt_one)
  by_cases hx : (0 : Real) ≤ x
  · simp [h1, hx]
    change mulNonneg (qreal 1) x h1 hx = x
    exact mulNonneg_one_left x h1 hx
  · simp [h1, hx]
    change -mulNonneg (qreal 1) (-x) h1 (nonneg_neg_of_not_nonneg hx) = x
    rw [mulNonneg_one_left (-x) h1 (nonneg_neg_of_not_nonneg hx), neg_neg]

theorem mul_one (x : Real) : x * 1 = x := by
  classical
  change mul x 1 = x
  unfold mul
  have h1 : (0 : Real) ≤ (1 : Real) := by
    change (0 : Real) ≤ qreal 1
    exact (qreal_nonneg_iff 1).mpr (QRat.lt_asymm QRat.zero_lt_one)
  by_cases hx : (0 : Real) ≤ x
  · simp [h1, hx]
    change mulNonneg x (qreal 1) hx h1 = x
    exact mulNonneg_one_right x hx h1
  · simp [h1, hx]
    change -mulNonneg (-x) (qreal 1) (nonneg_neg_of_not_nonneg hx) h1 = x
    rw [mulNonneg_one_right (-x) (nonneg_neg_of_not_nonneg hx) h1, neg_neg]

theorem mul_zero (x : Real) : x * 0 = 0 := by
  classical
  change mul x 0 = 0
  unfold mul
  have h0 : (0 : Real) ≤ (0 : Real) := by
    intro q hq0
    exact hq0
  by_cases hx : (0 : Real) ≤ x
  · simp [hx, h0]
    change mulNonneg x (qreal 0) hx h0 = 0
    exact mulNonneg_zero_right x hx h0
  · simp [hx, h0]
    change -mulNonneg (-x) (qreal 0) (nonneg_neg_of_not_nonneg hx) h0 = 0
    rw [mulNonneg_zero_right (-x) (nonneg_neg_of_not_nonneg hx) h0]
    apply qreal_neg

theorem mul_neg (x y : Real) : x * -y = -(x * y) := by
  classical
  by_cases hyzero : y = 0
  · rw [hyzero, neg_zero, mul_zero]
    exact neg_zero.symm
  change mul x (-y) = -(mul x y)
  unfold mul
  by_cases hx : (0 : Real) ≤ x
  · simp [hx]
    by_cases hny : (0 : Real) ≤ -y
    · simp [hny]
      by_cases hy : (0 : Real) ≤ y
      · exact False.elim (hyzero (eq_zero_of_nonneg_of_neg_nonneg hy hny))
      · simp [hy]
        rw [neg_neg]
    · simp [hny]
      have hy : (0 : Real) ≤ y := nonneg_of_not_nonneg_neg hny
      simp [hy]
      change
        -mulNonneg x (-(-y)) hx (nonneg_neg_of_not_nonneg hny) =
          -mulNonneg x y hx hy
      rw [mulNonneg_congr rfl (neg_neg y) hx
        (nonneg_neg_of_not_nonneg hny) hx hy]
  · simp [hx]
    by_cases hny : (0 : Real) ≤ -y
    · simp [hny]
      by_cases hy : (0 : Real) ≤ y
      · exact False.elim (hyzero (eq_zero_of_nonneg_of_neg_nonneg hy hny))
      · simp [hy]
    · simp [hny]
      have hy : (0 : Real) ≤ y := nonneg_of_not_nonneg_neg hny
      simp [hy]
      change
        mulNonneg (-x) (-(-y)) (nonneg_neg_of_not_nonneg hx)
            (nonneg_neg_of_not_nonneg hny) =
          -(-mulNonneg (-x) y (nonneg_neg_of_not_nonneg hx) hy)
      rw [mulNonneg_congr rfl (neg_neg y) (nonneg_neg_of_not_nonneg hx)
        (nonneg_neg_of_not_nonneg hny) (nonneg_neg_of_not_nonneg hx) hy,
        neg_neg]

theorem neg_mul (x y : Real) : -x * y = -(x * y) := by
  calc
    -x * y = y * -x := mul_comm (-x) y
    _ = -(y * x) := mul_neg y x
    _ = -(x * y) := by rw [mul_comm y x]

theorem right_distrib_nonneg (x y z : Real)
    (hx : (0 : Real) ≤ x) (hy : (0 : Real) ≤ y)
    (hz : (0 : Real) ≤ z) :
    (x + y) * z = x * z + y * z := by
  classical
  change mul (x + y) z = mul x z + mul y z
  unfold mul
  have hxy : (0 : Real) ≤ x + y := add_nonneg hx hy
  simp [hxy, hx, hy, hz]
  exact mulNonneg_add_right x y z hx hy hz

private theorem right_distrib_nonneg_right_first_nonneg_second_neg
    (x y z : Real) (hx : (0 : Real) ≤ x) (hy : ¬ (0 : Real) ≤ y)
    (hz : (0 : Real) ≤ z) :
    (x + y) * z = x * z + y * z := by
  have hny : (0 : Real) ≤ -y := nonneg_neg_of_not_nonneg hy
  by_cases hsum : (0 : Real) ≤ x + y
  · have hdist := right_distrib_nonneg (x + y) (-y) z hsum hny hz
    have hcancel : (x + y) * z + -(y * z) = x * z := by
      simpa [add_neg_right_cancel, neg_mul] using hdist.symm
    exact eq_add_of_add_neg_eq hcancel
  · have hneg_sum : (0 : Real) ≤ -(x + y) := nonneg_neg_of_not_nonneg hsum
    have hdist := right_distrib_nonneg (-(x + y)) x z hneg_sum hx hz
    have hneg :
        -(y * z) = -((x + y) * z) + x * z := by
      simpa [neg_add_add_left_cancel, neg_mul] using hdist
    have hcancel : (x + y) * z + -(y * z) = x * z := by
      calc
        (x + y) * z + -(y * z) =
            (x + y) * z + (-((x + y) * z) + x * z) := by rw [hneg]
        _ = ((x + y) * z + -((x + y) * z)) + x * z :=
            (add_assoc ((x + y) * z) (-((x + y) * z)) (x * z)).symm
        _ = 0 + x * z := by rw [add_neg_cancel]
        _ = x * z := zero_add (x * z)
    exact eq_add_of_add_neg_eq hcancel

theorem right_distrib_nonneg_right (x y z : Real)
    (hz : (0 : Real) ≤ z) :
    (x + y) * z = x * z + y * z := by
  by_cases hx : (0 : Real) ≤ x
  · by_cases hy : (0 : Real) ≤ y
    · exact right_distrib_nonneg x y z hx hy hz
    · exact right_distrib_nonneg_right_first_nonneg_second_neg x y z hx hy hz
  · by_cases hy : (0 : Real) ≤ y
    · calc
        (x + y) * z = (y + x) * z := by rw [add_comm x y]
        _ = y * z + x * z :=
            right_distrib_nonneg_right_first_nonneg_second_neg y x z hy hx hz
        _ = x * z + y * z := add_comm (y * z) (x * z)
    · have hnx : (0 : Real) ≤ -x := nonneg_neg_of_not_nonneg hx
      have hny : (0 : Real) ≤ -y := nonneg_neg_of_not_nonneg hy
      have hdist := right_distrib_nonneg (-x) (-y) z hnx hny hz
      have hneg :
          -((x + y) * z) = -(x * z) + -(y * z) := by
        simpa [← neg_add x y, neg_mul] using hdist
      have htarget_neg :
          -((x + y) * z) = -(x * z + y * z) := by
        simpa [neg_add] using hneg
      have hcong := congrArg (fun t : Real => -t) htarget_neg
      simpa [neg_neg] using hcong

theorem right_distrib (x y z : Real) :
    (x + y) * z = x * z + y * z := by
  classical
  by_cases hz : (0 : Real) ≤ z
  · exact right_distrib_nonneg_right x y z hz
  · have hnz : (0 : Real) ≤ -z := nonneg_neg_of_not_nonneg hz
    have hdist := right_distrib_nonneg_right x y (-z) hnz
    have hneg :
        -((x + y) * z) = -(x * z) + -(y * z) := by
      simpa [mul_neg] using hdist
    have htarget_neg :
        -((x + y) * z) = -(x * z + y * z) := by
      simpa [neg_add] using hneg
    have hcong := congrArg (fun t : Real => -t) htarget_neg
    simpa [neg_neg] using hcong

theorem left_distrib (x y z : Real) :
    x * (y + z) = x * y + x * z := by
  calc
    x * (y + z) = (y + z) * x := mul_comm x (y + z)
    _ = y * x + z * x := right_distrib y z x
    _ = x * y + x * z := by rw [mul_comm y x, mul_comm z x]

/-!
**Associativity of multiplication.** On nonnegative cuts, multiplication is the
cut product {name}`mulNonneg`, whose associativity {name}`mulNonneg_assoc` is
proved directly on lower sets. The sign-split definition of {name}`Real.mul`
then reduces the general case to the nonnegative core by pulling negations out
with {name}`neg_mul` and {name}`mul_neg`, one factor at a time.
-/

theorem mul_nonneg {x y : Real}
    (hx : (0 : Real) ≤ x) (hy : (0 : Real) ≤ y) :
    (0 : Real) ≤ x * y := by
  classical
  change (0 : Real) ≤ mul x y
  unfold mul
  simp [hx, hy]
  exact mulNonneg_nonneg x y hx hy

theorem mul_eq_mulNonneg {x y : Real}
    (hx : (0 : Real) ≤ x) (hy : (0 : Real) ≤ y) :
    x * y = mulNonneg x y hx hy := by
  classical
  change mul x y = mulNonneg x y hx hy
  unfold mul
  simp [hx, hy]

private theorem mul_assoc_nonneg (x y z : Real)
    (hx : (0 : Real) ≤ x) (hy : (0 : Real) ≤ y) (hz : (0 : Real) ≤ z) :
    (x * y) * z = x * (y * z) := by
  have hxy : (0 : Real) ≤ x * y := mul_nonneg hx hy
  have hyz : (0 : Real) ≤ y * z := mul_nonneg hy hz
  calc
    (x * y) * z = mulNonneg (x * y) z hxy hz :=
      mul_eq_mulNonneg hxy hz
    _ = mulNonneg (mulNonneg x y hx hy) z (mulNonneg_nonneg x y hx hy) hz :=
      mulNonneg_congr (mul_eq_mulNonneg hx hy) rfl hxy hz
        (mulNonneg_nonneg x y hx hy) hz
    _ = mulNonneg x (mulNonneg y z hy hz) hx (mulNonneg_nonneg y z hy hz) :=
      mulNonneg_assoc x y z hx hy hz
    _ = mulNonneg x (y * z) hx hyz :=
      mulNonneg_congr rfl (mul_eq_mulNonneg hy hz).symm hx
        (mulNonneg_nonneg y z hy hz) hx hyz
    _ = x * (y * z) := (mul_eq_mulNonneg hx hyz).symm

private theorem mul_assoc_nonneg_left_pair (x y z : Real)
    (hx : (0 : Real) ≤ x) (hy : (0 : Real) ≤ y) :
    (x * y) * z = x * (y * z) := by
  classical
  by_cases hz : (0 : Real) ≤ z
  · exact mul_assoc_nonneg x y z hx hy hz
  · have hnz : (0 : Real) ≤ -z := nonneg_neg_of_not_nonneg hz
    have hneg : -((x * y) * z) = -(x * (y * z)) := by
      calc
        -((x * y) * z) = (x * y) * -z := (mul_neg (x * y) z).symm
        _ = x * (y * -z) := mul_assoc_nonneg x y (-z) hx hy hnz
        _ = x * -(y * z) := by rw [mul_neg y z]
        _ = -(x * (y * z)) := mul_neg x (y * z)
    have hcong := congrArg (fun t : Real => -t) hneg
    simpa [neg_neg] using hcong

private theorem mul_assoc_nonneg_left (x y z : Real)
    (hx : (0 : Real) ≤ x) :
    (x * y) * z = x * (y * z) := by
  classical
  by_cases hy : (0 : Real) ≤ y
  · exact mul_assoc_nonneg_left_pair x y z hx hy
  · have hny : (0 : Real) ≤ -y := nonneg_neg_of_not_nonneg hy
    have hneg : -((x * y) * z) = -(x * (y * z)) := by
      calc
        -((x * y) * z) = (-(x * y)) * z := (neg_mul (x * y) z).symm
        _ = (x * -y) * z := by rw [mul_neg x y]
        _ = x * ((-y) * z) := mul_assoc_nonneg_left_pair x (-y) z hx hny
        _ = x * -(y * z) := by rw [neg_mul y z]
        _ = -(x * (y * z)) := mul_neg x (y * z)
    have hcong := congrArg (fun t : Real => -t) hneg
    simpa [neg_neg] using hcong

theorem mul_assoc (x y z : Real) : (x * y) * z = x * (y * z) := by
  classical
  by_cases hx : (0 : Real) ≤ x
  · exact mul_assoc_nonneg_left x y z hx
  · have hnx : (0 : Real) ≤ -x := nonneg_neg_of_not_nonneg hx
    have hneg : -((x * y) * z) = -(x * (y * z)) := by
      calc
        -((x * y) * z) = (-(x * y)) * z := (neg_mul (x * y) z).symm
        _ = ((-x) * y) * z := by rw [neg_mul x y]
        _ = (-x) * (y * z) := mul_assoc_nonneg_left (-x) y z hnx
        _ = -(x * (y * z)) := neg_mul x (y * z)
    have hcong := congrArg (fun t : Real => -t) hneg
    simpa [neg_neg] using hcong

theorem qreal_mul (a b : QRat) :
    qreal a * qreal b = qreal (a * b) := by
  classical
  change mul (qreal a) (qreal b) = qreal (a * b)
  unfold mul
  by_cases ha : (0 : Real) ≤ qreal a
  · simp [ha]
    by_cases hb : (0 : Real) ≤ qreal b
    · simp [hb, qreal_mulNonneg]
    · simp [hb]
      calc
        -(mulNonneg (qreal a) (-qreal b) ha (nonneg_neg_of_not_nonneg hb))
            = -qreal (a * -b) := by
                rw [qreal_mulNonneg_neg_right]
        _ = qreal (-(a * -b)) := qreal_neg (a * -b)
        _ = qreal (a * b) := by
            rw [QRat.mul_neg, QRat.neg_neg]
  · simp [ha]
    by_cases hb : (0 : Real) ≤ qreal b
    · simp [hb]
      calc
        -(mulNonneg (-qreal a) (qreal b) (nonneg_neg_of_not_nonneg ha) hb)
            = -qreal ((-a) * b) := by
                rw [qreal_mulNonneg_neg_left]
        _ = qreal (-((-a) * b)) := qreal_neg ((-a) * b)
        _ = qreal (a * b) := by
            rw [QRat.neg_mul, QRat.neg_neg]
    · simp [hb]
      calc
        mulNonneg (-qreal a) (-qreal b)
            (nonneg_neg_of_not_nonneg ha)
            (nonneg_neg_of_not_nonneg hb)
            = qreal ((-a) * (-b)) := by
                rw [qreal_mulNonneg_neg_neg]
        _ = qreal (a * b) := by
            rw [QRat.neg_mul_neg]

theorem rational_mul {x y : Real}
    (hx : Rational x) (hy : Rational y) : Rational (x * y) := by
  cases hx with
  | intro a hxa =>
      cases hy with
      | intro b hyb =>
          exists a * b
          rw [hxa, hyb, qreal_mul]

noncomputable def powNat (x : Real) : Nat -> Real
  | 0 => 1
  | n + 1 => powNat x n * x

theorem qreal_powNat (q : QRat) (n : Nat) :
    powNat (qreal q) n = qreal (QRat.powNat q n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        powNat (qreal q) (n + 1) = powNat (qreal q) n * qreal q := rfl
        _ = qreal (QRat.powNat q n) * qreal q := by rw [ih]
        _ = qreal (QRat.powNat q n * q) := qreal_mul (QRat.powNat q n) q
        _ = qreal (QRat.powNat q (n + 1)) := rfl

theorem rational_add {x y : Real}
    (hx : Rational x) (hy : Rational y) : Rational (x + y) := by
  cases hx with
  | intro a hxa =>
      cases hy with
      | intro b hyb =>
          exists a + b
          rw [hxa, hyb, qreal_add]

theorem rational_neg {x : Real} (hx : Rational x) : Rational (-x) := by
  cases hx with
  | intro a hxa =>
      exists -a
      rw [hxa, qreal_neg]

theorem rational_sub {x y : Real}
    (hx : Rational x) (hy : Rational y) : Rational (x - y) := by
  cases hx with
  | intro a hxa =>
      cases hy with
      | intro b hyb =>
          exists a - b
          rw [hxa, hyb, qreal_sub]

theorem irrational_neg {x : Real} (hx : Irrational x) : Irrational (-x) := by
  intro hrat
  apply hx
  have hnn : Rational (-(-x)) := rational_neg hrat
  rwa [neg_neg] at hnn
end Real
end Foundation
end FoC
