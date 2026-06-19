import FoC.Foundation.Reals.BasicPart1

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

/-!
**Nonzero division by cancellation.** The theorem {name}`right_distrib` and
{name}`mul_ne_zero` turn equality after multiplication by a nonzero denominator
into cancellation. The quotient selector below uses classical choice only to
pick a preimage; the cancellation theorem proves that, for an actual product
{lit}`a * d`, the selected quotient is the original {lit}`a`.
-/

theorem mul_right_cancel_of_right_distrib
    (right_distrib : forall a b c : Real, (a + b) * c = a * c + b * c)
    {a b d : Real} (hd : d ≠ 0) (h : a * d = b * d) : a = b := by
  by_cases hdiff : a + -b = 0
  · exact eq_of_add_neg_eq_zero hdiff
  · have hprod_ne : (a + -b) * d ≠ 0 := mul_ne_zero hdiff hd
    exfalso
    apply hprod_ne
    calc
      (a + -b) * d = a * d + (-b) * d := right_distrib a (-b) d
      _ = a * d + -(b * d) := by rw [neg_mul]
      _ = b * d + -(b * d) := by rw [h]
      _ = 0 := add_neg_cancel (b * d)

noncomputable def divByNonzeroOfRightDistrib
    (_right_distrib : forall a b c : Real, (a + b) * c = a * c + b * c)
    (num : Real) (d : Real) (_hd : d ≠ 0) : Real := by
  classical
  exact if h : exists q : Real, q * d = num then Classical.choose h else 0

theorem divByNonzeroOfRightDistrib_mul_cancel
    (right_distrib : forall a b c : Real, (a + b) * c = a * c + b * c)
    (a d : Real) (hd : d ≠ 0) :
    divByNonzeroOfRightDistrib right_distrib (a * d) d hd = a := by
  classical
  unfold divByNonzeroOfRightDistrib
  by_cases h : exists q : Real, q * d = a * d
  · simp [h]
    exact mul_right_cancel_of_right_distrib right_distrib hd
      (Classical.choose_spec h)
  · exact False.elim (h ⟨a, rfl⟩)

noncomputable def divByNonzero (num : Real) (d : Real) (hd : d ≠ 0) : Real :=
  divByNonzeroOfRightDistrib right_distrib num d hd

theorem divByNonzero_mul_cancel (a d : Real) (hd : d ≠ 0) :
    divByNonzero (a * d) d hd = a :=
  divByNonzeroOfRightDistrib_mul_cancel right_distrib a d hd

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

def scalePos (c : QRat) (hc : 0 < c) (x : Real) : Real where
  lower := fun q => exists a, x.lower a ∧ q < c * a
  nonempty := by
    cases x.nonempty with
    | intro a ha =>
        cases QRat.exists_lower_upper (c * a) with
        | intro l hrest =>
            cases hrest with
            | intro _ hl =>
                exact Exists.intro l (Exists.intro a (And.intro ha hl.left))
  proper := by
    cases x.proper with
    | intro u hu =>
        exists c * u
        intro h
        cases h with
        | intro a ha =>
            have hua : u < a :=
              QRat.lt_of_mul_lt_mul_left ha.right hc
            exact hu (x.downward_closed u a hua ha.left)
  downward_closed := by
    intro q r hqr hr
    cases hr with
    | intro a ha =>
        exact Exists.intro a
          (And.intro ha.left (QRat.lt_trans hqr ha.right))
  open_upward := by
    intro q hq
    cases hq with
    | intro a ha =>
        cases QRat.density ha.right with
        | intro r hr =>
            exact Exists.intro r
              (And.intro hr.left
                (Exists.intro a (And.intro ha.left hr.right)))

theorem scalePos_lower_iff (c : QRat) (hc : 0 < c) (x : Real) (p : QRat) :
    (scalePos c hc x).lower p <-> x.lower (p / c) := by
  constructor
  · intro h
    cases h with
    | intro a ha =>
        have hpac : p < a * c := by
          simpa [QRat.mul_comm] using ha.right
        exact x.downward_closed (p / c) a
          ((QRat.div_lt_iff (x := p) (y := c) (c := a) hc).mpr hpac) ha.left
  · intro hp
    cases x.open_upward (p / c) hp with
    | intro a ha =>
        have hpac : p < a * c :=
          (QRat.div_lt_iff (x := p) (y := c) (c := a) hc).mp ha.left
        have hpca : p < c * a := by
          rwa [QRat.mul_comm] at hpac
        exact Exists.intro a (And.intro ha.right hpca)

theorem qreal_scalePos (c : QRat) (hc : 0 < c) (r : QRat) :
    scalePos c hc (qreal r) = qreal (c * r) := by
  apply ext
  intro p
  rw [scalePos_lower_iff, qreal_lower_iff, qreal_lower_iff]
  simpa [QRat.mul_comm] using
    (QRat.div_lt_iff (x := p) (y := c) (c := r) hc)

theorem rational_scalePos {x : Real} {c : QRat} (hc : 0 < c)
    (hx : Rational x) : Rational (scalePos c hc x) := by
  cases hx with
  | intro r hxr =>
      exists c * r
      rw [hxr, qreal_scalePos]

theorem irrational_scalePos {x : Real} {c : QRat} (hc : 0 < c)
    (hx : Irrational x) : Irrational (scalePos c hc x) := by
  intro hrat
  cases hrat with
  | intro r hxr =>
      apply hx
      exists r / c
      have hc_ne : c ≠ 0 := by
        intro hzero
        rw [hzero] at hc
        exact QRat.lt_irrefl 0 hc
      apply ext
      intro p
      constructor
      · intro hp
        have hscale : (scalePos c hc x).lower (c * p) := by
          rw [scalePos_lower_iff]
          have hcancel : c * p / c = p := by
            rw [QRat.mul_comm]
            exact QRat.mul_div_cancel p hc_ne
          rwa [hcancel]
        have hr : (qreal r).lower (c * p) :=
          (lower_congr hxr (c * p)).mp hscale
        have hpc : p * c < r := by
          simpa [QRat.mul_comm] using hr
        exact (qreal_lower_iff (r / c) p).mpr
          ((QRat.lt_div_iff (x := p) (y := r) (c := c) hc).mpr hpc)
      · intro hpr
        have hpc : p * c < r :=
          (QRat.lt_div_iff (x := p) (y := r) (c := c) hc).mp hpr
        have hcp : c * p < r := by
          simpa [QRat.mul_comm] using hpc
        have hscale : (scalePos c hc x).lower (c * p) :=
          (lower_congr hxr (c * p)).mpr hcp
        have hp : x.lower (c * p / c) :=
          (scalePos_lower_iff c hc x (c * p)).mp hscale
        have hcancel : c * p / c = p := by
          rw [QRat.mul_comm]
          exact QRat.mul_div_cancel p hc_ne
        rwa [hcancel] at hp

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

noncomputable def scale (c : QRat) (x : Real) : Real := by
  classical
  exact
    if hpos : 0 < c then
      scalePos c hpos x
    else if hneg : c < 0 then
      -(scalePos (-c) (QRat.neg_pos_of_neg hneg) x)
    else
      0

theorem qreal_scale (c r : QRat) :
    scale c (qreal r) = qreal (c * r) := by
  classical
  unfold scale
  by_cases hpos : 0 < c
  · simp [hpos, qreal_scalePos]
  · by_cases hneg : c < 0
    · simp [hpos, hneg]
      calc
        -(scalePos (-c) (QRat.neg_pos_of_neg hneg) (qreal r))
            = -qreal ((-c) * r) := by
                rw [qreal_scalePos]
        _ = qreal (-((-c) * r)) := qreal_neg ((-c) * r)
        _ = qreal (c * r) := by
            rw [QRat.neg_mul, QRat.neg_neg]
    · have hzero : c = 0 := by
        cases QRat.lt_trichotomy 0 c with
        | inl hcpos =>
            exact False.elim (hpos hcpos)
        | inr hrest =>
            cases hrest with
            | inl heq =>
                exact heq.symm
            | inr hcneg =>
                exact False.elim (hneg hcneg)
      have h00 : ¬ (0 : QRat) < 0 := QRat.lt_irrefl 0
      simp [hzero, h00, QRat.zero_mul]
      rfl

noncomputable def divByQ (x : Real) (q : QRat) (_hq : q ≠ 0) : Real :=
  scale q⁻¹ x

theorem qreal_divByQ (r q : QRat) (hq : q ≠ 0) :
    divByQ (qreal r) q hq = qreal (r / q) := by
  unfold divByQ
  calc
    scale q⁻¹ (qreal r) = qreal (q⁻¹ * r) := qreal_scale q⁻¹ r
    _ = qreal (r / q) := by
        change qreal (q⁻¹ * r) = qreal (r * q⁻¹)
        rw [QRat.mul_comm]

/-!
# Square-root cuts and irrationality bridges

Square-root cuts are specified by rational square inequalities. The bridge
theorems turn quotient-rational no-square-root facts into real irrationality
statements.  The concrete cut equalities for sqrt(2) and sqrt(3) use explicit
quotient-rational approximants to prove that the cut products are exactly the
embedded rationals {lit}`2` and {lit}`3`.
-/

def sqrtNatLower (c : Nat) (q : QRat) : Prop :=
  q < 0 ∨ exists r : QRat, q < r ∧ r * r < QRat.ofNat c

theorem sqrtNatLower_nonempty (c : Nat) :
    exists q : QRat, sqrtNatLower c q := by
  cases QRat.exists_lower_upper (0 : QRat) with
  | intro l hrest =>
      cases hrest with
      | intro _ hbounds =>
          exact Exists.intro l (Or.inl hbounds.left)

theorem sqrtNatLower_downward_closed (c : Nat) {q r : QRat}
    (hqr : q < r) (hr : sqrtNatLower c r) : sqrtNatLower c q := by
  cases hr with
  | inl hr0 =>
      exact Or.inl (QRat.lt_trans hqr hr0)
  | inr hsq =>
      cases hsq with
      | intro s hs =>
          exact Or.inr (Exists.intro s
            (And.intro (QRat.lt_trans hqr hs.left) hs.right))

theorem sqrtNatLower_open_upward (c : Nat) {q : QRat}
    (hq : sqrtNatLower c q) :
    exists r : QRat, q < r ∧ sqrtNatLower c r := by
  cases hq with
  | inl hq0 =>
      cases QRat.density hq0 with
      | intro r hr =>
          exact Exists.intro r (And.intro hr.left (Or.inl hr.right))
  | inr hsq =>
      cases hsq with
      | intro s hs =>
          cases QRat.density hs.left with
          | intro r hr =>
              exact Exists.intro r
                (And.intro hr.left
                  (Or.inr (Exists.intro s (And.intro hr.right hs.right))))

theorem sqrtNatLower_proper_of_one_lt {c : Nat} (hc : 1 < c) :
    exists q : QRat, ¬ sqrtNatLower c q := by
  exists QRat.ofNat c
  intro h
  have h0c : (0 : QRat) < QRat.ofNat c :=
    QRat.ofNat_pos (Nat.lt_trans (by decide : 0 < 1) hc)
  cases h with
  | inl hc0 =>
      exact QRat.lt_asymm h0c hc0
  | inr hsq =>
      cases hsq with
      | intro r hr =>
          have hcr : QRat.ofNat c < r := hr.left
          have hccrr : QRat.ofNat c * QRat.ofNat c < r * r :=
            QRat.mul_lt_mul_of_pos hcr hcr h0c h0c
          have hccrr' : QRat.ofNat (c * c) < r * r := by
            rw [QRat.ofNat_mul]
            exact hccrr
          have hlarge : QRat.ofNat c < QRat.ofNat (c * c) := by
            apply QRat.ofNat_lt_of_nat_lt
            have hcpos : 0 < c := Nat.lt_trans (by decide : 0 < 1) hc
            simpa [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hc hcpos
          exact QRat.lt_asymm hlarge (QRat.lt_trans hccrr' hr.right)

def sqrtTwoCut : Real where
  lower := sqrtNatLower 2
  nonempty := sqrtNatLower_nonempty 2
  proper := sqrtNatLower_proper_of_one_lt (by decide : 1 < 2)
  downward_closed := by
    intro q r hqr hr
    exact sqrtNatLower_downward_closed 2 hqr hr
  open_upward := by
    intro q hq
    exact sqrtNatLower_open_upward 2 hq

def sqrtThreeCut : Real where
  lower := sqrtNatLower 3
  nonempty := sqrtNatLower_nonempty 3
  proper := sqrtNatLower_proper_of_one_lt (by decide : 1 < 3)
  downward_closed := by
    intro q r hqr hr
    exact sqrtNatLower_downward_closed 3 hqr hr
  open_upward := by
    intro q hq
    exact sqrtNatLower_open_upward 3 hq

theorem sqrtTwoCut_lower_iff (q : QRat) :
    sqrtTwoCut.lower q <-> sqrtNatLower 2 q :=
  Iff.rfl

theorem sqrtThreeCut_lower_iff (q : QRat) :
    sqrtThreeCut.lower q <-> sqrtNatLower 3 q :=
  Iff.rfl

theorem sqrtTwoCut_nonneg : (0 : Real) ≤ sqrtTwoCut := by
  intro q hq0
  exact Or.inl hq0

theorem sqrtThreeCut_nonneg : (0 : Real) ≤ sqrtThreeCut := by
  intro q hq0
  exact Or.inl hq0

theorem sqrtNatLower_positive_witness {c : Nat} {q : QRat}
    (hq0 : 0 < q) (hq : sqrtNatLower c q) :
    exists r : QRat, 0 < r ∧ q < r ∧ r * r < QRat.ofNat c := by
  cases hq with
  | inl hqneg =>
      exact False.elim (QRat.lt_asymm hq0 hqneg)
  | inr hw =>
      cases hw with
      | intro r hr =>
          exact Exists.intro r
            (And.intro (QRat.lt_trans hq0 hr.left) hr)

theorem qrat_mul_lt_of_square_bounds {r s c : QRat}
    (hr0 : 0 < r) (hs0 : 0 < s)
    (hrr : r * r < c) (hss : s * s < c) : r * s < c := by
  cases QRat.lt_trichotomy r s with
  | inl hrs =>
      exact QRat.lt_trans (QRat.mul_lt_mul_of_pos_right hrs hs0) hss
  | inr hrest =>
      cases hrest with
      | inl hrsEq =>
          rw [hrsEq]
          exact hss
      | inr hsr =>
          have hsrr : s * r < r * r :=
            QRat.mul_lt_mul_of_pos_right hsr hr0
          have hrsr : r * s < r * r := by
            simpa [QRat.mul_comm] using hsrr
          exact QRat.lt_trans hrsr hrr

theorem sqrtNatLower_product_lt_of_pos {c : Nat} {a b : QRat}
    (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : sqrtNatLower c a) (hb : sqrtNatLower c b) :
    a * b < QRat.ofNat c := by
  cases sqrtNatLower_positive_witness ha0 ha with
  | intro r hr =>
      cases sqrtNatLower_positive_witness hb0 hb with
      | intro s hs =>
          have habrs : a * b < r * s :=
            QRat.mul_lt_mul_of_pos hr.right.left hs.right.left ha0 hb0
          exact QRat.lt_trans habrs
            (qrat_mul_lt_of_square_bounds hr.left hs.left
              hr.right.right hs.right.right)

theorem sqrtNatLower_mulNonneg_self_eq_qreal
    (x : Real) (c : Nat)
    (hx : forall q : QRat, x.lower q <-> sqrtNatLower c q)
    (hxnonneg : (0 : Real) ≤ x)
    (hcpos : 0 < c)
    (hcofinal : forall q : QRat, q < QRat.ofNat c ->
      exists t : QRat, 0 < t ∧ q < t * t ∧ t * t < QRat.ofNat c) :
    mulNonneg x x hxnonneg hxnonneg = qreal (QRat.ofNat c) := by
  apply ext
  intro q
  constructor
  · intro hq
    cases hq with
    | inl hq0 =>
        exact QRat.lt_trans hq0 (QRat.ofNat_pos hcpos)
    | inr hprod =>
        cases hprod with
        | intro a harest =>
            cases harest with
            | intro b hbounds =>
                have ha : sqrtNatLower c a :=
                  (hx a).mp hbounds.right.right.left
                have hb : sqrtNatLower c b :=
                  (hx b).mp hbounds.right.right.right.left
                have habc : a * b < QRat.ofNat c :=
                  sqrtNatLower_product_lt_of_pos
                    hbounds.left hbounds.right.left ha hb
                exact QRat.lt_trans hbounds.right.right.right.right habc
  · intro hq
    by_cases hq0 : q < 0
    · exact Or.inl hq0
    · cases hcofinal q hq with
      | intro t ht =>
          have hqdivt : q / t < t :=
            (QRat.div_lt_iff (x := q) (y := t) (c := t) ht.left).mpr
              ht.right.left
          cases QRat.density hqdivt with
          | intro a ha =>
              have hqdivt_nonneg : ¬ q / t < 0 :=
                QRat.div_nonneg hq0 ht.left
              have ha0 : 0 < a :=
                QRat.zero_lt_of_not_lt_zero_of_lt hqdivt_nonneg ha.left
              have hqat : q < a * t :=
                (QRat.div_lt_iff (x := q) (y := t) (c := a) ht.left).mp
                  ha.left
              have hqdiva : q / a < t := by
                apply (QRat.div_lt_iff (x := q) (y := a) (c := t) ha0).mpr
                simpa [QRat.mul_comm] using hqat
              cases QRat.density hqdiva with
              | intro b hb =>
                  have hqdiva_nonneg : ¬ q / a < 0 :=
                    QRat.div_nonneg hq0 ha0
                  have hb0 : 0 < b :=
                    QRat.zero_lt_of_not_lt_zero_of_lt hqdiva_nonneg hb.left
                  have hqab : q < a * b := by
                    have hqba : q < b * a :=
                      (QRat.div_lt_iff (x := q) (y := a) (c := b) ha0).mp
                        hb.left
                    simpa [QRat.mul_comm] using hqba
                  exact Or.inr (Exists.intro a (Exists.intro b
                    (And.intro ha0
                      (And.intro hb0
                        (And.intro ((hx a).mpr
                          (Or.inr (Exists.intro t
                            (And.intro ha.right ht.right.right))))
                          (And.intro ((hx b).mpr
                            (Or.inr (Exists.intro t
                              (And.intro hb.right ht.right.right))))
                            hqab))))))

theorem sqrtTwoCut_mul_self_eq_two :
    sqrtTwoCut * sqrtTwoCut = (2 : Real) := by
  classical
  have hmul : mulNonneg sqrtTwoCut sqrtTwoCut sqrtTwoCut_nonneg sqrtTwoCut_nonneg =
      qreal (QRat.ofNat 2) :=
    sqrtNatLower_mulNonneg_self_eq_qreal sqrtTwoCut 2
      (fun q => sqrtTwoCut_lower_iff q)
      sqrtTwoCut_nonneg (by decide)
      (fun q hq => QRat.sqrtTwoApprox_square_cofinal hq)
  change FoC.Foundation.Real.mul sqrtTwoCut sqrtTwoCut = qreal (QRat.ofNat 2)
  unfold FoC.Foundation.Real.mul
  simp [sqrtTwoCut_nonneg, hmul]

theorem sqrtThreeCut_mul_self_eq_three :
    sqrtThreeCut * sqrtThreeCut = (3 : Real) := by
  classical
  have hmul :
      mulNonneg sqrtThreeCut sqrtThreeCut sqrtThreeCut_nonneg sqrtThreeCut_nonneg =
        qreal (QRat.ofNat 3) :=
    sqrtNatLower_mulNonneg_self_eq_qreal sqrtThreeCut 3
      (fun q => sqrtThreeCut_lower_iff q)
      sqrtThreeCut_nonneg (by decide)
      (fun q hq => QRat.sqrtThreeApprox_square_cofinal hq)
  change FoC.Foundation.Real.mul sqrtThreeCut sqrtThreeCut = qreal (QRat.ofNat 3)
  unfold FoC.Foundation.Real.mul
  simp [sqrtThreeCut_nonneg, hmul]

theorem irrational_scale_nonzero {x : Real} {c : QRat}
    (hc : c ≠ 0) (hx : Irrational x) : Irrational (scale c x) := by
  classical
  unfold scale
  by_cases hpos : 0 < c
  · simp [hpos]
    exact irrational_scalePos hpos hx
  · by_cases hneg : c < 0
    · simp [hpos, hneg]
      exact irrational_neg (irrational_scalePos (QRat.neg_pos_of_neg hneg) hx)
    · have hzero : c = 0 := by
        cases QRat.lt_trichotomy 0 c with
        | inl hlt =>
            exact False.elim (hpos hlt)
        | inr hrest =>
            cases hrest with
            | inl heq =>
                exact heq.symm
            | inr hlt =>
                exact False.elim (hneg hlt)
      exact False.elim (hc hzero)

theorem irrational_add_qreal {x : Real} {q : QRat}
    (hx : Irrational x) : Irrational (x + qreal q) := by
  intro hrat
  cases hrat with
  | intro r hxr =>
      apply hx
      exists r - q
      apply ext
      intro p
      constructor
      · intro hp
        have hsum : (x + qreal q).lower (p + q) := by
          rw [add_qreal_lower_iff, QRat.add_sub_cancel]
          exact hp
        have hpqr : (qreal r).lower (p + q) :=
          (lower_congr hxr (p + q)).mp hsum
        exact (qreal_lower_iff (r - q) p).mpr
          (QRat.lt_sub_right_iff_add_lt.mpr hpqr)
      · intro hpr
        have hpqr : p + q < r :=
          QRat.lt_sub_right_iff_add_lt.mp hpr
        have hsum : (x + qreal q).lower (p + q) :=
          (lower_congr hxr (p + q)).mpr hpqr
        have hp : x.lower ((p + q) - q) :=
          (add_qreal_lower_iff x q (p + q)).mp hsum
        rwa [QRat.add_sub_cancel] at hp

theorem irrational_qreal_add {x : Real} {q : QRat}
    (hx : Irrational x) : Irrational (qreal q + x) := by
  rw [add_comm]
  exact irrational_add_qreal hx

def qrealSquareCharacterization (x : Real) (c : Nat) : Prop :=
  forall q : QRat, x = qreal q -> q * q = QRat.ofNat c

theorem qrealSquareCharacterization_of_square_eq_qreal
    {x : Real} {c : Nat}
    (hsquare : x * x = qreal (QRat.ofNat c)) :
    qrealSquareCharacterization x c := by
  intro q hx
  apply qreal_injective
  calc
    qreal (q * q) = qreal q * qreal q := by
      rw [qreal_mul]
    _ = x * x := by
      rw [← hx]
    _ = qreal (QRat.ofNat c) := hsquare

theorem irrational_of_qreal_square_characterization
    {x : Real} {c : Nat}
    (hno : forall q : QRat, q * q ≠ QRat.ofNat c)
    (hsquare : qrealSquareCharacterization x c) : Irrational x := by
  intro hx
  cases hx with
  | intro q hq =>
      exact hno q (hsquare q hq)

theorem irrational_of_qreal_square_eq_two {x : Real}
    (hsquare : qrealSquareCharacterization x 2) : Irrational x :=
  irrational_of_qreal_square_characterization QRat.no_square_root_two hsquare

theorem irrational_of_qreal_square_eq_three {x : Real}
    (hsquare : qrealSquareCharacterization x 3) : Irrational x :=
  irrational_of_qreal_square_characterization QRat.no_square_root_three hsquare

theorem irrational_of_square_eq_qreal
    {x : Real} {c : Nat}
    (hno : forall q : QRat, q * q ≠ QRat.ofNat c)
    (hsquare : x * x = qreal (QRat.ofNat c)) : Irrational x :=
  irrational_of_qreal_square_characterization hno
    (qrealSquareCharacterization_of_square_eq_qreal hsquare)

theorem irrational_of_square_eq_two {x : Real}
    (hsquare : x * x = (2 : Real)) : Irrational x :=
  irrational_of_square_eq_qreal QRat.no_square_root_two hsquare

theorem irrational_of_square_eq_three {x : Real}
    (hsquare : x * x = (3 : Real)) : Irrational x :=
  irrational_of_square_eq_qreal QRat.no_square_root_three hsquare

theorem sqrtTwoCut_irrational : Irrational sqrtTwoCut :=
  irrational_of_square_eq_two sqrtTwoCut_mul_self_eq_two

theorem sqrtThreeCut_irrational : Irrational sqrtThreeCut :=
  irrational_of_square_eq_three sqrtThreeCut_mul_self_eq_three

theorem sqrtTwoCut_square_rational : Rational (sqrtTwoCut * sqrtTwoCut) := by
  rw [sqrtTwoCut_mul_self_eq_two]
  exact rational_qreal (QRat.ofNat 2)

theorem sqrtThreeCut_square_rational : Rational (sqrtThreeCut * sqrtThreeCut) := by
  rw [sqrtThreeCut_mul_self_eq_three]
  exact rational_qreal (QRat.ofNat 3)

theorem rational_not_square_eq_two {x : Real}
    (hx : Rational x) : x * x ≠ (2 : Real) := by
  intro hsquare
  exact irrational_of_square_eq_two hsquare hx

theorem rational_not_square_eq_three {x : Real}
    (hx : Rational x) : x * x ≠ (3 : Real) := by
  intro hsquare
  exact irrational_of_square_eq_three hsquare hx

/-!
# Density

The final theorem constructs a rational cut strictly between any two ordered
Dedekind cuts, matching the dense-order statement used in the book layer.
-/

theorem density {x y : Real} (h : x < y) :
    exists z : Real, x < z ∧ z < y := by
  cases h.right with
  | intro q hq =>
      cases y.open_upward q hq.left with
      | intro r hr =>
          exists qreal r
          constructor
          · constructor
            · intro s hs
              cases QRat.lt_trichotomy s r with
              | inl hsr =>
                  exact hsr
              | inr hrest =>
                  cases hrest with
                  | inl hsrEq =>
                      rw [hsrEq] at hs
                      exact False.elim (hq.right
                        (x.downward_closed q r hr.left hs))
                  | inr hrs =>
                      have hqs : q < s := QRat.lt_trans hr.left hrs
                      exact False.elim (hq.right
                        (x.downward_closed q s hqs hs))
            · exact Exists.intro q (And.intro hr.left hq.right)
          · constructor
            · intro s hsr
              exact y.downward_closed s r hsr hr.right
            · cases y.open_upward r hr.right with
              | intro t ht =>
                  exact Exists.intro t
                    (And.intro ht.right (QRat.lt_asymm ht.left))

theorem exists_between {x y : Real} (h : x < y) :
    exists z : Real, x < z ∧ z < y :=
  density h

end Real

end Foundation
end FoC
