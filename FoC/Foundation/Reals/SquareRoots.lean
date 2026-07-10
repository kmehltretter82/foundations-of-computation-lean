import FoC.Foundation.Reals.Division

set_option doc.verso true

/-!
# Dedekind-real square roots and irrationality

Square-root cuts are specified by rational square inequalities. The bridge
theorems turn quotient-rational no-square-root facts into real irrationality
statements. The concrete cut equalities for the square roots of two and three
use explicit quotient-rational approximants.
-/

namespace FoC
namespace Foundation
namespace Real

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
end Real
end Foundation
end FoC
