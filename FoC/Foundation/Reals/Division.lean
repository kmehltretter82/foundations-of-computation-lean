import FoC.Foundation.Reals.Multiplication

set_option doc.verso true

/-!
# Dedekind-real division and rational scaling

This module develops cancellation and the two deliberately limited division
interfaces used by the book. It also defines rational scalar multiplication,
which supplies the implementation of division by a nonzero quotient rational.
The general selector is specified on exact products; this module does not claim
that arbitrary nonzero Dedekind cuts have multiplicative inverses.
-/

namespace FoC
namespace Foundation
namespace Real

/-!
**Nonzero division as a classical selector.** The theorem {name}`right_distrib`
and {name}`mul_ne_zero` turn equality after multiplication by a nonzero
denominator into cancellation. The quotient selector below uses classical
choice to pick a preimage under multiplication by the denominator, if one
exists, and returns {lit}`0` otherwise. Its specification applies to exact
products: for an actual product {lit}`a * d`, the selected quotient is the
original {lit}`a`. Existence
of multiplicative inverses for arbitrary nonzero cuts is not proved here, so
this is not total field division.
-/

theorem mul_right_cancel {a b d : Real} (hd : d ≠ 0)
    (h : a * d = b * d) : a = b := by
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

noncomputable def divByNonzero (num : Real) (d : Real) (_hd : d ≠ 0) : Real := by
  classical
  exact if h : exists q : Real, q * d = num then Classical.choose h else 0

theorem divByNonzero_mul_cancel (a d : Real) (hd : d ≠ 0) :
    divByNonzero (a * d) d hd = a := by
  classical
  unfold divByNonzero
  by_cases h : exists q : Real, q * d = a * d
  · simp [h]
    exact mul_right_cancel hd (Classical.choose_spec h)
  · exact False.elim (h ⟨a, rfl⟩)

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
          simpa [QRat.mul_comm] using! hr
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
end Real
end Foundation
end FoC
