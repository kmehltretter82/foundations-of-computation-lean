import FoC.Foundation.QuotientRationals

namespace FoC
namespace Foundation

/-!
Dedekind-cut real numbers over quotient rationals.

This module is the first real-number layer needed by the book formalization.
It uses one-sided lower cuts over `QRat`: nonempty, proper, downward closed,
and open upward/no-greatest-element.  Arithmetic on cuts is intentionally left
to later phases; this phase establishes rational embeddings, order, density,
and rational/irrational predicates.

Used by:
- Future Chapter 1 real-number wrappers for density and irrational examples
- Future square-root cuts and irrationality transport
- Future Chapter 2 real-number uncountability bridge
-/

structure Real where
  lower : QRat -> Prop
  nonempty : exists q, lower q
  proper : exists q, ¬ lower q
  downward_closed : forall q r, q < r -> lower r -> lower q
  open_upward : forall q, lower q -> exists r, q < r ∧ lower r

namespace Real

theorem ext {x y : Real} (h : forall q, x.lower q <-> y.lower q) : x = y := by
  cases x with
  | mk xl xn xp xd xo =>
      cases y with
      | mk yl yn yp yd yo =>
          have hfun : xl = yl := by
            funext q
            exact propext (h q)
          subst hfun
          rfl

theorem lower_congr {x y : Real} (h : x = y) (q : QRat) :
    x.lower q <-> y.lower q := by
  rw [h]

def qreal (r : QRat) : Real where
  lower := fun q => q < r
  nonempty := by
    cases QRat.exists_lower_upper r with
    | intro l hrest =>
        cases hrest with
        | intro u hbounds =>
            exact Exists.intro l hbounds.left
  proper := by
    exact Exists.intro r (QRat.lt_irrefl r)
  downward_closed := by
    intro q s hqs hsr
    exact QRat.lt_trans hqs hsr
  open_upward := by
    intro q hqr
    cases QRat.density hqr with
    | intro s hs =>
        exact Exists.intro s hs

theorem qreal_lower_iff (r q : QRat) :
    (qreal r).lower q <-> q < r :=
  Iff.rfl

theorem qreal_lower {r q : QRat} (h : q < r) :
    (qreal r).lower q :=
  h

instance : Zero Real where
  zero := qreal 0

instance : One Real where
  one := qreal 1

instance : OfNat Real n where
  ofNat := qreal (QRat.ofNat n)

instance : IntCast Real where
  intCast n := qreal (QRat.ofInt n)

def le (x y : Real) : Prop :=
  forall q, x.lower q -> y.lower q

def lt (x y : Real) : Prop :=
  le x y ∧ exists q, y.lower q ∧ ¬ x.lower q

instance : LE Real where
  le := le

instance : LT Real where
  lt := lt

theorem le_def (x y : Real) :
    x ≤ y <-> forall q, x.lower q -> y.lower q :=
  Iff.rfl

theorem lt_def (x y : Real) :
    x < y <-> x ≤ y ∧ exists q, y.lower q ∧ ¬ x.lower q :=
  Iff.rfl

theorem le_refl (x : Real) : x ≤ x := by
  intro q hq
  exact hq

theorem le_trans {x y z : Real} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  intro q hq
  exact hyz q (hxy q hq)

theorem le_antisymm {x y : Real} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  apply ext
  intro q
  constructor
  · exact hxy q
  · exact hyx q

theorem lt_irrefl (x : Real) : ¬ x < x := by
  intro h
  cases h.right with
  | intro q hq =>
      exact hq.right hq.left

theorem lt_asymm {x y : Real} (h : x < y) : ¬ y < x := by
  intro hyx
  cases h.right with
  | intro q hq =>
      exact hq.right (hyx.left q hq.left)

theorem lt_of_lt_of_le {x y z : Real} (hxy : x < y) (hyz : y ≤ z) : x < z := by
  constructor
  · exact le_trans hxy.left hyz
  · cases hxy.right with
    | intro q hq =>
        exact Exists.intro q (And.intro (hyz q hq.left) hq.right)

theorem lt_of_le_of_lt {x y z : Real} (hxy : x ≤ y) (hyz : y < z) : x < z := by
  constructor
  · exact le_trans hxy hyz.left
  · cases hyz.right with
    | intro q hq =>
        exact Exists.intro q (And.intro hq.left (fun hx => hq.right (hxy q hx)))

theorem lt_trans {x y z : Real} (hxy : x < y) (hyz : y < z) : x < z :=
  lt_of_lt_of_le hxy hyz.left

theorem qreal_le_of_qrat_lt_or_eq {a b : QRat} (h : a < b ∨ a = b) :
    qreal a ≤ qreal b := by
  intro q hqa
  cases h with
  | inl hab =>
      exact QRat.lt_trans hqa hab
  | inr heq =>
      rw [heq] at hqa
      exact hqa

theorem qreal_lt_of_qrat_lt {a b : QRat} (h : a < b) :
    qreal a < qreal b := by
  constructor
  · intro q hqa
    exact QRat.lt_trans hqa h
  · cases QRat.density h with
    | intro c hc =>
        exact Exists.intro c
          (And.intro hc.right (QRat.lt_asymm hc.left))

theorem qrat_lt_of_qreal_lt {a b : QRat} (h : qreal a < qreal b) :
    a < b := by
  cases h.right with
  | intro c hc =>
      cases QRat.lt_trichotomy a b with
      | inl hab =>
          exact hab
      | inr hrest =>
          cases hrest with
          | inl heq =>
              have hca : c < a := by
                rw [← heq] at hc
                exact hc.left
              exact False.elim (hc.right hca)
          | inr hba =>
              have hca : c < a := QRat.lt_trans hc.left hba
              exact False.elim (hc.right hca)

theorem qreal_lt_iff (a b : QRat) :
    qreal a < qreal b <-> a < b := by
  constructor
  · exact qrat_lt_of_qreal_lt
  · exact qreal_lt_of_qrat_lt

theorem qreal_injective : Fn.Injective qreal := by
  intro a b h
  cases QRat.lt_trichotomy a b with
  | inl hab =>
      have hlt : qreal a < qreal b := qreal_lt_of_qrat_lt hab
      rw [h] at hlt
      exact False.elim (lt_irrefl (qreal b) hlt)
  | inr hrest =>
      cases hrest with
      | inl heq =>
          exact heq
      | inr hba =>
          have hlt : qreal b < qreal a := qreal_lt_of_qrat_lt hba
          rw [h] at hlt
          exact False.elim (lt_irrefl (qreal b) hlt)

theorem qreal_eq_iff (a b : QRat) :
    qreal a = qreal b <-> a = b := by
  constructor
  · exact qreal_injective
  · intro h
    rw [h]

def Rational (x : Real) : Prop :=
  exists q : QRat, x = qreal q

def Irrational (x : Real) : Prop :=
  ¬ Rational x

theorem rational_qreal (q : QRat) : Rational (qreal q) := by
  exact Exists.intro q rfl

theorem rational_zero : Rational 0 := by
  exact rational_qreal 0

theorem rational_one : Rational 1 := by
  exact rational_qreal 1

theorem qreal_order_embedding {a b : QRat} :
    qreal a < qreal b <-> a < b :=
  qreal_lt_iff a b

theorem qreal_order_preserving {a b : QRat} (h : a < b) :
    qreal a < qreal b :=
  qreal_lt_of_qrat_lt h

theorem qreal_order_reflecting {a b : QRat} (h : qreal a < qreal b) :
    a < b :=
  qrat_lt_of_qreal_lt h

def add (x y : Real) : Real where
  lower := fun q => exists a b, x.lower a ∧ y.lower b ∧ q < a + b
  nonempty := by
    cases x.nonempty with
    | intro a ha =>
        cases y.nonempty with
        | intro b hb =>
            cases QRat.exists_lower_upper (a + b) with
            | intro l hrest =>
                cases hrest with
                | intro _ hl =>
                    exact Exists.intro l
                      (Exists.intro a (Exists.intro b
                        (And.intro ha (And.intro hb hl.left))))
  proper := by
    cases x.proper with
    | intro ux hux =>
        cases y.proper with
        | intro uy huy =>
            exists ux + uy
            intro h
            cases h with
            | intro a hrest =>
                cases hrest with
                | intro b hbounds =>
                    have hax : a < ux := by
                      cases QRat.lt_trichotomy a ux with
                      | inl hlt =>
                          exact hlt
                      | inr hcases =>
                          cases hcases with
                          | inl heq =>
                              rw [← heq] at hux
                              exact False.elim (hux hbounds.left)
                          | inr huxlt =>
                              exact False.elim (hux
                                (x.downward_closed ux a huxlt hbounds.left))
                    have hby : b < uy := by
                      cases QRat.lt_trichotomy b uy with
                      | inl hlt =>
                          exact hlt
                      | inr hcases =>
                          cases hcases with
                          | inl heq =>
                              rw [← heq] at huy
                              exact False.elim (huy hbounds.right.left)
                          | inr huylt =>
                              exact False.elim (huy
                                (y.downward_closed uy b huylt hbounds.right.left))
                    exact QRat.lt_asymm hbounds.right.right (QRat.add_lt_add hax hby)
  downward_closed := by
    intro q r hqr hr
    cases hr with
    | intro a hrest =>
        cases hrest with
        | intro b hbounds =>
            exact Exists.intro a (Exists.intro b
              (And.intro hbounds.left
                (And.intro hbounds.right.left
                  (QRat.lt_trans hqr hbounds.right.right))))
  open_upward := by
    intro q hq
    cases hq with
    | intro a hrest =>
        cases hrest with
        | intro b hbounds =>
            cases QRat.density hbounds.right.right with
            | intro r hr =>
                exact Exists.intro r
                  (And.intro hr.left
                    (Exists.intro a (Exists.intro b
                      (And.intro hbounds.left
                        (And.intro hbounds.right.left hr.right)))))

def neg (x : Real) : Real where
  lower := fun q => exists r, ¬ x.lower r ∧ q < -r
  nonempty := by
    cases x.proper with
    | intro r hr =>
        cases QRat.exists_lower_upper (-r) with
        | intro l hrest =>
            cases hrest with
            | intro _ hl =>
                exact Exists.intro l
                  (Exists.intro r (And.intro hr hl.left))
  proper := by
    cases x.nonempty with
    | intro a ha =>
        exists -a
        intro h
        cases h with
        | intro r hr =>
            have hra : r < a := by
              have hneg := QRat.neg_lt_neg hr.right
              rwa [QRat.neg_neg, QRat.neg_neg] at hneg
            exact hr.left (x.downward_closed r a hra ha)
  downward_closed := by
    intro q s hqs hs
    cases hs with
    | intro r hr =>
        exact Exists.intro r
          (And.intro hr.left (QRat.lt_trans hqs hr.right))
  open_upward := by
    intro q hq
    cases hq with
    | intro r hr =>
        cases QRat.density hr.right with
        | intro s hs =>
            exact Exists.intro s
              (And.intro hs.left (Exists.intro r (And.intro hr.left hs.right)))

def sub (x y : Real) : Real :=
  add x (neg y)

instance : Add Real where
  add := add

instance : Neg Real where
  neg := neg

instance : Sub Real where
  sub := sub

theorem add_comm (x y : Real) : x + y = y + x := by
  apply ext
  intro q
  constructor
  · intro h
    cases h with
    | intro a hrest =>
        cases hrest with
        | intro b hbounds =>
            have hqba : q < b + a := by
              simpa [QRat.add_comm] using hbounds.right.right
            exact Exists.intro b (Exists.intro a
              (And.intro hbounds.right.left
                (And.intro hbounds.left hqba)))
  · intro h
    cases h with
    | intro b hrest =>
        cases hrest with
        | intro a hbounds =>
            have hqab : q < a + b := by
              simpa [QRat.add_comm] using hbounds.right.right
            exact Exists.intro a (Exists.intro b
              (And.intro hbounds.right.left
                (And.intro hbounds.left hqab)))

theorem add_qreal_lower_iff (x : Real) (q p : QRat) :
    (x + qreal q).lower p <-> x.lower (p - q) := by
  constructor
  · intro h
    cases h with
    | intro a hrest =>
        cases hrest with
        | intro b hbounds =>
            have habq : a + b < a + q :=
              QRat.add_lt_add_left a hbounds.right.left
            have hpaq : p < a + q :=
              QRat.lt_trans hbounds.right.right habq
            exact x.downward_closed (p - q) a
              (QRat.sub_lt_iff.mpr hpaq) hbounds.left
  · intro hp
    cases x.open_upward (p - q) hp with
    | intro a ha =>
        have hpaq : p < a + q := QRat.sub_lt_iff.mp ha.left
        have hpqa : p < q + a := by
          rwa [QRat.add_comm] at hpaq
        have hpa_lt_q : p - a < q := QRat.sub_lt_iff.mpr hpqa
        cases QRat.density hpa_lt_q with
        | intro b hb =>
            have hpab : p < a + b := by
              have hpba : p < b + a := QRat.sub_lt_iff.mp hb.left
              rwa [QRat.add_comm] at hpba
            exact Exists.intro a (Exists.intro b
              (And.intro ha.right (And.intro hb.right hpab)))

theorem qreal_add (r s : QRat) :
    qreal r + qreal s = qreal (r + s) := by
  apply ext
  intro p
  rw [add_qreal_lower_iff, qreal_lower_iff, qreal_lower_iff]
  exact QRat.sub_lt_iff

theorem qreal_neg (r : QRat) :
    -qreal r = qreal (-r) := by
  apply ext
  intro q
  constructor
  · intro h
    cases h with
    | intro a ha =>
        cases QRat.lt_trichotomy r a with
        | inl hra =>
            exact QRat.lt_trans ha.right (QRat.neg_lt_neg hra)
        | inr hrest =>
            cases hrest with
            | inl hraEq =>
                rw [hraEq]
                exact ha.right
            | inr har =>
                exact False.elim (ha.left har)
  · intro h
    exact Exists.intro r (And.intro (QRat.lt_irrefl r) h)

theorem neg_neg (x : Real) : -(-x) = x := by
  apply ext
  intro q
  constructor
  · intro h
    cases h with
    | intro r hr =>
        apply Classical.byContradiction
        intro hq
        have hrnq : r < -q := by
          have hneg := QRat.neg_lt_neg hr.right
          rwa [QRat.neg_neg] at hneg
        exact hr.left (Exists.intro q (And.intro hq hrnq))
  · intro hq
    cases x.open_upward q hq with
    | intro a ha =>
        exists -a
        constructor
        · intro hneg
          cases hneg with
          | intro s hs =>
              have hsa : s < a := by
                have hneglt := QRat.neg_lt_neg hs.right
                rwa [QRat.neg_neg, QRat.neg_neg] at hneglt
              exact hs.left (x.downward_closed s a hsa ha.right)
        · rw [QRat.neg_neg]
          exact ha.left

theorem qreal_sub (r s : QRat) :
    qreal r - qreal s = qreal (r - s) := by
  calc
    qreal r - qreal s = qreal r + -(qreal s) := rfl
    _ = qreal r + qreal (-s) := by rw [qreal_neg]
    _ = qreal (r + -s) := qreal_add r (-s)
    _ = qreal (r - s) := rfl

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
