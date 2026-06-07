import FoC.Foundation.QuotientRationals

set_option doc.verso true

/-!
# Dedekind-cut real numbers

## Dedekind cuts

This module is the first real-number layer needed by the book formalization. It
uses one-sided lower cuts over {lit}`QRat`: nonempty, proper, downward closed,
and open upward with no greatest element.  It establishes rational embeddings,
order, density, cut addition/subtraction/multiplication, rational scaling, and
rational/irrational predicates.

## Book coordinates

Used by:
- Chapter 1 real-number wrappers for density and irrational examples
- Square-root cuts and square-equality irrationality transport
- Chapter 2 real-number uncountability bridge
-/

namespace FoC
namespace Foundation

/-!
# Lower cuts

A real is a lower set of quotient rationals with the usual Dedekind-cut
conditions: inhabited, proper, downward closed, and with no greatest lower
element.
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

/-!
# Rational embedding

The embedding {lit}`qreal r` is the cut of rationals strictly below {lit}`r`.
The surrounding lemmas show that equality and order of embedded rationals
reflect quotient-rational equality and order.
-/

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

/-!
# Order and rationality

Real order is inclusion of lower cuts. Strict order is proper inclusion, and the
rationality predicate records exactly those cuts that come from {lit}`qreal`.
-/

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

theorem qreal_nonneg_iff (r : QRat) :
    (0 : Real) ≤ qreal r <-> ¬ r < 0 := by
  constructor
  · intro h hr0
    have hrr : (qreal r).lower r := h r hr0
    exact QRat.lt_irrefl r hrr
  · intro hr q hq0
    cases QRat.lt_trichotomy q r with
    | inl hqr =>
        exact hqr
    | inr hrest =>
        cases hrest with
        | inl hqrEq =>
            rw [hqrEq] at hq0
            exact False.elim (hr hq0)
        | inr hrq =>
            exact False.elim (hr (QRat.lt_trans hrq hq0))

theorem lower_lt_of_not_lower {x : Real} {a u : QRat}
    (ha : x.lower a) (hu : ¬ x.lower u) : a < u := by
  cases QRat.lt_trichotomy a u with
  | inl hau =>
      exact hau
  | inr hrest =>
      cases hrest with
      | inl hauEq =>
          exact False.elim (hu (by rwa [hauEq] at ha))
      | inr hua =>
          exact False.elim (hu (x.downward_closed u a hua ha))

/-!
# Cut arithmetic

Arithmetic is defined directly on cuts, then related back to rational
arithmetic. These definitions support the book-facing real-number examples
without importing a larger real-number development.
-/

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

theorem nonneg_neg_of_not_nonneg {x : Real}
    (hx : ¬ (0 : Real) ≤ x) : (0 : Real) ≤ -x := by
  classical
  have hw : exists r : QRat, r < 0 ∧ ¬ x.lower r := Classical.byContradiction (by
    intro hnone
    apply hx
    intro r hr0
    exact Classical.byContradiction (by
      intro hxr
      exact hnone (Exists.intro r (And.intro hr0 hxr))))
  intro q hq0
  cases hw with
  | intro r hr =>
      exact Exists.intro r
        (And.intro hr.right (QRat.lt_trans hq0 (QRat.neg_pos_of_neg hr.left)))

theorem exists_pos_not_lower_of_nonneg {x : Real}
    (_hx : (0 : Real) ≤ x) : exists u : QRat, 0 < u ∧ ¬ x.lower u := by
  cases x.proper with
  | intro u hu =>
      cases QRat.lt_trichotomy 0 u with
      | inl h0u =>
          exact Exists.intro u (And.intro h0u hu)
      | inr hrest =>
          cases QRat.exists_lower_upper (0 : QRat) with
          | intro _ hvrest =>
              cases hvrest with
              | intro v hv =>
                  exists v
                  constructor
                  · exact hv.right
                  · intro hvx
                    cases hrest with
                    | inl h0uEq =>
                        have h0x : x.lower 0 :=
                          x.downward_closed 0 v hv.right hvx
                        exact hu (by simpa [← h0uEq] using h0x)
                    | inr hu0 =>
                        exact hu (x.downward_closed u v
                          (QRat.lt_trans hu0 hv.right) hvx)

def mulNonneg (x y : Real)
    (hx : (0 : Real) ≤ x) (hy : (0 : Real) ≤ y) : Real where
  lower := fun q =>
    q < 0 ∨ exists a b,
      0 < a ∧ 0 < b ∧ x.lower a ∧ y.lower b ∧ q < a * b
  nonempty := by
    cases QRat.exists_lower_upper (0 : QRat) with
    | intro l hrest =>
        cases hrest with
        | intro _ hbounds =>
            exact Exists.intro l (Or.inl hbounds.left)
  proper := by
    cases exists_pos_not_lower_of_nonneg hx with
    | intro ux hux =>
        cases exists_pos_not_lower_of_nonneg hy with
        | intro uy huy =>
            exists ux * uy
            intro h
            cases h with
            | inl hneg =>
                exact QRat.lt_asymm (QRat.mul_pos hux.left huy.left) hneg
            | inr hprod =>
                cases hprod with
                | intro a harest =>
                    cases harest with
                    | intro b hbounds =>
                        have haux : a < ux :=
                          lower_lt_of_not_lower hbounds.right.right.left hux.right
                        have hbuy : b < uy :=
                          lower_lt_of_not_lower hbounds.right.right.right.left huy.right
                        have habuxuy : a * b < ux * uy :=
                          QRat.mul_lt_mul_of_pos haux hbuy
                            hbounds.left hbounds.right.left
                        exact QRat.lt_asymm hbounds.right.right.right.right habuxuy
  downward_closed := by
    intro q r hqr hr
    cases hr with
    | inl hr0 =>
        exact Or.inl (QRat.lt_trans hqr hr0)
    | inr hprod =>
        cases hprod with
        | intro a harest =>
            cases harest with
            | intro b hbounds =>
                exact Or.inr (Exists.intro a (Exists.intro b
                  (And.intro hbounds.left
                    (And.intro hbounds.right.left
                      (And.intro hbounds.right.right.left
                        (And.intro hbounds.right.right.right.left
                          (QRat.lt_trans hqr hbounds.right.right.right.right)))))))
  open_upward := by
    intro q hq
    cases hq with
    | inl hq0 =>
        cases QRat.density hq0 with
        | intro r hr =>
            exact Exists.intro r (And.intro hr.left (Or.inl hr.right))
    | inr hprod =>
        cases hprod with
        | intro a harest =>
            cases harest with
            | intro b hbounds =>
                cases QRat.density hbounds.right.right.right.right with
                | intro r hr =>
                    exact Exists.intro r
                      (And.intro hr.left
                        (Or.inr (Exists.intro a (Exists.intro b
                          (And.intro hbounds.left
                            (And.intro hbounds.right.left
                              (And.intro hbounds.right.right.left
                                (And.intro hbounds.right.right.right.left hr.right))))))))

theorem mulNonneg_congr {x x' y y' : Real}
    (hxx : x = x') (hyy : y = y')
    (hx : (0 : Real) ≤ x) (hy : (0 : Real) ≤ y)
    (hx' : (0 : Real) ≤ x') (hy' : (0 : Real) ≤ y') :
    mulNonneg x y hx hy = mulNonneg x' y' hx' hy' := by
  cases hxx
  cases hyy
  apply ext
  intro q
  rfl

theorem qreal_mulNonneg {a b : QRat}
    (ha : (0 : Real) ≤ qreal a) (hb : (0 : Real) ≤ qreal b) :
    mulNonneg (qreal a) (qreal b) ha hb = qreal (a * b) := by
  apply ext
  intro q
  have hanna : ¬ a < 0 := (qreal_nonneg_iff a).mp ha
  have hannb : ¬ b < 0 := (qreal_nonneg_iff b).mp hb
  constructor
  · intro hq
    cases hq with
    | inl hq0 =>
        exact QRat.lt_of_lt_zero_of_not_lt_zero hq0
          (QRat.mul_nonneg hanna hannb)
    | inr hprod =>
        cases hprod with
        | intro c hcrest =>
            cases hcrest with
            | intro d hd =>
                have hcprod : c * d < a * b :=
                  QRat.mul_lt_mul_of_pos
                    hd.right.right.left
                    hd.right.right.right.left
                    hd.left
                    hd.right.left
                exact QRat.lt_trans hd.right.right.right.right hcprod
  · intro hq
    by_cases hq0 : q < 0
    · exact Or.inl hq0
    · have hprodpos : 0 < a * b :=
        QRat.zero_lt_of_not_lt_zero_of_lt hq0 hq
      have hapos : 0 < a :=
        QRat.pos_of_nonneg_mul_pos_left hanna hannb hprodpos
      have hbpos : 0 < b :=
        QRat.pos_of_nonneg_mul_pos_right hanna hannb hprodpos
      have hqdiva : q / b < a :=
        (QRat.div_lt_iff (x := q) (y := b) (c := a) hbpos).mpr hq
      cases QRat.density hqdiva with
      | intro c hc =>
          have hcpos : 0 < c :=
            QRat.zero_lt_of_not_lt_zero_of_lt
              (QRat.div_nonneg hq0 hbpos) hc.left
          have hqcb : q < c * b :=
            (QRat.div_lt_iff (x := q) (y := b) (c := c) hbpos).mp hc.left
          have hqdivb : q / c < b := by
            apply (QRat.div_lt_iff (x := q) (y := c) (c := b) hcpos).mpr
            simpa [QRat.mul_comm] using hqcb
          cases QRat.density hqdivb with
          | intro d hd =>
              have hdpos : 0 < d :=
                QRat.zero_lt_of_not_lt_zero_of_lt
                  (QRat.div_nonneg hq0 hcpos) hd.left
              have hqcd : q < c * d := by
                have hqdc : q < d * c :=
                  (QRat.div_lt_iff (x := q) (y := c) (c := d) hcpos).mp hd.left
                simpa [QRat.mul_comm] using hqdc
              exact Or.inr (Exists.intro c (Exists.intro d
                (And.intro hcpos
                  (And.intro hdpos
                    (And.intro hc.right
                      (And.intro hd.right hqcd))))))

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

theorem powNat_zero (x : Real) : powNat x 0 = 1 :=
  rfl

theorem powNat_succ (x : Real) (n : Nat) :
    powNat x (n + 1) = powNat x n * x :=
  rfl

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

theorem rational_powNat {x : Real} (n : Nat)
    (hx : Rational x) : Rational (powNat x n) := by
  cases hx with
  | intro q hxq =>
      exists QRat.powNat q n
      rw [hxq, qreal_powNat]

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

theorem rational_divByQ {x : Real} {q : QRat}
    (hq : q ≠ 0) (hx : Rational x) : Rational (divByQ x q hq) := by
  cases hx with
  | intro r hxr =>
      exists r / q
      rw [hxr, qreal_divByQ]

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
