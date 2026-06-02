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
