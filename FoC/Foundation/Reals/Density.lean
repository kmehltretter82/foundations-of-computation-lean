import FoC.Foundation.Reals.SquareRoots

set_option doc.verso true

/-!
# Density of Dedekind reals

The theorem in this module constructs an embedded rational strictly between
any two ordered Dedekind cuts.
-/

namespace FoC
namespace Foundation
namespace Real

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
end Real
end Foundation
end FoC
