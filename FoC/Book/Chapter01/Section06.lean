import FoC.Foundation.Arithmetic
import FoC.Book.Chapter01.Section01
import FoC.Book.Chapter01.Section02

namespace FoC
namespace Book
namespace Chapter01
namespace Section06

/-!
Book: Chapter 1, Section 1.6, Proof.
-/

open Foundation

-- Book: Chapter 1, Section 1.6, Exercise 2
theorem exercise_2_or_as_implication (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or p q)
      (PropForm.imp (PropForm.not p) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.6, Exercise 3
theorem exercise_3_or_implication (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.imp (PropForm.or p q) r)
      (PropForm.and (PropForm.imp p r) (PropForm.imp q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.6
theorem product_of_even_numbers_even (m n : Nat)
    (hm : NatPred.Even m) : NatPred.Even (m * n) := by
  cases hm with
  | intro k hk =>
      exists k * n
      rw [hk, Nat.mul_assoc]

-- Book: Chapter 1, Section 1.6
theorem product_even_if_right_even (m n : Nat)
    (hn : NatPred.Even n) : NatPred.Even (m * n) := by
  cases hn with
  | intro k hk =>
      exists m * k
      rw [hk]
      calc
        m * (2 * k) = (m * 2) * k := by rw [Nat.mul_assoc]
        _ = (2 * m) * k := by rw [Nat.mul_comm m 2]
        _ = 2 * (m * k) := by rw [Nat.mul_assoc]

end Section06
end Chapter01
end Book
end FoC
