import FoC.Foundation.Sets
import FoC.Foundation.Finite

namespace FoC
namespace Foundation

/-!
Countability via explicit partial enumerations by natural numbers.
-/

namespace FSet

def EnumeratedBy (A : FSet alpha) (f : Nat -> Option alpha) : Prop :=
  forall x, x ∈ A <-> exists n, f n = some x

def Countable (A : FSet alpha) : Prop :=
  exists f : Nat -> Option alpha, EnumeratedBy A f

def CountablyInfinite (A : FSet alpha) : Prop :=
  Countable A ∧ ¬ Finite A

theorem empty_countable : Countable (Empty : FSet alpha) := by
  exists fun _ => none
  intro x
  constructor
  · intro hx
    cases hx
  · intro hx
    cases hx with
    | intro n hn =>
        cases hn

end FSet

end Foundation
end FoC

