import FoC.Foundation.Countable

namespace FoC
namespace Foundation

/-!
Cantor diagonalization for binary digit streams.

This module provides the formal core of the book's real-number diagonal
argument without committing to a full real-number construction.  A future
`Real` module can prove that suitable digit streams inject into the real
interval `[0,1]`, then transport this uncountability theorem to reals.

Used by:
- Chapter 2, Section 2.6: real-number uncountability diagonal argument
- Future `Real` bridge: uncountability of an interval and of `Real`
-/

def DigitStream : Type :=
  Nat -> Bool

namespace DigitStream

def diagonal (f : Nat -> Option DigitStream) : DigitStream :=
  fun n =>
    match f n with
    | some s => !s n
    | none => true

theorem diagonal_differs_at {f : Nat -> Option DigitStream}
    {n : Nat} {s : DigitStream} (h : f n = some s) :
    diagonal f n ≠ s n := by
  simp [diagonal, h]

theorem uncountable_univ :
    FSet.Uncountable (FSet.Univ : FSet DigitStream) := by
  intro hcount
  cases hcount with
  | intro f hf =>
      let d := diagonal f
      have hd : d ∈ (FSet.Univ : FSet DigitStream) := True.intro
      have hlisted := (hf d).mp hd
      cases hlisted with
      | intro n hn =>
          exact diagonal_differs_at (f := f) (n := n) (s := d) hn rfl

end DigitStream

end Foundation
end FoC
