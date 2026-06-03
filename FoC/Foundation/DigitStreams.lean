import FoC.Foundation.Countable

set_option doc.verso true

/-!
# Binary digit streams

## Diagonal streams

This module provides the formal core of the book's real-number diagonal
argument.  `FoC.Foundation.RealUncountability` injects these streams into the
Dedekind-cut real type and transports this theorem to real uncountability.

## Book coordinates

Used by:
- Chapter 2, Section 2.6: real-number uncountability diagonal argument
- {lit}`Real` bridge: uncountability of an interval and of {lit}`Real`
-/

namespace FoC
namespace Foundation

/-!
# Stream type

A digit stream is an infinite Boolean sequence indexed by natural numbers.
-/

def DigitStream : Type :=
  Nat -> Bool

namespace DigitStream

/-!
# Diagonal construction

Given a partial enumeration of streams, the diagonal stream flips the bit at
position {lit}`n` of the {lit}`n`th listed stream.
-/

def diagonal (f : Nat -> Option DigitStream) : DigitStream :=
  fun n =>
    match f n with
    | some s => !s n
    | none => true

theorem diagonal_differs_at {f : Nat -> Option DigitStream}
    {n : Nat} {s : DigitStream} (h : f n = some s) :
    diagonal f n ≠ s n := by
  simp [diagonal, h]

/-!
# Uncountability of streams

The diagonal stream belongs to the universal set of streams but differs from
every stream listed by the alleged enumeration.
-/

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
