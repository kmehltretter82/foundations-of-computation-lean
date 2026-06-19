set_option doc.verso true

/-!
# Natural-number divisibility and parity

## Divisibility and parity

This module supplies the elementary natural-number predicates used by the proof
examples in Chapter 1.  Divisibility is represented directly by an existential
factor, and evenness and oddness are phrased in terms of that representation.

The statements here are deliberately small: they are the reusable arithmetic
facts needed by the book-facing files, not a replacement for a full arithmetic
library.
-/

namespace FoC
namespace Foundation

namespace NatPred

/-!
# Natural-number predicates

Divisibility is represented by an explicit factor.  The even and odd predicates
are then phrased in the same elementary language used by the textbook examples.
-/

def Divides (a b : Nat) : Prop :=
  exists k, b = a * k

def Even (n : Nat) : Prop :=
  Divides 2 n

def Odd (n : Nat) : Prop :=
  exists k, n = 2 * k + 1

end NatPred

end Foundation
end FoC
