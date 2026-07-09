import FoC.Book.Chapter04.Section06.UnarySquares.Basic
import FoC.Book.Chapter04.Section06.UnarySquares.Shape
import FoC.Book.Chapter04.Section06.UnarySquares.Potential
import FoC.Book.Chapter04.Section06.UnarySquares.PostStop
import FoC.Book.Chapter04.Section06.UnarySquares.Reachability
import FoC.Book.Chapter04.Section06.UnarySquares.FourAs

set_option doc.verso true

/-!
# Section 4.6 unary squares

Book: Section 4.6, third sample grammar (the unary-square language
{lit}`a^(n^2)`) together with Exercise 1's derivation of {lit}`aaaa`.

This module re-exports the split unary-square grammar development: grammar
definitions, shared count and occurrence lemmas, the potential function and
post-stop invariants, the reachability proof of the exact generated language,
and the concrete four-{lit}`a` derivation.
-/
