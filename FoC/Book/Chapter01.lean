import FoC.Foundation
import FoC.Book.Chapter01.Section01
import FoC.Book.Chapter01.Section02
import FoC.Book.Chapter01.Section03
import FoC.Book.Chapter01.Section04
import FoC.Book.Chapter01.Section05
import FoC.Book.Chapter01.Section06
import FoC.Book.Chapter01.Section07
import FoC.Book.Chapter01.Section08
import FoC.Book.Chapter01.Section09
import FoC.Book.Chapter01.Section10

set_option doc.verso true

/-!
# Chapter 1: Logic and Proof

Chapter 1 is where the companion establishes the habit that every later chapter
uses: informal mathematical claims are translated into precise Lean statements,
and proof techniques become reusable theorem patterns.

The reusable definitions are mostly in {module}`FoC.Foundation`. The section
modules keep statements close to the book coordinates, while still using Lean
definitions that later chapters can reuse.

## Story of the Chapter

The chapter begins with truth-table semantics for propositional formulas, then
uses those semantics to explain Boolean algebra and deduction rules. The middle
sections shift from symbolic logic to proof patterns: direct proof,
contradiction, induction, and recursive definitions. The final sections use the
same methods on small mathematical objects such as parity predicates, rational
representations, finite sums, Fibonacci numbers, and binary trees.

## What to Inspect

Start with {module}`FoC.Book.Chapter01.Section01` and
{module}`FoC.Foundation.Logic` for the logic syntax and semantics. Then compare
the proof-method sections with the arithmetic support files:
{module}`FoC.Foundation.Arithmetic`, {module}`FoC.Foundation.Integers`,
{module}`FoC.Foundation.Primes`, and {module}`FoC.Foundation.Summation`.

Many short proofs are truth-table splits or induction, so the important content
is often the theorem type itself. It tells which informal statement has been
formalized, while the proof shows that Lean can check the required cases.

## Status Notes

The formal core of the chapter is covered. Coverage records a few intentional
deferrals for application-style material such as circuit drawings and some
exercise-specific presentation details. The finite-cardinality pigeonhole
principle and direct square-equation irrationality bridges are now checked; the
remaining mathematical deferral is the concrete square equality for the
Dedekind-cut square-root candidates. The logical, arithmetic, induction, and
recursive-definition machinery is present in checked form.
-/
