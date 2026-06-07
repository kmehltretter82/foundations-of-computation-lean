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

The formal core of the chapter is covered. The propositional-logic and Boolean
algebra sections include truth-table equivalences, substitution laws, NOR
expressibility, and circuit/formula bridges. The circuit section now also links
the full-adder DNF tables to compact XOR and carry formulas, so the table,
formula, and gate-reading presentations are checked against one another.

The proof sections cover parity, divisibility, rational closure, irrational
real examples, contradiction, pigeonhole, induction, finite sums, recursive
definitions, Hanoi move counts, and binary-tree recursions. Recent cleanup
adds explicit odd-plus-odd, odd-times-odd, and even-sum induction wrappers.

Remaining deferrals are intentionally presentational: drawn circuit layouts,
long exercise lists whose Lean counterparts are already represented by more
general theorem schemas, and informal prose about proof-writing style.
-/
