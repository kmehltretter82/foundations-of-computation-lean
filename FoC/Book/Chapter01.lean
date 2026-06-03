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

The Chapter 1 files are book-indexed entry points for the formalized core of
the textbook's introduction to propositional logic, predicate logic, proof
methods, induction, elementary number theory examples, finite sums, recursion,
and Fibonacci estimates.

The reusable definitions are mostly in {module}`FoC.Foundation`. These section
modules keep the statements close to the book coordinates, while still using
Lean definitions that can be reused by later chapters.

The chapter begins with truth-table semantics for propositional formulas, then
uses those semantics to explain Boolean algebra and deduction rules. The middle
sections shift from symbolic logic to proof patterns: direct proof,
contradiction, induction, and recursive definitions. The final sections use the
same methods on small mathematical objects such as parity predicates, rational
representations, finite sums, Fibonacci numbers, and binary trees.

When reading a section page, the definitions name the book concepts and the
theorems record the examples or laws. Many short proofs are truth-table splits
or induction, so the important content is usually the type of the declaration:
it tells which informal statement has been formalized.
-/
