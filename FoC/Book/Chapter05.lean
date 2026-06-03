import FoC.Computability
import FoC.Book.Chapter05.Section01
import FoC.Book.Chapter05.Section02
import FoC.Book.Chapter05.Section03

set_option doc.verso true

/-!
# Chapter 5: Turing Machines and Computability

The Chapter 5 files are the book-facing layer for Turing-machine tapes,
configurations, computations, computability, recognizability, enumerability,
and undecidability vocabulary.

The reusable computability vocabulary lives in {module}`FoC.Computability`.
The companion rendering should help readers see how the informal computation
concepts are represented as Lean structures and predicates.

The section pages move from a concrete machine model to language-level notions.
A Turing machine has configurations and computations; a computable or
recognizable language is then a predicate for which some machine has the right
behavior. The final page abstracts further to reductions and diagonal
arguments, where the key statements are impossibility theorems rather than
machine constructions.
-/
