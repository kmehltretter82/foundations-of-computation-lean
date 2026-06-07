import FoC.Foundation.Logic
import FoC.Foundation.Lists
import FoC.Foundation.Sets
import FoC.Foundation.Functions
import FoC.Foundation.Finite
import FoC.Foundation.Countable
import FoC.Foundation.Relations
import FoC.Foundation.Arithmetic
import FoC.Foundation.Summation
import FoC.Foundation.Integers
import FoC.Foundation.Rationals
import FoC.Foundation.RationalCore
import FoC.Foundation.QuotientRationals
import FoC.Foundation.Reals
import FoC.Foundation.QuadraticSurd
import FoC.Foundation.DigitStreams
import FoC.Foundation.RealUncountability
import FoC.Foundation.Primes
import FoC.Foundation.Cardinality
import FoC.Languages.Words
import FoC.Languages.Language
import FoC.Languages.RegularExpression
import FoC.Languages.DFA
import FoC.Languages.NFA
import FoC.Languages.NFAPath
import FoC.Languages.Thompson
import FoC.Languages.Regular
import FoC.Languages.Pumping
import FoC.Grammars.CFG
import FoC.Grammars.CFL
import FoC.Grammars.RightRegular
import FoC.Grammars.BNF
import FoC.Grammars.ParseTree
import FoC.Grammars.PDA
import FoC.Grammars.PDANormalize
import FoC.Grammars.GeneralGrammar
import FoC.Computability.Tape
import FoC.Computability.TuringMachine
import FoC.Computability.Computable
import FoC.Computability.Recognizable
import FoC.Computability.Enumerable
import FoC.Computability.Undecidable
import FoC.Computability.Coding
import FoC.Computability.Encoding
import FoC.Computability.Compiler
import FoC.Computability.FiniteProgram
import FoC.Foundation
import FoC.Languages
import FoC.Grammars
import FoC.Computability
import FoC.Book

set_option doc.verso true

/-!
# Foundations of Computation Lean Companion

## What this site is

This is a Lean 4 companion to the textbook
[Foundations of Computation](https://math.hws.edu/FoundationsOfComputation/),
Second Edition, Version 2.3.2, by Carol Critchlow and David Eck. The textbook is
the source for exposition, motivation, and exercises. This site shows the
checked Lean development that follows the book's mathematical and computational
content.

The pages here are generated directly from the source files. That matters:
after each explanatory note, the definitions and theorems you see are the
actual declarations checked by Lean. Module links lead to neighboring parts of
the development, and declaration links let you inspect the exact statement that
supports a chapter claim.

This formalization is not a copy of the textbook text. It is a companion layer:
it explains how the ideas are represented in Lean, records which parts have
been formalized, and exposes the reusable API used to state and prove the
book-facing results.

## How to read it

There are two useful paths through the site.

* Follow {module -checked}`FoC.Book` if you want textbook order. These modules
  mirror the chapters and sections, state book-facing definitions and theorems,
  and point back to reusable constructions when a section relies on larger
  infrastructure.
* Follow the reusable libraries if you want the formal API. These modules are
  organized by mathematical role rather than by chapter, so they are the right
  place to inspect definitions, closure constructions, machine semantics, and
  proof infrastructure.

When reading a declaration, focus first on the type. A theorem's type is the
checked mathematical statement; the proof term below it is the certificate that
Lean accepted. Many chapter pages include short wrappers around reusable
theorems so that the statement appears under a textbook-coordinate name.

## Library map

The reusable infrastructure is split into four large layers.

* {module}`FoC.Foundation` develops the logic, set, function, relation,
  arithmetic, finite, countable, rational, real-number, prime-number, and
  diagonalization vocabulary used by the early chapters.
* {module}`FoC.Languages` treats words as lists, languages as predicates, and
  regular languages through regular expressions, finite automata, Thompson
  construction, closure operations, state elimination, and pumping arguments.
* {module}`FoC.Grammars` develops context-free grammars, BNF expression
  semantics, parse trees, pushdown automata, CFG/PDA conversions, CFL pumping,
  and unrestricted grammars.
* {module}`FoC.Computability` builds the Chapter 5 layer: Turing-machine tapes,
  configurations, computations, total and partial computability,
  recognizability, enumerability, staged programs, finite machine descriptions,
  compiler bridges, reductions, diagonalization, and halting-problem
  vocabulary.

## Chapter route

The chapter-facing pages collect the formal statements in the order a textbook
reader expects.

* {module}`FoC.Book.Chapter01` covers propositional logic, Boolean algebra,
  predicates, deduction, proof methods, induction, recursion, finite sums,
  divisibility, primes, and Fibonacci estimates.
* {module}`FoC.Book.Chapter02` covers sets, functions, relations, finite and
  countable collections, quotient rationals, Dedekind-cut reals, and
  diagonalization.
* {module}`FoC.Book.Chapter03` covers languages, regular expressions, finite
  automata, regular-language closure, state elimination, and non-regularity via
  pumping arguments.
* {module}`FoC.Book.Chapter04` covers context-free grammars, BNF, parse trees,
  pushdown automata, grammar/automaton conversions, CFL pumping, and general
  grammars.
* {module}`FoC.Book.Chapter05` covers Turing machines, computable functions,
  decidable and recursively enumerable languages, compiler and encoding
  surfaces, reductions, diagonalization, and the halting problem.

The current coverage classification is maintained in the repository's
{lit}`data/coverage.yaml`. It distinguishes the checked formal core from
application examples, drawings, language-specific programming details, and
larger construction surfaces that are intentionally recorded as conditional
theorem shapes.

## Design notes

The project is intentionally self-contained. It does not depend on Mathlib,
CSLib, or other external Lean libraries; the development builds its own small
vocabulary for the book's purposes. Verso is used only to render this in-source
literate HTML companion.

Source code and issue tracking are available in the
[GitHub repository](https://github.com/kmehltretter82/foundations-of-computation-lean).

This formalization is distributed under the Creative Commons
Attribution-NonCommercial-ShareAlike 4.0 International License; see the
[license file](https://github.com/kmehltretter82/foundations-of-computation-lean/blob/main/LICENSE.md)
and [notice file](https://github.com/kmehltretter82/foundations-of-computation-lean/blob/main/NOTICE.md)
for details.
-/
