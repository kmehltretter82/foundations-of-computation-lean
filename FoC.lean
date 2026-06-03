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
import FoC.Foundation
import FoC.Languages
import FoC.Grammars
import FoC.Computability
import FoC.Book.Chapter01
import FoC.Book.Chapter02
import FoC.Book.Chapter03
import FoC.Book.Chapter04
import FoC.Book.Chapter05

set_option doc.verso true

/-!
# Foundations of Computation Lean Companion

This Lean library is an in-source companion to the textbook Foundations of
Computation. The rendered HTML site uses Verso to show the actual formalization
files, enriched with short explanations, book coordinates, links between
definitions, and proof-state information.

The original textbook is
[Foundations of Computation](https://math.hws.edu/FoundationsOfComputation/),
Second Edition, Version 2.3.2, by Carol Critchlow and David Eck. This Lean
project is a companion formalization; it is not a replacement for the textbook
and does not copy the book text.

The `FoC.Book` modules are organized in the order of the textbook. They state
the book-facing definitions and theorems. The reusable infrastructure lives in
the foundation, language, grammar, and computability modules:

* {module}`FoC.Foundation` develops the logic, set, function, arithmetic,
  rational, real-number, countability, and relation vocabulary used by the early
  chapters.
* {module}`FoC.Languages` contains words, languages, regular expressions,
  finite automata, regular-language constructions, and pumping-style material.
* {module}`FoC.Grammars` contains context-free grammars, parse trees, pushdown
  automata, and grammar-automaton conversions.
* {module}`FoC.Computability` contains Turing-machine tapes, configurations,
  computations, computability, recognizability, enumerability, and
  undecidability vocabulary.

The goal of the companion is not to copy the textbook. It explains how the
mathematical and computational ideas are represented in Lean, then lets the
reader inspect the checked statements and proofs directly.

Source code and issue tracking are available in the
[GitHub repository](https://github.com/kmehltretter82/foundations-of-computation-lean).

This formalization is distributed under the Creative Commons
Attribution-NonCommercial-ShareAlike 4.0 International License; see the
[license file](https://github.com/kmehltretter82/foundations-of-computation-lean/blob/main/LICENSE.md)
and [notice file](https://github.com/kmehltretter82/foundations-of-computation-lean/blob/main/NOTICE.md)
for details.
-/
