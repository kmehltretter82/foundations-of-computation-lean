# Foundations of Computation Lean

Standalone Lean formalization companion for the textbook *Foundations of
Computation*, Second Edition, Version 2.3.2.

Source textbook metadata:

- Textbook website: <https://math.hws.edu/FoundationsOfComputation/>
- Authors: Carol Critchlow and David Eck
- Affiliation: Hobart and William Smith Colleges
- Copyright year: 2011
- Publisher: Carol Critchlow and David Eck
- Language: English

This project is intentionally self-contained: it does not depend on Mathlib,
CSLib, or other external Lean libraries.

This formalization was developed with assistance from OpenAI Codex.

Current status: standalone foundation layer plus the Chapter 1, Chapter 2,
Chapter 3, Chapter 4, and Chapter 5 formal cores. Chapter 1 is represented by proved Lean modules for all
ten sections, including expanded Section 1.1 truth-table wrappers, NOR-only
operator encodings, Euclid's prime-list argument, a pigeonhole collision
schema, generalized natural-number geometric sums, and a scaled Fibonacci lower
bound. Chapter 2 adds proved modules for set operations, Boolean algebra
of sets, functions, countability examples, Cantor's theorem, relations,
equivalence classes, partitions, and a small relational-database model. Chapter
2 also includes countable-union and uncountable-difference theorems by explicit
enumeration. Chapter 3 adds words, languages, regular expressions, DFA/NFA semantics, Thompson
regular-expression-to-NFA construction, subset construction, automata closure
constructions, pumping-lemma vocabulary, and count groundwork for the
`a^n b^n` example. Chapter 4 adds context-free grammar derivations, CFG
construction lemmas, BNF expansion vocabulary, parse trees, an explicit
ambiguous-grammar witness, pushdown automata, context-free pumping vocabulary,
and general grammars.
Chapter 5 adds finite-window Turing-machine tapes, deterministic one-tape
machines, configurations, step and multi-step computation, halting/output,
Turing-computable functions, decidable and acceptable languages, recursive and
recursively enumerable vocabulary, enumeration/range formulations, and
undecidability vocabulary, including decidable-language complement closure and
an abstract diagonal contradiction core.
The foundation layer also includes quotient rational numbers over
positive-denominator integer fractions, future-real-compatible reduced rational
representatives for the square-root irrationality arguments, a tiny quadratic
surd surrogate for the `sqrt(2)` product counterexample, and binary digit-stream
diagonalization for the real-uncountability argument.
Prose-heavy application exercises and results requiring future
full real-number, numeric-cardinality, full state-elimination, or pumping-lemma,
full CFG/PDA-equivalence, and machine-encoding/simulation infrastructure are not
represented as placeholder theorems.

Coverage status is tracked in [data/coverage.yaml](data/coverage.yaml).

Foundation modules currently include:

- propositional-formula syntax and semantics,
- small list enumeration helpers,
- sets as predicates,
- function vocabulary,
- finite sets and finite types by list enumeration,
- countability by partial natural-number enumeration,
- binary relations,
- basic arithmetic predicates for divisibility, parity, and proof examples.
- words and languages as lists and predicates,
- regular-expression syntax and denotational semantics,
- deterministic and nondeterministic finite-state automata,
- NFA path semantics and Thompson construction for regular expressions.
- quotient rational arithmetic, order, density, embeddings from existing
  rational representatives, reduced rational square-root contradiction cores,
  quadratic-surd surrogates, and digit-stream diagonalization.
- context-free grammars, parse trees, pushdown automata, and general grammars.
- Turing-machine tapes, configurations, computations, and computability
  vocabulary.

Build with:

```sh
lake build
```

## License

This repository is distributed under the Creative Commons
Attribution-NonCommercial-ShareAlike 4.0 International License. See
[LICENSE.md](LICENSE.md) and [NOTICE.md](NOTICE.md).
