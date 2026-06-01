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

Current status: standalone foundation layer plus the Chapter 1, Chapter 2, and
Chapter 3 formal cores. Chapter 1 is represented by proved Lean modules for all
ten sections. Chapter 2 adds proved modules for set operations, Boolean algebra
of sets, functions, countability examples, Cantor's theorem, relations,
equivalence classes, partitions, and a small relational-database model. Chapter
3 adds words, languages, regular expressions, DFA/NFA semantics, Thompson
regular-expression-to-NFA construction, subset construction, automata closure
constructions, and pumping-lemma vocabulary.
Prose-heavy application exercises and results requiring future
integer/rational/real-number, numeric-cardinality, full state-elimination, or
pumping-lemma infrastructure are not represented as placeholder theorems.

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

Build with:

```sh
lake build
```

## License

This repository is distributed under the Creative Commons
Attribution-NonCommercial-ShareAlike 4.0 International License. See
[LICENSE.md](LICENSE.md) and [NOTICE.md](NOTICE.md).
