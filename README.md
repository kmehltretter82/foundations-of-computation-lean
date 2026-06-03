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
  rational representatives, Dedekind-cut real numbers with rational embedding
  and order/density plus cut addition/subtraction/multiplication and rational
  powers, rational scaling, embedded-rational division, concrete square-root cut
  candidates, reduced rational and quotient-rational square-root contradiction
  cores, real square-characterization irrationality bridges, quadratic-surd
  surrogates, and digit-stream diagonalization with real and irrational-real
  uncountability.
- context-free grammars, parse trees, pushdown automata, and general grammars.
- Turing-machine tapes, configurations, computations, and computability
  vocabulary.

Build with:

```sh
lake build
```

Build the in-source literate HTML companion with Verso:

```sh
lake build :literateHtml
```

The generated site is written to `.lake/build/literate-html/`. For local
preview, serve it over HTTP rather than opening files directly:

```sh
python3 -m http.server 8000 --directory .lake/build/literate-html
```

Then open <http://localhost:8000/>.

GitHub Pages builds the same site from source with the workflow in
`.github/workflows/verso-literate-pages.yml`.

## License

This repository is distributed under the Creative Commons
Attribution-NonCommercial-ShareAlike 4.0 International License. See
[LICENSE.md](LICENSE.md) and [NOTICE.md](NOTICE.md).
