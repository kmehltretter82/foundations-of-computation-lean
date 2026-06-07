# Foundations of Computation Lean Companion

This is a standalone Lean 4 formalization companion for Carol Critchlow and
David Eck's textbook *Foundations of Computation*, Second Edition, Version
2.3.2.

The public reading experience is the rendered Verso site:

<https://kmehltretter82.github.io/foundations-of-computation-lean/>

The site is generated from the Lean source in this repository. It is meant to
be read beside the textbook, not instead of it: the textbook supplies the
exposition and exercises, while this project records checked definitions,
theorems, constructions, examples, and formal status notes.

## What This Project Does

The formalization follows the book's chapter order through a book-facing layer
under `FoC.Book`, while reusable mathematics and automata theory live in
separate library layers:

- `FoC.Foundation`: logic, sets, functions, relations, arithmetic, countability,
  rationals, Dedekind-cut reals, primes, and diagonal arguments.
- `FoC.Languages`: words, languages, regular expressions, DFA/NFA semantics,
  Thompson construction, regular-language closure, and pumping arguments.
- `FoC.Grammars`: context-free grammars, BNF, parse trees, pushdown automata,
  PDA/CFG conversions, pumping for CFLs, and unrestricted grammars.
- `FoC.Computability`: Turing-machine tapes and computations, computable and
  recognizable languages, enumerability, machine descriptions, compiler
  bridges, and undecidability vocabulary.
- `FoC.Book`: chapter- and section-level wrappers that keep the Lean statements
  aligned with the textbook's structure.

The project is intentionally self-contained. It does not depend on Mathlib,
CSLib, or any other external Lean library beyond Verso for the literate HTML
site.

## Start Here

If you want to read the formalization, start with the
[Verso companion site](https://kmehltretter82.github.io/foundations-of-computation-lean/).
The landing page explains the main library layers and links to the chapter
pages.

If you want to inspect textbook-coordinate statements, start with
`FoC.Book`, then open the chapter and section modules. These files use names and
comments that point back to the book's organization.

If you want reusable Lean APIs, start with the corresponding infrastructure
module:

- early mathematical vocabulary: `FoC.Foundation`
- regular languages and automata: `FoC.Languages`
- grammars and pushdown automata: `FoC.Grammars`
- Turing machines and computability: `FoC.Computability`

If you want the current formalization status, read
[`data/coverage.yaml`](data/coverage.yaml). It records the chapter-level
coverage, section-level formalized material, and any deferred application or
construction work.

## Coverage Snapshot

The coverage file is the source of truth, but the current high-level picture is:

| Chapter | Area | Status | Declarations |
| --- | --- | --- | --- |
| 1 | Logic and proof | formal core covered | 162 theorem declarations |
| 2 | Sets, functions, and relations | formal core covered | 94 theorem / 18 definition declarations |
| 3 | Regular languages | formal core covered | 125 theorem / 19 definition declarations |
| 4 | Grammars and pushdown automata | formal core covered | 629 theorem / 365 definition declarations |
| 5 | Turing machines and computability | formal core covered | 250 theorem / 151 definition declarations |

"Formal core covered" does not mean every example, drawing, programming
language detail, or construction artifact from the book has been reproduced.
The coverage file distinguishes checked mathematical content from deferred
application material and from larger construction surfaces that are represented
conditionally.

## Build

Use the Lean version pinned in [`lean-toolchain`](lean-toolchain).

Build the library:

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

## Source Textbook

- Textbook website: <https://math.hws.edu/FoundationsOfComputation/>
- Authors: Carol Critchlow and David Eck
- Edition: Second Edition, Version 2.3.2
- Copyright year: 2011
- Publisher: Carol Critchlow and David Eck

This repository does not copy the textbook text. It is a formal companion that
tracks the mathematical and computational content in Lean.

## Development Notes

Most user-facing explanation for the HTML site lives in Lean module doc blocks
with `set_option doc.verso true`. Update those source comments rather than the
generated files under `.lake/build/literate-html/`.

This formalization was developed with assistance from OpenAI Codex.

## License

This repository is distributed under the Creative Commons
Attribution-NonCommercial-ShareAlike 4.0 International License. See
[LICENSE.md](LICENSE.md) and [NOTICE.md](NOTICE.md).
