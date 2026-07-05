# Foundations of Computation Lean Companion

This is a standalone Lean 4 formalization companion for Carol Critchlow and
David Eck's textbook *Foundations of Computation*, Second Edition, Version
2.3.2.

The project follows a familiar theory-of-computation course into a proof
assistant and keeps going when the informal story usually waves its hands. It
starts with truth tables, sets, induction, and finite automata, then builds up
to grammars, pushdown automata, Turing machines, diagonal arguments, and
concrete finite-machine compiler boundaries.

The public reading experience is the
[rendered Verso site](https://kmehltretter82.github.io/foundations-of-computation-lean/),
generated from the Lean source in this repository. It is meant to be read
beside the textbook, not instead of it: the textbook supplies the exposition and
exercises, while this project records checked definitions, theorems,
constructions, examples, and formal status notes.

## Why It Is Interesting

Most of the project is not just a catalog of final theorem statements. The
regular-language and grammar chapters expose reusable constructions, the
computability chapters separate semantic claims from finite machine
descriptions, and the compiler layer records the places where a concrete
construction is still a real engineering problem rather than a hidden
assumption.

That makes the repository useful in two different ways. It can be read as a
checked companion to the book, and it can also be inspected as a Lean library
for the mechanics behind automata, languages, grammars, computability, and
machine encodings.

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

If you are curious about the more ambitious backend work, look under
`FoC.Computability.Compiler`. That is where the project tracks concrete
machine-description, normalized-output, staged-search, and finite-source
construction boundaries.

If you want the current formalization status, read
[`data/coverage.yaml`](data/coverage.yaml). It records the chapter-level
coverage, section-level formalized material, and any deferred application or
construction work.

## Coverage Snapshot

The coverage file is the source of truth, but the current high-level picture is:

| Chapter | Area | Status | Declarations |
| --- | --- | --- | --- |
| 1 | Logic and proof | formal core covered | 241 theorem / 91 definition declarations |
| 2 | Sets, functions, and relations | formal core covered | 126 theorem / 18 definition declarations |
| 3 | Regular languages | formal core covered | 177 theorem / 34 definition declarations |
| 4 | Grammars and pushdown automata | formal core covered | 797 theorem / 444 definition declarations |
| 5 | Turing machines and computability | formal core covered | 601 theorem / 275 definition declarations |

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

Build the project documentation target, currently an alias for the Verso
literate HTML site:

```sh
lake build :docs
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

For API reference policy, see [`docs/API_WORKFLOW.md`](docs/API_WORKFLOW.md).
Broad API inventories should be generated from Lean declarations and docstrings
rather than maintained by hand.

For concrete finite-machine debugging, import
`FoC.Computability.MachineDescriptionDebug`. It provides printable tape,
configuration, and transition views; trace windows; breakpoints; watchpoints;
compact summaries; final comparison reports; exact and `Tape.Equiv` comparers;
and step-expectation checks for finding the first bad tape boundary. These
helpers are opt-in diagnostics, not replacements for general run proofs.

For compiler construction leaves that are easier to state as multi-tape
algorithms, use
`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured`.
It provides a finite structured logical-tape semantics, bounded runner, basic
halt/run facts, and debugger/comparison helpers. The existing one-tape
`MachineDescription` layer remains the backend contract until a particular
structured machine has a proved lowering.
For the first restricted backend bridge, import
`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredLowering`.
It lowers one-logical-tape structured rows with one read, one local action, and
a left/right move; `HeadMove.stay` is deliberately outside that first fragment.
For reusable move/write/scan/copy/append building blocks over that semantics,
import
`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredPrimitives`.
For lowerer-facing three-logical-tape proof scripts, import
`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeTactic`.
It provides opt-in tactics such as `three_tape_step [...]` for local table-step
simplification, `three_tape_phase_step [...]` for phase-composed descriptions,
`three_tape_support` for all-read row support branches, and `three_tape_run`
for short runs assembled from explicit step lemmas.

This formalization was developed with assistance from OpenAI Codex and Google Gemini.

## License

This repository is distributed under the Creative Commons
Attribution-NonCommercial-ShareAlike 4.0 International License. See
[LICENSE.md](LICENSE.md) and [NOTICE.md](NOTICE.md).
