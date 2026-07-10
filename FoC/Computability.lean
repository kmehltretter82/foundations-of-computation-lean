import FoC.Computability.Tape
import FoC.Computability.ListLemmas
import FoC.Computability.TapeLemmas
import FoC.Computability.TuringMachine
import FoC.Computability.Computable
import FoC.Computability.Recognizable
import FoC.Computability.Transform
import FoC.Computability.Enumerable
import FoC.Computability.Program
import FoC.Computability.Grammar
import FoC.Computability.Undecidable
import FoC.Computability.Coding
import FoC.Computability.Encoding
import FoC.Computability.DiagonalPairMachine
import FoC.Computability.MachineBuilder
import FoC.Computability.Compiler
import FoC.Computability.FiniteProgram

set_option doc.verso true

/-!
# Computability

The Computability library is the reusable foundation beneath Chapter 5.  Its
dependency direction runs from machine semantics, through language and
function classes, into finite syntax and compilers, and finally to book-facing
corollaries.  A theorem at a semantic layer does not by itself claim that a
finite machine description has been constructed.

## Layers

| Layer | Principal modules | Responsibility |
|---|---|---|
| machine semantics | {module}`FoC.Computability.Tape`, {module}`FoC.Computability.TuringMachine` | finite tape windows, transitions, computation, halting, output, and acceptance |
| functions and language classes | {module}`FoC.Computability.Computable`, {module}`FoC.Computability.Recognizable`, {module}`FoC.Computability.Enumerable` | partial/total computability, decidability, recognizability, and listability |
| staged semantic programs | {module}`FoC.Computability.Program`, {module}`FoC.Computability.Grammar` | finite-stage search and semantic program/grammar bridges |
| finite syntax and encodings | {module}`FoC.Computability.Coding`, {module}`FoC.Computability.Encoding`, {module}`FoC.Computability.FiniteProgram` | concrete codes, parsers, and finite description witnesses |
| machine construction | {module}`FoC.Computability.MachineBuilder`, {module}`FoC.Computability.Compiler` | executable descriptions, simulation, lowering, and compiler contracts |
| semantic limitations | {module}`FoC.Computability.Undecidable` | reductions, diagonalization, and noncomputability |

The staged-program layer is a proof tool rather than a replacement for Turing
machines.  Construction modules must explicitly supply finite descriptions or
state the finite construction still required.  Detailed declaration inventories
and construction status belong in the defining module docs and generated API
reports, not in this facade.

## Reading Route

The chapter-facing material in {module -checked}`FoC.Book.Chapter05` points to
these definitions while keeping the textbook-order statements separate from the
reusable infrastructure.

For a conceptual pass, read the modules in dependency order:

* tapes and Turing machines;
* computable and recognizable language classes;
* enumerable languages and staged programs;
* finite program descriptions and compiler bridges;
* coding, encoding, and undecidability.
-/
