import FoC.Book.Chapter05.Section01
import FoC.Book.Chapter05.Section02
import FoC.Book.Chapter05.Section03

set_option doc.verso true

/-!
# Chapter 5: Turing Machines and Computability

Chapter 5 is the computability layer of the companion. It begins with concrete
Turing-machine mechanics, raises those mechanics to computable functions and
language classes, and then uses diagonalization and reductions to mark the
limits of computation.

The reusable computability vocabulary lives in the
{module -checked}`FoC.Computability` module family.

## Story of the Chapter

The section pages move from a concrete machine model to language-level notions.
A Turing machine has configurations and computations; a computable or
recognizable language is then a predicate for which some machine has the right
behavior. The final page abstracts further to reductions and diagonal
arguments, where the key statements are impossibility theorems rather than
machine constructions.

Section 5.1 builds the semantic foundation: tapes, configurations, finite-step
runs, halting, output, accepted languages, partial computable functions,
deciders, characteristic functions, complement closure, and a stopped-decider
to acceptor transformation.

Section 5.2 compares recursive, recursively enumerable, listable, range, and
general-grammar views. Its semantic equivalences and the finite-machine routes
used by their concrete witnesses are formalized. Broad compiler principles
remain named explicitly when a statement quantifies over every staged program
or every acceptable language.

Section 5.3 states the diagonal, reduction, self-halting, pair-halting,
machine-encoding, and universal-machine vocabulary. Finite-table execution,
description encoding and parsing, the decoded-description interpreter, and a
faithful diagonal-pair copy-machine witness are present. A finite prefix
recognizer supplies one unconditional universal-prefix runner. Covering every
acceptable-language row is a stronger statement and still consumes the named
encoded-input description compiler principle.

## Architecture and Scope

The pages cover the textbook's main theorem shapes: Turing-machine semantics,
decidability and recognizability, RE/listing/range equivalences,
grammar-recognizer traces, diagonalization, self-halting and pair-halting
reductions, concrete machine descriptions, and universal-machine rows.
Concrete finite constructions live in the reusable computability layer;
book-facing results are thin semantic corollaries of those constructions.

Some textbook presentations are deliberately recast. The book's two-tape
listing-machine and enumerated {lit}`T_n`/{lit}`G`/{lit}`U` storyline is
represented here by semantic listing/range witnesses, encoded machine
descriptions, diagonal pair maps, and universal-prefix row coverage. That
presentation keeps the theorem shapes while separating the completed finite
runner from the general compiler principle used to obtain row coverage.

Two source discrepancies are not reproduced in Lean.  The range-machine
discussion types its computed value as a symbol where the surrounding argument
requires a word; the formal statement is word-valued.  In the final diagonal
argument, one prose branch reverses the halting conclusion needed by the
contradiction; the Lean theorem states the intended diagonal property.

## What to Inspect

For machine semantics, start with {module}`FoC.Computability.Tape` and
{module}`FoC.Computability.TuringMachine`. For language classes and functions,
see {module}`FoC.Computability.Computable`,
{module}`FoC.Computability.Recognizable`, and
{module}`FoC.Computability.Enumerable`. For staged programs and grammar
recognizers, see {module}`FoC.Computability.Program` and
{module}`FoC.Computability.Grammar.SemanticAndTraceTables`. For finite table
execution, encoded-code
languages, encodings, compiler bridges, and undecidability, inspect
{module}`FoC.Computability.MachineDescription`,
{module}`FoC.Computability.DescriptionLanguages`,
{module}`FoC.Computability.Encoding`,
{module}`FoC.Computability.Compiler`, {module}`FoC.Computability.FiniteProgram`,
{module}`FoC.Computability.Coding`,
{module}`FoC.Computability.DiagonalPairMachine`, and
{module}`FoC.Computability.Undecidable`.

## Semantic Boundaries

Machine execution, computability and language classes, listing/range
equivalences, grammar traces, reductions, and the abstract diagonal arguments
are unconditional. Concrete finite descriptions implement the scanners,
encoders, transducers, decoded interpreter, and universal-prefix runner used by
the chapter. General compiler principles stay visible in theorem hypotheses
when the theorem genuinely needs them.

Section 5.1 uses a partial transition function, so a missing row stops an
execution without being the same event as entering the designated halt state.
Its tapes are finite observed windows into an implicitly blank bi-infinite
tape.  Exact physical-tape equality is reserved for local handoffs; public
results normally observe tape equivalence or normalized output and therefore
ignore far-edge blank padding and, for normalized output, head position.

Section 5.2 treats the Church–Turing thesis as explanatory motivation, not a
Lean proposition.  The structured logical-tape layer is useful construction
infrastructure, but it does not by itself prove the textbook's general
multi-tape-to-one-tape equivalence: that claim requires a semantics-preserving
lowering theorem. Semantic RE/co-RE, listability, range, and grammar results do
not depend on such a blanket equivalence.

Section 5.3 proves description syntax, parsing inversions, interpreter
semantics, compiled-machine simulation interfaces, row-language facts, and
conditional diagonal consequences. The finite prefix recognizer and its
universal-prefix runner are constructed. Statements covering all acceptable
languages retain only the encoded-input description compiler hypothesis needed
to choose a description for an arbitrary acceptable language.
-/
