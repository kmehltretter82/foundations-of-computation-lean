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
general-grammar views. Its set-theoretic equivalences and completed
finite-machine directions are formalized. Effective finite converses retain
the exact compiler principles they still require; the section's compiler
status page distinguishes those premises from completed constructions.

Section 5.3 states the diagonal, reduction, self-halting, pair-halting,
machine-encoding, and universal-machine vocabulary. Finite-table execution,
description encoding and parsing, the decoded-description interpreter, and a
faithful diagonal-pair copy-machine witness are present. An exact-code validator
and the unconditional universal-prefix runner compose into a concrete finite
self-halting recognizer, closing the canonical direct-code theorem: the valid
self-halting language is recognizable, is not decidable, and has a complement
that is not recognizable. A checked self-delimiting finite reduction also
transports this result to pair halting, and a countable-image argument proves
that some code language is not recognized by any well-formed finite
description. Covering every acceptable-language row is a stronger statement
and still consumes the named encoded-input description compiler principle.

## Architecture and Scope

The pages state the textbook's main theorem shapes: Turing-machine semantics,
decidability and recognizability, corrected RE/listing/range equivalences,
grammar-recognizer traces, diagonalization, self-halting and pair-halting
reductions, concrete machine descriptions, and universal-machine rows.
Completed concrete finite constructions live in the reusable computability
layer; open finite routes remain explicit hypotheses of their book-facing
results.

Some textbook presentations are deliberately recast. The canonical
self-halting result is stated directly over complete finite-description codes.
The printed duplicate-free unary {lit}`T_n`/{lit}`G` enumeration has not been
formalized and is not claimed equivalent to this endpoint. Semantic
listing/range witnesses and universal-prefix row coverage are separate
interfaces; the completed finite runner remains distinct from the general
compiler principle used to obtain row coverage.

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

Machine execution, computability and language classes, set-theoretic
listing/range equivalences, grammar traces, reductions, and the abstract
diagonal arguments are unconditional. The effective finite listing/range and
grammar converses are conditional on named finite compiler interfaces.
Concrete finite descriptions implement the scanners, encoders, transducers,
decoded interpreter, exact-code validator, self-halting recognizer, and
universal-prefix runner used by the chapter. General compiler principles stay
visible in theorem hypotheses when the theorem genuinely needs them.

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
semantics, compiled-machine simulation interfaces, row-language facts, the
direct-code self-halting theorem, the checked finite pair-halting reduction,
and the finite-description cardinality obstruction. The finite prefix
recognizer and its universal-prefix runner are constructed. Statements covering
all acceptable languages retain only the encoded-input description compiler
hypothesis needed to choose a description for an arbitrary acceptable
language.
-/
