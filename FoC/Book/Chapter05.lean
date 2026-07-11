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

The reusable computability vocabulary lives in the {lit}`FoC.Computability`
module family.

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
general-grammar views. The formalization separates semantic equivalences from
compiler assumptions: staged-program constructions are proved directly, while
concrete machine-description compilers are exposed as named construction
surfaces.

Section 5.3 states the diagonal, reduction, self-halting, pair-halting,
machine-encoding, and universal-machine vocabulary. Finite-table execution,
description encoding and parsing, semantic interpreter relations,
compiled-machine simulation, and a faithful diagonal-pair copy-machine witness
are present. The remaining implementation boundary is the finite-source
compiler and universal-prefix runner machinery needed to realize the semantic
interpreter by one finite universal machine without extra hypotheses.

## Source Audit

The Chapter 5 formalization has been checked against the textbook source file
{lit}`turing.tex`. The current Lean pages cover the book's main theorem shapes:
Turing-machine semantics, decidability and recognizability, RE/listing/range
equivalences, grammar-recognizer traces, diagonalization, self-halting and
pair-halting reductions, concrete machine descriptions, and universal-machine
row coverage. The places where the textbook says to construct a machine are now
represented either by concrete descriptions/proofs or by named compiler
principles and closeout records in the reusable computability layer.

Some textbook presentations are deliberately recast. The book's two-tape
listing-machine and enumerated {lit}`T_n`/{lit}`G`/{lit}`U` storyline is
represented here by semantic listing/range witnesses, encoded machine
descriptions, diagonal pair maps, and universal-prefix row coverage. That
presentation keeps the theorem shapes but makes the remaining finite-source
machine construction obligations explicit.

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

## Status Notes

The semantic layer is proved: machine execution, computability and language
classes, listing/range equivalences, grammar traces, reductions, and the
abstract diagonal arguments do not rely on unfinished construction providers.
Concrete finite descriptions are also proved for many scanners, encoders,
transducers, and local compiler phases.  The remaining finite compiler leaves
are exposed as construction records or explicit hypotheses; importing this
chapter does not turn them into unconditional theorems through {lit}`sorryAx`.

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
lowering theorem.  Semantic RE/co-RE, listability, range, and grammar results
are proved independently of that unfinished compiler boundary.

Section 5.3 proves description syntax, parsing inversions, interpreter
semantics, compiled-machine simulation interfaces, row-language facts, and
conditional diagonal consequences.  A single finite universal-prefix machine
is not yet constructed.  The live path is the finite-source closeout plus the
prefix recognizer/runner contract; statements that require that machine retain
the corresponding explicit hypothesis.
-/
