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

The chapter's formal core is covered. The remaining work is not hidden: the
book pages and reusable APIs identify concrete finite compiler constructions,
finite/effective grammar construction, and the universal-machine construction
as explicit deferred surfaces. The closeout records have been narrowed to the
actual construction handoffs: Section 5.2 now relates semantic and finite
grammar closeouts directly, while Section 5.3 uses the finite-source closeout,
the universal-prefix row-coverage route, the prefix recognizer machine, and the
encoded-input description compiler as the live construction path. The older
encoded-input program-compiler surface remains as compatibility scaffolding,
not as the route to finish first. The surrounding theorems are therefore stated
with closeout records or named construction hypotheses where a textbook proof
says "build the machine" but the formal repository has not yet completed that
finite machine description.
-/
