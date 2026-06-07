import FoC.Computability
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

The reusable computability vocabulary lives in {module}`FoC.Computability`.

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
machine-encoding, and universal-machine vocabulary. The concrete encoding,
interpreter, compiled-machine simulation, and faithful diagonal-pair
copy-machine witness are present. The remaining implementation boundary is the
uniform compiler and universal-runner machinery needed to turn the interpreter
layer into one finite universal machine theorem without extra hypotheses.

## Source Audit

The Chapter 5 formalization has been checked against the textbook source file
{lit}`turing.tex`. The current Lean pages cover the book's main theorem shapes:
Turing-machine semantics, decidability and recognizability, RE/listing/range
equivalences, grammar-recognizer traces, diagonalization, self-halting and
pair-halting reductions, concrete machine descriptions, and universal-machine
row coverage. The places where the textbook says to construct a machine are now
represented either by concrete descriptions/proofs or by named compiler
principles in the reusable computability layer.

## What to Inspect

For machine semantics, start with {module}`FoC.Computability.Tape` and
{module}`FoC.Computability.TuringMachine`. For language classes and functions,
see {module}`FoC.Computability.Computable`,
{module}`FoC.Computability.Recognizable`, and
{module}`FoC.Computability.Enumerable`. For staged programs and grammar
recognizers, see {module}`FoC.Computability.Program` and
{module}`FoC.Computability.Grammar`. For encodings, compiler bridges, and
undecidability, inspect {module}`FoC.Computability.Encoding`,
{module}`FoC.Computability.Compiler`, {module}`FoC.Computability.FiniteProgram`,
{module}`FoC.Computability.Coding`,
{module}`FoC.Computability.DiagonalPairMachine`, and
{module}`FoC.Computability.Undecidable`.

## Status Notes

The chapter's formal core is covered. The remaining work is not hidden: the
book pages and reusable APIs identify concrete finite compiler constructions
and the universal-machine construction as explicit deferred surfaces. The
surrounding theorems are therefore stated with named construction hypotheses
where a textbook proof says "build the machine" but the formal repository has
not yet completed that finite machine description.
-/
