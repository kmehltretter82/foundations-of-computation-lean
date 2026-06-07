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
interpreter, and non-injective diagonal-pair machine witness are present, while
the faithful copy-machine theorem and final finite universal-runner theorem are
still explicit construction targets.

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
{module}`FoC.Computability.Coding`, and
{module}`FoC.Computability.Undecidable`.

## Status Notes

The chapter's formal core is covered. The remaining work is not hidden: the
coverage file identifies concrete finite compiler constructions and the
universal-machine construction as explicit deferred surfaces. The surrounding
theorems are therefore stated with named construction hypotheses where a
textbook proof says "build the machine" but the formal repository has not yet
completed that finite machine description.
-/
