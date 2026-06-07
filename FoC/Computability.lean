import FoC.Computability.Tape
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
import FoC.Computability.Compiler
import FoC.Computability.FiniteProgram

set_option doc.verso true

/-!
# Computability

## Turing-Machine Layer

The Computability library is the reusable layer beneath Chapter 5.  It builds
from concrete Turing-machine configurations to the abstract vocabulary of
computable functions, decidable languages, recursively enumerable languages,
and undecidability.

The library is split so that semantic facts, construction principles, finite
program descriptions, and concrete encodings are visible as separate layers.
This is important in a formalization of computability: a textbook construction
that says "build a machine" becomes either a checked finite description or an
explicit construction hypothesis.

## Machine Semantics

{module}`FoC.Computability.Tape` represents the book's two-way infinite tape by
a finite visible window around the head.  {module}`FoC.Computability.TuringMachine`
then defines deterministic one-tape machines, configurations, single steps,
multi-step computations, halting, output, and acceptance by halting.

These files are the operational base. They prove determinism, finite-step
reasoning, halted-state stability, output uniqueness, and the bridges between
exact-step runs and ordinary reachability.

## Language Classes and Programs

The next files separate the common language-theoretic predicates.
{module}`FoC.Computability.Computable` defines total and partial computable
string functions.  {module}`FoC.Computability.Recognizable` defines
Turing-acceptable and Turing-decidable languages.  {module}`FoC.Computability.Transform`
contains reusable machine transformations.  {module}`FoC.Computability.Enumerable`
records the enumeration and range-of-computable-function views of recursively
enumerable languages.  {module}`FoC.Computability.Program` supplies a staged
program semantics for trace-level dovetailing and partial listing/range/program
equivalences.  {module}`FoC.Computability.Grammar` connects finite general
grammar derivations with staged program recognizers.

The staged-program layer is a proof tool, not a replacement for Turing
machines. It captures finite-stage acceptance and bounded search directly, then
the compiler layers state what is needed to turn those staged programs into
machine descriptions.

## Diagonalization, Encoding, and Compilers

Finally, {module}`FoC.Computability.Undecidable` packages the diagonal,
halting-problem, reduction, preimage-construction, and noncomputability
vocabulary used by the limits of computation section.
{module}`FoC.Computability.Coding` supplies concrete pair-code words,
injectivity facts, and computable-map preimage bridges for those reductions.
{module}`FoC.Computability.Encoding` starts the concrete machine-description
and interpreter layer needed to discharge the remaining compiler and universal
machine theorem shapes, including a description-backed code-word decoder
relation for Section 5.3 diagonalization.
{module}`FoC.Computability.Compiler` proves exact simulation between
well-formed descriptions and their compiled one-tape machines, then exposes
description-backed compiler bridges for staged acceptors, Boolean deciders,
paired-trace dovetailing, and partial unary range programs.
{module}`FoC.Computability.FiniteProgram` packages finite executable
program-description syntax and proves concrete bridges for trace recognizers,
Boolean deciders, dovetailing deciders, and partial unary range outputs when
their descriptions are explicitly supplied, including finite construction
surfaces for dovetailing and output-complete partial unary range descriptions.

The current Chapter 5 boundary is visible here. Description encodings,
interpreter semantics, exact compiled-machine simulation, supplied-description
bridges, and finite construction surfaces are present. The remaining universal
runner and some uniform finite compiler constructions are named explicitly so
that downstream theorem statements can be precise without pretending those
finite machines have already been built.

## Reading Route

The chapter-facing material in {module -checked}`FoC.Book.Chapter05` points to
these definitions while keeping the textbook-order statements separate from the
reusable infrastructure.

For a fast conceptual pass, read the modules in this order:

* tapes and Turing machines;
* computable and recognizable language classes;
* enumerable languages and staged programs;
* finite program descriptions and compiler bridges;
* coding, encoding, and undecidability.
-/
