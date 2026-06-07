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

## Turing-machine layer

The Computability library is the reusable layer beneath Chapter 5.  It builds
from concrete Turing-machine configurations to the abstract vocabulary of
computable functions, decidable languages, recursively enumerable languages,
and undecidability.

{module}`FoC.Computability.Tape` represents the book's two-way infinite tape by
a finite visible window around the head.  {module}`FoC.Computability.TuringMachine`
then defines deterministic one-tape machines, configurations, single steps,
multi-step computations, halting, output, and acceptance by halting.

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

Finally, {module}`FoC.Computability.Undecidable` packages the diagonal,
halting-problem, reduction, and noncomputability vocabulary used by the limits
of computation section.  {module}`FoC.Computability.Coding` supplies concrete
pair-code words and injectivity facts for those reductions.
{module}`FoC.Computability.Encoding` starts the concrete machine-description
and interpreter layer needed to discharge the remaining compiler and universal
machine theorem shapes, including a description-backed code-word decoder
relation for Section 5.3 diagonalization.
{module}`FoC.Computability.Compiler` proves exact simulation between
well-formed descriptions and their compiled one-tape machines, then exposes
description-backed compiler bridges for staged acceptors, Boolean deciders,
and partial unary range programs.
{module}`FoC.Computability.FiniteProgram` packages finite executable
program-description syntax and proves concrete bridges for trace recognizers,
Boolean deciders, dovetailing deciders, and partial unary range outputs when
their descriptions are explicitly supplied.

The chapter-facing material in {module -checked}`FoC.Book.Chapter05` points to
these definitions while keeping the textbook-order statements separate from the
reusable infrastructure.
-/
