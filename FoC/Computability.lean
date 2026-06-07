import FoC.Computability.Tape
import FoC.Computability.TuringMachine
import FoC.Computability.Computable
import FoC.Computability.Recognizable
import FoC.Computability.Transform
import FoC.Computability.Enumerable
import FoC.Computability.Program
import FoC.Computability.Undecidable

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
equivalences.

Finally, {module}`FoC.Computability.Undecidable` packages the diagonal,
halting-problem, reduction, and noncomputability vocabulary used by the limits
of computation section.

The chapter-facing material in {module -checked}`FoC.Book.Chapter05` points to
these definitions while keeping the textbook-order statements separate from the
reusable infrastructure.
-/
