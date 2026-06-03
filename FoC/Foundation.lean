import FoC.Foundation.Logic
import FoC.Foundation.Lists
import FoC.Foundation.Sets
import FoC.Foundation.Functions
import FoC.Foundation.Finite
import FoC.Foundation.Countable
import FoC.Foundation.Relations
import FoC.Foundation.Arithmetic
import FoC.Foundation.Summation
import FoC.Foundation.Integers
import FoC.Foundation.Rationals
import FoC.Foundation.RationalCore
import FoC.Foundation.QuotientRationals
import FoC.Foundation.Reals
import FoC.Foundation.QuadraticSurd
import FoC.Foundation.DigitStreams
import FoC.Foundation.RealUncountability
import FoC.Foundation.Primes
import FoC.Foundation.Cardinality

set_option doc.verso true

/-!
# Foundation

## Reusable mathematical layer

The Foundation library is the reusable mathematical layer beneath the
book-facing modules.  The chapter files state the definitions and theorems in
the order of the textbook; the Foundation files collect the structures that are
used repeatedly across chapters.

The early chapters begin with logic and proof.  {module}`FoC.Foundation.Logic`
models propositional formulas, truth assignments, tautologies, contradictions,
logical equivalence, implication, substitution, and formula contexts.
{module}`FoC.Foundation.Arithmetic`, {module}`FoC.Foundation.Integers`,
{module}`FoC.Foundation.Primes`, and {module}`FoC.Foundation.Summation` provide
the number-theoretic and induction examples used in Chapter 1.

Chapter 2 uses sets and functions as its main language.  Sets are represented
extensionally in {module}`FoC.Foundation.Sets`, with finite and countable
variants developed in {module}`FoC.Foundation.Finite`,
{module}`FoC.Foundation.Cardinality`, and {module}`FoC.Foundation.Countable`.
The function and relation vocabulary lives in {module}`FoC.Foundation.Functions`
and {module}`FoC.Foundation.Relations`.

The real-number material is split into small layers so the formal statements can
reuse exactly the amount of structure they need.  {module}`FoC.Foundation.Rationals`
starts with raw rational representatives, {module}`FoC.Foundation.RationalCore`
contains reduced-rational divisibility arguments, and
{module}`FoC.Foundation.QuotientRationals` supplies quotient rationals for the
Dedekind-cut construction in {module}`FoC.Foundation.Reals`.  The
diagonalization modules, {module}`FoC.Foundation.DigitStreams` and
{module}`FoC.Foundation.RealUncountability`, connect the countability material
to the book's proof that the real numbers are uncountable.

The Foundation pages are intentionally more infrastructure-oriented than the
chapter pages.  They explain how the textbook's ordinary mathematical objects
are encoded in Lean, while the visible Lean declarations give the precise
checked API used by the formalized statements.
-/
