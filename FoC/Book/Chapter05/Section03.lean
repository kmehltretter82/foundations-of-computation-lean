import FoC.Book.Chapter05.Section03.Basic
import FoC.Book.Chapter05.Section03.Cardinality
import FoC.Book.Chapter05.Section03.ContractGuardrails
import FoC.Book.Chapter05.Section03.ConstructionStatus

set_option doc.verso true

/-!
# Chapter 5, Section 5.3: Undecidability and Universal Machines

This module provides the supporting declarations and helper lemmas for
Section 5.3. It covers diagonal arguments, reductions, self-halting,
pair-halting, encodings, and the universal machine vocabulary.  Its canonical
direct-code theorem gives a finite recognizer for valid self-halting codes,
proves that language undecidable in the halt-stable finite currency, and proves
its complement is not finitely recognizable.

## Section Pages

The book-facing development is split between the diagonal and encoding
vocabulary in {module}`FoC.Book.Chapter05.Section03.BasicPart1` and the
pair-halting and universal-prefix results in
{module}`FoC.Book.Chapter05.Section03.BasicPart2`. The currency collapse of
the legacy decidability predicate and the resulting proof obligations are
recorded in {module}`FoC.Book.Chapter05.Section03.ContractGuardrails`.  The
countability obstruction for exact finite-description languages and the
direct-code enumeration-fidelity decision are recorded in
{module}`FoC.Book.Chapter05.Section03.Cardinality`, and
the honest theorem-status table is
{module}`FoC.Book.Chapter05.Section03.ConstructionStatus`.

## Reusable Foundations

The semantic diagonal theorems live in
{module}`FoC.Computability.Undecidable`. Finite-description countability lives
in {module}`FoC.Computability.DescriptionCardinality`, and the checked
pair-halting endpoint lives in
{module}`FoC.Computability.DescriptionPairHaltingUndecidable`. The concrete
decoded interpreter, finite prefix recognizer, exact-code validator,
self-halting recognizer, pair-reduction machine, and universal-prefix runner
live under {module}`FoC.Computability.Compiler`.
-/
