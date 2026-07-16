import FoC.Book.Chapter05.Section03.Basic

set_option doc.verso true

/-!
# Chapter 5, Section 5.3: Undecidability and Universal Machines

This module provides the supporting declarations and helper lemmas for
Section 5.3. It covers diagonal arguments, reductions, self-halting,
pair-halting, encodings, and the universal machine vocabulary.

## Section Pages

The book-facing development is split between the diagonal and encoding
vocabulary in {module}`FoC.Book.Chapter05.Section03.BasicPart1` and the
pair-halting and universal-prefix results in
{module}`FoC.Book.Chapter05.Section03.BasicPart2`.

## Reusable Foundations

The semantic diagonal theorems live in
{module}`FoC.Computability.Undecidable`. The concrete decoded interpreter,
finite prefix recognizer, and universal-prefix runner live under
{module}`FoC.Computability.Compiler`.
-/
