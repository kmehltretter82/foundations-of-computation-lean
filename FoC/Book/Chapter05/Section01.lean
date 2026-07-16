import FoC.Book.Chapter05.Section01.Basic
import FoC.Book.Chapter05.Section01.DeciderToAcceptor

set_option doc.verso true

/-!
# Chapter 5, Section 5.1: Turing Machines

## Section Pages

This wrapper preserves the original section module while the implementation is
split into a basic semantic page and a decider-to-acceptor construction page.

The semantic page covers tapes, computations, halting, output, computable
functions, decidable languages, complements, and extensional transport; see
{module}`FoC.Book.Chapter05.Section01.Basic`.

The construction page gives the concrete stopped-decider to acceptor
transformations; see
{module}`FoC.Book.Chapter05.Section01.DeciderToAcceptor`.

## Reusable Foundations

The section pages present the book-facing route through
{module}`FoC.Computability.Tape`,
{module}`FoC.Computability.TuringMachine`,
{module}`FoC.Computability.Computable`, and
{module}`FoC.Computability.Recognizable`. The transition-level
decider-to-acceptor implementation is provided by
{module}`FoC.Computability.Transform`.
-/
