import FoC.Book.Chapter05.Section02.Vocabulary
import FoC.Book.Chapter05.Section02.ConstructionStatus
import FoC.Book.Chapter05.Section02.Dovetailing
import FoC.Book.Chapter05.Section02.MachineCompiler
import FoC.Book.Chapter05.Section02.Ranges
import FoC.Book.Chapter05.Section02.Grammars
import FoC.Book.Chapter05.Section02.Closeouts

set_option doc.verso true

/-!
# Chapter 5, Section 5.2: Recursively Enumerable Languages

## Scope

This module provides the supporting declarations and helper lemmas for
Section 5.2. It compares recursive, recursively enumerable, listable,
range, and general-grammar views of computability.

The semantic vocabulary is kept separate from finite compiler assumptions.
That separation lets the chapter state unconditional trace, listing, range,
and grammar facts while naming every transition-table construction needed by
the executable closeout route.

## Page and Dependency Map

This wrapper is the re-export point for the section pages.  The pages form a
shallow dependency graph rather than a linear chain: the vocabulary and
machine-compiler pages depend only on reusable computability modules, the
construction-status page defines the named compiler hypotheses, and the
dovetailing, ranges, grammar, and closeout pages import only the pages whose
declarations they actually use.

Start with {module}`FoC.Book.Chapter05.Section02.Vocabulary` for the language
classes and {module}`FoC.Book.Chapter05.Section02.Dovetailing` for the RE/co-RE
argument. Then use {module}`FoC.Book.Chapter05.Section02.Ranges` and
{module}`FoC.Book.Chapter05.Section02.Grammars` for the two enumeration views.
The construction-status and machine-compiler pages document the finite
handoffs, and {module}`FoC.Book.Chapter05.Section02.Closeouts` assembles their
public consequences.
-/
