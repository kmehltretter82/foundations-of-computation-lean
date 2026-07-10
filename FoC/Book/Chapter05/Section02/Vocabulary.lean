import FoC.Computability.Compiler.Core.Language

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Chapter 5, Section 5.2: Computability

This section connects recursive, recursively enumerable, acceptable, and
listable languages. It also records the statement shape for the theorem that
finite general grammars generate exactly the recursively enumerable languages.
The reusable semantic modules are {module}`FoC.Computability.Recognizable`,
{module}`FoC.Computability.Program`, and
{module}`FoC.Computability.Compiler.Core.Language`.  Finite compiler and grammar
status is presented separately on the construction-status and grammar pages.

The guiding distinction is total decision versus semi-decision. Recursive
languages have deciders. Recursively enumerable languages have recognizers or
listings: members eventually appear, but nonmembers may never be ruled out.

The formal page separates three levels of argument.

* At the semantic level, traces, listings, ranges, partial functions, and staged
  programs are related directly.
* At the bounded-trace level, finite machine runs, encoded configurations,
  finite derivation searches, and recognizer-to-grammar trace simulations are
  checked without requiring a generic transition-table compiler.
* At the compiler-principle level, staged programs and bounded trace checkers
  are connected to Turing machines by named construction hypotheses.
* At the finite-description level, concrete supplied descriptions and finite
  program records expose the construction interfaces used for executable
  machine descriptions.

The finite compiler boundaries are now first-order where possible. Boolean
finite grammar presentations use explicit {lit}`Fin n` nonterminals and a
production list, with the remaining recognizer compiler factored through a
bounded checked-indexed-certificate recognizer. Paired-recognizer dovetailing
is split into a halt-free bounded layout runner and a subroutine-ready
runner-search driver that performs the unbounded stage search.

This makes the theorem statements honest about implementation work. When a
textbook proof says to dovetail two recognizers or check a finite derivation,
this page proves the bounded trace core and names the finite compiler
interfaces instead of treating them as implicit.
-/

open Languages
open Computability

universe u v

/-!
## Recursive and Recursively Enumerable Languages

The definitions name the main language classes and the construction principles
used by the book's proofs: decidable-to-acceptable conversion and dovetailing
paired recognizers for a language and its complement.

The construction principles are kept as explicit hypotheses where the reusable
library avoids assuming a concrete universal machine. This lets the page state
the textbook theorem shapes without smuggling in unproved implementation
details.

The page uses the reusable semantic predicates directly.  Explicit compiler
hypotheses and grouped construction handoffs are isolated in
{module -checked}`FoC.Book.Chapter05.Section02.ConstructionStatus`.
-/

/-!
The next group changes representation level. The preceding staged-program
predicates are semantic; the description predicates say that a supplied finite
machine description realizes the same staged computation. Later theorems use
these bridges to state exactly which compiler facts are supplied by closeout
records.
-/

theorem concrete_machine_description_acceptance_trace
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionAcceptsLanguage D L) :
    AcceptanceTrace (fun w n => D.HaltsIn n w) L := by
  intro w
  exact h.right w

end Section02
end Chapter05
end Book
end FoC
