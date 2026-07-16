import FoC.Computability.Compiler.Core.Language

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2: Language Classes

This section connects recursive, recursively enumerable, acceptable, and
listable languages and fixes the semantic vocabulary used by the finite grammar
characterizations.
The reusable semantic modules are {module}`FoC.Computability.Recognizable`,
{module}`FoC.Computability.Program`, and
{module}`FoC.Computability.Compiler.Core.Language`. Concrete compiler interfaces
are documented in
{module -checked}`FoC.Book.Chapter05.Section02.ConstructionStatus`, while the
grammar and closeout pages assemble the finite consequences.

The guiding distinction is total decision versus semi-decision. Recursive
languages have deciders. Recursively enumerable languages have recognizers or
listings: members eventually appear, but nonmembers may never be ruled out.

The formal development separates four representation levels.

* At the semantic level, traces, listings, ranges, partial functions, and staged
  programs are related directly.
* At the bounded-trace level, finite machine runs, encoded configurations,
  finite derivation searches, and recognizer-to-grammar trace simulations are
  checked without requiring a generic transition-table compiler.
* At the compiler-principle level, semantic staged programs are connected to
  Turing machines by named interfaces.
* At the finite-description level, concrete supplied descriptions and finite
  program records expose executable machine descriptions directly.

Boolean finite grammar presentations use {name}`Fin`-indexed nonterminals and
a production list. Their recognizer interface is factored through a bounded
checked-indexed-certificate recognizer. Paired-recognizer dovetailing uses a
halt-free bounded layout runner and a subroutine-ready runner-search driver for
the unbounded stage search.

Thus a theorem can use the weakest appropriate currency: a semantic language
principle, finite trace evidence, or a supplied finite machine description.
-/

open Languages
open Computability

universe u v

/-!
## Recursive and Recursively Enumerable Languages

The definitions name the main language classes and the construction principles
used by the book's proofs: decidable-to-acceptable conversion and dovetailing
paired recognizers for a language and its complement.

Semantic construction principles remain explicit when a theorem quantifies
over arbitrary Lean-level programs. Concrete finite-program theorems instead
consume the description-backed interfaces supplied by the compiler pages.

The page uses the reusable semantic predicates directly. Compiler interfaces
and concrete finite-presentation predicates are isolated in
{module -checked}`FoC.Book.Chapter05.Section02.ConstructionStatus`.
-/

/-!
The next group changes representation level. The preceding staged-program
predicates are semantic; the description predicates say that a supplied finite
machine description realizes the same staged computation. Later theorems use
these bridges to compose language-level and finite-description results.
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
