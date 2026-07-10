import FoC.Grammars
import FoC.Book.Chapter04.Section01
import FoC.Book.Chapter04.Section01.RegularBoundary
import FoC.Book.Chapter04.Section02
import FoC.Book.Chapter04.Section03
import FoC.Book.Chapter04.Section04
import FoC.Book.Chapter04.Section05
import FoC.Book.Chapter04.Section06

set_option doc.verso true

/-!
# Chapter 4: Grammars and Pushdown Automata

Chapter 4 moves from finite memory to stack-based computation. The formal
development connects context-free grammars, parse trees, pushdown automata,
grammar/automaton conversions, pumping arguments for context-free languages,
and unrestricted grammars.

The reusable machinery lives in {module}`FoC.Grammars`; the book modules state
the chapter-level correspondences and examples in book order.

## Story of the Chapter

The chapter has three intertwined stories. First, grammars generate languages
by derivation. Second, parse trees and pushdown automata give two operational
views of the same context-free behavior. Third, pumping and closure arguments
separate context-free languages from languages that need more power.

The unrestricted grammar section is also a bridge into Chapter 5: it introduces
the kind of grammar power that later lines up with recursively enumerable
languages.

The reusable grammar layer is intentionally semantic-first. Core CFG and PDA
structures carry derivation or transition relations directly, while finite
production lists, finite stack alphabets, and other book-style finite
presentations are supplied by secondary predicates and presentation records.
Chapter-facing theorems call out the finite presentation hypotheses where they
matter.

## What to Inspect

Start with {module}`FoC.Grammars.CFG` and {module}`FoC.Grammars.CFL` for
grammar and language vocabulary. Use {module}`FoC.Grammars.ParseTree` for the
frontier, ambiguity, derivation, and pumping support. The automaton layer lives
in {module}`FoC.Grammars.PDA`, with normalization in
{module}`FoC.Grammars.PDANormalize`.

The conversion pages are intentionally substantial:
{module}`FoC.Grammars.CFGToPDA` and {module}`FoC.Grammars.PDAToCFG` expose the
proof obligations behind the textbook equivalence between context-free
grammars and pushdown automata. {module}`FoC.Grammars.GeneralGrammar` supplies
the unrestricted grammar vocabulary used at the computability boundary.

## Coverage at a Glance

| Source section | Canonical Lean surface | Status |
|---|---|---|
| 4.1 CFGs | {module}`FoC.Grammars.CFG`, {module}`FoC.Grammars.CFL` | Core laws, closures, regular boundary, and representative exact grammars complete |
| 4.2 BNF | {module}`FoC.Grammars.BNF` | Expansion semantics and representative applications complete; exhaustive application listings deferred |
| 4.3 Parsing | {module}`FoC.Grammars.ParseTree`, {module}`FoC.Book.Chapter04.Section03` | Parse-tree/derivation correspondence complete; LL(1) successful-run soundness complete; generic FIRST/FOLLOW and parser completeness not claimed |
| 4.4 PDAs | {module}`FoC.Grammars.PDA`, {module}`FoC.Grammars.CFGToPDA`, {module}`FoC.Grammars.PDAToCFG` | Exact CFG/PDA equivalence for finite presentations complete |
| 4.5 Non-CFLs | {module}`FoC.Grammars.CFL`, {module}`FoC.Book.Chapter04.Section05` | Pumping and the {lit}`a^n b^n c^n` result complete; the duplicate-word position argument remains partial |
| 4.6 General grammars | {module}`FoC.Grammars.GeneralGrammar`, {module}`FoC.Book.Chapter04.Section06` | Core semantics, exact CFG embedding, and principal examples complete; selected exercise converses remain deferred |

The executable LL(1) development proves that every successful run returns a
valid parse tree. Its conflict and fixed-point checks do not yet prove semantic
completeness of the supplied production list or computed {lit}`FIRST` and
{lit}`FOLLOW` sets. Section 4.3 includes the source's concrete {lit}`G1`
ambiguity for {lit}`x+y*z` and a successful {lit}`G2` LL(1) run.
-/
