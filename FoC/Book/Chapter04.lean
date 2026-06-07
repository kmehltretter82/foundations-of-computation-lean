import FoC.Grammars
import FoC.Book.Chapter04.Section01
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

## Status Notes

The formal core is covered. The CFG sections include derivation/context laws,
closure under union, concatenation, star, and reversal, exact generated-language
theorems for representative grammars, and the right/left-regular boundary.
The BNF page records the notation semantics and many concrete expansion
examples; small helper rules now cover both sides of alternatives and
single-use repetition directly.

The parse-tree section connects generated-language membership, parse trees,
and leftmost derivation traces in both directions. The PDA sections include
computation APIs, CFG-to-PDA and PDA-to-CFG conversion boundaries, exact PDA
examples, intersection/difference with DFA and regular languages, CFL pumping,
and nonclosure proofs. General grammars include finite-presentation
countability, CFG embedding, and substantial counting/order examples.

Remaining deferrals are parser-generator algorithms, large purely
application-oriented BNF enumerations, and optional exercise families whose
mathematical pattern is already represented by the general closure, pumping,
or exact-language theorem schemas.
-/
