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

The Chapter 4 files organize the formalization of context-free grammars,
parse trees, pushdown automata, normalizing PDA acceptance, and conversions
between grammar and automaton presentations.

The reusable machinery lives in {module}`FoC.Grammars`; the book modules state
the chapter-level correspondences and examples in book order.

The chapter has three intertwined stories. First, grammars generate languages
by derivation. Second, parse trees and pushdown automata give two operational
views of the same context-free behavior. Third, pumping and closure arguments
separate context-free languages from languages that need more power.

Some section pages are necessarily long because they expose full conversion
theorems, not just vocabulary. The surrounding prose identifies the invariant
being proved before the Lean declarations spell out the exact quantified
statement.
-/
