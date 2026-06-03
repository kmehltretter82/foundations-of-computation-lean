import FoC.Languages
import FoC.Book.Chapter03.Section01
import FoC.Book.Chapter03.Section02
import FoC.Book.Chapter03.Section03
import FoC.Book.Chapter03.Section04
import FoC.Book.Chapter03.Section05
import FoC.Book.Chapter03.Section06
import FoC.Book.Chapter03.Section07

set_option doc.verso true

/-!
# Chapter 3: Regular Languages

The Chapter 3 formalization develops words, languages, regular expressions,
deterministic and nondeterministic finite automata, NFA paths, Thompson-style
constructions, and regular-language closure statements.

These files are the chapter-facing layer over reusable language and automata
modules in {module}`FoC.Languages`.

The chapter follows the book's progression. Sections 3.1 through 3.3 set up
languages and regular expressions, including the book's programming-oriented
operators such as optional subexpressions, plus, and character classes. Sections
3.4 through 3.6 introduce finite-state machines and the standard conversions
that explain why regular expressions and finite automata describe the same
class of languages. Section 3.7 then turns the equivalence around: the Pumping
Lemma gives a reusable obstruction to regularity, and the formalization applies
it to the book's non-regular examples and selected exercises.
-/
