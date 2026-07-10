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
# Chapter 3: Regular Expressions and Finite-State Automata

Chapter 3 is the first automata-theory chapter. It starts with words and
languages, then shows that regular expressions and finite automata describe the
same class of languages, and finally uses pumping arguments to prove that some
languages are not regular.

These files are the chapter-facing layer over reusable language and automata
modules in {module}`FoC.Languages`.

The Lean library broadens the book's alphabet convention. Words and languages
are defined over an arbitrary element type; finite alphabets are introduced as
explicit hypotheses or finite witnesses for automata and regular-expression
conversion theorems that need them.

## Story of the Chapter

The chapter follows the book's progression. Sections 3.1 through 3.3 set up
languages and regular expressions, including the book's programming-oriented
operators such as optional subexpressions, plus, and character classes. Sections
3.4 through 3.6 introduce finite-state machines and the standard conversions
that explain why regular expressions and finite automata describe the same
class of languages. Section 3.7 then turns the equivalence around: the Pumping
Lemma gives a reusable obstruction to regularity, and the formalization applies
it to the book's non-regular examples and selected exercises.

## What to Inspect

For words and language operations, start with {module}`FoC.Languages.Words` and
{module}`FoC.Languages.Language`. For regular expressions, see
{module}`FoC.Languages.RegularExpression`. For automata, compare
{module}`FoC.Languages.DFA`, {module}`FoC.Languages.NFA`, and
{module}`FoC.Languages.NFAPath`.

The equivalence machinery is split deliberately. {module}`FoC.Languages.Thompson`
constructs NFAs from regular expressions, while {module}`FoC.Languages.Regular`
collects regular-language closure and recognition theorems. The pumping
infrastructure lives in {module}`FoC.Languages.Pumping` and is used by
{module}`FoC.Book.Chapter03.Section07`.

## Coverage

The formalization includes the uncountability of the collection of languages
over a finite nonempty alphabet, regular-expression-to-NFA, NFA-to-DFA,
DFA/NFA-to-regular-expression, and closure under the book's regular-language
operations. Pumping arguments cover the main nonregular example and the four
exercise families from Section 3.7.

Editor-specific regular-expression syntax and search/replace behavior remain
application material; their mathematical language operators are represented by
checked semantic theorems.
-/
