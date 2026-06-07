import FoC.Languages.Words
import FoC.Languages.Language
import FoC.Languages.RegularExpression
import FoC.Languages.DFA
import FoC.Languages.NFA
import FoC.Languages.NFAPath
import FoC.Languages.Thompson
import FoC.Languages.Regular
import FoC.Languages.Pumping

set_option doc.verso true

/-!
# Languages

## Regular-Language Layer

The Languages library is the reusable layer beneath Chapter 3.  It gives Lean
representations for words, formal languages, regular expressions, deterministic
and nondeterministic finite automata, and the main regular-language closure and
pumping tools.

The layer is organized around one simple idea: a word is finite data, and a
language is a predicate on words. Regular expressions and automata are then two
different kinds of finite descriptions for such predicates.

## Core Objects

The basic objects are split into small files.  {module}`FoC.Languages.Words`
models strings as lists over an alphabet, while {module}`FoC.Languages.Language`
models languages as predicates on words and defines the usual set and language
operations.  {module}`FoC.Languages.RegularExpression` gives regular-expression
syntax and denotational semantics.

This split keeps notation-heavy word lemmas separate from language-level
closure statements. It also lets later grammar and computability modules reuse
words and languages without depending on regular-expression machinery.

## Automata Semantics

The automata files then provide two equivalent machine models.
{module}`FoC.Languages.DFA` develops deterministic finite automata and their
extended transition function.  {module}`FoC.Languages.NFA` adds nondeterminism
and epsilon transitions, and {module}`FoC.Languages.NFAPath` supplies the path
semantics used by construction proofs.

The path semantics are especially useful in formal proofs: they give a concrete
finite witness for an accepting NFA run, while the reachability-set presentation
is better for executable-style transition closure.

## Regularity and Non-Regularity

The comparison between regular expressions and machines is factored through
{module}`FoC.Languages.Thompson`, which builds NFAs from regular expressions,
and {module}`FoC.Languages.Regular`, which collects the regular-language
vocabulary and closure theorems.  Finally, {module}`FoC.Languages.Pumping`
records the quantified pumping property used in Section 3.7.

The library therefore supports both directions of Chapter 3. To prove that a
language is regular, use expression constructors, automata constructors, or the
conversion theorems. To prove that a language is not regular, use the pumping
property and one of the chapter-facing counterexample schemas.

## Reading Route

These pages explain the reusable API.  The corresponding {module -checked}`FoC.Book.Chapter03`
pages state the chapter-facing definitions, examples, and exercises in the
order of the textbook.

For most readers, the best path is:

* words and language operations;
* regular expressions;
* DFA and NFA semantics;
* Thompson construction and state-elimination/closure results;
* pumping arguments for non-regularity.
-/
