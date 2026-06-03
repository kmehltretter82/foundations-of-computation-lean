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

## Regular-language layer

The Languages library is the reusable layer beneath Chapter 3.  It gives Lean
representations for words, formal languages, regular expressions, deterministic
and nondeterministic finite automata, and the main regular-language closure and
pumping tools.

The basic objects are split into small files.  {module}`FoC.Languages.Words`
models strings as lists over an alphabet, while {module}`FoC.Languages.Language`
models languages as predicates on words and defines the usual set and language
operations.  {module}`FoC.Languages.RegularExpression` gives regular-expression
syntax and denotational semantics.

The automata files then provide two equivalent machine models.
{module}`FoC.Languages.DFA` develops deterministic finite automata and their
extended transition function.  {module}`FoC.Languages.NFA` adds nondeterminism
and epsilon transitions, and {module}`FoC.Languages.NFAPath` supplies the path
semantics used by construction proofs.

The comparison between regular expressions and machines is factored through
{module}`FoC.Languages.Thompson`, which builds NFAs from regular expressions,
and {module}`FoC.Languages.Regular`, which collects the regular-language
vocabulary and closure theorems.  Finally, {module}`FoC.Languages.Pumping`
records the quantified pumping property used in Section 3.7.

These pages explain the reusable API.  The corresponding {module -checked}`FoC.Book.Chapter03`
pages state the chapter-facing definitions, examples, and exercises in the
order of the textbook.
-/
