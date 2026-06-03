import FoC.Book.Chapter01
import FoC.Book.Chapter02
import FoC.Book.Chapter03
import FoC.Book.Chapter04
import FoC.Book.Chapter05

set_option doc.verso true

/-!
# Book-Facing Modules

## Chapter-facing layer

The `FoC.Book` modules are organized in the order of the textbook.  They state
the definitions, examples, theorems, and selected exercises as chapter-facing
Lean files, while the reusable infrastructure remains in the Foundation,
Languages, Grammars, and Computability libraries.

Each page is meant to be read in two layers. The prose explains the informal
mathematical idea and points out the modeling choice used in Lean. The
following declarations then give the exact statements that have been checked.
When a page delegates a large construction to a reusable module, the book page
usually records the chapter-level theorem, a named wrapper, or the concrete
example from the text.

* {module}`FoC.Book.Chapter01` covers logic, proof methods, induction,
  elementary number theory examples, finite sums, recursive definitions, and
  Fibonacci estimates.
* {module}`FoC.Book.Chapter02` covers sets, functions, relations, finite
  cardinality, countability, and diagonal arguments.
* {module}`FoC.Book.Chapter03` covers languages, regular expressions, finite
  automata, regular-language closure, and pumping-lemma statements.
* {module}`FoC.Book.Chapter04` covers context-free grammars, BNF, parse trees,
  pushdown automata, grammar-automaton conversions, and general grammars.
* {module}`FoC.Book.Chapter05` covers Turing machines, computable functions,
  recursively enumerable languages, and undecidability vocabulary.

The source textbook remains the reference for exposition and exercises. These
Verso pages are a formal companion: they explain what has been represented,
which reusable library file supplies the machinery, and what the checked Lean
statement says.
-/
