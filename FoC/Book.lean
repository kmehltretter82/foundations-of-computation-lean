import FoC.Book.Chapter01
import FoC.Book.Chapter02
import FoC.Book.Chapter03
import FoC.Book.Chapter04
import FoC.Book.Chapter05

set_option doc.verso true

/-!
# Book-Facing Modules

## Chapter-Facing Layer

The {module -checked}`FoC.Book` modules are the reader-facing route through the
formalization. They are organized in the order of the textbook and give each
chapter a stable Lean coordinate for definitions, examples, theorems, selected
exercises, and status notes.

The reusable proofs are deliberately not duplicated here. Instead, the book
pages sit on top of {module}`FoC.Foundation`, {module}`FoC.Languages`,
{module}`FoC.Grammars`, and {module}`FoC.Computability`. A section page usually
does one of three things:

* names the textbook concept with a chapter-facing definition;
* records a theorem, example, or selected exercise under a book-coordinate name;
* points to the reusable construction that proves the underlying result.

This gives the site two reading modes. A textbook reader can follow chapters in
order and see which informal claims have checked statements. A Lean reader can
jump from those wrappers into the reusable library modules and inspect the
actual definitions and proof infrastructure.

## Chapter Map

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
  recursively enumerable languages, machine encodings, reductions, and
  undecidability vocabulary.

## Reading Status

The source textbook remains the reference for exposition and exercises. These
Verso pages are a formal companion: they explain what has been represented,
which reusable library file supplies the machinery, and what the checked Lean
statement says.

Some application material is intentionally not reproduced as Lean code. Circuit
drawings, programming-language examples, parser tables, and machine diagrams are
documented in coverage as application artifacts when the mathematical core has
already been formalized. Larger constructions that require a concrete compiler
or universal machine are stated with explicit construction hypotheses rather
than hidden assumptions.
-/
