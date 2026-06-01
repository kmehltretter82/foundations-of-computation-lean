# Foundation Traceability

The `Foundation/` modules are standalone infrastructure for the book-facing
formalization. They should grow only when a book coordinate needs reusable
definitions or lemmas.

| Module | Why it exists |
| --- | --- |
| `Logic.lean` | Chapter 1 propositional logic, Boolean algebra, deduction, and substitution laws. |
| `Lists.lean` | Chapter 2 finite enumeration infrastructure and later finite alphabets/states. |
| `Sets.lean` | Chapter 2 set operations, Boolean algebra of sets, powersets, and Cantor diagonalization. |
| `Functions.lean` | Chapter 2 functions, graphs, image/preimage, composition, partial functions, and evaluation. |
| `Finite.lean` | Chapter 2 finite sets by list enumeration; later finite automata state sets. |
| `Countable.lean` | Chapter 2 countability by explicit natural-number enumeration. |
| `Relations.lean` | Chapter 2 binary relations, equivalence classes, partitions, and transitive closure. |
| `Arithmetic.lean` | Chapter 1 proof examples using divisibility and parity. |
| `Summation.lean` | Chapter 1 induction examples with finite sums; later Chapter 2 finite-cardinality arithmetic. |
| `Integers.lean` | Chapter 1 integer parity and divisibility examples; later Chapter 2 integer countability. |
