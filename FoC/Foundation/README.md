# Foundation Traceability

The `Foundation/` modules are standalone infrastructure for the book-facing
formalization. They should grow only when a book coordinate needs reusable
definitions or lemmas.

| Module | Why it exists |
| --- | --- |
| `Logic.lean` | Chapter 1 propositional logic, Boolean algebra, deduction, and substitution laws. |
| `Lists.lean` | Chapter 2 finite enumeration infrastructure and later finite alphabets/states. |
| `Sets.lean` | Chapter 2 set operations, Boolean algebra of sets, powersets, and Cantor diagonalization. |
| `Functions.lean` | Chapter 2 functions, graphs, image/preimage, composition, partial functions, evaluation, and the Chapter 1 pigeonhole collision schema. |
| `Finite.lean` | Chapter 2 finite sets by list enumeration, including finite-subset closure; later finite automata state sets. |
| `Countable.lean` | Chapter 2 countability by explicit natural-number enumeration, countable unions, and uncountable-difference arguments. |
| `Relations.lean` | Chapter 2 binary relations, equivalence classes, partitions, and transitive closure. |
| `Arithmetic.lean` | Chapter 1 proof examples using divisibility and parity. |
| `Summation.lean` | Chapter 1 induction examples with finite sums and geometric-series cores; later Chapter 2 finite-cardinality arithmetic. |
| `Integers.lean` | Chapter 1 integer parity and divisibility examples; later Chapter 2 integer countability. |
| `Rationals.lean` | Chapter 1 rational-number closure examples; later Chapter 2 rational countability. |
| `RationalCore.lean` | Chapter 1 reduced rational-square-root contradiction proofs; future quotient-rational and real embedding bridge. |
| `QuotientRationals.lean` | Quotient rational numbers over positive-denominator integer fractions, with arithmetic, order, density, and embeddings for future Dedekind-cut reals. |
| `Reals.lean` | Dedekind-cut real numbers over quotient rationals, with rational embedding, order, density, and rational/irrational predicates for future book wrappers. |
| `QuadraticSurd.lean` | Chapter 1 surrogate model for `sqrt(2)` examples before a full real-number construction exists. |
| `DigitStreams.lean` | Chapter 2 diagonal uncountability core for future real-number uncountability. |
| `Primes.lean` | Chapter 1 prime divisor, Euclid prime-list, and product-of-primes induction examples. |
| `Cardinality.lean` | Chapter 2 finite-cardinality laws via explicit list products, sublists, tuples, and cardinality witnesses. |
