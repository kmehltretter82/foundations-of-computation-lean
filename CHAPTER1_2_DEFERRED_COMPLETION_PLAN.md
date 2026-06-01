# Chapter 1-2 Deferred Completion Plan

This plan covers the remaining Chapter 1 and Chapter 2 material that was
classified as deferred after the first formal-core pass. The project remains
standalone: no Mathlib, no CSLib, and no hidden assumptions.

## Completion Standard

A deferred item is closed only when one of the following is true:

- it has a proved Lean declaration with a book-coordinate comment,
- it is represented by a small executable/formal model that captures the book's
  mathematical content,
- it is permanently classified as informal/application prose with a specific
  reason in `data/coverage.yaml`.

Completed files must pass:

```sh
lake build
rg --line-number '\bsorry\b|\baxiom\b|\bunsafe\b' FoC README.md data/coverage.yaml
git diff --check
```

## Phase 1: Summation And Natural-Number Induction

Purpose: close the deferred Chapter 1, Section 1.8 summation material that can
be handled over `Nat`.

Add:

- `FoC/Foundation/Summation.lean`
- recursive finite sums over ranges starting at `1` and `0`
- closed forms for selected sums from Chapter 1, Section 1.8

Targets:

- `sum_{i=1}^n i = n(n+1)/2`
- `sum_{i=1}^n i 2^(i-1) = (n-1)2^n + 1` for positive `n`
- `sum_{i=0}^n 2^i = 2^(n+1)-1`
- `sum_{i=1}^n (2i-1) = n^2`

Leave real-valued geometric series deferred until the rational/real layer
exists.

## Phase 2: Integer Divisibility And Parity

Purpose: close Chapter 1, Sections 1.6 and 1.7 integer proof examples.

Add or expand:

- `FoC/Foundation/Integers.lean`
- `FoC/Foundation/Divisibility.lean`

Targets:

- integer even/odd definitions,
- even square is even,
- odd square is odd,
- selected divisibility-by-3 and divisibility-by-4 exercises,
- counterexamples for false exercise claims where appropriate.

Use Lean core `Int` as the carrier type, but prove the book-needed lemmas in
the project.

## Phase 3: Rationals And Irrationality

Purpose: close Chapter 1 rational/irrational proof examples and support the
Chapter 2 countability discussion.

Add:

- `FoC/Foundation/Rationals.lean`
- minimal rational representation as integer pairs with nonzero denominator,
- equality of rational representatives where needed,
- rational addition and multiplication closure.

Targets:

- sum/product of rationals is rational,
- `sqrt(2)` and `sqrt(3)` irrational, formalized through integer-square
  divisibility statements before connecting to rationals,
- rational plus irrational is irrational,
- nonzero rational times irrational is irrational.

Avoid building a full real analysis library unless a later chapter forces it.

## Phase 4: Prime Basics

Purpose: close prime-number examples in Chapter 1 and support future
number-theory exercises.

Add:

- `FoC/Foundation/Primes.lean`

Targets:

- prime and composite definitions over `Nat`,
- every natural number greater than one has a prime divisor,
- every natural number greater than one can be written as a product of primes
  in a simple list-based sense,
- Euclid-style infinitely-many-primes theorem if needed for Chapter 1
  coverage.

## Phase 5: Chapter 1 Recursion Models

Purpose: finish deferred algorithmic material without formalizing Java.

Add or expand:

- factorial specification/correctness lemmas,
- Towers of Hanoi move-count and correctness model,
- binary tree sum correctness,
- Fibonacci lower-bound theorem from Chapter 1, Section 1.10, using the
  weakest standalone numeric setting that faithfully expresses the book claim.

## Phase 6: Finite Cardinality

Purpose: close central Chapter 2, Section 2.6 finite-cardinality material and
prepare for finite automata in Chapter 3.

Add:

- `FoC/Foundation/Cardinality.lean`

Targets:

- cardinality via duplicate-free enumerating lists,
- cardinality well-defined under bijection,
- product cardinality: `|A x B| = |A| * |B|`,
- union cardinality: `|A union B| = |A| + |B| - |A inter B|`,
- disjoint union cardinality,
- powerset cardinality: `|P(A)| = 2^|A|`,
- function-space cardinality: `|A^B| = |A|^|B|`.

## Phase 7: Countability

Purpose: close the countability parts of Chapter 2, Section 2.6.

Targets:

- integers are countable,
- `Nat x Nat` is countable,
- finite unions and countable unions needed by the book,
- nonnegative rationals are countable,
- rationals are countable,
- uncountable-minus-countable theorem.

For real uncountability, prefer a standalone stream/decimal-sequence
diagonalization model unless a full real-number construction becomes necessary.

## Phase 8: Application Sections

Purpose: make application sections precise without overbuilding programming or
database language semantics.

Targets:

- Chapter 2, Section 2.3: bit-vector model for finite subsets and set
  operations,
- Chapter 2, Section 2.5: partial and higher-order function examples,
- Chapter 2, Section 2.8: relational tables, primary keys, insert/delete/update
  and selection models.

Do not formalize C++, JavaScript, or SQL grammars unless that becomes an
explicit later project.

## Phase 9: Coverage Cleanup

After each phase:

- update `data/coverage.yaml`,
- update `FoC/Foundation/README.md`,
- keep `main` buildable,
- commit with `Assisted-By: OpenAI Codex`.

The recommended execution order is:

1. Summation and natural-number induction.
2. Integer divisibility and parity.
3. Finite cardinality.
4. Rationals and countability.
5. Irrationality and real-number-related material.
6. Application models.
7. Final Chapter 1-2 coverage cleanup.
