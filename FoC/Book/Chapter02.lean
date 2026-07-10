import FoC.Foundation
import FoC.Book.Chapter02.Section01
import FoC.Book.Chapter02.Section02
import FoC.Book.Chapter02.Section03
import FoC.Book.Chapter02.Section04
import FoC.Book.Chapter02.Section05
import FoC.Book.Chapter02.Section06
import FoC.Book.Chapter02.Section07
import FoC.Book.Chapter02.Section08

set_option doc.verso true

/-!
# Chapter 2: Sets, Functions, and Relations

Chapter 2 turns the informal language of collections, mappings, and relations
into the typed vocabulary used by the rest of the project. The reusable support
lives in {module}`FoC.Foundation`.

## Modeling Choice

The main modeling choice is extensional: a set is represented by its membership
predicate. This makes set equality, subsets, unions, intersections, and
complements ordinary logical statements about membership. Functions and
relations are then introduced on top of those typed domains.

Finite sets are represented by finite presentations. Countability is
represented by encodings and partial enumerations. This keeps the proofs close
to the book's arguments while making the hidden quantifiers explicit.

## Story of the Chapter

The early sections establish set operations and their Boolean algebra. The
function sections formalize total, partial, injective, surjective, inverse, and
composition vocabulary. The relation sections define equivalence relations,
orders, and database-style relation operations. The countability section builds
the bridge to diagonal arguments, quotient rationals, Dedekind-cut reals, and
uncountability.

## What to Inspect

For the core set model, start with {module}`FoC.Foundation.Sets`. For functions
and relations, use {module}`FoC.Foundation.Functions` and
{module}`FoC.Foundation.Relations`. For finite and countable material, compare
{module}`FoC.Foundation.Finite`, {module}`FoC.Foundation.Cardinality`, and
{module}`FoC.Foundation.Countable`.

## Formal Coverage

The chapter API includes set algebra, functional graphs, restricted function
spaces, finite cardinality via counting-segment bijections, set-level product,
powerset, union, and function-space laws, partial functions, countability,
Cantor diagonalization, and the rational/real uncountability bridge.

The application sections use fixed-width bitsets and distinguish declarative
database tables from duplicate-free finite storage. Projection, products,
joins, updates, and primary-key preservation are stated through their row
membership semantics.
-/
