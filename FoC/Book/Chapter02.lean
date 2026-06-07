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

## Status Notes

The formal core of the chapter is covered. The set sections include the
membership tests, subset/equality principles, Boolean algebra laws, De Morgan
laws, absorption identities, universe/empty identities, and difference
simplifications. The programming-with-sets section mirrors these laws in the
bit-vector model where finite-set operations are pointwise Boolean operations.

The function and counting sections cover graphs, images, preimages,
composition, injectivity, surjectivity, countability, Cantor diagonalization,
and the rational/real uncountability bridge. Recent cleanup adds exact
image/preimage transport laws for composition, union, intersection, and
complement.

The relation and database sections cover equivalence classes, partitions,
class overlap/disjointness, transitive closure, relational tables, filtering,
updates, and primary-key preservation under insertion, selection, and deletion.
Programming-language examples and database-management-system implementation
details remain application material rather than formal source obligations.
-/
