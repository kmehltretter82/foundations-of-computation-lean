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

The Chapter 2 files connect the book's set-theoretic language to predicate-set
definitions in Lean, using the reusable vocabulary in {module}`FoC.Foundation`.
They cover set operations, finite-set bit-vector models, functions, relations,
equivalence relations, orders, countability vocabulary, and the chapter's core
algebraic laws.

The companion HTML rendered from these files is meant to show the actual Lean
statements alongside short explanations of the modeling choices.

The main modeling choice is that a set of elements of type `alpha` is
represented by its membership predicate, `alpha -> Prop`. This makes set
equality, subsets, unions, intersections, and complements ordinary logical
statements about membership. Functions and relations are then introduced on top
of those typed domains.

The later sections use the same perspective for counting arguments. Finite
sets are represented by finite presentations, countability is represented by
encodings into natural numbers, and diagonal arguments are stated as theorems
about what no enumeration or surjection can accomplish.
-/
