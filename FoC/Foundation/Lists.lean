namespace FoC
namespace Foundation

/-!
Small list lemmas and definitions used by the standalone development.

This file starts intentionally small. It should grow only as the book
formalization needs concrete list facts.
-/

def ListContains (xs : List alpha) (x : alpha) : Prop :=
  x ∈ xs

def ListEnumerates (xs : List alpha) (p : alpha -> Prop) : Prop :=
  forall x, p x <-> x ∈ xs

def ListDuplicateFree (xs : List alpha) : Prop :=
  xs.Nodup

def ListUniquelyEnumerates (xs : List alpha) (p : alpha -> Prop) : Prop :=
  ListDuplicateFree xs ∧ ListEnumerates xs p

theorem ListEnumerates.left {xs : List alpha} {p : alpha -> Prop}
    (h : ListEnumerates xs p) {x : alpha} : p x -> x ∈ xs :=
  (h x).mp

theorem ListEnumerates.right {xs : List alpha} {p : alpha -> Prop}
    (h : ListEnumerates xs p) {x : alpha} : x ∈ xs -> p x :=
  (h x).mpr

end Foundation
end FoC
