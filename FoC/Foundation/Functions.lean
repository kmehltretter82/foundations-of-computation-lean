import FoC.Foundation.Sets

set_option doc.verso true

/-!
# Functions

## Function vocabulary

Chapter 2 treats functions as mathematical objects with graphs, images,
preimages, injectivity, surjectivity, and bijectivity.  This module packages
that vocabulary in a small namespace so later chapters can reuse the same
language for encodings, automata maps, and computability statements.

## Book coordinates

Used by:
- Chapter 2, Section 2.4: Functions
- Chapter 2, Section 2.5: Application: Programming with Functions
- Chapter 2, Section 2.6: Counting Past Infinity
-/

namespace FoC
namespace Foundation

namespace Fn

/-!
# Core function notions

The basic predicates record identity, composition, injectivity, surjectivity,
bijectivity, graphs, images, preimages, function spaces, and partial functions.
-/

def Identity (alpha : Type u) : alpha -> alpha :=
  fun x => x

def Compose (g : beta -> gamma) (f : alpha -> beta) : alpha -> gamma :=
  fun x => g (f x)

def Injective (f : alpha -> beta) : Prop :=
  forall {x y}, f x = f y -> x = y

def Surjective (f : alpha -> beta) : Prop :=
  forall y, exists x, f x = y

def Bijective (f : alpha -> beta) : Prop :=
  Injective f ∧ Surjective f

def Graph (f : alpha -> beta) : FSet (alpha × beta) :=
  fun p => p.2 = f p.1

def Image (f : alpha -> beta) (A : FSet alpha) : FSet beta :=
  fun y => exists x, x ∈ A ∧ f x = y

def Preimage (f : alpha -> beta) (B : FSet beta) : FSet alpha :=
  fun x => f x ∈ B

def FunctionSpace (alpha : Type u) (beta : Type v) : FSet (alpha -> beta) :=
  fun _ => True

def Evaluation {alpha : Type u} {beta : Type v} (p : (alpha -> beta) × alpha) : beta :=
  p.1 p.2

def Partial (alpha : Type u) (beta : Type v) : Type (max u v) :=
  alpha -> Option beta

def TotalAsPartial {alpha : Type u} {beta : Type v} (f : alpha -> beta) : Partial alpha beta :=
  fun x => some (f x)

/-!
# Identity and composition

The first proof block establishes the expected identity, associativity, and
composition facts.
-/

theorem identity_injective : Injective (Identity alpha) := by
  intro x y h
  exact h

theorem identity_surjective : Surjective (Identity alpha) := by
  intro y
  exact Exists.intro y rfl

theorem identity_bijective : Bijective (Identity alpha) :=
  And.intro identity_injective identity_surjective

theorem compose_assoc (h : gamma -> delta) (g : beta -> gamma) (f : alpha -> beta) :
    Compose h (Compose g f) = Compose (Compose h g) f :=
  rfl

theorem compose_apply (g : beta -> gamma) (f : alpha -> beta) (x : alpha) :
    Compose g f x = g (f x) :=
  rfl

theorem compose_identity_left (f : alpha -> beta) :
    Compose (Identity beta) f = f :=
  rfl

theorem compose_identity_right (f : alpha -> beta) :
    Compose f (Identity alpha) = f :=
  rfl

theorem injective_comp {f : alpha -> beta} {g : beta -> gamma}
    (hg : Injective g) (hf : Injective f) : Injective (Compose g f) := by
  intro x y h
  exact hf (hg h)

theorem surjective_comp {f : alpha -> beta} {g : beta -> gamma}
    (hf : Surjective f) (hg : Surjective g) : Surjective (Compose g f) := by
  intro z
  cases hg z with
  | intro y hy =>
      cases hf y with
      | intro x hx =>
          exact Exists.intro x (by
            unfold Compose
            rw [hx, hy])

theorem injective_of_comp_injective {f : alpha -> beta} {g : beta -> gamma}
    (hgf : Injective (Compose g f)) : Injective f := by
  intro x y h
  apply hgf
  unfold Compose
  rw [h]

theorem surjective_of_comp_surjective {f : alpha -> beta} {g : beta -> gamma}
    (hgf : Surjective (Compose g f)) : Surjective g := by
  intro z
  cases hgf z with
  | intro x hx =>
      exact Exists.intro (f x) hx

/-!
# Graphs, images, and preimages

Graphs are represented as sets of ordered pairs, and images/preimages are
represented by existential or direct membership conditions.
-/

theorem graph_contains_value (f : alpha -> beta) (x : alpha) :
    (x, f x) ∈ Graph f :=
  rfl

theorem graph_unique_value {f : alpha -> beta} {x : alpha} {y z : beta}
    (hy : (x, y) ∈ Graph f) (hz : (x, z) ∈ Graph f) : y = z :=
  Eq.trans hy hz.symm

theorem image_intro {f : alpha -> beta} {A : FSet alpha}
    {x : alpha} (hx : x ∈ A) : f x ∈ Image f A := by
  exact Exists.intro x (And.intro hx rfl)

theorem preimage_intro {f : alpha -> beta} {B : FSet beta} {x : alpha}
    (hx : f x ∈ B) : x ∈ Preimage f B :=
  hx

theorem image_membership (f : alpha -> beta) (A : FSet alpha) (y : beta) :
    y ∈ Image f A <-> exists x, x ∈ A ∧ f x = y :=
  Iff.rfl

theorem preimage_membership (f : alpha -> beta) (B : FSet beta) (x : alpha) :
    x ∈ Preimage f B <-> f x ∈ B :=
  Iff.rfl

theorem preimage_compose (g : beta -> gamma) (f : alpha -> beta) (C : FSet gamma) :
    FSet.Equal (Preimage (Compose g f) C) (Preimage f (Preimage g C)) := by
  intro x
  constructor <;> intro hx <;> exact hx

theorem preimage_union (f : alpha -> beta) (A B : FSet beta) :
    FSet.Equal (Preimage f (FSet.Union A B))
      (FSet.Union (Preimage f A) (Preimage f B)) := by
  intro x
  constructor
  · intro hx
    exact hx
  · intro hx
    exact hx

theorem preimage_inter (f : alpha -> beta) (A B : FSet beta) :
    FSet.Equal (Preimage f (FSet.Inter A B))
      (FSet.Inter (Preimage f A) (Preimage f B)) := by
  intro x
  constructor
  · intro hx
    exact hx
  · intro hx
    exact hx

theorem preimage_compl (f : alpha -> beta) (A : FSet beta) :
    FSet.Equal (Preimage f (FSet.Compl A)) (FSet.Compl (Preimage f A)) := by
  intro x
  constructor
  · intro hx
    exact hx
  · intro hx
    exact hx

theorem image_union (f : alpha -> beta) (A B : FSet alpha) :
    FSet.Equal (Image f (FSet.Union A B))
      (FSet.Union (Image f A) (Image f B)) := by
  intro y
  constructor
  · intro hy
    cases hy with
    | intro x hx =>
        cases hx.left with
        | inl hA => exact Or.inl (Exists.intro x (And.intro hA hx.right))
        | inr hB => exact Or.inr (Exists.intro x (And.intro hB hx.right))
  · intro hy
    cases hy with
    | inl hA =>
        cases hA with
        | intro x hx =>
            exact Exists.intro x (And.intro (Or.inl hx.left) hx.right)
    | inr hB =>
        cases hB with
        | intro x hx =>
            exact Exists.intro x (And.intro (Or.inr hx.left) hx.right)

theorem image_compose (g : beta -> gamma) (f : alpha -> beta) (A : FSet alpha) :
    FSet.Equal (Image (Compose g f) A) (Image g (Image f A)) := by
  intro z
  constructor
  · intro hz
    cases hz with
    | intro x hx =>
        exact Exists.intro (f x)
          (And.intro (Exists.intro x (And.intro hx.left rfl)) hx.right)
  · intro hz
    cases hz with
    | intro y hy =>
        cases hy.left with
        | intro x hx =>
            exact Exists.intro x (And.intro hx.left (by
              unfold Compose
              rw [hx.right, hy.right]))

/-!
# Injectivity tests

The remaining function lemmas rephrase injectivity in terms of distinct images
and explicit collisions.
-/

theorem injective_iff_distinct_images (f : alpha -> beta) :
    Injective f <-> forall x y, x ≠ y -> f x ≠ f y := by
  classical
  constructor
  · intro hf x y hxy hImage
    exact hxy (hf hImage)
  · intro h x y hImage
    by_cases hxy : x = y
    · exact hxy
    · exact False.elim (h x y hxy hImage)

theorem collision_of_not_injective {f : alpha -> beta}
    (h : ¬ Injective f) : exists x y, x ≠ y ∧ f x = f y := by
  classical
  apply Classical.byContradiction
  intro hno
  apply h
  intro x y hxy
  by_cases hxy' : x = y
  · exact hxy'
  · exfalso
    apply hno
    exact Exists.intro x (Exists.intro y (And.intro hxy' hxy))

/-!
# Partial functions

Total functions embed into partial functions by wrapping every output in
{lit}`some`.
-/

theorem total_as_partial_defined (f : alpha -> beta) (x : alpha) :
    TotalAsPartial f x = some (f x) :=
  rfl

end Fn

end Foundation
end FoC
