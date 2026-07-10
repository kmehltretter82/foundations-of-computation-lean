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
**Core function notions.**

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

def RestrictedFunction (A : FSet alpha) (B : FSet beta) :=
  {x // x ∈ A} -> {y // y ∈ B}

def RestrictedFunctionSpace (A : FSet alpha) (B : FSet beta) :
    FSet (RestrictedFunction A B) :=
  FSet.Univ

def FunctionalGraph (A : FSet alpha) (B : FSet beta)
    (R : FSet (alpha × beta)) : Prop :=
  (forall {x y}, (x, y) ∈ R -> x ∈ A ∧ y ∈ B) ∧
    forall x, x ∈ A ->
      exists y, (y ∈ B ∧ (x, y) ∈ R) ∧
        forall z, z ∈ B ∧ (x, z) ∈ R -> z = y

def GraphOfRestrictedFunction {A : FSet alpha} {B : FSet beta}
    (f : RestrictedFunction A B) : FSet (alpha × beta) :=
  fun p => exists hx : p.1 ∈ A, p.2 = (f ⟨p.1, hx⟩).val

structure SetBijection (A : FSet alpha) (B : FSet beta) where
  toFun : {x // x ∈ A} -> {y // y ∈ B}
  injective : Injective toFun
  surjective : Surjective toFun

noncomputable def SetBijection.symm {A : FSet alpha} {B : FSet beta}
    (e : SetBijection A B) : SetBijection B A where
  toFun := fun y => Classical.choose (e.surjective y)
  injective := by
    intro y₁ y₂ h
    have h₁ := Classical.choose_spec (e.surjective y₁)
    have h₂ := Classical.choose_spec (e.surjective y₂)
    apply Subtype.ext
    have := congrArg e.toFun h
    simpa [h₁, h₂] using congrArg Subtype.val this
  surjective := by
    intro x
    refine ⟨e.toFun x, ?_⟩
    apply e.injective
    exact Classical.choose_spec (e.surjective (e.toFun x))

def Image (f : alpha -> beta) (A : FSet alpha) : FSet beta :=
  fun y => exists x, x ∈ A ∧ f x = y

def Preimage (f : alpha -> beta) (B : FSet beta) : FSet alpha :=
  fun x => f x ∈ B

def Evaluation {alpha : Type u} {beta : Type v} (p : (alpha -> beta) × alpha) : beta :=
  p.1 p.2

def Partial (alpha : Type u) (beta : Type v) : Type (max u v) :=
  alpha -> Option beta

def TotalAsPartial {alpha : Type u} {beta : Type v} (f : alpha -> beta) : Partial alpha beta :=
  fun x => some (f x)

/-!
**Identity and composition.**

The first proof block establishes the expected identity, associativity, and
cancellation facts for composition.
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
**Graphs, images, and preimages.**

Graphs are represented as sets of ordered pairs, and images/preimages are
represented by existential or direct membership conditions.
-/

theorem graph_contains_value (f : alpha -> beta) (x : alpha) :
    (x, f x) ∈ Graph f :=
  rfl

theorem graph_unique_value {f : alpha -> beta} {x : alpha} {y z : beta}
    (hy : (x, y) ∈ Graph f) (hz : (x, z) ∈ Graph f) : y = z :=
  Eq.trans hy hz.symm

theorem graphOfRestrictedFunction_functional {A : FSet alpha} {B : FSet beta}
    (f : RestrictedFunction A B) :
    FunctionalGraph A B (GraphOfRestrictedFunction f) := by
  constructor
  · intro x y hxy
    rcases hxy with ⟨hx, hy⟩
    constructor
    · exact hx
    · change y = (f ⟨x, hx⟩).val at hy
      rw [hy]
      exact (f ⟨x, hx⟩).property
  · intro x hx
    refine ⟨(f ⟨x, hx⟩).val,
      ⟨⟨(f ⟨x, hx⟩).property, ⟨hx, rfl⟩⟩, ?_⟩⟩
    intro y hy
    rcases hy.right with ⟨hx', hy'⟩
    exact hy'

noncomputable def FunctionOfFunctionalGraph {A : FSet alpha} {B : FSet beta}
    {R : FSet (alpha × beta)} (hR : FunctionalGraph A B R) :
    RestrictedFunction A B :=
  fun x =>
    ⟨Classical.choose (hR.right x.val x.property),
      (Classical.choose_spec (hR.right x.val x.property)).left.left⟩

theorem graphOf_functionOfFunctionalGraph {A : FSet alpha} {B : FSet beta}
    {R : FSet (alpha × beta)} (hR : FunctionalGraph A B R) :
    FSet.Equal (GraphOfRestrictedFunction (FunctionOfFunctionalGraph hR)) R := by
  intro p
  rcases p with ⟨x, y⟩
  constructor
  · rintro ⟨hx, hy⟩
    change y = (FunctionOfFunctionalGraph hR ⟨x, hx⟩).val at hy
    rw [hy]
    exact (Classical.choose_spec (hR.right x hx)).left.right
  · intro hxy
    have hx := (hR.left hxy).left
    refine ⟨hx, ?_⟩
    exact (Classical.choose_spec (hR.right x hx)).right y
      ⟨(hR.left hxy).right, hxy⟩

theorem functionOf_graphOfRestrictedFunction {A : FSet alpha} {B : FSet beta}
    (f : RestrictedFunction A B) :
    FunctionOfFunctionalGraph (graphOfRestrictedFunction_functional f) = f := by
  funext x
  apply Subtype.ext
  exact (Classical.choose_spec
      ((graphOfRestrictedFunction_functional f).right x.val x.property)).right
    (f x).val
    ⟨(f x).property, ⟨x.property, rfl⟩⟩ |>.symm

def FunctionalGraphSpace (A : FSet alpha) (B : FSet beta) :=
  {R : FSet (alpha × beta) // FunctionalGraph A B R}

def restrictedFunctionGraph {A : FSet alpha} {B : FSet beta}
    (f : RestrictedFunction A B) : FunctionalGraphSpace A B :=
  ⟨GraphOfRestrictedFunction f, graphOfRestrictedFunction_functional f⟩

theorem restrictedFunctionGraph_bijective {A : FSet alpha} {B : FSet beta} :
    Bijective (restrictedFunctionGraph (A := A) (B := B)) := by
  constructor
  · intro f g hfg
    funext x
    apply Subtype.ext
    have hsets := congrArg Subtype.val hfg
    change GraphOfRestrictedFunction f = GraphOfRestrictedFunction g at hsets
    have hmem : (x.val, (f x).val) ∈ GraphOfRestrictedFunction g := by
      rw [← hsets]
      exact ⟨x.property, rfl⟩
    rcases hmem with ⟨hx, hvalue⟩
    simpa using hvalue
  · intro R
    let f := FunctionOfFunctionalGraph R.property
    refine ⟨f, ?_⟩
    apply Subtype.ext
    exact FSet.eq_of_equal (graphOf_functionOfFunctionalGraph R.property)

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
**Injectivity tests.**

The remaining function lemmas rephrase injectivity in terms of distinct images
and explicit collisions.
-/

theorem distinct_images_of_injective {f : alpha -> beta}
    (hf : Injective f) : forall x y, x ≠ y -> f x ≠ f y := by
  intro x y hxy hImage
  exact hxy (hf hImage)

theorem injective_of_distinct_images [DecidableEq alpha]
    {f : alpha -> beta}
    (h : forall x y, x ≠ y -> f x ≠ f y) : Injective f := by
  intro x y hImage
  by_cases hxy : x = y
  · exact hxy
  · exact False.elim (h x y hxy hImage)

theorem injective_iff_distinct_images [DecidableEq alpha]
    (f : alpha -> beta) :
    Injective f <-> forall x y, x ≠ y -> f x ≠ f y := by
  constructor
  · exact distinct_images_of_injective
  · exact injective_of_distinct_images

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
**Partial functions.**

Total functions embed into partial functions by wrapping every output in
{lit}`some`.
-/

theorem total_as_partial_defined (f : alpha -> beta) (x : alpha) :
    TotalAsPartial f x = some (f x) :=
  rfl

end Fn

end Foundation
end FoC
