import FoC.Foundation.Functions

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section04

/-!
# Chapter 2, Section 2.4: Functions

This section records the chapter's function vocabulary: composition, graphs,
surjective and injective functions, bijections, and the evaluation operation.
The reusable definitions live in {module}`FoC.Foundation.Functions`.

Lean's function type already represents total mathematical functions. This
page mostly names the properties the book studies and records how they behave
under composition, graphs, and evaluation.
-/

open Foundation

/-!
## Composition and Graphs

Composition is stated by its value at an input. The graph statements connect
the function-as-rule view to the relation-as-set-of-pairs view: the graph
contains each actual value and cannot contain two different values for one
input.
-/

theorem composition_value (g : beta -> gamma) (f : alpha -> beta) (x : alpha) :
    Fn.Compose g f x = g (f x) :=
  rfl

theorem graph_contains_value (f : alpha -> beta) (x : alpha) :
    (x, f x) ∈ Fn.Graph f :=
  Fn.graph_contains_value f x

theorem graph_unique_value {f : alpha -> beta} {x : alpha} {y z : beta}
    (hy : (x, y) ∈ Fn.Graph f) (hz : (x, z) ∈ Fn.Graph f) : y = z :=
  Fn.graph_unique_value hy hz

/-!
## Injective, Surjective, and Bijective

The next statements expose the formal meanings of one-to-one, onto, and
bijection. The distinct-images theorem is the usual contrapositive form of
injectivity.

The quantifier order matters: injectivity starts with two inputs and compares
their outputs, while surjectivity starts with a desired output and asks for an
input that reaches it.
-/

theorem surjective_definition (f : alpha -> beta) :
    Fn.Surjective f <-> forall y, exists x, f x = y :=
  Iff.rfl

theorem injective_definition (f : alpha -> beta) :
    Fn.Injective f <-> forall {x y}, f x = f y -> x = y :=
  Iff.rfl

theorem injective_iff_distinct_images (f : alpha -> beta) :
    Fn.Injective f <-> forall x y, x ≠ y -> f x ≠ f y :=
  Fn.injective_iff_distinct_images f

theorem bijective_definition (f : alpha -> beta) :
    Fn.Bijective f <-> Fn.Injective f ∧ Fn.Surjective f :=
  Iff.rfl

/-!
## Evaluation and Exercises

The evaluation statement treats applying a function to an input as a function
on pairs. The exercise wrappers record associativity of composition and the
one-sided consequences of an injective or surjective composite.
-/

theorem evaluation_value (f : alpha -> beta) (x : alpha) :
    Fn.Evaluation (f, x) = f x :=
  rfl

theorem composition_associative
    (h : gamma -> delta) (g : beta -> gamma) (f : alpha -> beta) :
    Fn.Compose h (Fn.Compose g f) = Fn.Compose (Fn.Compose h g) f :=
  Fn.compose_assoc h g f

theorem composition_injective_implies_first_injective
    {f : alpha -> beta} {g : beta -> gamma}
    (hgf : Fn.Injective (Fn.Compose g f)) : Fn.Injective f :=
  Fn.injective_of_comp_injective hgf

theorem composition_surjective_implies_second_surjective
    {f : alpha -> beta} {g : beta -> gamma}
    (hgf : Fn.Surjective (Fn.Compose g f)) : Fn.Surjective g :=
  Fn.surjective_of_comp_surjective hgf

theorem identity_bijective : Fn.Bijective (Fn.Identity alpha) :=
  Fn.identity_bijective

end Section04
end Chapter02
end Book
end FoC
