import FoC.Foundation.Functions

namespace FoC
namespace Book
namespace Chapter02
namespace Section04

/-!
Book: Chapter 2, Section 2.4, Functions.
-/

open Foundation

-- Book: Chapter 2, Section 2.4, composition.
theorem composition_value (g : beta -> gamma) (f : alpha -> beta) (x : alpha) :
    Fn.Compose g f x = g (f x) :=
  rfl

-- Book: Chapter 2, Section 2.4, graph of a function.
theorem graph_contains_value (f : alpha -> beta) (x : alpha) :
    (x, f x) ∈ Fn.Graph f :=
  Fn.graph_contains_value f x

-- Book: Chapter 2, Section 2.4, a graph has only one value at each input.
theorem graph_unique_value {f : alpha -> beta} {x : alpha} {y z : beta}
    (hy : (x, y) ∈ Fn.Graph f) (hz : (x, z) ∈ Fn.Graph f) : y = z :=
  Fn.graph_unique_value hy hz

-- Book: Chapter 2, Section 2.4, onto/surjective definition.
theorem surjective_definition (f : alpha -> beta) :
    Fn.Surjective f <-> forall y, exists x, f x = y :=
  Iff.rfl

-- Book: Chapter 2, Section 2.4, one-to-one/injective definition.
theorem injective_definition (f : alpha -> beta) :
    Fn.Injective f <-> forall {x y}, f x = f y -> x = y :=
  Iff.rfl

-- Book: Chapter 2, Section 2.4, contrapositive form of one-to-one.
theorem injective_iff_distinct_images (f : alpha -> beta) :
    Fn.Injective f <-> forall x y, x ≠ y -> f x ≠ f y :=
  Fn.injective_iff_distinct_images f

-- Book: Chapter 2, Section 2.4, bijective definition.
theorem bijective_definition (f : alpha -> beta) :
    Fn.Bijective f <-> Fn.Injective f ∧ Fn.Surjective f :=
  Iff.rfl

-- Book: Chapter 2, Section 2.4, evaluation function.
theorem evaluation_value (f : alpha -> beta) (x : alpha) :
    Fn.Evaluation (f, x) = f x :=
  rfl

-- Book: Chapter 2, Section 2.4, Exercise 5.
theorem composition_associative
    (h : gamma -> delta) (g : beta -> gamma) (f : alpha -> beta) :
    Fn.Compose h (Fn.Compose g f) = Fn.Compose (Fn.Compose h g) f :=
  Fn.compose_assoc h g f

-- Book: Chapter 2, Section 2.4, Exercise 6(a).
theorem composition_injective_implies_first_injective
    {f : alpha -> beta} {g : beta -> gamma}
    (hgf : Fn.Injective (Fn.Compose g f)) : Fn.Injective f :=
  Fn.injective_of_comp_injective hgf

-- Book: Chapter 2, Section 2.4, Exercise 7(a).
theorem composition_surjective_implies_second_surjective
    {f : alpha -> beta} {g : beta -> gamma}
    (hgf : Fn.Surjective (Fn.Compose g f)) : Fn.Surjective g :=
  Fn.surjective_of_comp_surjective hgf

-- Book: Chapter 2, Section 2.4, identity is a bijection.
theorem identity_bijective : Fn.Bijective (Fn.Identity alpha) :=
  Fn.identity_bijective

end Section04
end Chapter02
end Book
end FoC
