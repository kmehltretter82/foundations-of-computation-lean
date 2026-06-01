import FoC.Foundation.Functions

namespace FoC
namespace Book
namespace Chapter02
namespace Section05

/-!
Book: Chapter 2, Section 2.5, Application: Programming with Functions.
-/

open Foundation

-- Book: Chapter 2, Section 2.5, total functions as partial functions.
theorem total_function_as_partial (f : alpha -> beta) (x : alpha) :
    Fn.TotalAsPartial f x = some (f x) :=
  Fn.total_as_partial_defined f x

-- Book: Chapter 2, Section 2.5, JavaScript-style compose exercise.
theorem program_compose_value (f : beta -> gamma) (g : alpha -> beta) (x : alpha) :
    Fn.Compose f g x = f (g x) :=
  rfl

-- Book: Chapter 2, Section 2.5, functions are first-class values in the model.
theorem evaluation_of_function_value (f : alpha -> beta) (x : alpha) :
    Fn.Evaluation (f, x) = f x :=
  rfl

def ApplyTwice (f : alpha -> alpha) (x : alpha) : alpha :=
  f (f x)

-- Book: Chapter 2, Section 2.5, higher-order functions take functions as inputs.
theorem apply_twice_value (f : alpha -> alpha) (x : alpha) :
    ApplyTwice f x = f (f x) :=
  rfl

def PartialCompose (g : beta -> Option gamma) (f : alpha -> Option beta) :
    alpha -> Option gamma :=
  fun x =>
    match f x with
    | none => none
    | some y => g y

-- Book: Chapter 2, Section 2.5, partial composition is undefined when the first map is.
theorem partial_compose_none_left {g : beta -> Option gamma} {f : alpha -> Option beta}
    {x : alpha} (h : f x = none) :
    PartialCompose g f x = none := by
  simp [PartialCompose, h]

-- Book: Chapter 2, Section 2.5, partial composition continues when the first map is defined.
theorem partial_compose_some_left {g : beta -> Option gamma} {f : alpha -> Option beta}
    {x : alpha} {y : beta} (h : f x = some y) :
    PartialCompose g f x = g y := by
  simp [PartialCompose, h]

end Section05
end Chapter02
end Book
end FoC
