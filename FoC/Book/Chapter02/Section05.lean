import FoC.Foundation.Functions

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section05

/-!
# Chapter 2, Section 2.5: Application - Programming with Functions

This section gives a small programming-oriented layer over the function
definitions from {module}`FoC.Foundation.Functions`. It records total
functions as always-defined partial functions, higher-order functions, and
composition for optional results.

The page separates mathematical total functions from program-like partial
computations. {lit}`Option beta` is the formal stand-in for "the computation may
fail to return a beta", and the partial-composition theorems describe how that
failure propagates.
-/

open Foundation

/-!
## Total Functions and Evaluation

Lean's total functions already match the mathematical model. A partial
function is represented here with {lean}`Option`, where {lit}`some` means
defined and {lit}`none` means undefined.
-/

theorem total_function_as_partial (f : alpha -> beta) (x : alpha) :
    Fn.TotalAsPartial f x = some (f x) :=
  Fn.total_as_partial_defined f x

theorem program_compose_value (f : beta -> gamma) (g : alpha -> beta) (x : alpha) :
    Fn.Compose f g x = f (g x) :=
  rfl

theorem evaluation_of_function_value (f : alpha -> beta) (x : alpha) :
    Fn.Evaluation (f, x) = f x :=
  rfl

/-!
## Higher-Order Functions

{lit}`ApplyTwice` is a minimal example of a function that takes another
function as an input. The theorem states its defining equation.

This is the book's first-class function idea in its smallest form: the input
{lit}`f` is data that the new function can call.
-/

def ApplyTwice (f : alpha -> alpha) (x : alpha) : alpha :=
  f (f x)

theorem apply_twice_value (f : alpha -> alpha) (x : alpha) :
    ApplyTwice f x = f (f x) :=
  rfl

/-!
## Partial Composition

Partial composition stops when the first computation is undefined and otherwise
continues by feeding the produced value into the second partial function.

The two following theorems are the two cases a program would branch on: if the
first result is {lit}`none`, the composite is {lit}`none`; if it is {lit}`some y`, the second
function receives {lit}`y`.
-/

def PartialCompose (g : beta -> Option gamma) (f : alpha -> Option beta) :
    alpha -> Option gamma :=
  fun x =>
    match f x with
    | none => none
    | some y => g y

theorem partial_compose_none_left {g : beta -> Option gamma} {f : alpha -> Option beta}
    {x : alpha} (h : f x = none) :
    PartialCompose g f x = none := by
  simp [PartialCompose, h]

theorem partial_compose_some_left {g : beta -> Option gamma} {f : alpha -> Option beta}
    {x : alpha} {y : beta} (h : f x = some y) :
    PartialCompose g f x = g y := by
  simp [PartialCompose, h]

end Section05
end Chapter02
end Book
end FoC
