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

end Section05
end Chapter02
end Book
end FoC
