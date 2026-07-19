import FoC.Foundation.Countable

set_option doc.verso true

/-!
# Countable images

An explicit partial enumeration remains an enumeration after mapping every
present value through a function.  This small bridge lets later cardinality
arguments state the exact image being counted rather than merely bounding it
by an unrelated universal set.
-/

namespace FoC
namespace Foundation
namespace FSet

/-- The image of a countable predicate set under any function is countable. -/
theorem countable_image
    {A : FSet alpha} (hA : Countable A) (f : alpha -> beta) :
    Countable (Fn.Image f A) := by
  rcases hA with ⟨enumerate, henumerate⟩
  refine ⟨fun n => (enumerate n).map f, ?_⟩
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (henumerate x).1 hx with ⟨n, hn⟩
    exact ⟨n, by simp [hn]⟩
  · rintro ⟨n, hn⟩
    cases henum : enumerate n with
    | none => simp [henum] at hn
    | some x =>
        have hfx : f x = y := by simpa [henum] using hn
        exact ⟨x, (henumerate x).2 ⟨n, henum⟩, hfx⟩

end FSet
end Foundation
end FoC
