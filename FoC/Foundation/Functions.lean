namespace FoC
namespace Foundation

/-!
Standalone function vocabulary used in Chapter 2.
-/

namespace Fn

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

end Fn

end Foundation
end FoC

