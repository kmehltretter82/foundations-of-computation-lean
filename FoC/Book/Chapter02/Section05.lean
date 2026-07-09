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
## Total Functions as Partial Functions

Lean's total functions already match the mathematical model. A partial
function is represented here with {lean}`Option`, where {lit}`some` means
defined and {lit}`none` means undefined. The composition and evaluation
equations that this page shares with the mathematical treatment are already
recorded in the Section 2.4 file as {lit}`composition_value` and
{lit}`evaluation_value`, so they are not repeated here.
-/

theorem total_function_as_partial (f : alpha -> beta) (x : alpha) :
    Fn.TotalAsPartial f x = some (f x) :=
  Fn.total_as_partial_defined f x

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

/-!
## Partial Functions and a Bottom Value

Exercise 13 of Section 2.6 asks for a one-to-one correspondence between the
functions from {lit}`A` to {lit}`B ∪ {⊥}` and the partial functions from
{lit}`A` to {lit}`B`, where {lit}`⊥` is an entity that is not a member of
{lit}`B`. Since the exercise is about the partial functions defined in this
section, the correspondence is formalized here.

The bottom-extended codomain is modeled by a set {lit}`B` together with a
designated element {lit}`bot` outside it, and a function into that codomain is
a total function whose values all lie in {lit}`FSet.Union B (FSet.Singleton bot)`.
The correspondence is an explicit pair of mutually inverse translations:
{lit}`RestrictToPartial` sends the {lit}`bot` outputs to {lit}`none`, and
{lit}`ExtendWithBottom` sends {lit}`none` back to {lit}`bot`. The two
round-trip theorems say the translations are inverse at every input, and the
two value theorems say each translation lands in the intended function space.
The book's hypothesis that {lit}`⊥` is not in {lit}`B` is used exactly once,
to recover a partial function from its bottom-extended form. The restricting
direction is noncomputable because testing whether an output equals
{lit}`bot` has no algorithmic content for an arbitrary codomain type.
-/

open Classical in
noncomputable def RestrictToPartial (bot : beta) (f : alpha -> beta) :
    Fn.Partial alpha beta :=
  fun x => if f x = bot then none else some (f x)

def ExtendWithBottom (bot : beta) (p : Fn.Partial alpha beta) : alpha -> beta :=
  fun x =>
    match p x with
    | none => bot
    | some y => y

theorem restrict_to_partial_values {B : FSet beta} {bot : beta}
    {f : alpha -> beta}
    (hf : forall x, f x ∈ FSet.Union B (FSet.Singleton bot))
    {x : alpha} {y : beta} (h : RestrictToPartial bot f x = some y) :
    y ∈ B := by
  classical
  by_cases hbot : f x = bot
  · simp [RestrictToPartial, hbot] at h
  · simp [RestrictToPartial, hbot] at h
    cases hf x with
    | inl hB =>
        rw [<-h]
        exact hB
    | inr hsing =>
        exact absurd hsing hbot

theorem extend_with_bottom_values {B : FSet beta} {bot : beta}
    {p : Fn.Partial alpha beta}
    (hp : forall x y, p x = some y -> y ∈ B) (x : alpha) :
    ExtendWithBottom bot p x ∈ FSet.Union B (FSet.Singleton bot) := by
  cases hpx : p x with
  | none =>
      have hval : ExtendWithBottom bot p x = bot := by
        simp [ExtendWithBottom, hpx]
      rw [hval]
      exact Or.inr rfl
  | some y =>
      have hval : ExtendWithBottom bot p x = y := by
        simp [ExtendWithBottom, hpx]
      rw [hval]
      exact Or.inl (hp x y hpx)

theorem extend_after_restrict (bot : beta) (f : alpha -> beta) (x : alpha) :
    ExtendWithBottom bot (RestrictToPartial bot f) x = f x := by
  classical
  by_cases hbot : f x = bot
  · simp [ExtendWithBottom, RestrictToPartial, hbot]
  · simp [ExtendWithBottom, RestrictToPartial, hbot]

theorem restrict_after_extend {B : FSet beta} {bot : beta}
    (hbot : ¬ bot ∈ B) {p : Fn.Partial alpha beta}
    (hp : forall x y, p x = some y -> y ∈ B) (x : alpha) :
    RestrictToPartial bot (ExtendWithBottom bot p) x = p x := by
  classical
  cases hpx : p x with
  | none =>
      have hval : ExtendWithBottom bot p x = bot := by
        simp [ExtendWithBottom, hpx]
      simp [RestrictToPartial, hval]
  | some y =>
      have hval : ExtendWithBottom bot p x = y := by
        simp [ExtendWithBottom, hpx]
      have hne : ¬ y = bot := by
        intro hyb
        exact hbot (hyb ▸ hp x y hpx)
      simp [RestrictToPartial, hval, hne]

end Section05
end Chapter02
end Book
end FoC
