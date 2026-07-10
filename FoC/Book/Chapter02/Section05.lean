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

{lit}`applyTwice` is a minimal example of a function that takes another
function as an input. The theorem states its defining equation.

This is the book's first-class function idea in its smallest form: the input
{lit}`f` is data that the new function can call.
-/

def applyTwice (f : alpha -> alpha) (x : alpha) : alpha :=
  f (f x)

theorem apply_twice_value (f : alpha -> alpha) (x : alpha) :
    applyTwice f x = f (f x) :=
  rfl

/-!
## Partial Composition

Partial composition stops when the first computation is undefined and otherwise
continues by feeding the produced value into the second partial function.

The two following theorems are the two cases a program would branch on: if the
first result is {lit}`none`, the composite is {lit}`none`; if it is {lit}`some y`, the second
function receives {lit}`y`.
-/

def partialCompose (g : beta -> Option gamma) (f : alpha -> Option beta) :
    alpha -> Option gamma :=
  fun x =>
    match f x with
    | none => none
    | some y => g y

theorem partial_compose_none_left {g : beta -> Option gamma} {f : alpha -> Option beta}
    {x : alpha} (h : f x = none) :
    partialCompose g f x = none := by
  simp [partialCompose, h]

theorem partial_compose_some_left {g : beta -> Option gamma} {f : alpha -> Option beta}
    {x : alpha} {y : beta} (h : f x = some y) :
    partialCompose g f x = g y := by
  simp [partialCompose, h]

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
{lit}`restrictToPartial` sends the {lit}`bot` outputs to {lit}`none`, and
{lit}`extendWithBottom` sends {lit}`none` back to {lit}`bot`. The two
round-trip theorems say the translations are inverse at every input, and the
two value theorems say each translation lands in the intended function space.
The book's hypothesis that {lit}`⊥` is not in {lit}`B` is used to recover a
partial function from its bottom-extended form. The restricting direction is
computable when the codomain has decidable equality, and the final theorem
packages the constrained subtype spaces as a bijection.
-/

def restrictToPartial [DecidableEq beta] (bot : beta) (f : alpha -> beta) :
    Fn.Partial alpha beta :=
  fun x => if f x = bot then none else some (f x)

def extendWithBottom (bot : beta) (p : Fn.Partial alpha beta) : alpha -> beta :=
  fun x =>
    match p x with
    | none => bot
    | some y => y

theorem restrict_to_partial_values [DecidableEq beta] {B : FSet beta} {bot : beta}
    {f : alpha -> beta}
    (hf : forall x, f x ∈ FSet.Union B (FSet.Singleton bot))
    {x : alpha} {y : beta} (h : restrictToPartial bot f x = some y) :
    y ∈ B := by
  by_cases hbot : f x = bot
  · simp [restrictToPartial, hbot] at h
  · simp [restrictToPartial, hbot] at h
    cases hf x with
    | inl hB =>
        rw [<-h]
        exact hB
    | inr hsing =>
        exact absurd hsing hbot

theorem extend_with_bottom_values {B : FSet beta} {bot : beta}
    {p : Fn.Partial alpha beta}
    (hp : forall x y, p x = some y -> y ∈ B) (x : alpha) :
    extendWithBottom bot p x ∈ FSet.Union B (FSet.Singleton bot) := by
  cases hpx : p x with
  | none =>
      have hval : extendWithBottom bot p x = bot := by
        simp [extendWithBottom, hpx]
      rw [hval]
      exact Or.inr rfl
  | some y =>
      have hval : extendWithBottom bot p x = y := by
        simp [extendWithBottom, hpx]
      rw [hval]
      exact Or.inl (hp x y hpx)

theorem extend_after_restrict [DecidableEq beta]
    (bot : beta) (f : alpha -> beta) (x : alpha) :
    extendWithBottom bot (restrictToPartial bot f) x = f x := by
  by_cases hbot : f x = bot
  · simp [extendWithBottom, restrictToPartial, hbot]
  · simp [extendWithBottom, restrictToPartial, hbot]

theorem restrict_after_extend [DecidableEq beta] {B : FSet beta} {bot : beta}
    (hbot : ¬ bot ∈ B) {p : Fn.Partial alpha beta}
    (hp : forall x y, p x = some y -> y ∈ B) (x : alpha) :
    restrictToPartial bot (extendWithBottom bot p) x = p x := by
  cases hpx : p x with
  | none =>
      have hval : extendWithBottom bot p x = bot := by
        simp [extendWithBottom, hpx]
      simp [restrictToPartial, hval]
  | some y =>
      have hval : extendWithBottom bot p x = y := by
        simp [extendWithBottom, hpx]
      have hne : ¬ y = bot := by
        intro hyb
        exact hbot (hyb ▸ hp x y hpx)
      simp [restrictToPartial, hval, hne]

def BottomValuedFunctions {alpha : Type u} (B : FSet beta) (bot : beta) :=
  {f : alpha -> beta // forall x, f x ∈ FSet.Union B (FSet.Singleton bot)}

def PartialFunctionsInto {alpha : Type u} (B : FSet beta) :=
  {p : Fn.Partial alpha beta // forall x y, p x = some y -> y ∈ B}

def restrictBottomValued [DecidableEq beta] {B : FSet beta} {bot : beta}
    (f : BottomValuedFunctions (alpha := alpha) B bot) :
    PartialFunctionsInto (alpha := alpha) B :=
  ⟨restrictToPartial bot f.val, fun _ _ h =>
    restrict_to_partial_values f.property h⟩

def extendPartialValued {B : FSet beta} {bot : beta}
    (p : PartialFunctionsInto (alpha := alpha) B) :
    BottomValuedFunctions (alpha := alpha) B bot :=
  ⟨extendWithBottom bot p.val, extend_with_bottom_values p.property⟩

theorem bottomValue_partialFunction_bijective [DecidableEq beta]
    {B : FSet beta} {bot : beta} (hbot : ¬ bot ∈ B) :
    Fn.Bijective
      (restrictBottomValued (alpha := alpha) (B := B) (bot := bot)) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    funext x
    have hp := congrArg Subtype.val hfg
    have hf := extend_after_restrict bot f.val x
    have hg := extend_after_restrict bot g.val x
    exact hf.symm.trans
      ((congrFun (congrArg (extendWithBottom bot) hp) x).trans hg)
  · intro p
    refine ⟨extendPartialValued (bot := bot) p, ?_⟩
    apply Subtype.ext
    funext x
    exact restrict_after_extend hbot p.property x

end Section05
end Chapter02
end Book
end FoC
