namespace FoC
namespace Book
namespace Chapter01
namespace Section04

/-!
Book: Chapter 1, Section 1.4, Predicates and Quantifiers.
-/

-- Book: Chapter 1, Section 1.4, Definition 1.6
def OnePlacePredicate (domain : Type u) : Type u :=
  domain -> Prop

-- Book: Chapter 1, Section 1.4, Definition 1.7
def Universal (P : alpha -> Prop) : Prop :=
  forall x, P x

-- Book: Chapter 1, Section 1.4, Definition 1.7
def Existential (P : alpha -> Prop) : Prop :=
  exists x, P x

-- Book: Chapter 1, Section 1.4, Figure 1.5
theorem not_forall_equiv_exists_not (P : alpha -> Prop) :
    (¬ forall x, P x) <-> exists x, ¬ P x := by
  classical
  constructor
  · intro h
    exact Classical.byContradiction (fun hnone =>
      h (fun x =>
        Classical.byContradiction (fun hx =>
          hnone (Exists.intro x hx))))
  · intro h hforall
    cases h with
    | intro x hx =>
        exact hx (hforall x)

-- Book: Chapter 1, Section 1.4, Figure 1.5
theorem not_exists_equiv_forall_not (P : alpha -> Prop) :
    (¬ exists x, P x) <-> forall x, ¬ P x := by
  constructor
  · intro h x hx
    exact h (Exists.intro x hx)
  · intro h hexists
    cases hexists with
    | intro x hx =>
        exact h x hx

-- Book: Chapter 1, Section 1.4, Figure 1.5
theorem forall_comm (Q : alpha -> beta -> Prop) :
    (forall x, forall y, Q x y) <-> forall y, forall x, Q x y := by
  constructor
  · intro h y x
    exact h x y
  · intro h x y
    exact h y x

-- Book: Chapter 1, Section 1.4, Figure 1.5
theorem exists_comm (Q : alpha -> beta -> Prop) :
    (exists x, exists y, Q x y) <-> exists y, exists x, Q x y := by
  constructor
  · intro h
    cases h with
    | intro x hy =>
        cases hy with
        | intro y hq =>
            exact Exists.intro y (Exists.intro x hq)
  · intro h
    cases h with
    | intro y hx =>
        cases hx with
        | intro x hq =>
            exact Exists.intro x (Exists.intro y hq)

end Section04
end Chapter01
end Book
end FoC
