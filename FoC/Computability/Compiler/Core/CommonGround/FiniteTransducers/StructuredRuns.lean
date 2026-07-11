import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured

/-!
# Shared run-composition vocabulary for structured descriptions

Raw-level companion to `Structured/Lowering/TypedStateTableExecution.lean`.
Most compiler machines are built as raw `Description`s rather than typed
tables, and each run proof currently re-derives step composition and loop
induction from `runConfig_add`.  This module packages an exact-step relation
`RunsIn`, its step-count-free existential `Leads`, and the standard
`refl`/`trans`/one-step/list/unary combinators once, so downstream leaves cite
a lemma instead of hand-rolling `induction ... generalizing` over
`runConfig`.

The older per-file `Leads` relations use the continuation form
`exists steps, forall tail, runConfig (tail + steps) c = runConfig tail d`.
That form is equivalent to `Leads` here (`continues` and `of_continues`), so
those files can drop their local relation and its lemmas.
-/

namespace FoC
namespace Computability
namespace CommonGround
namespace FiniteTransducers
namespace Structured

namespace Description

variable (D : Description)

/-- Exact execution: `D` runs from `c` to `d` in exactly `steps` steps. -/
def RunsIn (steps : Nat) (c d : Configuration) : Prop :=
  D.runConfig steps c = d

/-- Step-count-free reachability between configurations. -/
def Leads (c d : Configuration) : Prop :=
  exists steps : Nat, D.RunsIn steps c d

namespace RunsIn

theorem refl (c : Configuration) : D.RunsIn 0 c c := rfl

theorem trans {c d e : Configuration} {n m : Nat}
    (h1 : D.RunsIn n c d) (h2 : D.RunsIn m d e) :
    D.RunsIn (n + m) c e := by
  unfold Description.RunsIn at h1 h2 ⊢
  rw [D.runConfig_add, h1, h2]

/-- An exact run stays valid before any common continuation. -/
theorem continues {n tail : Nat} {c d : Configuration}
    (h : D.RunsIn n c d) :
    D.runConfig (tail + n) c = D.runConfig tail d := by
  unfold Description.RunsIn at h
  rw [Nat.add_comm, D.runConfig_add, h]

end RunsIn

namespace Leads

theorem refl (c : Configuration) : D.Leads c c :=
  ⟨0, RunsIn.refl D c⟩

theorem trans {c d e : Configuration}
    (h1 : D.Leads c d) (h2 : D.Leads d e) :
    D.Leads c e := by
  obtain ⟨n, h1⟩ := h1
  obtain ⟨m, h2⟩ := h2
  exact ⟨n + m, RunsIn.trans D h1 h2⟩

theorem to_runConfig {c d : Configuration} (h : D.Leads c d) :
    exists steps : Nat, D.runConfig steps c = d := h

/-- Continuation form used by the older per-file `Leads` relations. -/
theorem continues {c d : Configuration} (h : D.Leads c d) :
    exists steps : Nat, forall tail : Nat,
      D.runConfig (tail + steps) c = D.runConfig tail d := by
  obtain ⟨steps, h⟩ := h
  exact ⟨steps, fun tail => RunsIn.continues D h⟩

/-- Recover `Leads` from the continuation form (`tail = 0`). -/
theorem of_continues {c d : Configuration}
    (h : exists steps : Nat, forall tail : Nat,
      D.runConfig (tail + steps) c = D.runConfig tail d) :
    D.Leads c d := by
  obtain ⟨steps, h⟩ := h
  exact ⟨steps, by simpa [Description.RunsIn, runConfig] using h 0⟩

end Leads

/-- A single structured step lifts to a one-step lead. -/
theorem leads_step_of_stepConfig {c d : Configuration}
    (h : D.stepConfig c = some d) : D.Leads c d :=
  ⟨1, by simp [Description.RunsIn, runConfig, h]⟩

/-- List induction: a per-element lead composes across a whole list,
    threading an accumulator via `List.foldl`. -/
theorem leads_list {alpha beta : Type}
    (inv : List alpha -> beta -> Configuration)
    (update : beta -> alpha -> beta)
    (hstep : forall (x : alpha) (xs : List alpha) (acc : beta),
      D.Leads (inv (x :: xs) acc) (inv xs (update acc x)))
    (input : List alpha) (acc : beta) :
    D.Leads (inv input acc) (inv [] (input.foldl update acc)) := by
  induction input generalizing acc with
  | nil => exact Leads.refl D _
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact Leads.trans D (hstep x xs acc) (ih (update acc x))

/-- Unary drive down a natural-number indexed configuration family. -/
theorem leads_unary
    (inv : Nat -> Configuration)
    (hstep : forall (n : Nat), D.Leads (inv (n + 1)) (inv n))
    (n : Nat) :
    D.Leads (inv n) (inv 0) := by
  induction n with
  | zero => exact Leads.refl D _
  | succ k ih => exact Leads.trans D (hstep k) ih

end Description

end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
