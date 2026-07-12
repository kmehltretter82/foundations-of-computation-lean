import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable

set_option doc.verso true

/-!
# Run combinators for typed three-tape tables

Step-count-free reachability, its one-row constructor, and the small explicit
tape-window identities used by typed structured-machine run proofs.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

open ThreeTape

namespace TypedStateTable

variable {σ : Type}

/-- A typed configuration for a three-tape table. -/
def config (M : TypedStateTable σ) (s : σ)
    (T0 T1 T2 : Tape Bool) : Configuration :=
  ThreeTape.config (M.stateId s) T0 T1 T2

/-- Reachability that hides the concrete number of table steps. -/
def Leads (M : TypedStateTable σ) (c d : Configuration) : Prop :=
  exists j : Nat,
    forall k : Nat,
      M.description.runConfig (k + j) c = M.description.runConfig k d

namespace Leads

theorem refl (M : TypedStateTable σ) (c : Configuration) :
    M.Leads c c :=
  ⟨0, fun _ => rfl⟩

theorem trans {M : TypedStateTable σ} {c d e : Configuration}
    (hcd : M.Leads c d) (hde : M.Leads d e) : M.Leads c e := by
  rcases hcd with ⟨jcd, hcd⟩
  rcases hde with ⟨jde, hde⟩
  refine ⟨jde + jcd, fun k => ?_⟩
  rw [show k + (jde + jcd) = (k + jde) + jcd by lia,
    hcd (k + jde), hde k]

theorem to_runConfig {M : TypedStateTable σ} {c d : Configuration}
    (h : M.Leads c d) :
    exists j : Nat, M.description.runConfig j c = d := by
  rcases h with ⟨j, hj⟩
  have h0 := hj 0
  rw [Nat.zero_add] at h0
  exact ⟨j, h0⟩

end Leads

/-- Execute one typed row and expose the three resulting tapes. -/
theorem leads_step (M : TypedStateTable σ)
    [DecidableEq σ]
    {s : σ} (hs : s ∈ M.states)
    {T0 T1 T2 : Tape Bool} {st : TypedStep σ}
    (hnext :
      M.next s (Tape.read T0) (Tape.read T1) (Tape.read T2) = some st)
    {T0' T1' T2' : Tape Bool}
    (h0 : st.action0.apply T0 = T0')
    (h1 : st.action1.apply T1 = T1')
    (h2 : st.action2.apply T2 = T2') :
    M.Leads (M.config s T0 T1 T2) (M.config st.target T0' T1' T2') := by
  refine ⟨1, fun k => ?_⟩
  have hstep := M.runConfig_succ_config hs hnext k
  simpa [config, h0, h1, h2] using hstep

end TypedStateTable

namespace ThreeTape

theorem read_tapeAtCells_cons
    (left : List (Option Bool)) (cell : Option Bool)
    (right : List (Option Bool)) :
    Tape.read (tapeAtCells left (cell :: right)) = cell := rfl

theorem read_tapeAtCells_nil (left : List (Option Bool)) :
    Tape.read (tapeAtCells left []) = none := rfl

theorem keepR_apply_tapeAtCells
    (left : List (Option Bool)) (cell : Option Bool)
    (right : List (Option Bool)) :
    keepR.apply (tapeAtCells left (cell :: right)) =
      tapeAtCells (cell :: left) right := by
  cases right <;> rfl

theorem keepL_apply_tapeAtCells
    (left : List (Option Bool)) (previous cell : Option Bool)
    (right : List (Option Bool)) :
    keepL.apply (tapeAtCells (previous :: left) (cell :: right)) =
      tapeAtCells left (previous :: cell :: right) := rfl

theorem keepL_apply_tapeAtCells_nil
    (left : List (Option Bool)) (previous : Option Bool) :
    keepL.apply (tapeAtCells (previous :: left) []) =
      tapeAtCells left [previous, none] := rfl

theorem keepL_apply_tapeAtCells_left_nil
    (cell : Option Bool) (right : List (Option Bool)) :
    keepL.apply (tapeAtCells [] (cell :: right)) =
      tapeAtCells [] (none :: cell :: right) := by
  cases right <;> rfl

theorem writeR_apply_tapeAtCells
    (value : Option Bool) (left : List (Option Bool))
    (cell : Option Bool) (right : List (Option Bool)) :
    (writeR value).apply (tapeAtCells left (cell :: right)) =
      tapeAtCells (value :: left) right := by
  cases right <;> rfl

theorem writeL_apply_tapeAtCells
    (value : Option Bool) (left : List (Option Bool))
    (previous cell : Option Bool) (right : List (Option Bool)) :
    (writeL value).apply
        (tapeAtCells (previous :: left) (cell :: right)) =
      tapeAtCells left (previous :: value :: right) := rfl

end ThreeTape

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
