import FoC.Computability.TuringMachine

set_option doc.verso true

/-!
# Turing-machine phase embeddings

Configuration and run lifting for a control-state embedding that preserves
the physical tape.
-/

namespace FoC
namespace Computability
namespace TuringMachine
namespace PhaseEmbedding

/-- Embed an inner control state while preserving its physical tape. -/
def liftConfig
    (embed : innerState -> outerState)
    (c : Configuration symbol innerState) :
    Configuration symbol outerState where
  state := embed c.state
  tape := c.tape

/-- A pointwise step-configuration simulation lifts every exact run. -/
theorem runConfigExact?_lift
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (hstep : forall c : Configuration symbol innerState,
      outer.stepConfig (liftConfig embed c) =
        Option.map (liftConfig embed) (inner.stepConfig c)) :
    forall (steps : Nat) (c : Configuration symbol innerState),
      outer.runConfigExact? steps (liftConfig embed c) =
        Option.map (liftConfig embed) (inner.runConfigExact? steps c) := by
  intro steps
  induction steps with
  | zero =>
      intro c
      rfl
  | succ steps ih =>
      intro c
      rw [TuringMachine.runConfigExact?, TuringMachine.runConfigExact?]
      rw [hstep]
      cases hnext : inner.stepConfig c with
      | none =>
          rfl
      | some next =>
          simp only [Option.map]
          exact ih next

/-- Convenient exact-endpoint form of {name}`runConfigExact?_lift`. -/
theorem runConfigExact?_lift_of_eq_some
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (hstep : forall c : Configuration symbol innerState,
      outer.stepConfig (liftConfig embed c) =
        Option.map (liftConfig embed) (inner.stepConfig c))
    {steps : Nat} {source target : Configuration symbol innerState}
    (hrun : inner.runConfigExact? steps source = some target) :
    outer.runConfigExact? steps (liftConfig embed source) =
      some (liftConfig embed target) := by
  rw [runConfigExact?_lift embed hstep, hrun]
  rfl

/-- The same pointwise simulation lifts unbounded reachability. -/
theorem computes_lift
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (hstep : forall c : Configuration symbol innerState,
      outer.stepConfig (liftConfig embed c) =
        Option.map (liftConfig embed) (inner.stepConfig c))
    {source target : Configuration symbol innerState}
    (hrun : Computes inner source target) :
    Computes outer (liftConfig embed source) (liftConfig embed target) := by
  rcases computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  apply computesIn_to_computes
  apply runConfigExact?_eq_some_iff_computesIn.mp
  apply runConfigExact?_lift_of_eq_some embed hstep
  exact runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

end PhaseEmbedding
end TuringMachine
end Computability
end FoC
