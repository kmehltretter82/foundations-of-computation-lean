import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.CfgHitClose
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.SelectorSpliceRuns
import FoC.Computability.Compiler.Structured.Lowering.LogicalEquivRuns

set_option doc.verso true

/-!
# Selector splice runs on carried logical representatives

The configuration-and-hit materializer carries logical tapes whose finite
windows retain blank workspace.  The selector splice sees the same logical
head cells as the canonical classified layout, so its structured run follows
the same control path.  Its exact physical guarded encoding is intentionally
left unchanged: guarded encoding is not invariant under logical tape
equivalence.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.SelectorSplice

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open FieldDecomposition.ClassifiedBoundary

/-- Structured selector source with the exact representatives returned by the
configuration-and-hit materializer. -/
def representedSourceConfig
    (D : MachineDescription) (L : SimulatorLayout) :
    Structured.Configuration where
  state := (description D).start
  tapes :=
    FieldDecomposition.MetadataPrefix.ConfigTapeAndHit.representedTapes D L

/-- The carried source has the same control state and logically equivalent
tapes as the canonical selector-splice source. -/
theorem representedSourceConfig_equiv
    (D : MachineDescription) (L : SimulatorLayout) :
    LogicalConfigurationEquiv (representedSourceConfig D L)
      ((table D).config (.ingress .start)
        L.config.tape
        (FieldDecomposition.stageCounterTape L.stage)
        (metadataHitTapeWithSelector D L)) := by
  constructor
  · rfl
  · exact
      FieldDecomposition.MetadataPrefix.ConfigTapeAndHit.representedTapes_equiv
        D L

/--
The selector splice reaches its halt state from the carried representatives.
Its concrete resulting logical tapes are pointwise equivalent to the canonical
done-witness tapes; no equality or physical guarded-tape equivalence is
claimed.
-/
theorem description_runConfig_represented_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    exists steps : Nat,
      LogicalConfigurationEquiv
        ((description D).runConfig steps (representedSourceConfig D L))
        { state := (description D).halt
          tapes := loopDispatcherDoneWitnessTapes D L } := by
  rcases description_runConfig_layout D L with ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hrunEquiv :=
    runConfig_preserves_logicalConfigurationEquiv
      (description D) steps (representedSourceConfig_equiv D L)
  rw [hrun] at hrunEquiv
  exact hrunEquiv

private theorem configuration_eq_of_state_eq
    (c : Structured.Configuration) (state : Nat)
    (hstate : c.state = state) :
    c = { state := state, tapes := c.tapes } := by
  cases c with
  | mk currentState tapes =>
      cases hstate
      rfl

/-- Exact run equality with the concrete output representative exposed as a
witness, followed by its semantic relation to the canonical done layout. -/
theorem description_haltsWith_equivTapes_represented_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    exists steps : Nat, exists actualTapes : List (Tape Bool),
      (description D).runConfig steps (representedSourceConfig D L) =
          { state := (description D).halt
            tapes := actualTapes } ∧
        LogicalTapeListEquiv actualTapes
          (loopDispatcherDoneWitnessTapes D L) := by
  rcases description_runConfig_represented_layout D L with
    ⟨steps, hrun⟩
  refine
    ⟨steps,
      ((description D).runConfig steps
        (representedSourceConfig D L)).tapes,
      ?_, hrun.right⟩
  exact configuration_eq_of_state_eq _ _ hrun.left

end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.SelectorSplice
