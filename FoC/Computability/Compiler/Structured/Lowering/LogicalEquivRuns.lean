import FoC.Computability.Compiler.Structured.Lowering.Layout

set_option doc.verso true

/-!
# Structured runs on equivalent logical tape representatives

Structured machines inspect only the current logical cells and apply local
writes and head moves.  Consequently their executions do not distinguish
finite tape windows that differ only by far-end blank padding.  This module
records that fact at the logical-tape level; it does not identify the guarded
physical encodings of those representatives.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-- Applying the same structured head move preserves tape equivalence. -/
theorem headMove_apply_preserves_equiv
    (move : HeadMove) {actual expected : Tape Bool}
    (h : Tape.Equiv actual expected) :
    Tape.Equiv (move.apply actual) (move.apply expected) := by
  cases move with
  | stay =>
      exact h
  | left =>
      exact Tape.Equiv.move h Direction.left
  | right =>
      exact Tape.Equiv.move h Direction.right

/-- Applying the same structured tape action preserves tape equivalence. -/
theorem tapeAction_apply_preserves_equiv
    (action : TapeAction) {actual expected : Tape Bool}
    (h : Tape.Equiv actual expected) :
    Tape.Equiv (action.apply actual) (action.apply expected) := by
  unfold TapeAction.apply
  cases action.write? with
  | none =>
      exact headMove_apply_preserves_equiv action.move h
  | some cell =>
      exact
        headMove_apply_preserves_equiv action.move
          (Tape.Equiv.write h cell)

/-- Equivalent logical tape lists expose the same tuple of current cells. -/
theorem currentReads_eq_of_logicalTapeListEquiv
    (D : Description) {actual expected : Configuration}
    (h : LogicalTapeListEquiv actual.tapes expected.tapes) :
    D.currentReads actual = D.currentReads expected := by
  unfold Description.currentReads
  apply List.map_congr_left
  intro index _hindex
  exact Tape.Equiv.read_eq (logicalTapeListEquiv_tapeAt h index)

/-- Applying one row's action tuple preserves pointwise logical-tape equivalence. -/
theorem applyActions_preserves_logicalTapeListEquiv
    (D : Description) (actions : List TapeAction)
    {actual expected : List (Tape Bool)}
    (h : LogicalTapeListEquiv actual expected) :
    LogicalTapeListEquiv
      (D.applyActions actions actual)
      (D.applyActions actions expected) := by
  unfold Description.applyActions
  generalize List.range D.tapeCount = indices
  induction indices with
  | nil =>
      trivial
  | cons index rest ih =>
      constructor
      · exact
          tapeAction_apply_preserves_equiv
            (actions.getD index TapeAction.stay)
            (logicalTapeListEquiv_tapeAt h index)
      · exact ih

/--
Two structured configurations have the same control state and pointwise
equivalent logical tape representatives.
-/
def LogicalConfigurationEquiv
    (actual expected : Configuration) : Prop :=
  actual.state = expected.state ∧
    LogicalTapeListEquiv actual.tapes expected.tapes

/-- Lift logical-configuration equivalence through an optional next step. -/
def LogicalConfigurationOptionEquiv :
    Option Configuration -> Option Configuration -> Prop
  | none, none => True
  | some actual, some expected =>
      LogicalConfigurationEquiv actual expected
  | _, _ => False

/-- Equivalent logical configurations select the same structured row. -/
theorem lookupTransition_eq_of_logicalConfigurationEquiv
    (D : Description) {actual expected : Configuration}
    (h : LogicalConfigurationEquiv actual expected) :
    D.lookupTransition actual = D.lookupTransition expected := by
  unfold Description.lookupTransition
  rw [h.left]
  rw [currentReads_eq_of_logicalTapeListEquiv D h.right]

/-- One structured step preserves control-state equality and logical-tape equivalence. -/
theorem stepConfig_preserves_logicalConfigurationEquiv
    (D : Description) {actual expected : Configuration}
    (h : LogicalConfigurationEquiv actual expected) :
    LogicalConfigurationOptionEquiv
      (D.stepConfig actual) (D.stepConfig expected) := by
  unfold Description.stepConfig
  rw [lookupTransition_eq_of_logicalConfigurationEquiv D h]
  cases hlookup : D.lookupTransition expected with
  | none =>
      trivial
  | some transition =>
      constructor
      · rfl
      · exact
          applyActions_preserves_logicalTapeListEquiv
            D transition.actions h.right

/--
Running a structured machine for the same number of steps preserves equal
control state and pointwise logical-tape equivalence.
-/
theorem runConfig_preserves_logicalConfigurationEquiv
    (D : Description) (steps : Nat)
    {actual expected : Configuration}
    (h : LogicalConfigurationEquiv actual expected) :
    LogicalConfigurationEquiv
      (D.runConfig steps actual) (D.runConfig steps expected) := by
  induction steps generalizing actual expected with
  | zero =>
      exact h
  | succ steps ih =>
      unfold Description.runConfig
      unfold Description.stepConfig
      rw [lookupTransition_eq_of_logicalConfigurationEquiv D h]
      cases hlookup : D.lookupTransition expected with
      | none =>
          exact h
      | some transition =>
          apply ih
          constructor
          · rfl
          · exact
              applyActions_preserves_logicalTapeListEquiv
                D transition.actions h.right

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
