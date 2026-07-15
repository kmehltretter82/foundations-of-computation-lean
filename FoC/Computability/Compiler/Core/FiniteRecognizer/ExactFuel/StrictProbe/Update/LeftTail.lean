import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftKernel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.OptionalField
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.PositionedRight

set_option doc.verso true

/-!
# Nonempty-left tail transport

Tape-equivalence transport and serialized-layout identities prepare the
replacement and right-prepend tail shared by the left-update runners.
-/

namespace FoC
namespace Computability
open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Update
namespace LeftTail
open SerializedFieldComposer

/-- Lift an actual inner step through a phase constructor.  The outer
transition may still add a handoff when the inner transition is absent. -/
theorem stepConfig_some_of_transition_some
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (htransition : forall state read written direction target,
      inner.transition state read = some (written, direction, target) ->
        outer.transition (embed state) read =
          some (written, direction, embed target))
    {source target : TuringMachine.Configuration symbol innerState}
    (hstep : inner.stepConfig source = some target) :
    outer.stepConfig (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  cases source with
  | mk state tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      cases hinner : inner.transition state (Tape.read tape) with
      | none =>
          rw [hinner] at hstep
          contradiction
      | some action =>
          rcases action with ⟨written, direction, next⟩
          rw [hinner] at hstep
          simp only at hstep
          cases hstep
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          rw [htransition state (Tape.read tape) written direction next hinner]

theorem runConfigExact_some_of_transition_some
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (htransition : forall state read written direction target,
      inner.transition state read = some (written, direction, target) ->
        outer.transition (embed state) read =
          some (written, direction, embed target))
    {steps : Nat}
    {source target : TuringMachine.Configuration symbol innerState}
    (hrun : inner.runConfigExact? steps source = some target) :
    outer.runConfigExact? steps
        (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some embed
  · intro c d hstep
    exact stepConfig_some_of_transition_some embed htransition hstep
  · exact hrun

theorem payloadAppend_eq_append (cells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) : encodeOptionalCodeSymbolsPayloadAppend cells suffix =
      List.append (encodeOptionalCodeSymbolsPayloadAppend cells []) suffix := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [encodeOptionalCodeSymbolsPayloadAppend]
      rw [ih]
      simp [encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend, List.append_assoc]
theorem replacement_cursor_eq_payload_source {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    (Edits.OptionalField.LayoutSpecialization.sourceConfig L callerData).tape =
      (Edits.PositionedRightLocator.sourceConfig (headPrefix L).reverse L.head L.right.length
        (RightPrepend.rightPayloadSuffix L callerData)).tape := by
  unfold Edits.OptionalField.LayoutSpecialization.sourceConfig Edits.PositionedRightLocator.sourceConfig
    Edits.PositionedRightLocator.config headSuffix RightPrepend.rightPayloadSuffix optionalCellsWord
    encodeOptionalCodeSymbolsAppend
  rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend]
  rw [payloadAppend_eq_append L.right (Frame.callerTag :: callerData)]
  simp [MachineDescription.encodeNatAppend, List.append_assoc]
theorem protectedWord_eq_head_rightCount_tail {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Frame.protectedWord L callerData = List.append (headPrefix L) (List.append (optionalCellWord L.head)
          (MachineDescription.encodeNatAppend L.right.length (RightPrepend.rightPayloadSuffix L callerData))) := by
  simpa [RightPrepend.rightPayloadPrefix, RightPrepend.rightCountPrefix,
    MachineDescription.encodeNatAppend, List.append_assoc] using RightPrepend.protectedWord_decomp L callerData
theorem afterWriteWord_eq_head_rightCount_tail {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) : RightPrepend.afterWriteWord L write callerData =
      List.append (headPrefix L) (List.append (optionalCellWord L.head)
          (MachineDescription.encodeNatAppend L.right.length (List.append (optionalCellWord write)
              (RightPrepend.rightPayloadSuffix L callerData)))) := by
  simp [RightPrepend.afterWriteWord, RightPrepend.rightPayloadPrefix, RightPrepend.rightCountPrefix,
    MachineDescription.encodeNatAppend, List.append_assoc]
/- The layout-specialized replacement proof has an exact cursor source.  This
transport form is the one needed after a physical cursor locator, whose tape
may contain only far-edge padding relative to that clean source. -/
theorem replace_run_exact_of_tape_equiv {stateCount : Nat} (L : Layout stateCount) (newHead : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) (T : Tape MachineCodeSymbol) (hsource : Tape.Equiv
      (Edits.OptionalField.LayoutSpecialization.sourceConfig L callerData).tape T) :
    exists endpoint, (Edits.OptionalField.Replace.machine L.head newHead).runConfigExact?
          (Edits.OptionalField.LayoutSpecialization.runSteps L newHead callerData)
          { state := Edits.OptionalField.Replace.Control.markLeft
            tape := T } = some endpoint ∧ endpoint.state =
        Edits.OptionalField.Replace.Control.insert (.rewind .gate) ∧ Tape.Equiv
        (Tape.input (Frame.protectedWord (HeadReplacement.replaceHead L newHead) callerData)) endpoint.tape := by
  rcases Edits.OptionalField.LayoutSpecialization.run_exact L newHead callerData with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, ?_, Tape.Equiv.trans hcleanTape htape⟩
  · simpa [Edits.OptionalField.LayoutSpecialization.sourceConfig] using hrun
  · exact hstate ▸ hcleanState
end LeftTail
end Update
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
