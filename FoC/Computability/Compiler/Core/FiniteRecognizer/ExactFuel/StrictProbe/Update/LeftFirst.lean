import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.OptionalCell
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.PresentAction
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.SerializedHead

set_option doc.verso true

/-!
# Nonempty-left first edit

This finite runner performs the selected-action prefix, decodes and removes
the first serialized left cell, and decrements the remaining-left count.
-/

namespace FoC
namespace Computability
open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Update
namespace LeftFirst
open SerializedFieldComposer

namespace Prefix
abbrev Control :=
  Update.PresentAction.SelectedFuelThenLeftBoundary.Control

namespace Control
abbrev finite :=
  Update.PresentAction.SelectedFuelThenLeftBoundary.Control.finite
end Control
abbrev transition {stateCount : Nat} :=
  @Update.PresentAction.SelectedFuelThenLeftBoundary.transition stateCount
abbrev machine {stateCount : Nat} :=
  @Update.PresentAction.SelectedFuelThenLeftBoundary.machine stateCount
abbrev fuelConfig {stateCount : Nat} :=
  @Update.PresentAction.SelectedFuelThenLeftBoundary.fuelConfig stateCount
abbrev runSteps {stateCount : Nat} :=
  @Update.PresentAction.SelectedFuelThenLeftBoundary.runSteps stateCount
end Prefix

namespace Decoder
abbrev Control := Dispatch.OptionalCell.Control

namespace Control
abbrev finite := Dispatch.OptionalCell.Control.finite
end Control
abbrev transition := Dispatch.OptionalCell.transition
abbrev machine := Dispatch.OptionalCell.machine
abbrev sourceConfig := Dispatch.OptionalCell.sourceConfig
abbrev gateConfig := Dispatch.OptionalCell.gateConfig
abbrev runSteps := Dispatch.OptionalCell.runSteps
end Decoder
abbrev Selected := SerializedHeadDispatch.Selected

namespace Selected
abbrev finite := SerializedHeadDispatch.Selected.finite
abbrev elems := SerializedHeadDispatch.Selected.elems
end Selected
/-- Canonical-header restart, left-count positioning, and the one-token count
decrement following the first optional-cell deletion. -/
inductive CountControl where
  | handoffReturn
  | locate (inner : FieldLocator.Control)
  | editReturn
  | delete (inner : DeleteRestagedMachine.Control)
deriving DecidableEq

namespace CountControl
def elems : List CountControl :=
  [CountControl.handoffReturn, CountControl.editReturn] ++
    (FieldLocator.Control.finite.elems.map CountControl.locate) ++
    (DeleteRestagedMachine.Control.finite.elems.map CountControl.delete)
def finite : Foundation.FiniteType CountControl where
  elems := elems
  complete := by
    intro control
    cases control with
    | handoffReturn => simp [elems]
    | locate inner =>
        have h := FieldLocator.Control.finite.complete inner
        simp [elems, h]
    | editReturn => simp [elems]
    | delete inner =>
        have h := DeleteRestagedMachine.Control.finite.complete inner
        simp [elems, h]
end CountControl
/-- One concrete machine through the first hard nonempty-left edit.  It carries
the selected row, decodes the neighboring optional cell at the located cursor,
and retargets directly into the existing delete-and-rewind implementation. -/
inductive Control (stateCount : Nat) where
  | prefix (inner : Prefix.Control stateCount)
  | decodeReturn (selected : Selected stateCount)
  | decode (selected : Selected stateCount) (inner : Decoder.Control)
  | editReturn (selected : Selected stateCount) (cell : Option MachineCodeSymbol)
  | delete (selected : Selected stateCount) (cell : Option MachineCodeSymbol) (inner : DeleteRestagedMachine.Control)
  | count (selected : Selected stateCount) (cell : Option MachineCodeSymbol) (inner : CountControl)
deriving DecidableEq

namespace Control
def optionalFinite : Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite
def decodeFinite (stateCount : Nat) : Foundation.FiniteType (Selected stateCount × Decoder.Control) :=
  Foundation.FiniteType.prod (Selected.finite stateCount) Decoder.Control.finite
def editReturnFinite (stateCount : Nat) : Foundation.FiniteType (Selected stateCount × Option MachineCodeSymbol) :=
  Foundation.FiniteType.prod (Selected.finite stateCount) optionalFinite
def deleteFinite (stateCount : Nat) : Foundation.FiniteType
      ((Selected stateCount × Option MachineCodeSymbol) × DeleteRestagedMachine.Control) :=
  Foundation.FiniteType.prod (editReturnFinite stateCount) DeleteRestagedMachine.Control.finite
def countFinite (stateCount : Nat) : Foundation.FiniteType
      ((Selected stateCount × Option MachineCodeSymbol) × CountControl) :=
  Foundation.FiniteType.prod (editReturnFinite stateCount) CountControl.finite
def elems (stateCount : Nat) : List (Control stateCount) :=
  List.append ((Prefix.Control.finite stateCount).elems.map Control.prefix) (List.append
      ((Selected.elems stateCount).map Control.decodeReturn) (List.append
        ((decodeFinite stateCount).elems.map fun payload =>
          Control.decode payload.1 payload.2) (List.append ((editReturnFinite stateCount).elems.map fun payload =>
            Control.editReturn payload.1 payload.2) (List.append ((deleteFinite stateCount).elems.map fun payload =>
              Control.delete payload.1.1 payload.1.2 payload.2) ((countFinite stateCount).elems.map fun payload =>
              Control.count payload.1.1 payload.1.2 payload.2)))))
def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | «prefix» inner =>
        have h := (Prefix.Control.finite stateCount).complete inner
        simp [elems, h]
    | decodeReturn selected =>
        have h : selected ∈ Selected.elems stateCount :=
          (Selected.finite stateCount).complete selected
        simp [elems, h]
    | decode selected inner =>
        have h := (decodeFinite stateCount).complete (selected, inner)
        simp [elems, h]
    | editReturn selected cell =>
        have h := (editReturnFinite stateCount).complete (selected, cell)
        simp [elems, h]
    | delete selected cell inner =>
        have h := (deleteFinite stateCount).complete ((selected, cell), inner)
        simp [elems]
        exact ⟨selected, cell, inner, h, rfl, rfl, rfl⟩
    | count selected cell inner =>
        have h := (countFinite stateCount).complete ((selected, cell), inner)
        simp [elems]
        exact ⟨selected, cell, inner, h, rfl, rfl, rfl⟩
end Control
def transition {stateCount : Nat} : Control stateCount -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control stateCount)
  | .prefix (.locate selected .gate), read =>
      some (read, Direction.right, .decodeReturn selected)
  | .prefix inner, read =>
      match Prefix.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .prefix target)
  | .decodeReturn selected, read =>
      some (read, Direction.left, .decode selected (.decode ⟨0, by decide⟩))
  | .decode selected (.gate cell), read =>
      some (read, Direction.right, .editReturn selected cell)
  | .decode selected inner, read =>
      match Decoder.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .decode selected target)
  | .editReturn selected cell, read =>
      some (read, Direction.left, .delete selected cell (.edit (.erase (DeleteBlock.optionalGap cell))))
  | .delete selected cell (.rewind .gate), read =>
      some (read, Direction.right, .count selected cell .handoffReturn)
  | .delete selected cell inner, read =>
      match DeleteRestagedMachine.transition cell inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .delete selected cell target)
  | .count selected cell .handoffReturn, read =>
      some (read, Direction.left, .count selected cell (.locate .header))
  | .count selected cell (.locate .gate), read =>
      some (read, Direction.right, .count selected cell .editReturn)
  | .count selected cell (.locate inner), read =>
      match FieldLocator.transition .leftCount inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .count selected cell (.locate target))
  | .count selected cell .editReturn, read =>
      some (read, Direction.left, .count selected cell (.delete (.edit (.erase (DeleteBlock.optionalGap none)))))
  | .count selected cell (.delete inner), read =>
      match DeleteRestagedMachine.transition none inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .count selected cell (.delete target))
def machine {stateCount : Nat} (selected : Selected stateCount) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .prefix (Prefix.machine selected).start
  halt := .delete selected none (.rewind .gate)
  transition := transition
  statesFinite := Control.finite stateCount
def prefixConfig {stateCount : Nat} (c : TuringMachine.Configuration MachineCodeSymbol (Prefix.Control stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .prefix c.state
  tape := c.tape
def decoderConfig {stateCount : Nat} (selected : Selected stateCount)
    (c : TuringMachine.Configuration MachineCodeSymbol Decoder.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .decode selected c.state
  tape := c.tape
def deleteConfig {stateCount : Nat} (selected : Selected stateCount) (cell : Option MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.delete selected cell) c
def countLocateConfig {stateCount : Nat} (selected : Selected stateCount) (cell : Option MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol FieldLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .count selected cell (.locate c.state)
  tape := c.tape
def countDeleteConfig {stateCount : Nat} (selected : Selected stateCount) (cell : Option MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig (fun inner => Control.count selected cell (.delete inner)) c
private theorem write_read_eq_self (T : Tape MachineCodeSymbol) : Tape.write (Tape.read T) T = T := by
  cases T
  rfl
def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)
theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) : Tape.Equiv (roundTripTape T) T := by
  exact Machine.moveLeft_moveRight_equiv_self T
theorem leftPayload_gate_eq_decoder_source {stateCount : Nat} (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) (hleft : L.left = nextHead :: remainingLeft) :
    (FieldLocator.config .gate (LeftPrepend.leftPayloadPrefix L).reverse
        (LeftPrepend.leftPayloadSuffix L callerData)).tape = (Decoder.sourceConfig
        (MoveLeftNonempty.leftPayloadPrefix L).reverse nextHead
        (MoveLeftNonempty.afterFirstLeftCell L remainingLeft callerData)).tape := by
  cases L with
  | mk fuel state left head right =>
      simp only at hleft
      subst left
      have hprefix : LeftPrepend.leftPayloadPrefix
              { fuel := fuel, state := state,
                left := nextHead :: remainingLeft,
                head := head, right := right } = MoveLeftNonempty.leftPayloadPrefix
              { fuel := fuel, state := state,
                left := nextHead :: remainingLeft,
                head := head, right := right } := by
        simp [LeftPrepend.leftPayloadPrefix, LeftPrepend.leftCountPrefix, MoveLeftNonempty.leftPayloadPrefix,
          MachineDescription.encodeNatAppend, List.append_assoc]
      have hsuffix : LeftPrepend.leftPayloadSuffix
              { fuel := fuel, state := state,
                left := nextHead :: remainingLeft,
                head := head, right := right } callerData = List.append (optionalCellWord nextHead)
              (MoveLeftNonempty.afterFirstLeftCell
                { fuel := fuel, state := state,
                  left := nextHead :: remainingLeft,
                  head := head, right := right } remainingLeft callerData) := by
        rfl
      rw [hprefix, hsuffix]
      rfl
/-- The existing left-count locator needs no well-formed payload after the
state field.  This generic form is what permits locating the stale count after
the first payload cell has already been physically removed. -/
theorem locate_leftCount_prefix_exact {stateCount : Nat} (L : Layout stateCount) (rest : Word MachineCodeSymbol) :
    (FieldLocator.machine .leftCount).runConfigExact? (FieldLocator.leftCountSteps L) (FieldLocator.config .header []
          (List.append (MoveLeftNonempty.leftCountPrefix L) rest)) = some
        (FieldLocator.config .gate (MoveLeftNonempty.leftCountPrefix L).reverse rest) := by
  unfold FieldLocator.leftCountSteps
  have hsource : List.append (MoveLeftNonempty.leftCountPrefix L) rest = MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend L.fuel (MachineDescription.encodeNatAppend L.state.val rest) := by
    simp [MoveLeftNonempty.leftCountPrefix, MachineDescription.encodeNatAppend, List.append_assoc]
  rw [hsource]
  rw [FieldLocator.runConfigExact?_add]
  have hheader : (FieldLocator.machine .leftCount).runConfigExact? 1 (FieldLocator.config .header []
            (MachineCodeSymbol.header :: MachineDescription.encodeNatAppend L.fuel
                (MachineDescription.encodeNatAppend L.state.val rest))) = some
          (FieldLocator.config .fuel [MachineCodeSymbol.header] (MachineDescription.encodeNatAppend L.fuel
              (MachineDescription.encodeNatAppend L.state.val rest))) := by
    rw [TuringMachine.runConfigExact?]
    rw [FieldLocator.header_step]
    rfl
  rw [hheader]
  simp only
  rw [FieldLocator.runConfigExact?_add]
  rw [FieldLocator.fuel_run_later .leftCount (by decide)]
  simp only
  rw [FieldLocator.state_run_leftCount]
  simp [MoveLeftNonempty.leftCountPrefix, MachineDescription.encodeNatAppend, List.reverse_cons,
    List.reverse_append, List.append_assoc]
theorem firstDeleteOutput_count_decomp {stateCount : Nat} (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) (hleft : L.left = nextHead :: remainingLeft) :
    PhysicalBranch.deleteOutput (MoveLeftNonempty.leftPayloadPrefix L).reverse
        (MoveLeftNonempty.afterFirstLeftCell L remainingLeft callerData) =
      List.append (MoveLeftNonempty.leftCountPrefix L) (MachineCodeSymbol.tick ::
          MoveLeftNonempty.afterCountTick L remainingLeft callerData) := by
  rw [show PhysicalBranch.deleteOutput (MoveLeftNonempty.leftPayloadPrefix L).reverse
        (MoveLeftNonempty.afterFirstLeftCell L remainingLeft callerData) =
      MoveLeftNonempty.afterDeleteWord L remainingLeft callerData by
    simp [PhysicalBranch.deleteOutput, MoveLeftNonempty.afterDeleteWord]]
  exact MoveLeftNonempty.afterDeleteWord_count_decomp L nextHead remainingLeft callerData hleft
def countDeleteRunSteps (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  DeleteBlock.runOneSteps suffix + DeleteEndpointRewind.runSteps none (List.append suffix.reverse leftRev)
/-- {lit}`DeleteRestagedMachine none` can delete an arbitrary single token, not
only the canonical encoding of {lit}`none`. This is the run used to remove
the stale unary count tick. -/
theorem countDelete_run_exact (leftRev suffix : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact? (DeleteBlock.runOneSteps suffix +
          DeleteEndpointRewind.runSteps none (List.append suffix.reverse leftRev))
        (DeleteRestagedMachine.editConfig (DeleteBlock.oneSourceConfig MachineCodeSymbol.tick
            leftRev suffix)) = some (DeleteRestagedMachine.rewindConfig (DeleteEndpointRewind.gateConfig
            (PhysicalBranch.deleteOutput leftRev suffix) none)) := by
  rw [DeleteRestagedMachine.runConfigExact?_add]
  rw [DeleteRestagedMachine.edit_run_of_eq_some none _ _ _
    (DeleteBlock.run_one_exact MachineCodeSymbol.tick leftRev suffix)]
  simp only
  rw [DeleteRestagedMachine.rewind_run_exact]
  simp [PhysicalBranch.deleteOutput, List.reverse_append]
theorem prefix_step_of_some {stateCount : Nat} (selected : Selected stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol (Prefix.Control stateCount))
    (hstep : (Prefix.machine selected).stepConfig c = some d) :
    (machine selected).stepConfig (prefixConfig c) = some (prefixConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Update.PresentAction.SelectedFuelThenLeftBoundary.machine] at hstep
      have hmachineTransition : (Prefix.machine selected).transition = Prefix.transition := rfl
      rw [hmachineTransition] at hstep
      cases htransition : Prefix.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | locate carried inner =>
              cases inner with
              | gate =>
                  simp [Prefix.transition, Update.PresentAction.SelectedFuelThenLeftBoundary.transition,
                    FieldLocator.transition] at htransition
              | header | fuel | state | leftCount =>
                  simp [machine, transition, prefixConfig, htransition]
          | fuel carried inner =>
              simp [machine, transition, prefixConfig, htransition]
          | handoffReturn carried =>
              simp [machine, transition, prefixConfig, htransition]
theorem prefix_run_of_some {stateCount : Nat} (selected : Selected stateCount) :
    forall (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol (Prefix.Control stateCount)),
      (Prefix.machine selected).runConfigExact? steps c = some d ->
        (machine selected).runConfigExact? steps (prefixConfig c) = some (prefixConfig d) := by
  intro steps
  induction steps with
  | zero =>
      intro c d hrun
      simpa [TuringMachine.runConfigExact?] using congrArg prefixConfig (Option.some.inj hrun)
  | succ steps ih =>
      intro c d hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : (Prefix.machine selected).stepConfig c with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [prefix_step_of_some selected c next hstep]
          simp only
          exact ih next d hrun
theorem prefix_handoff_run_exact {stateCount : Nat} (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := Control.prefix (.locate selected .gate), tape := T } = some (decoderConfig selected
          { state := Dispatch.OptionalCell.Control.decode ⟨0, by decide⟩
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, decoderConfig,
    roundTripTape, write_read_eq_self]
theorem decoder_step_of_some {stateCount : Nat} (selected : Selected stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol Decoder.Control)
    (hstep : Decoder.machine.stepConfig c = some d) : (machine selected).stepConfig (decoderConfig selected c) =
      some (decoderConfig selected d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Dispatch.OptionalCell.machine] at hstep
      have hmachineTransition : Decoder.machine.transition = Decoder.transition := rfl
      rw [hmachineTransition] at hstep
      cases htransition : Decoder.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate cell =>
              simp [Decoder.transition, Dispatch.OptionalCell.transition] at htransition
          | decode count =>
              simp [machine, transition, decoderConfig, htransition]
          | returnLeft cell count =>
              simp [machine, transition, decoderConfig, htransition]
          | zeroBounce cell =>
              simp [machine, transition, decoderConfig, htransition]
theorem decoder_run_of_some {stateCount : Nat} (selected : Selected stateCount) :
    forall (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol Decoder.Control),
      Decoder.machine.runConfigExact? steps c = some d ->
        (machine selected).runConfigExact? steps (decoderConfig selected c) = some (decoderConfig selected d) := by
  intro steps
  induction steps with
  | zero =>
      intro c d hrun
      simpa [TuringMachine.runConfigExact?] using congrArg (decoderConfig selected) (Option.some.inj hrun)
  | succ steps ih =>
      intro c d hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : Decoder.machine.stepConfig c with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [decoder_step_of_some selected c next hstep]
          simp only
          exact ih next d hrun
theorem decoder_handoff_run_exact {stateCount : Nat} (selected : Selected stateCount)
    (cell : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) : (machine selected).runConfigExact? 2
        { state := Control.decode selected (.gate cell), tape := T } = some (deleteConfig selected cell
          { state := DeleteRestagedMachine.Control.edit (.erase (DeleteBlock.optionalGap cell))
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, deleteConfig,
    TuringMachine.PhaseEmbedding.liftConfig, roundTripTape, write_read_eq_self]
theorem delete_step_of_some {stateCount : Nat} (selected : Selected stateCount) (cell : Option MachineCodeSymbol)
    (c d : TuringMachine.Configuration MachineCodeSymbol DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine cell).stepConfig c = some d) :
    (machine selected).stepConfig (deleteConfig selected cell c) = some (deleteConfig selected cell d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [DeleteRestagedMachine.machine] at hstep
      cases htransition : DeleteRestagedMachine.transition cell inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hnot : inner ≠ DeleteRestagedMachine.Control.rewind DeleteEndpointRewind.Control.gate := by
            intro hgate
            subst inner
            simp [DeleteRestagedMachine.transition, DeleteEndpointRewind.transition] at htransition
          simp [machine, transition, deleteConfig, TuringMachine.PhaseEmbedding.liftConfig, htransition]
theorem delete_run_of_some {stateCount : Nat} (selected : Selected stateCount) (cell : Option MachineCodeSymbol) :
    forall (steps : Nat) (source target : TuringMachine.Configuration MachineCodeSymbol
        DeleteRestagedMachine.Control), (DeleteRestagedMachine.machine cell).runConfigExact?
          steps source = some target -> (machine selected).runConfigExact? steps
            (deleteConfig selected cell source) = some (deleteConfig selected cell target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using congrArg (deleteConfig selected cell) (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : (DeleteRestagedMachine.machine cell).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [delete_step_of_some selected cell source next hstep]
          simp only
          exact ih next target hrun
theorem first_delete_handoff_run_exact {stateCount : Nat} (selected : Selected stateCount)
    (cell : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2 (deleteConfig selected cell
          { state := DeleteRestagedMachine.Control.rewind .gate
            tape := T }) = some (countLocateConfig selected cell
          { state := FieldLocator.Control.header
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, deleteConfig, countLocateConfig,
    TuringMachine.PhaseEmbedding.liftConfig, roundTripTape, write_read_eq_self]
theorem countLocate_step_of_some {stateCount : Nat} (selected : Selected stateCount) (cell : Option MachineCodeSymbol)
    (c d : TuringMachine.Configuration MachineCodeSymbol FieldLocator.Control)
    (hstep : (FieldLocator.machine .leftCount).stepConfig c = some d) :
    (machine selected).stepConfig (countLocateConfig selected cell c) = some (countLocateConfig selected cell d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FieldLocator.machine] at hstep
      cases htransition : FieldLocator.transition .leftCount inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate =>
              simp [FieldLocator.transition] at htransition
          | header | fuel | state | leftCount =>
              simp [machine, transition, countLocateConfig, htransition]
theorem countLocate_run_of_some {stateCount : Nat} (selected : Selected stateCount) (cell : Option MachineCodeSymbol) :
    forall (steps : Nat) (source target : TuringMachine.Configuration MachineCodeSymbol
        FieldLocator.Control), (FieldLocator.machine .leftCount).runConfigExact?
          steps source = some target -> (machine selected).runConfigExact? steps
            (countLocateConfig selected cell source) = some (countLocateConfig selected cell target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using congrArg (countLocateConfig selected cell) (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : (FieldLocator.machine .leftCount).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [countLocate_step_of_some selected cell source next hstep]
          simp only
          exact ih next target hrun
theorem count_locator_handoff_run_exact {stateCount : Nat} (selected : Selected stateCount)
    (cell : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2 (countLocateConfig selected cell
          { state := FieldLocator.Control.gate, tape := T }) = some (countDeleteConfig selected cell
          { state := DeleteRestagedMachine.Control.edit (.erase (DeleteBlock.optionalGap none))
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, countLocateConfig, countDeleteConfig, TuringMachine.PhaseEmbedding.liftConfig,
    roundTripTape, write_read_eq_self]
theorem countDelete_run_of_some {stateCount : Nat} (selected : Selected stateCount) (cell : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol DeleteRestagedMachine.Control}
    (hrun : (DeleteRestagedMachine.machine none).runConfigExact? steps source = some target) :
    (machine selected).runConfigExact? steps (countDeleteConfig selected cell source) =
      some (countDeleteConfig selected cell target) := by
  apply TuringMachine.PhaseEmbedding.runConfigExact?_lift_of_eq_some
    (inner := DeleteRestagedMachine.machine none) (outer := machine selected)
    (fun inner => Control.count selected cell (.delete inner))
  · intro c
    cases c with
    | mk inner tape =>
        unfold TuringMachine.stepConfig
        simp only [TuringMachine.PhaseEmbedding.liftConfig, machine, transition, DeleteRestagedMachine.machine]
        cases htransition : DeleteRestagedMachine.transition none inner (Tape.read tape) with
        | none => rfl
        | some action =>
            rcases action with ⟨write, direction, target⟩
            rfl
  · exact hrun
theorem runConfigExact_trans {stateCount : Nat} (selected : Selected stateCount)
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol (Control stateCount)}
    (hab : (machine selected).runConfigExact? first a = some b)
    (hbc : (machine selected).runConfigExact? second b = some c) :
    (machine selected).runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)
def firstEditSteps {stateCount : Nat} (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) (nextHead : Option MachineCodeSymbol)
    (remainingLeft : List (Option MachineCodeSymbol)) : Nat :=
  (((Prefix.runSteps fuel L callerData + 2) + Decoder.runSteps nextHead) + 2) + DeleteRestagedMachine.runSteps nextHead
      (MoveLeftNonempty.leftPayloadPrefix (FuelDecrementMachine.withFuel fuel L)).reverse
      (MoveLeftNonempty.afterFirstLeftCell (FuelDecrementMachine.withFuel fuel L) remainingLeft callerData)
/-- One exact run of one finite machine through the difficult first edit of the
nonempty-left motion branch.  The run decrements fuel, locates and decodes the
first left cell on the actual padded tape, deletes that encoding, and physically
rewinds to the canonical header boundary. -/
theorem unified_run_to_first_left_delete {stateCount : Nat} (selected : Selected stateCount)
    (fuel : Nat) (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : L.left = nextHead :: remainingLeft) :
    let target := FuelDecrementMachine.withFuel fuel L
    let leftRev : Word MachineCodeSymbol :=
      (MoveLeftNonempty.leftPayloadPrefix target).reverse
    let suffix : Word MachineCodeSymbol := MoveLeftNonempty.afterFirstLeftCell
      target remainingLeft callerData
    exists endpoint, (machine selected).runConfigExact? (firstEditSteps fuel L callerData nextHead remainingLeft)
          (prefixConfig (Prefix.fuelConfig selected (FuelDecrementMachine.startConfig (Frame.protectedWord
                  (FuelDecrementMachine.withFuel (fuel + 1) L) callerData)))) = some endpoint ∧ endpoint.state =
        Control.delete selected nextHead (.rewind .gate) ∧ Tape.Equiv (DeleteRestagedMachine.rewindConfig
          (DeleteEndpointRewind.gateConfig (PhysicalBranch.deleteOutput leftRev suffix) nextHead)).tape
        endpoint.tape := by
  let target := FuelDecrementMachine.withFuel fuel L
  let leftRev : Word MachineCodeSymbol :=
    (MoveLeftNonempty.leftPayloadPrefix target).reverse
  let suffix : Word MachineCodeSymbol := MoveLeftNonempty.afterFirstLeftCell
    target remainingLeft callerData
  have htargetLeft : target.left = nextHead :: remainingLeft := by
    simpa [target, FuelDecrementMachine.withFuel] using hleft
  have hleftRev : leftRev ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp [leftRev, MoveLeftNonempty.leftPayloadPrefix, MachineDescription.encodeNatAppend] at hlength
  rcases Update.PresentAction.SelectedFuelThenLeftBoundary.unified_run_to_leftPayload
        selected fuel L callerData with
    ⟨prefixEndpoint, hprefix, hprefixState, hprefixTape⟩
  have hprefixOuter :=
    prefix_run_of_some selected _ _ _ hprefix
  have hprefixHandoff :=
    prefix_handoff_run_exact selected prefixEndpoint.tape
  have hprefixHandoff' : (machine selected).runConfigExact? 2 (prefixConfig prefixEndpoint) = some
          (decoderConfig selected
            { state := Dispatch.OptionalCell.Control.decode ⟨0, by decide⟩
              tape := roundTripTape prefixEndpoint.tape }) := by
    simpa [prefixConfig, hprefixState] using hprefixHandoff
  have hboundary := leftPayload_gate_eq_decoder_source target nextHead remainingLeft callerData htargetLeft
  have hdecoderTape : Tape.Equiv (Decoder.sourceConfig leftRev nextHead suffix).tape
        (roundTripTape prefixEndpoint.tape) := by
    have hclean := Tape.Equiv.trans hprefixTape (Tape.Equiv.symm (roundTripTape_equiv prefixEndpoint.tape))
    rw [hboundary] at hclean
    simpa only [leftRev, suffix] using hclean
  rcases Dispatch.OptionalCell.run_exact_of_tape_equiv leftRev nextHead suffix hleftRev
      (roundTripTape prefixEndpoint.tape) hdecoderTape with
    ⟨decoderEndpoint, hdecoder, hdecoderState, hdecoderTapeFinal⟩
  have hdecoderOuter := decoder_run_of_some selected _ _ _ hdecoder
  have hdecoderHandoff := decoder_handoff_run_exact selected nextHead decoderEndpoint.tape
  have hdecoderHandoff' : (machine selected).runConfigExact? 2 (decoderConfig selected decoderEndpoint) = some
          (deleteConfig selected nextHead
            { state := DeleteRestagedMachine.Control.edit (.erase (DeleteBlock.optionalGap nextHead))
              tape := roundTripTape decoderEndpoint.tape }) := by
    simpa [decoderConfig, hdecoderState] using hdecoderHandoff
  have hdeleteTape : Tape.Equiv (DeleteRestagedMachine.editConfig
          (DeleteBlock.sourceConfig nextHead leftRev suffix)).tape (roundTripTape decoderEndpoint.tape) := by
    exact Tape.Equiv.trans hdecoderTapeFinal (Tape.Equiv.symm (roundTripTape_equiv decoderEndpoint.tape))
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (DeleteRestagedMachine.run_exact nextHead leftRev suffix) hdeleteTape with
    ⟨deleteEndpoint, hdelete, hdeleteState, hdeleteTapeFinal⟩
  have hdeleteOuter := delete_run_of_some selected nextHead _ _ _ hdelete
  have hrun1 := runConfigExact_trans selected hprefixOuter hprefixHandoff'
  have hrun2 := runConfigExact_trans selected hrun1 hdecoderOuter
  have hrun3 := runConfigExact_trans selected hrun2 hdecoderHandoff'
  have hrun4 := runConfigExact_trans selected hrun3 hdeleteOuter
  refine ⟨deleteConfig selected nextHead deleteEndpoint, ?_, ?_, ?_⟩
  · simpa [firstEditSteps, target, leftRev, suffix, Nat.add_assoc] using hrun4
  · simpa [deleteConfig, TuringMachine.PhaseEmbedding.liftConfig, DeleteRestagedMachine.rewindConfig,
      DeleteEndpointRewind.gateConfig] using hdeleteState
  · exact hdeleteTapeFinal
def countPhaseSteps {stateCount : Nat} (L : Layout stateCount) (remainingLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Nat :=
  ((2 + FieldLocator.leftCountSteps L) + 2) + countDeleteRunSteps (MoveLeftNonempty.leftCountPrefix L).reverse
      (MoveLeftNonempty.afterCountTick L remainingLeft callerData)
/-- From any padded representative of the first-delete rewind endpoint, the
same finite machine restarts at the header, locates the stale left count,
deletes its leading unary tick, and rewinds to a canonical representative of
the layout with the first left cell removed. -/
theorem continue_to_left_count_decrement {stateCount : Nat} (selected : Selected stateCount)
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : L.left = nextHead :: remainingLeft) (T : Tape MachineCodeSymbol) (hT : Tape.Equiv
      (DeleteRestagedMachine.rewindConfig (DeleteEndpointRewind.gateConfig
          (PhysicalBranch.deleteOutput (MoveLeftNonempty.leftPayloadPrefix L).reverse
            (MoveLeftNonempty.afterFirstLeftCell L remainingLeft callerData)) nextHead)).tape T) :
    let countLeftRev : Word MachineCodeSymbol :=
      (MoveLeftNonempty.leftCountPrefix L).reverse
    let countSuffix : Word MachineCodeSymbol :=
      MoveLeftNonempty.afterCountTick L remainingLeft callerData
    exists endpoint, (machine selected).runConfigExact? (countPhaseSteps L remainingLeft callerData)
          (deleteConfig selected nextHead
            { state := DeleteRestagedMachine.Control.rewind .gate
              tape := T }) = some endpoint ∧ endpoint.state = Control.count selected nextHead
          (.delete (.rewind .gate)) ∧ Tape.Equiv (DeleteRestagedMachine.rewindConfig (DeleteEndpointRewind.gateConfig
            (PhysicalBranch.deleteOutput countLeftRev countSuffix) none)).tape endpoint.tape := by
  let firstOutput : Word MachineCodeSymbol :=
    PhysicalBranch.deleteOutput (MoveLeftNonempty.leftPayloadPrefix L).reverse
      (MoveLeftNonempty.afterFirstLeftCell L remainingLeft callerData)
  let countLeftRev : Word MachineCodeSymbol :=
    (MoveLeftNonempty.leftCountPrefix L).reverse
  let countSuffix : Word MachineCodeSymbol :=
    MoveLeftNonempty.afterCountTick L remainingLeft callerData
  let countRest : Word MachineCodeSymbol :=
    MachineCodeSymbol.tick :: countSuffix
  have hdecomp : firstOutput = List.append (MoveLeftNonempty.leftCountPrefix L) countRest := by
    simpa [firstOutput, countRest, countSuffix] using firstDeleteOutput_count_decomp
        L nextHead remainingLeft callerData hleft
  have hhandoff := first_delete_handoff_run_exact selected nextHead T
  have hgateInput : Tape.Equiv (DeleteEndpointRewind.gateConfig firstOutput nextHead).tape (Tape.input firstOutput) :=
    DeleteEndpointRewind.gateTape_equiv_input firstOutput nextHead
  have hT' : Tape.Equiv (DeleteEndpointRewind.gateConfig firstOutput nextHead).tape T := by
    simpa [firstOutput, DeleteRestagedMachine.rewindConfig] using hT
  have hlocatorSourceInput : (FieldLocator.config .header [] (List.append (MoveLeftNonempty.leftCountPrefix L)
          countRest)).tape = Tape.input firstOutput := by
    rw [hdecomp]
    rfl
  have hlocatorTape : Tape.Equiv (FieldLocator.config .header [] (List.append (MoveLeftNonempty.leftCountPrefix L)
            countRest)).tape (roundTripTape T) := by
    rw [hlocatorSourceInput]
    exact Tape.Equiv.trans (Tape.Equiv.symm hgateInput) (Tape.Equiv.trans hT' (Tape.Equiv.symm (roundTripTape_equiv T)))
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (locate_leftCount_prefix_exact L countRest) hlocatorTape with
    ⟨locatorEndpoint, hlocator, hlocatorState, hlocatorTapeFinal⟩
  have hlocatorOuter := countLocate_run_of_some selected nextHead _ _ _ hlocator
  have hlocatorHandoff := count_locator_handoff_run_exact selected nextHead locatorEndpoint.tape
  have hlocatorHandoff' : (machine selected).runConfigExact? 2 (countLocateConfig selected nextHead locatorEndpoint) =
        some (countDeleteConfig selected nextHead
            { state := DeleteRestagedMachine.Control.edit (.erase (DeleteBlock.optionalGap none))
              tape := roundTripTape locatorEndpoint.tape }) := by
    simpa [countLocateConfig, FieldLocator.config, hlocatorState] using hlocatorHandoff
  have hcountDeleteTape : Tape.Equiv (DeleteRestagedMachine.editConfig
          (DeleteBlock.oneSourceConfig MachineCodeSymbol.tick countLeftRev countSuffix)).tape
        (roundTripTape locatorEndpoint.tape) := by
    have hclean : (DeleteRestagedMachine.editConfig (DeleteBlock.oneSourceConfig MachineCodeSymbol.tick
            countLeftRev countSuffix)).tape = (FieldLocator.config .gate countLeftRev countRest).tape := by
      rfl
    rw [hclean]
    exact Tape.Equiv.trans hlocatorTapeFinal (Tape.Equiv.symm (roundTripTape_equiv locatorEndpoint.tape))
  let countSteps := countDeleteRunSteps countLeftRev countSuffix
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (by simpa [countSteps, countDeleteRunSteps] using
          (countDelete_run_exact countLeftRev countSuffix)) hcountDeleteTape with
    ⟨countEndpoint, hcount, hcountState, hcountTapeFinal⟩
  have hcountOuter := countDelete_run_of_some selected nextHead hcount
  have hrun1 := runConfigExact_trans selected hhandoff hlocatorOuter
  have hrun2 := runConfigExact_trans selected hrun1 hlocatorHandoff'
  have hrun3 := runConfigExact_trans selected hrun2 hcountOuter
  refine ⟨countDeleteConfig selected nextHead countEndpoint, ?_, ?_, ?_⟩
  · simpa [countPhaseSteps, countSteps, countLeftRev, countSuffix, countDeleteRunSteps, Nat.add_assoc] using hrun3
  · simpa [countDeleteConfig, TuringMachine.PhaseEmbedding.liftConfig, DeleteRestagedMachine.rewindConfig,
      DeleteEndpointRewind.gateConfig] using hcountState
  · exact hcountTapeFinal
def throughCountSteps {stateCount : Nat} (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) (nextHead : Option MachineCodeSymbol)
    (remainingLeft : List (Option MachineCodeSymbol)) : Nat :=
  firstEditSteps fuel L callerData nextHead remainingLeft + countPhaseSteps (FuelDecrementMachine.withFuel fuel L)
      remainingLeft callerData
/-- Canonical layout-to-layout checkpoint for the nonempty-left branch.  One
finite machine now reaches the physically rewound frame whose left payload and
unary count both reflect removal of the decoded neighboring cell. -/
theorem unified_run_to_removed_left_layout {stateCount : Nat} (selected : Selected stateCount)
    (fuel : Nat) (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : L.left = nextHead :: remainingLeft) :
    let target := FuelDecrementMachine.withFuel fuel L
    let removed := MoveLeftNonempty.removedLeftLayout target remainingLeft
    exists endpoint, (machine selected).runConfigExact?
          (throughCountSteps fuel L callerData nextHead remainingLeft) (prefixConfig
            (Prefix.fuelConfig selected (FuelDecrementMachine.startConfig (Frame.protectedWord
                  (FuelDecrementMachine.withFuel (fuel + 1) L) callerData)))) = some endpoint ∧ endpoint.state =
        Control.count selected nextHead (.delete (.rewind .gate)) ∧ Tape.Equiv
        (Tape.input (Frame.protectedWord removed callerData)) endpoint.tape := by
  let target := FuelDecrementMachine.withFuel fuel L
  let removed := MoveLeftNonempty.removedLeftLayout target remainingLeft
  have htargetLeft : target.left = nextHead :: remainingLeft := by
    simpa [target, FuelDecrementMachine.withFuel] using hleft
  rcases unified_run_to_first_left_delete selected fuel L callerData nextHead remainingLeft hleft with
    ⟨firstEndpoint, hfirst, hfirstState, hfirstTape⟩
  rcases continue_to_left_count_decrement selected target callerData
      nextHead remainingLeft htargetLeft firstEndpoint.tape hfirstTape with
    ⟨countEndpoint, hcount, hcountState, hcountTape⟩
  have hfirstEndpointEq : firstEndpoint = deleteConfig selected nextHead
          { state := DeleteRestagedMachine.Control.rewind .gate
            tape := firstEndpoint.tape } := by
    cases firstEndpoint with
    | mk firstState firstTape =>
        simp only at hfirstState ⊢
        subst firstState
        rfl
  have hcount' : (machine selected).runConfigExact? (countPhaseSteps target remainingLeft callerData)
          firstEndpoint = some countEndpoint := by
    rw [hfirstEndpointEq]
    exact hcount
  have hrun := runConfigExact_trans selected hfirst hcount'
  refine ⟨countEndpoint, ?_, hcountState, ?_⟩
  · simpa [throughCountSteps, target] using hrun
  · let countLeftRev : Word MachineCodeSymbol :=
      (MoveLeftNonempty.leftCountPrefix target).reverse
    let countSuffix : Word MachineCodeSymbol :=
      MoveLeftNonempty.afterCountTick target remainingLeft callerData
    let countOutput : Word MachineCodeSymbol :=
      PhysicalBranch.deleteOutput countLeftRev countSuffix
    have houtput : countOutput = Frame.protectedWord removed callerData := by
      simpa [countOutput, countLeftRev, countSuffix, removed] using PhysicalBranch.decrementLeft_output_eq_protectedWord
          target remainingLeft callerData
    have hgateInput : Tape.Equiv (DeleteEndpointRewind.gateConfig countOutput none).tape (Tape.input countOutput) :=
      DeleteEndpointRewind.gateTape_equiv_input countOutput none
    have hinputGate : Tape.Equiv (Tape.input (Frame.protectedWord removed callerData))
          (DeleteRestagedMachine.rewindConfig (DeleteEndpointRewind.gateConfig countOutput none)).tape := by
      rw [← houtput]
      simpa [DeleteRestagedMachine.rewindConfig] using Tape.Equiv.symm hgateInput
    exact Tape.Equiv.trans hinputGate (by simpa [countOutput, countLeftRev, countSuffix] using hcountTape)
/-- The canonical layout checkpoint is stable under all padding accumulated by
the dispatch prefix.  This is the form needed by the eventual update-kernel
consumer, whose selected-entry tape is only equivalent to a clean input. -/
theorem unified_run_to_removed_left_layout_of_source_equiv
    {stateCount : Nat} (selected : Selected stateCount) (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) (nextHead : Option MachineCodeSymbol)
    (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : L.left = nextHead :: remainingLeft) (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input (Frame.protectedWord
          (FuelDecrementMachine.withFuel (fuel + 1) L) callerData)) T) :
    let target := FuelDecrementMachine.withFuel fuel L
    let removed := MoveLeftNonempty.removedLeftLayout target remainingLeft
    exists endpoint, (machine selected).runConfigExact? (throughCountSteps fuel L callerData nextHead remainingLeft)
          { state := (machine selected).start, tape := T } = some endpoint ∧ endpoint.state =
        Control.count selected nextHead (.delete (.rewind .gate)) ∧ Tape.Equiv
        (Tape.input (Frame.protectedWord removed callerData)) endpoint.tape := by
  let target := FuelDecrementMachine.withFuel fuel L
  let removed := MoveLeftNonempty.removedLeftLayout target remainingLeft
  rcases unified_run_to_removed_left_layout selected fuel L callerData nextHead remainingLeft hleft with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  have hcleanSource : (prefixConfig (Prefix.fuelConfig selected (FuelDecrementMachine.startConfig (Frame.protectedWord
              (FuelDecrementMachine.withFuel (fuel + 1) L) callerData))) : TuringMachine.Configuration MachineCodeSymbol
          (Control stateCount)) =
        { state := (machine selected).start
          tape := Tape.input (Frame.protectedWord (FuelDecrementMachine.withFuel (fuel + 1) L) callerData) } := by
    rfl
  rw [hcleanSource] at hclean
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, hrun, ?_, ?_⟩
  · exact hstate.trans hcleanState
  · exact Tape.Equiv.trans hcleanTape htape
end LeftFirst
end Update
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
