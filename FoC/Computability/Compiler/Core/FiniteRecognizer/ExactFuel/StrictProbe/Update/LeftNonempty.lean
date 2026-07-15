import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftEmpty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.SerializedHead

set_option doc.verso true

/-!
# Nonempty-left selected update

The complete nonempty-left machine composes the first-cell edit with the
shared replacement and right-prepend tail.
-/

namespace FoC
namespace Computability
open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Update
namespace LeftNonempty
open SerializedFieldComposer
abbrev Selected := SerializedHeadDispatch.Selected
abbrev TailControl := Update.LeftEmpty.General.Control

inductive Control (stateCount : Nat) where
  | left (inner : Update.LeftFirst.Control stateCount)
  | leftReturn (newHead : Option MachineCodeSymbol)
  | tail (newHead : Option MachineCodeSymbol) (inner : TailControl)
  | done
deriving DecidableEq

namespace Control
def optionalFinite : Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite
def tailFinite : Foundation.FiniteType (Option MachineCodeSymbol × TailControl) :=
  Foundation.FiniteType.prod optionalFinite Update.LeftEmpty.General.Control.finite
def elems (stateCount : Nat) : List (Control stateCount) :=
  (Update.LeftFirst.Control.finite stateCount).elems.map Control.left ++
    optionalFinite.elems.map Control.leftReturn ++
    tailFinite.elems.map (fun payload => Control.tail payload.1 payload.2) ++ [Control.done]
def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | left inner =>
        have h := (Update.LeftFirst.Control.finite stateCount).complete inner
        simp [elems, h]
    | leftReturn newHead =>
        have h := optionalFinite.complete newHead
        simp [elems, h]
    | tail newHead inner =>
        have h := tailFinite.complete (newHead, inner)
        simpa [elems] using h
    | done => simp [elems]
end Control
def tailHalt : TailControl :=
  Update.LeftEmpty.General.Control.count (.insert (.rewind .gate))
def embedTail {stateCount : Nat} (newHead : Option MachineCodeSymbol) (inner : TailControl) : Control stateCount :=
  if inner = tailHalt then .done else .tail newHead inner
def mapLeftAction {stateCount : Nat} : Option MachineCodeSymbol × Direction ×
        Update.LeftFirst.Control stateCount -> Option MachineCodeSymbol × Direction × Control stateCount
  | (write, direction, target) => (write, direction, .left target)
def mapTailAction {stateCount : Nat} (newHead : Option MachineCodeSymbol) :
    Option MachineCodeSymbol × Direction × TailControl -> Option MachineCodeSymbol × Direction × Control stateCount
  | (write, direction, target) => (write, direction, embedTail newHead target)
def transition {stateCount : Nat} (selected : Selected stateCount) : Control stateCount -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control stateCount)
  | .left inner, read =>
      match Update.LeftFirst.transition inner read with
      | some action => some (mapLeftAction action)
      | none =>
          match inner with
          | .count _ newHead (.delete (.rewind .gate)) =>
              some (read, Direction.right, .leftReturn newHead)
          | _ => none
  | .leftReturn newHead, read =>
      some (read, Direction.left, embedTail newHead (Update.LeftEmpty.General.machine
          newHead selected.write).start)
  | .tail newHead inner, read =>
      Option.map (mapTailAction newHead)
        (Update.LeftEmpty.General.transition newHead selected.write inner read)
  | .done, _ => none
def machine {stateCount : Nat} (selected : Selected stateCount) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .left (Update.LeftFirst.machine selected).start
  halt := .done
  transition := transition selected
  statesFinite := Control.finite stateCount
abbrev roundTripTape := Update.LeftEmpty.General.roundTripTape
theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) : Tape.Equiv (roundTripTape T) T :=
  Update.LeftEmpty.General.roundTripTape_equiv T
def leftConfig {stateCount : Nat} (c : TuringMachine.Configuration MachineCodeSymbol
      (Update.LeftFirst.Control stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.left c
def tailConfig {stateCount : Nat} (newHead : Option MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol TailControl) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig (embedTail newHead) c
theorem left_run_of_some {stateCount : Nat} (selected : Selected stateCount)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol (Update.LeftFirst.Control stateCount)}
    (hrun : (Update.LeftFirst.machine selected).runConfigExact? steps source = some target) :
    (machine selected).runConfigExact? steps (leftConfig source) = some (leftConfig target) := by
  apply Update.LeftTail.runConfigExact_some_of_transition_some Control.left ?_ hrun
  intro state read written direction target hinner
  have hinner' : Update.LeftFirst.transition state read = some (written, direction, target) := by
    simpa [Update.LeftFirst.machine] using hinner
  simp [machine, transition, hinner', mapLeftAction]
theorem tail_run_of_some {stateCount : Nat} (selected : Selected stateCount)
    (newHead : Option MachineCodeSymbol) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol TailControl}
    (hrun : (Update.LeftEmpty.General.machine newHead selected.write).runConfigExact?
      steps source = some target) : (machine selected).runConfigExact? steps (tailConfig newHead source) =
      some (tailConfig newHead target) := by
  apply Update.LeftTail.runConfigExact_some_of_transition_some (embedTail newHead) ?_ hrun
  intro state read written direction target hinner
  have hinner' : Update.LeftEmpty.General.transition
      newHead selected.write state read = some (written, direction, target) := by
    simpa [Update.LeftEmpty.General.machine] using hinner
  have hactive : state ≠ tailHalt := by
    intro hhalt
    subst state
    simp [tailHalt, Update.LeftEmpty.General.transition,
      Edits.PositionedRight.transition, InsertRestagedMachine.transition, RewindWord.transition] at hinner'
  simp [machine, transition, embedTail, hactive, hinner', mapTailAction]
private theorem write_read_eq_self (T : Tape MachineCodeSymbol) : Tape.write (Tape.read T) T = T := by
  cases T
  rfl
theorem left_tail_handoff {stateCount : Nat} (selected : Selected stateCount)
    (newHead : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) : (machine selected).runConfigExact? 2
        { state := Control.left (.count selected newHead (.delete (.rewind .gate)))
          tape := T } = some (tailConfig newHead
        { state := (Update.LeftEmpty.General.machine newHead selected.write).start
          tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine,
    transition, tailConfig, TuringMachine.PhaseEmbedding.liftConfig, embedTail, tailHalt, roundTripTape,
    Update.LeftEmpty.General.roundTripTape, write_read_eq_self,
    Update.LeftFirst.transition, DeleteRestagedMachine.transition,
    DeleteEndpointRewind.transition, Update.LeftEmpty.General.machine]
theorem runConfigExact_trans {stateCount : Nat} (selected : Selected stateCount)
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol (Control stateCount)}
    (hab : (machine selected).runConfigExact? first a = some b)
    (hbc : (machine selected).runConfigExact? second b = some c) :
    (machine selected).runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)
def runSteps {stateCount : Nat} (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextHead : Option MachineCodeSymbol)
    (remainingLeft : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) : Nat :=
  let removed := MoveLeftNonempty.removedLeftLayout
    (FuelDecrementMachine.withFuel fuel F.physicalFrame) remainingLeft
  (Update.LeftFirst.throughCountSteps fuel F.physicalFrame callerData nextHead remainingLeft + 2) +
    Update.LeftEmpty.General.runSteps removed nextHead write callerData
theorem run_exact {stateCount : Nat} (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : F.physicalFrame.left = nextHead :: remainingLeft) :
    let selected := Update.LeftKernel.selectedPayload
      write Direction.left nextState
    exists endpoint, (machine selected).runConfigExact? (runSteps fuel F write nextHead remainingLeft callerData)
          { state := (machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.left nextState } = some endpoint ∧
      endpoint.state = (machine selected).halt ∧ Tape.Equiv (Tape.input (Frame.protectedWord
            (CarriedStateFrame.afterSelected fuel write Direction.left
              nextState F).physicalFrame callerData)) endpoint.tape := by
  let selected := Update.LeftKernel.selectedPayload
    write Direction.left nextState
  let target := FuelDecrementMachine.withFuel fuel F.physicalFrame
  let removed := MoveLeftNonempty.removedLeftLayout target remainingLeft
  let replaced := HeadReplacement.replaceHead removed nextHead
  rcases Update.LeftKernel.selectedPrefix_run_to_removed_left_layout
      callerData fuel F write nextState nextHead remainingLeft hleft with
    ⟨leftEndpoint, hleftInner, hleftState, hleftTape⟩
  have hleftRun := left_run_of_some selected hleftInner
  have hhandoffClean := left_tail_handoff selected nextHead leftEndpoint.tape
  have hhandoff : (machine selected).runConfigExact? 2 (leftConfig leftEndpoint) = some (tailConfig nextHead
        { state := (Update.LeftEmpty.General.machine nextHead selected.write).start
          tape := roundTripTape leftEndpoint.tape }) := by
    cases leftEndpoint with
    | mk endpointState endpointTape =>
        simp only at hleftState ⊢
        subst endpointState
        exact hhandoffClean
  have htailSource : Tape.Equiv (Tape.input
      (Frame.protectedWord removed callerData)) (roundTripTape leftEndpoint.tape) :=
    Tape.Equiv.trans hleftTape (Tape.Equiv.symm (roundTripTape_equiv leftEndpoint.tape))
  rcases Update.LeftEmpty.General.run_from_equiv
      nextHead removed write callerData (roundTripTape leftEndpoint.tape) htailSource with
    ⟨tailEndpoint, htailInner, htailState, htailTape⟩
  have htailRun := tail_run_of_some selected nextHead htailInner
  have hfirst := runConfigExact_trans selected hleftRun hhandoff
  have hfull := runConfigExact_trans selected hfirst htailRun
  have hshape : RightPrepend.prependedRightLayout replaced write =
      (CarriedStateFrame.afterSelected fuel write Direction.left nextState F).physicalFrame := by
    simpa [target, removed, replaced] using Update.LeftKernel.right_tail_target_eq_afterSelected
        fuel F write nextState nextHead remainingLeft hleft
  refine ⟨tailConfig nextHead tailEndpoint, ?_, ?_, ?_⟩
  · simpa [runSteps, selected, target, removed, Update.LeftKernel.selectedPayload, leftConfig, machine,
      TuringMachine.PhaseEmbedding.liftConfig] using hfull
  · have htailState' : tailEndpoint.state = tailHalt := by
      simpa [Update.LeftEmpty.General.machine, tailHalt] using htailState
    simp [machine, tailConfig, TuringMachine.PhaseEmbedding.liftConfig, embedTail, htailState']
  · rw [← hshape]
    exact htailTape
theorem run_from_selectedPrefix_equiv {stateCount : Nat} (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount) (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : F.physicalFrame.left = nextHead :: remainingLeft) (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Update.LeftKernel.selectedPrefixTape
      callerData fuel F write Direction.left nextState) T) :
    let selected := Update.LeftKernel.selectedPayload
      write Direction.left nextState
    exists endpoint, (machine selected).runConfigExact? (runSteps fuel F write nextHead remainingLeft callerData)
          { state := (machine selected).start, tape := T } = some endpoint ∧
      endpoint.state = (machine selected).halt ∧ Tape.Equiv (Tape.input (Frame.protectedWord
            (CarriedStateFrame.afterSelected fuel write Direction.left
              nextState F).physicalFrame callerData)) endpoint.tape := by
  let selected := Update.LeftKernel.selectedPayload
    write Direction.left nextState
  rcases run_exact callerData fuel F write nextState nextHead remainingLeft hleft with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, hrun, ?_, Tape.Equiv.trans hcleanTape htape⟩
  exact hstate ▸ hcleanState
end LeftNonempty
end Update
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
