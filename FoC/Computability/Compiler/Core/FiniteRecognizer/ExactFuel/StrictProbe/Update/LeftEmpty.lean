import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.HeadCursorRuns
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftTail
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.PositionedRight

set_option doc.verso true

/-!
# Left-update tail runner

This finite phase union replaces the serialized head and updates the right
payload and its count. The general runner supports either carried head value;
the outer API specializes it to empty-left motion.
-/

namespace FoC
namespace Computability
open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Update
namespace LeftEmpty
namespace General
open SerializedFieldComposer
abbrev ReplaceControl := Edits.OptionalField.Replace.Control
abbrev RightEditControl := Edits.PositionedRight.Control
/- One finite phase union for the empty-left motion tail.  The decoded old
head is carried from the first locator into the replacement phase; no layout
value appears in the transition table. -/
inductive Control where
  | locate (inner : Dispatch.HeadCursor.Full.Control)
  | locateReturn (oldHead : Option MachineCodeSymbol)
  | replace (oldHead : Option MachineCodeSymbol) (inner : ReplaceControl)
  | replaceReturn
  | locatePayload (inner : Dispatch.HeadCursor.Full.Control)
  | locatePayloadReturn
  | payload (inner : RightEditControl)
  | payloadReturn
  | locateCount (inner : Dispatch.HeadCursor.Full.Control)
  | locateCountReturn
  | count (inner : RightEditControl)
deriving DecidableEq

namespace Control
def optionalFinite : Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite
def replaceFinite : Foundation.FiniteType (Option MachineCodeSymbol × ReplaceControl) :=
  Foundation.FiniteType.prod optionalFinite Edits.OptionalField.Replace.Control.finite
def elems : List Control :=
  Dispatch.HeadCursor.Full.Control.finite.elems.map Control.locate ++
    optionalFinite.elems.map Control.locateReturn ++ replaceFinite.elems.map (fun payload =>
      Control.replace payload.1 payload.2) ++ [Control.replaceReturn] ++
    Dispatch.HeadCursor.Full.Control.finite.elems.map Control.locatePayload ++ [Control.locatePayloadReturn] ++
    Edits.PositionedRight.Control.finite.elems.map Control.payload ++ [Control.payloadReturn] ++
    Dispatch.HeadCursor.Full.Control.finite.elems.map Control.locateCount ++ [Control.locateCountReturn] ++
    Edits.PositionedRight.Control.finite.elems.map Control.count
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        have h := Dispatch.HeadCursor.Full.Control.finite.complete inner
        simp [elems, h]
    | locateReturn oldHead =>
        have h := optionalFinite.complete oldHead
        simp [elems, h]
    | replace oldHead inner =>
        have h := replaceFinite.complete (oldHead, inner)
        simpa [elems] using h
    | replaceReturn => simp [elems]
    | locatePayload inner =>
        have h := Dispatch.HeadCursor.Full.Control.finite.complete inner
        simp [elems, h]
    | locatePayloadReturn => simp [elems]
    | payload inner =>
        have h := Edits.PositionedRight.Control.finite.complete inner
        simp [elems, h]
    | payloadReturn => simp [elems]
    | locateCount inner =>
        have h := Dispatch.HeadCursor.Full.Control.finite.complete inner
        simp [elems, h]
    | locateCountReturn => simp [elems]
    | count inner =>
        have h := Edits.PositionedRight.Control.finite.complete inner
        simp [elems, h]
end Control
def mapLocateAction : Option MachineCodeSymbol × Direction × Dispatch.HeadCursor.Full.Control ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) => (write, direction, .locate target)
def mapReplaceAction (oldHead : Option MachineCodeSymbol) : Option MachineCodeSymbol × Direction × ReplaceControl ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) =>
      (write, direction, .replace oldHead target)
def mapLocatePayloadAction : Option MachineCodeSymbol × Direction × Dispatch.HeadCursor.Full.Control ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) => (write, direction, .locatePayload target)
def mapPayloadAction : Option MachineCodeSymbol × Direction × RightEditControl ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) => (write, direction, .payload target)
def mapLocateCountAction : Option MachineCodeSymbol × Direction × Dispatch.HeadCursor.Full.Control ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) => (write, direction, .locateCount target)
def mapCountAction : Option MachineCodeSymbol × Direction × RightEditControl ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) => (write, direction, .count target)
variable (newHead : Option MachineCodeSymbol)
def transition (write : Option MachineCodeSymbol) : Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate inner, read =>
      match Dispatch.HeadCursor.Full.transition inner read with
      | some action => some (mapLocateAction action)
      | none =>
          match inner with
          | .post (.positioned oldHead) =>
              some (read, Direction.right, .locateReturn oldHead)
          | _ => none
  | .locateReturn oldHead, read =>
      some (read, Direction.left, .replace oldHead (Edits.OptionalField.Replace.machine oldHead newHead).start)
  | .replace oldHead inner, read =>
      match Edits.OptionalField.Replace.transition oldHead newHead inner read with
      | some action => some (mapReplaceAction oldHead action)
      | none =>
          match inner with
          | .insert (.rewind .gate) =>
              some (read, Direction.right, .replaceReturn)
          | _ => none
  | .replaceReturn, read =>
      some (read, Direction.left, .locatePayload Dispatch.HeadCursor.Full.machine.start)
  | .locatePayload inner, read =>
      match Dispatch.HeadCursor.Full.transition inner read with
      | some action => some (mapLocatePayloadAction action)
      | none =>
          match inner with
          | .post (.positioned _) =>
              some (read, Direction.right, .locatePayloadReturn)
          | _ => none
  | .locatePayloadReturn, read =>
      some (read, Direction.left, .payload (Edits.PositionedRight.machine .rightPayload
              (InsertBlock.optionalBuffer write)).start)
  | .payload inner, read =>
      match Edits.PositionedRight.transition .rightPayload (InsertBlock.optionalBuffer write) inner read with
      | some action => some (mapPayloadAction action)
      | none =>
          match inner with
          | .insert (.rewind .gate) =>
              some (read, Direction.right, .payloadReturn)
          | _ => none
  | .payloadReturn, read =>
      some (read, Direction.left, .locateCount Dispatch.HeadCursor.Full.machine.start)
  | .locateCount inner, read =>
      match Dispatch.HeadCursor.Full.transition inner read with
      | some action => some (mapLocateCountAction action)
      | none =>
          match inner with
          | .post (.positioned _) =>
              some (read, Direction.right, .locateCountReturn)
          | _ => none
  | .locateCountReturn, read =>
      some (read, Direction.left, .count (Edits.PositionedRight.machine .rightCountTicks
              (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).start)
  | .count inner, read =>
      Option.map mapCountAction (Edits.PositionedRight.transition .rightCountTicks
          (InsertBlock.singletonBuffer MachineCodeSymbol.tick) inner read)
def machine (newHead write : Option MachineCodeSymbol) : TuringMachine MachineCodeSymbol Control where
  start := .locate Dispatch.HeadCursor.Full.machine.start
  halt := .count (.insert (.rewind .gate))
  transition := transition newHead write
  statesFinite := Control.finite
@[simp] theorem transition_halt (newHead write read : Option MachineCodeSymbol) :
    transition newHead write (machine newHead write).halt read = none := by
  rfl
def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)
theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) : Tape.Equiv (roundTripTape T) T :=
  Machine.moveLeft_moveRight_equiv_self T
def locateConfig (c : TuringMachine.Configuration MachineCodeSymbol Dispatch.HeadCursor.Full.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.locate c
def replaceConfig (oldHead : Option MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol ReplaceControl) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.replace oldHead) c
def locatePayloadConfig (c : TuringMachine.Configuration MachineCodeSymbol Dispatch.HeadCursor.Full.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.locatePayload c
def payloadConfig (c : TuringMachine.Configuration MachineCodeSymbol RightEditControl) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.payload c
def locateCountConfig (c : TuringMachine.Configuration MachineCodeSymbol Dispatch.HeadCursor.Full.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.locateCount c
def countConfig (c : TuringMachine.Configuration MachineCodeSymbol RightEditControl) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.count c
theorem locate_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol Dispatch.HeadCursor.Full.Control}
    (hrun : Dispatch.HeadCursor.Full.machine.runConfigExact? steps source = some target) :
    (machine newHead write).runConfigExact? steps (locateConfig source) = some (locateConfig target) := by
  apply Update.LeftTail.runConfigExact_some_of_transition_some Control.locate ?_ hrun
  intro state read written direction target hinner
  have hinner' : Dispatch.HeadCursor.Full.transition state read =
      some (written, direction, target) := by
    simpa [Dispatch.HeadCursor.Full.machine] using hinner
  simp [machine, transition, hinner', mapLocateAction]
theorem replace_run_of_some (write oldHead : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol ReplaceControl} (hrun :
      (Edits.OptionalField.Replace.machine oldHead newHead).runConfigExact? steps source = some target) :
    (machine newHead write).runConfigExact? steps (replaceConfig oldHead source) = some (replaceConfig oldHead target) := by
  apply Update.LeftTail.runConfigExact_some_of_transition_some
    (Control.replace oldHead) ?_ hrun
  intro state read written direction target hinner
  have hinner' : Edits.OptionalField.Replace.transition oldHead newHead state read =
      some (written, direction, target) := by
    simpa [Edits.OptionalField.Replace.machine] using hinner
  simp [machine, transition, hinner', mapReplaceAction]
theorem locatePayload_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol Dispatch.HeadCursor.Full.Control}
    (hrun : Dispatch.HeadCursor.Full.machine.runConfigExact? steps source = some target) :
    (machine newHead write).runConfigExact? steps (locatePayloadConfig source) = some (locatePayloadConfig target) := by
  apply Update.LeftTail.runConfigExact_some_of_transition_some Control.locatePayload ?_ hrun
  intro state read written direction target hinner
  have hinner' : Dispatch.HeadCursor.Full.transition state read =
      some (written, direction, target) := by
    simpa [Dispatch.HeadCursor.Full.machine] using hinner
  simp [machine, transition, hinner', mapLocatePayloadAction]
theorem payload_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol RightEditControl} (hrun :
      (Edits.PositionedRight.machine .rightPayload
        (InsertBlock.optionalBuffer write)).runConfigExact? steps source = some target) :
    (machine newHead write).runConfigExact? steps (payloadConfig source) = some (payloadConfig target) := by
  apply Update.LeftTail.runConfigExact_some_of_transition_some Control.payload ?_ hrun
  intro state read written direction target hinner
  have hinner' : Edits.PositionedRight.transition .rightPayload
      (InsertBlock.optionalBuffer write) state read = some (written, direction, target) := by
    simpa [Edits.PositionedRight.machine] using hinner
  simp [machine, transition, hinner', mapPayloadAction]
theorem locateCount_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol Dispatch.HeadCursor.Full.Control}
    (hrun : Dispatch.HeadCursor.Full.machine.runConfigExact? steps source = some target) :
    (machine newHead write).runConfigExact? steps (locateCountConfig source) = some (locateCountConfig target) := by
  apply Update.LeftTail.runConfigExact_some_of_transition_some Control.locateCount ?_ hrun
  intro state read written direction target hinner
  have hinner' : Dispatch.HeadCursor.Full.transition state read =
      some (written, direction, target) := by
    simpa [Dispatch.HeadCursor.Full.machine] using hinner
  simp [machine, transition, hinner', mapLocateCountAction]
theorem count_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol RightEditControl} (hrun :
      (Edits.PositionedRight.machine .rightCountTicks
        (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).runConfigExact? steps source = some target) :
    (machine newHead write).runConfigExact? steps (countConfig source) = some (countConfig target) := by
  apply Update.LeftTail.runConfigExact_some_of_transition_some Control.count ?_ hrun
  intro state read written direction target hinner
  have hinner' : Edits.PositionedRight.transition .rightCountTicks
      (InsertBlock.singletonBuffer MachineCodeSymbol.tick) state read = some (written, direction, target) := by
    simpa [Edits.PositionedRight.machine] using hinner
  simp [machine, transition, hinner', mapCountAction]
theorem locate_replace_handoff (write oldHead : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine newHead write).runConfigExact? 2
        { state := Control.locate (.post (.positioned oldHead)), tape := T } = some (replaceConfig oldHead
          { state :=
              (Edits.OptionalField.Replace.machine oldHead newHead).start
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, replaceConfig,
    TuringMachine.PhaseEmbedding.liftConfig, roundTripTape, Tape.write_read_eq_self,
    Dispatch.HeadCursor.Full.transition, Dispatch.HeadCursor.Post.transition]
theorem replace_locatePayload_handoff (write oldHead : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine newHead write).runConfigExact? 2
        { state := Control.replace oldHead (.insert (.rewind .gate))
          tape := T } = some (locatePayloadConfig
          { state := Dispatch.HeadCursor.Full.machine.start
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, locatePayloadConfig,
    TuringMachine.PhaseEmbedding.liftConfig, roundTripTape, Tape.write_read_eq_self,
    Edits.OptionalField.Replace.transition, InsertRestagedMachine.transition, RewindWord.transition]
theorem locatePayload_payload_handoff (write head : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine newHead write).runConfigExact? 2
        { state := Control.locatePayload (.post (.positioned head))
          tape := T } = some (payloadConfig
          { state :=
              (Edits.PositionedRight.machine .rightPayload (InsertBlock.optionalBuffer write)).start
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, payloadConfig,
    TuringMachine.PhaseEmbedding.liftConfig, roundTripTape, Tape.write_read_eq_self,
    Dispatch.HeadCursor.Full.transition, Dispatch.HeadCursor.Post.transition]
theorem payload_locateCount_handoff (write : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine newHead write).runConfigExact? 2
        { state := Control.payload (.insert (.rewind .gate)), tape := T } = some (locateCountConfig
          { state := Dispatch.HeadCursor.Full.machine.start
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, locateCountConfig,
    TuringMachine.PhaseEmbedding.liftConfig, roundTripTape, Tape.write_read_eq_self,
    Edits.PositionedRight.transition, InsertRestagedMachine.transition, RewindWord.transition]
theorem locateCount_count_handoff (write head : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine newHead write).runConfigExact? 2
        { state := Control.locateCount (.post (.positioned head)), tape := T } = some (countConfig
          { state :=
              (Edits.PositionedRight.machine .rightCountTicks
                (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).start
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, countConfig,
    TuringMachine.PhaseEmbedding.liftConfig, roundTripTape, Tape.write_read_eq_self,
    Dispatch.HeadCursor.Full.transition, Dispatch.HeadCursor.Post.transition]
def rightCountFirst : Nat -> MachineCodeSymbol
  | 0 => MachineCodeSymbol.done
  | _ + 1 => MachineCodeSymbol.tick
def rightCountRest (count : Nat) (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  match count with
  | 0 => suffix
  | remaining + 1 =>
      MachineDescription.encodeNatAppend remaining suffix
theorem encodeNatAppend_eq_rightCountFirst_cons (count : Nat) (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend count suffix = rightCountFirst count :: rightCountRest count suffix := by
  cases count <;> rfl
theorem generic_sourceWord_eq_count_tail {stateCount : Nat} (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    Dispatch.HeadCursor.GenericPrefix.sourceWord L (rightCountFirst L.right.length ::
          rightCountRest L.right.length suffix) = List.append (headPrefix L) (List.append (optionalCellWord L.head)
          (MachineDescription.encodeNatAppend L.right.length suffix)) := by
  unfold Dispatch.HeadCursor.GenericPrefix.sourceWord
  rw [encodeNatAppend_eq_rightCountFirst_cons]
theorem full_positioned_tape_eq_positioned_source {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    (Dispatch.HeadCursor.Full.positionedConfig L (rightCountFirst L.right.length)
      (rightCountRest L.right.length suffix)).tape = (Edits.PositionedRightLocator.sourceConfig
        (headPrefix L).reverse L.head L.right.length suffix).tape := by
  unfold Dispatch.HeadCursor.Full.positionedConfig Dispatch.HeadCursor.Full.postConfig
    Dispatch.HeadCursor.Post.positionedConfig Dispatch.HeadCursor.Post.cursorConfig
    TuringMachine.PhaseEmbedding.liftConfig Edits.PositionedRightLocator.sourceConfig
    Edits.PositionedRightLocator.config
  rw [encodeNatAppend_eq_rightCountFirst_cons]
def throughReplaceSteps {stateCount : Nat} (L : Layout stateCount)
    (newHead : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Nat :=
  (Dispatch.HeadCursor.Full.runSteps L + 2) +
    Edits.OptionalField.LayoutSpecialization.runSteps L newHead callerData
def throughPayloadSteps {stateCount : Nat} (L : Layout stateCount)
    (newHead write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Nat :=
  let replaced := HeadReplacement.replaceHead L newHead
  ((((throughReplaceSteps L newHead callerData + 2) + Dispatch.HeadCursor.Full.runSteps replaced) + 2) +
    Edits.PositionedRight.payloadSteps replaced write callerData)
def runSteps {stateCount : Nat} (L : Layout stateCount)
    (newHead write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Nat :=
  let replaced := HeadReplacement.replaceHead L newHead
  ((((throughPayloadSteps L newHead write callerData + 2) + Dispatch.HeadCursor.Full.runSteps replaced) + 2) +
    Edits.PositionedRight.countIncrementSteps replaced write callerData)
/- One actual finite machine performs the complete empty-left motion tail
from any trailing-blank representative of the canonical protected frame. -/
theorem run_from_equiv {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input (Frame.protectedWord L callerData)) T) :
    exists endpoint, (machine newHead write).runConfigExact? (runSteps L newHead write callerData)
          { state := (machine newHead write).start, tape := T } = some endpoint ∧
      endpoint.state = (machine newHead write).halt ∧ Tape.Equiv (Tape.input (Frame.protectedWord
            (RightPrepend.prependedRightLayout (HeadReplacement.replaceHead L newHead) write) callerData)) endpoint.tape := by
  let initialSuffix := RightPrepend.rightPayloadSuffix L callerData
  have hlocatorSource : Tape.Equiv (Tape.input (Dispatch.HeadCursor.GenericPrefix.sourceWord L
          (rightCountFirst L.right.length :: rightCountRest L.right.length initialSuffix))) T := by
    rw [generic_sourceWord_eq_count_tail]
    rw [← Update.LeftTail.protectedWord_eq_head_rightCount_tail]
    exact hsource
  rcases Dispatch.HeadCursor.Full.run_from_equiv L (rightCountFirst L.right.length)
      (rightCountRest L.right.length initialSuffix) T hlocatorSource with
    ⟨locatorEndpoint, hlocate, hlocateState, hlocateTape⟩
  have hlocateOuter := locate_run_of_some newHead write hlocate
  cases locatorEndpoint with
  | mk locatorState locatorTape =>
      change locatorState = Dispatch.HeadCursor.Full.Control.post (.positioned L.head) at hlocateState
      subst locatorState
      have hlocateOuter' : (machine newHead write).runConfigExact? (Dispatch.HeadCursor.Full.runSteps L)
              { state := (machine newHead write).start, tape := T } = some
              { state := Control.locate (.post (.positioned L.head))
                tape := locatorTape } := by
        simpa [machine, locateConfig, TuringMachine.PhaseEmbedding.liftConfig] using hlocateOuter
      have hlocateHandoff :=
        locate_replace_handoff newHead write L.head locatorTape
      have hpositionedEq : (Dispatch.HeadCursor.Full.positionedConfig L (rightCountFirst L.right.length)
            (rightCountRest L.right.length initialSuffix)).tape =
            (Edits.OptionalField.LayoutSpecialization.sourceConfig L callerData).tape := by
        rw [full_positioned_tape_eq_positioned_source]
        simpa [initialSuffix] using (Update.LeftTail.replacement_cursor_eq_payload_source
            L callerData).symm
      have hreplaceSource : Tape.Equiv (Edits.OptionalField.LayoutSpecialization.sourceConfig L callerData).tape
          (roundTripTape locatorTape) := by
        rw [← hpositionedEq]
        exact Tape.Equiv.trans hlocateTape (Tape.Equiv.symm (roundTripTape_equiv locatorTape))
      rcases Update.LeftTail.replace_run_exact_of_tape_equiv
          L newHead callerData (roundTripTape locatorTape) hreplaceSource with
        ⟨replaceEndpoint, hreplace, hreplaceState, hreplaceTape⟩
      have hreplaceOuter := replace_run_of_some newHead write L.head hreplace
      cases replaceEndpoint with
      | mk replaceState replaceTape =>
          change replaceState = Edits.OptionalField.Replace.Control.insert (.rewind .gate) at hreplaceState
          subst replaceState
          have hreplaceHandoff :=
            replace_locatePayload_handoff newHead write L.head replaceTape
          let replaced := HeadReplacement.replaceHead L newHead
          let payloadSuffix :=
            RightPrepend.rightPayloadSuffix replaced callerData
          have hpayloadLocatorSource : Tape.Equiv (Tape.input
                (Dispatch.HeadCursor.GenericPrefix.sourceWord replaced (rightCountFirst replaced.right.length ::
                    rightCountRest replaced.right.length payloadSuffix))) (roundTripTape replaceTape) := by
            rw [generic_sourceWord_eq_count_tail]
            rw [← Update.LeftTail.protectedWord_eq_head_rightCount_tail]
            have hchain := Tape.Equiv.trans hreplaceTape (Tape.Equiv.symm (roundTripTape_equiv replaceTape))
            simpa [replaced, HeadReplacement.replaceHead] using hchain
          rcases Dispatch.HeadCursor.Full.run_from_equiv replaced (rightCountFirst replaced.right.length)
              (rightCountRest replaced.right.length payloadSuffix)
              (roundTripTape replaceTape) hpayloadLocatorSource with
            ⟨payloadLocatorEndpoint, hpayloadLocate, hpayloadLocateState, hpayloadLocateTape⟩
          have hpayloadLocateOuter :=
            locatePayload_run_of_some newHead write hpayloadLocate
          cases payloadLocatorEndpoint with
          | mk payloadLocatorState payloadLocatorTape =>
              change payloadLocatorState = Dispatch.HeadCursor.Full.Control.post
                  (.positioned replaced.head) at hpayloadLocateState
              subst payloadLocatorState
              have hpayloadLocateHandoff :=
                locatePayload_payload_handoff newHead write replaced.head payloadLocatorTape
              have hpayloadSource : Tape.Equiv (Edits.PositionedRightLocator.sourceConfig
                    (headPrefix replaced).reverse replaced.head replaced.right.length payloadSuffix).tape
                  (roundTripTape payloadLocatorTape) := by
                rw [← full_positioned_tape_eq_positioned_source]
                exact Tape.Equiv.trans hpayloadLocateTape (Tape.Equiv.symm (roundTripTape_equiv payloadLocatorTape))
              rcases Edits.PositionedRight.payload_insert_exact_of_tape_equiv replaced write callerData
                    (roundTripTape payloadLocatorTape) (by simpa [payloadSuffix] using hpayloadSource) with
                ⟨payloadEndpoint, hpayload, hpayloadState, hpayloadTape⟩
              have hpayloadOuter := payload_run_of_some newHead write hpayload
              cases payloadEndpoint with
              | mk payloadState payloadTape =>
                  change payloadState = Edits.PositionedRight.Control.insert (.rewind .gate) at hpayloadState
                  subst payloadState
                  have hpayloadHandoff :=
                    payload_locateCount_handoff newHead write payloadTape
                  let countSuffix : Word MachineCodeSymbol :=
                    List.append (optionalCellWord write) (RightPrepend.rightPayloadSuffix replaced callerData)
                  have hcountLocatorSource : Tape.Equiv (Tape.input (Dispatch.HeadCursor.GenericPrefix.sourceWord
                          replaced (rightCountFirst replaced.right.length ::
                            rightCountRest replaced.right.length countSuffix))) (roundTripTape payloadTape) := by
                    have hword : Dispatch.HeadCursor.GenericPrefix.sourceWord replaced
                            (rightCountFirst replaced.right.length :: rightCountRest replaced.right.length
                                countSuffix) = RightPrepend.afterWriteWord replaced write callerData := by
                      rw [generic_sourceWord_eq_count_tail]
                      simpa [countSuffix] using (Update.LeftTail.afterWriteWord_eq_head_rightCount_tail
                          replaced write callerData).symm
                    rw [hword]
                    exact Tape.Equiv.trans hpayloadTape (Tape.Equiv.symm (roundTripTape_equiv payloadTape))
                  rcases Dispatch.HeadCursor.Full.run_from_equiv replaced (rightCountFirst replaced.right.length)
                      (rightCountRest replaced.right.length countSuffix)
                      (roundTripTape payloadTape) hcountLocatorSource with
                    ⟨countLocatorEndpoint, hcountLocate, hcountLocateState, hcountLocateTape⟩
                  have hcountLocateOuter :=
                    locateCount_run_of_some newHead write hcountLocate
                  cases countLocatorEndpoint with
                  | mk countLocatorState countLocatorTape =>
                      change countLocatorState = Dispatch.HeadCursor.Full.Control.post
                          (.positioned replaced.head) at hcountLocateState
                      subst countLocatorState
                      have hcountLocateHandoff :=
                        locateCount_count_handoff newHead write replaced.head countLocatorTape
                      have hcountSource : Tape.Equiv (Edits.PositionedRightLocator.sourceConfig
                            (headPrefix replaced).reverse replaced.head replaced.right.length countSuffix).tape
                          (roundTripTape countLocatorTape) := by
                        rw [← full_positioned_tape_eq_positioned_source]
                        exact Tape.Equiv.trans hcountLocateTape (Tape.Equiv.symm (roundTripTape_equiv countLocatorTape))
                      rcases Edits.PositionedRight.count_increment_exact_of_tape_equiv replaced write callerData
                            (roundTripTape countLocatorTape) (by simpa [countSuffix] using hcountSource) with
                        ⟨countEndpoint, hcount, hcountState, hcountTape⟩
                      have hcountOuter := count_run_of_some newHead write hcount
                      have hrun1 := TuringMachine.runConfigExact?_trans hlocateOuter' hlocateHandoff
                      have hrun2 := TuringMachine.runConfigExact?_trans hrun1 hreplaceOuter
                      have hrun3 := TuringMachine.runConfigExact?_trans hrun2 hreplaceHandoff
                      have hrun4 := TuringMachine.runConfigExact?_trans hrun3 hpayloadLocateOuter
                      have hrun5 := TuringMachine.runConfigExact?_trans hrun4 hpayloadLocateHandoff
                      have hrun6 := TuringMachine.runConfigExact?_trans hrun5 hpayloadOuter
                      have hrun7 := TuringMachine.runConfigExact?_trans hrun6 hpayloadHandoff
                      have hrun8 := TuringMachine.runConfigExact?_trans hrun7 hcountLocateOuter
                      have hrun9 := TuringMachine.runConfigExact?_trans hrun8 hcountLocateHandoff
                      have hrun10 := TuringMachine.runConfigExact?_trans hrun9 hcountOuter
                      refine ⟨countConfig countEndpoint, ?_, ?_, ?_⟩
                      · simpa [runSteps, throughPayloadSteps, throughReplaceSteps, replaced,
                          Nat.add_assoc] using hrun10
                      · simpa [machine, countConfig, TuringMachine.PhaseEmbedding.liftConfig] using hcountState
                      · simpa [replaced, MoveLeftEmpty.reshapedLayout, countConfig,
                          TuringMachine.PhaseEmbedding.liftConfig] using hcountTape
end General
open SerializedFieldComposer
abbrev Control := General.Control

namespace Control
abbrev finite := General.Control.finite
end Control
def transition (write : Option MachineCodeSymbol) :=
  General.transition none write
def machine (write : Option MachineCodeSymbol) : TuringMachine MachineCodeSymbol Control where
  start := (General.machine none write).start
  halt := (General.machine none write).halt
  transition := transition write
  statesFinite := Control.finite
theorem run_from_equiv {stateCount : Nat} (L : Layout stateCount)
    (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol)
    (_hleft : L.left = []) (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input (Frame.protectedWord L callerData)) T) :
    exists steps endpoint, (machine write).runConfigExact? steps
          { state := (machine write).start, tape := T } = some endpoint ∧
      endpoint.state = (machine write).halt ∧ Tape.Equiv (Tape.input (Frame.protectedWord
            (MoveLeftEmpty.reshapedLayout L write) callerData)) endpoint.tape := by
  rcases General.run_from_equiv none L write callerData T hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨General.runSteps L none write callerData, endpoint, hrun, hstate,
    by simpa [MoveLeftEmpty.reshapedLayout, MoveLeftEmpty.blankedHeadLayout] using htape⟩
end LeftEmpty
end Update
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
