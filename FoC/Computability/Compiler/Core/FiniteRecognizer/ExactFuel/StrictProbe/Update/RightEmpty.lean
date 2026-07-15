import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightRemoval
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.HeadCursorRuns
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.OptionalField
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.PositionedLeft
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Empty-right update

A finite exact-fuel composition for a right move when the serialized right-cell
list is empty.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightEmpty

open Languages SerializedFieldComposer

local notation "liftRun" =>
  RightRemoval.lift_run_of_transition
private abbrev ReplaceControl := Edits.OptionalField.Replace.Control
private abbrev LeftEditControl := Edits.PositionedLeft.Control
inductive Control where
  | locate (inner : Dispatch.HeadCursor.Full.Control)
  | locateReturn (oldHead : Option MachineCodeSymbol)
  | replace (oldHead : Option MachineCodeSymbol) (inner : ReplaceControl)
  | replaceReturn
  | payload (inner : LeftEditControl)
  | payloadReturn
  | count (inner : LeftEditControl)
  | finishReturn
  | done
deriving DecidableEq
namespace Control
def optionalFinite : Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite
def replaceFinite : Foundation.FiniteType (Option MachineCodeSymbol × ReplaceControl) :=
  Foundation.FiniteType.prod optionalFinite
    Edits.OptionalField.Replace.Control.finite
def elems : List Control := List.append
  (Dispatch.HeadCursor.Full.Control.finite.elems.map Control.locate)
  (List.append (optionalFinite.elems.map Control.locateReturn) (List.append
      (replaceFinite.elems.map fun p => Control.replace p.1 p.2)
      (List.append [Control.replaceReturn]
        (List.append
          (Edits.PositionedLeft.Control.finite.elems.map Control.payload)
          (List.append [Control.payloadReturn]
            (List.append
              (Edits.PositionedLeft.Control.finite.elems.map Control.count)
              [Control.finishReturn, Control.done]))))))
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro c
    cases c with
    | locate inner =>
        have h := Dispatch.HeadCursor.Full.Control.finite.complete inner
        simp [elems, h]
    | locateReturn oldHead =>
        have h := optionalFinite.complete oldHead
        simp [elems, h]
    | replace oldHead inner =>
        have h := replaceFinite.complete (oldHead, inner)
        simpa [elems] using h
    | payload inner | count inner =>
        have h := Edits.PositionedLeft.Control.finite.complete inner
        simp [elems, h]
    | replaceReturn | payloadReturn | finishReturn | done => simp [elems]
end Control
def transition (write : Option MachineCodeSymbol) : Control ->
    Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .locate (.post (.positioned oldHead)), read =>
      some (read, .right, .locateReturn oldHead)
  | .locate inner, read =>
      match Dispatch.HeadCursor.Full.transition inner read with
      | none => none
      | some (written, direction, target) =>
          some (written, direction, .locate target)
  | .locateReturn oldHead, read =>
      some (read, .left, .replace oldHead
        (Edits.OptionalField.Replace.machine oldHead none).start)
  | .replace oldHead inner, read =>
      if inner = (Edits.OptionalField.Replace.machine oldHead none).halt
      then some (read, .right, .replaceReturn)
      else match Edits.OptionalField.Replace.transition
          oldHead none inner read with
        | none => none
        | some (written, direction, target) =>
            some (written, direction, .replace oldHead target)
  | .replaceReturn, read =>
      some (read, .left, .payload
        (Edits.PositionedLeft.machine .leftPayload
          (InsertBlock.optionalBuffer write)).start)
  | .payload inner, read =>
      if inner = (Edits.PositionedLeft.machine .leftPayload
        (InsertBlock.optionalBuffer write)).halt
      then some (read, .right, .payloadReturn)
      else match Edits.PositionedLeft.transition .leftPayload
          (InsertBlock.optionalBuffer write) inner read with
        | none => none
        | some (written, direction, target) =>
            some (written, direction, .payload target)
  | .payloadReturn, read =>
      some (read, .left, .count
        (Edits.PositionedLeft.machine .leftCountDone
          (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).start)
  | .count inner, read =>
      if inner = (Edits.PositionedLeft.machine .leftCountDone
        (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).halt
      then some (read, .right, .finishReturn)
      else match Edits.PositionedLeft.transition .leftCountDone
          (InsertBlock.singletonBuffer MachineCodeSymbol.tick) inner read with
        | none => none
        | some (written, direction, target) =>
            some (written, direction, .count target)
  | .finishReturn, read => some (read, .left, .done)
  | .done, _ => none
def machine (write : Option MachineCodeSymbol) :
    TuringMachine MachineCodeSymbol Control where
  start := .locate Dispatch.HeadCursor.Full.machine.start
  halt := .done
  transition := transition write
  statesFinite := Control.finite
private def locateConfig (c : TuringMachine.Configuration MachineCodeSymbol
    Dispatch.HeadCursor.Full.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.locate c
private def replaceConfig (oldHead : Option MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol ReplaceControl) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.replace oldHead) c
private def payloadConfig (c : TuringMachine.Configuration MachineCodeSymbol
    LeftEditControl) : TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.payload c
private def countConfig (c : TuringMachine.Configuration MachineCodeSymbol
    LeftEditControl) : TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.count c
private def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move .left (Tape.move .right T)
private theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T := Machine.moveLeft_moveRight_equiv_self T
private theorem write_read_eq_self (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by cases T; rfl
private theorem locate_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.HeadCursor.Full.Control} (hrun : Dispatch.HeadCursor.Full.machine.runConfigExact?
      steps source = some target) : (machine write).runConfigExact? steps (locateConfig source) =
      some (locateConfig target) := by
  apply liftRun Dispatch.HeadCursor.Full.machine (machine write)
    Control.locate ?_ hrun
  intro state read written direction target htransition
  change Dispatch.HeadCursor.Full.transition state read =
    some (written, direction, target) at htransition
  cases state with
  | locate inner => simp [machine, transition, htransition]
  | post inner =>
      cases inner with
      | positioned head =>
          simp [Dispatch.HeadCursor.Full.transition,
            Dispatch.HeadCursor.Post.transition] at htransition
      | _ => simp [machine, transition, htransition]
private theorem replace_run_of_some (write oldHead : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration
      MachineCodeSymbol ReplaceControl} (hrun : (Edits.OptionalField.Replace.machine oldHead none).runConfigExact?
      steps source = some target) : (machine write).runConfigExact? steps (replaceConfig oldHead source) =
      some (replaceConfig oldHead target) := by
  apply liftRun (Edits.OptionalField.Replace.machine oldHead none) (machine write) (Control.replace oldHead) ?_ hrun
  intro state read written direction target htransition
  change Edits.OptionalField.Replace.transition oldHead none state read =
    some (written, direction, target) at htransition
  have hnot : state ≠
      (Edits.OptionalField.Replace.machine oldHead none).halt := by
    intro h
    subst state
    simp [Edits.OptionalField.Replace.machine,
      Edits.OptionalField.Replace.transition,
      InsertRestagedMachine.transition, RewindWord.transition] at htransition
  simp [machine, transition, hnot, htransition]
private theorem payload_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration
      MachineCodeSymbol LeftEditControl} (hrun : (Edits.PositionedLeft.machine .leftPayload
      (InsertBlock.optionalBuffer write)).runConfigExact?
        steps source = some target) : (machine write).runConfigExact? steps (payloadConfig source) =
      some (payloadConfig target) := by
  apply liftRun (Edits.PositionedLeft.machine .leftPayload (InsertBlock.optionalBuffer write)) (machine write) Control.payload ?_ hrun
  intro state read written direction target htransition
  change Edits.PositionedLeft.transition .leftPayload
      (InsertBlock.optionalBuffer write) state read =
    some (written, direction, target) at htransition
  have hnot : state ≠ (Edits.PositionedLeft.machine .leftPayload
      (InsertBlock.optionalBuffer write)).halt := by
    intro h
    subst state
    simp [Edits.PositionedLeft.machine,
      Edits.PositionedLeft.transition,
      InsertRestagedMachine.transition, RewindWord.transition] at htransition
  simp [machine, transition, hnot, htransition]
private theorem count_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration
      MachineCodeSymbol LeftEditControl} (hrun : (Edits.PositionedLeft.machine .leftCountDone
      (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).runConfigExact?
        steps source = some target) : (machine write).runConfigExact? steps (countConfig source) =
      some (countConfig target) := by
  apply liftRun (Edits.PositionedLeft.machine .leftCountDone (InsertBlock.singletonBuffer MachineCodeSymbol.tick)) (machine write)
    Control.count ?_ hrun
  intro state read written direction target htransition
  change Edits.PositionedLeft.transition .leftCountDone
      (InsertBlock.singletonBuffer MachineCodeSymbol.tick) state read =
    some (written, direction, target) at htransition
  have hnot : state ≠ (Edits.PositionedLeft.machine .leftCountDone
      (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).halt := by
    intro h
    subst state
    simp [Edits.PositionedLeft.machine,
      Edits.PositionedLeft.transition,
      InsertRestagedMachine.transition, RewindWord.transition] at htransition
  simp [machine, transition, hnot, htransition]
private theorem locate_handoff_run_exact (write oldHead : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) : (machine write).runConfigExact? 2
      { state := Control.locate (.post (.positioned oldHead)), tape := T } =
      some (replaceConfig oldHead
        { state := (Edits.OptionalField.Replace.machine oldHead none).start
          tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine,
    transition, replaceConfig, TuringMachine.PhaseEmbedding.liftConfig,
    roundTripTape, write_read_eq_self]
private theorem replace_handoff_run_exact (write oldHead : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) : (machine write).runConfigExact? 2
      { state := Control.replace oldHead
          (Edits.OptionalField.Replace.machine oldHead none).halt, tape := T } =
      some (payloadConfig
        { state := (Edits.PositionedLeft.machine .leftPayload
            (InsertBlock.optionalBuffer write)).start
          tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine,
    transition, payloadConfig, TuringMachine.PhaseEmbedding.liftConfig,
    roundTripTape, write_read_eq_self]
private theorem payload_handoff_run_exact (write : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) : (machine write).runConfigExact? 2
      { state := Control.payload (Edits.PositionedLeft.machine .leftPayload
          (InsertBlock.optionalBuffer write)).halt, tape := T } =
      some (countConfig
        { state := (Edits.PositionedLeft.machine .leftCountDone
            (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).start
          tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine,
    transition, countConfig, TuringMachine.PhaseEmbedding.liftConfig,
    roundTripTape, write_read_eq_self]
private theorem finish_handoff_run_exact (write : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) : (machine write).runConfigExact? 2
      { state := Control.count (Edits.PositionedLeft.machine .leftCountDone
          (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).halt, tape := T } =
      some { state := Control.done, tape := roundTripTape T } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, roundTripTape, write_read_eq_self]
private theorem runConfigExact_trans (write : Option MachineCodeSymbol)
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol Control} (hab : (machine write).runConfigExact? first a = some b) (hbc : (machine write).runConfigExact? second b = some c) : (machine write).runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab) (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)
private theorem emptyRight_sourceWord_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) (hright : L.right = []) :
    Dispatch.HeadCursor.GenericPrefix.sourceWord L
      (MachineCodeSymbol.done :: Frame.callerTag :: callerData) =
      Frame.protectedWord L callerData := by
  rw [HeadReplacement.protectedWord_head_decomp]
  unfold Dispatch.HeadCursor.GenericPrefix.sourceWord
    HeadLocator.afterHeadWord optionalCellsWord
  rw [hright]
  simp [encodeOptionalCodeSymbolsAppend, MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat, encodeOptionalCodeSymbolsPayloadAppend]
private theorem emptyRight_positioned_tape_eq_replace_source {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) (hright : L.right = []) : (Dispatch.HeadCursor.Full.positionedConfig L MachineCodeSymbol.done
      (Frame.callerTag :: callerData)).tape = (Edits.OptionalField.LayoutSpecialization.sourceConfig
      L callerData).tape := by
  unfold Dispatch.HeadCursor.Full.positionedConfig
    Dispatch.HeadCursor.Full.postConfig
    Dispatch.HeadCursor.Post.positionedConfig
    Dispatch.HeadCursor.Post.cursorConfig
    Edits.OptionalField.LayoutSpecialization.sourceConfig
    headSuffix optionalCellsWord
  rw [hright]
  simp [TuringMachine.PhaseEmbedding.liftConfig,
    encodeOptionalCodeSymbolsAppend, MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat, encodeOptionalCodeSymbolsPayloadAppend]
private theorem replace_run_exact_of_tape_equiv {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) (T : Tape MachineCodeSymbol) (hsource : Tape.Equiv
      (Edits.OptionalField.LayoutSpecialization.sourceConfig
        L callerData).tape T) :
    ∃ endpoint,
      (Edits.OptionalField.Replace.machine L.head none).runConfigExact?
        (Edits.OptionalField.LayoutSpecialization.runSteps L none callerData)
        { state := Edits.OptionalField.Replace.Control.markLeft
          tape := T } = some endpoint ∧
      endpoint.state = Edits.OptionalField.Replace.Control.insert
        (.rewind .gate) ∧
      Tape.Equiv (Tape.input (Frame.protectedWord
        (HeadReplacement.replaceHead L none) callerData)) endpoint.tape := by
  rcases Edits.OptionalField.LayoutSpecialization.run_exact
      L none callerData with ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hclean hsource with ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, hstate ▸ hcleanState,
    Tape.Equiv.trans hcleanTape htape⟩
  simpa [Edits.OptionalField.LayoutSpecialization.sourceConfig] using hrun
theorem run_from_equiv {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) (hright : L.right = []) (T : Tape MachineCodeSymbol) (hsource : Tape.Equiv (Tape.input (Frame.protectedWord L callerData)) T) :
    ∃ steps endpoint,
      (machine write).runConfigExact? steps
        { state := (machine write).start, tape := T } = some endpoint ∧
      endpoint.state = Control.done ∧
      Tape.Equiv (Tape.input (Frame.protectedWord
        (MoveRightEmpty.reshapedLayout L write) callerData)) endpoint.tape := by
  have hfullSource : Tape.Equiv (Tape.input
      (Dispatch.HeadCursor.GenericPrefix.sourceWord L
        (MachineCodeSymbol.done :: Frame.callerTag :: callerData))) T := by
    rw [emptyRight_sourceWord_eq_protectedWord L callerData hright]
    exact hsource
  rcases Dispatch.HeadCursor.Full.run_from_equiv L MachineCodeSymbol.done
      (Frame.callerTag :: callerData) T hfullSource with
    ⟨locatorEndpoint, hlocate, hlocateState, hlocateTape⟩
  have hlocateOuter := locate_run_of_some write hlocate
  cases locatorEndpoint with
  | mk locatorState locatorTape =>
    change locatorState = Dispatch.HeadCursor.Full.Control.post
      (.positioned L.head) at hlocateState
    subst locatorState
    have hlocateOuter' : (machine write).runConfigExact?
        (Dispatch.HeadCursor.Full.runSteps L)
        { state := (machine write).start, tape := T } =
        some
          { state := Control.locate (.post (.positioned L.head))
            tape := locatorTape } := by
      simpa [machine, locateConfig,
        TuringMachine.PhaseEmbedding.liftConfig] using hlocateOuter
    have hlocateHandoff := locate_handoff_run_exact write L.head locatorTape
    have hreplaceSource : Tape.Equiv
        (Edits.OptionalField.LayoutSpecialization.sourceConfig
          L callerData).tape (roundTripTape locatorTape) := by
      rw [← emptyRight_positioned_tape_eq_replace_source L callerData hright]
      exact Tape.Equiv.trans hlocateTape
        (Tape.Equiv.symm (roundTripTape_equiv locatorTape))
    rcases replace_run_exact_of_tape_equiv L callerData
        (roundTripTape locatorTape) hreplaceSource with
      ⟨replaceEndpoint, hreplace, hreplaceState, hreplaceTape⟩
    have hreplaceOuter := replace_run_of_some write L.head hreplace
    cases replaceEndpoint with
    | mk replaceState replaceTape =>
      change replaceState = Edits.OptionalField.Replace.Control.insert
        (.rewind .gate) at hreplaceState
      subst replaceState
      have hreplaceHandoff := replace_handoff_run_exact write L.head replaceTape
      have hpayloadSource : Tape.Equiv (Tape.input (Frame.protectedWord
          (MoveRightEmpty.blankedHeadLayout L) callerData))
          (roundTripTape replaceTape) := by
        have hchain := Tape.Equiv.trans hreplaceTape
          (Tape.Equiv.symm (roundTripTape_equiv replaceTape))
        simpa [MoveRightEmpty.blankedHeadLayout,
          HeadReplacement.replaceHead] using hchain
      rcases Edits.PositionedLeft.payload_insert_exact_of_tape_equiv
          (MoveRightEmpty.blankedHeadLayout L) write callerData
          (roundTripTape replaceTape) hpayloadSource with
        ⟨payloadEndpoint, hpayload, hpayloadState, hpayloadTape⟩
      have hpayloadOuter := payload_run_of_some write hpayload
      cases payloadEndpoint with
      | mk payloadState payloadTape =>
        change payloadState = Edits.PositionedLeft.Control.insert
          (.rewind .gate) at hpayloadState
        subst payloadState
        have hpayloadHandoff := payload_handoff_run_exact write payloadTape
        have hcountSource : Tape.Equiv (Tape.input (LeftPrepend.afterWriteWord
            (MoveRightEmpty.blankedHeadLayout L) write callerData))
            (roundTripTape payloadTape) :=
          Tape.Equiv.trans hpayloadTape
            (Tape.Equiv.symm (roundTripTape_equiv payloadTape))
        rcases Edits.PositionedLeft.count_increment_exact_of_tape_equiv
            (MoveRightEmpty.blankedHeadLayout L) write callerData
            (roundTripTape payloadTape) hcountSource with
          ⟨countEndpoint, hcount, hcountState, hcountTape⟩
        have hcountOuter := count_run_of_some write hcount
        cases countEndpoint with
        | mk countState countTape =>
          change countState = Edits.PositionedLeft.Control.insert
            (.rewind .gate) at hcountState
          subst countState
          have hfinish := finish_handoff_run_exact write countTape
          have hrun := runConfigExact_trans write
            (runConfigExact_trans write
              (runConfigExact_trans write
                (runConfigExact_trans write
                  (runConfigExact_trans write
                    (runConfigExact_trans write
                      (runConfigExact_trans write hlocateOuter' hlocateHandoff)
                      hreplaceOuter) hreplaceHandoff) hpayloadOuter)
                  hpayloadHandoff) hcountOuter) hfinish
          have htarget : Tape.Equiv (Tape.input (Frame.protectedWord
              (MoveRightEmpty.reshapedLayout L write) callerData))
              (roundTripTape countTape) := by
            have hchain := Tape.Equiv.trans hcountTape
              (Tape.Equiv.symm (roundTripTape_equiv countTape))
            simpa [MoveRightEmpty.reshapedLayout,
              MoveRightEmpty.blankedHeadLayout] using hchain
          exact ⟨_, _, hrun, rfl, htarget⟩

end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightEmpty
