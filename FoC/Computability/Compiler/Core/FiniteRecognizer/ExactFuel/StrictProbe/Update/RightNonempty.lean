import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightRemoval
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.HeadCursorRuns
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.RightFieldLocator
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.RightFirstCell
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.MarkedPrefixRestorer
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.OptionalField
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.PositionedLeft
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Nonempty-right update

A finite exact-fuel composition that removes the first right cell, installs it
as the new head, and prepends the written cell to the left side.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightNonempty

open Languages SerializedFieldComposer

local notation "liftRun" =>
  RightRemoval.lift_run_of_transition
namespace HeadReplaceMachine
inductive Control where
  | locate (inner : Dispatch.HeadCursor.Full.Control)
  | replace (inner : Edits.OptionalField.Replace.Control)
deriving DecidableEq
namespace Control
def elems : List Control :=
  List.append (Dispatch.HeadCursor.Full.Control.elems.map Control.locate) (Edits.OptionalField.Replace.Control.elems.map Control.replace)
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro c
    cases c with
    | locate inner =>
        have h := Dispatch.HeadCursor.Full.Control.finite.complete inner
        change inner ∈ Dispatch.HeadCursor.Full.Control.elems at h
        simp [elems, h]
    | replace inner =>
        have h := Edits.OptionalField.Replace.Control.finite.complete inner
        change inner ∈ Edits.OptionalField.Replace.Control.elems at h
        simp [elems, h]
end Control
def locateEmbed : Dispatch.HeadCursor.Full.Control -> Control
  | .post (.positioned _) => .replace .markLeft
  | inner => .locate inner
def replaceEmbed : Edits.OptionalField.Replace.Control -> Control :=
  Control.replace
def transition (old new : Option MachineCodeSymbol) : Control ->
    Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .locate inner, read =>
      match Dispatch.HeadCursor.Full.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, locateEmbed target)
  | .replace inner, read =>
      match Edits.OptionalField.Replace.transition old new inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, replaceEmbed target)
def machine (old new : Option MachineCodeSymbol) :
    TuringMachine MachineCodeSymbol Control where
  start := locateEmbed Dispatch.HeadCursor.Full.machine.start
  halt := .replace (.insert (.rewind .gate))
  transition := transition old new
  statesFinite := Control.finite
private def locateConfig (c : TuringMachine.Configuration MachineCodeSymbol
    Dispatch.HeadCursor.Full.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig locateEmbed c
private def replaceConfig (c : TuringMachine.Configuration MachineCodeSymbol
    Edits.OptionalField.Replace.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig replaceEmbed c
private theorem locate_run_of_some (old new : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.HeadCursor.Full.Control} (hrun : Dispatch.HeadCursor.Full.machine.runConfigExact?
      steps source = some target) : (machine old new).runConfigExact? steps (locateConfig source) =
      some (locateConfig target) := by
  apply liftRun Dispatch.HeadCursor.Full.machine (machine old new) locateEmbed ?_ hrun
  intro state read write direction target htransition
  change Dispatch.HeadCursor.Full.transition state read =
    some (write, direction, target) at htransition
  cases state with
  | locate inner =>
      simp [machine, transition, locateEmbed, htransition]
  | post inner =>
      cases inner with
      | positioned head =>
          simp [Dispatch.HeadCursor.Full.transition,
            Dispatch.HeadCursor.Post.transition] at htransition
      | _ => simp [machine, transition, locateEmbed, htransition]
private theorem replace_run_of_some (old new : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      Edits.OptionalField.Replace.Control} (hrun : (Edits.OptionalField.Replace.machine old new).runConfigExact?
      steps source = some target) : (machine old new).runConfigExact? steps (replaceConfig source) =
      some (replaceConfig target) := by
  apply liftRun (Edits.OptionalField.Replace.machine old new) (machine old new)
    replaceEmbed ?_ hrun
  intro state read write direction target htransition
  change Edits.OptionalField.Replace.transition old new state read =
    some (write, direction, target) at htransition
  simp [machine, transition, replaceEmbed, htransition]
private def runSteps {stateCount : Nat} (L : Layout stateCount) (newHead : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Nat :=
  Dispatch.HeadCursor.Full.runSteps L +
    Edits.OptionalField.LayoutSpecialization.runSteps L newHead callerData
private theorem replace_run_exact_of_tape_equiv {stateCount : Nat}
    (L : Layout stateCount) (newHead : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Edits.OptionalField.LayoutSpecialization.sourceConfig
        L callerData).tape T) :
    exists endpoint,
      (Edits.OptionalField.Replace.machine L.head newHead).runConfigExact?
          (Edits.OptionalField.LayoutSpecialization.runSteps
            L newHead callerData)
          { state := Edits.OptionalField.Replace.Control.markLeft
            tape := T } = some endpoint ∧
      endpoint.state =
        Edits.OptionalField.Replace.Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (HeadReplacement.replaceHead L newHead) callerData))
        endpoint.tape := by
  rcases Edits.OptionalField.LayoutSpecialization.run_exact
      L newHead callerData with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, ?_, Tape.Equiv.trans hcleanTape htape⟩
  · simpa [Edits.OptionalField.LayoutSpecialization.sourceConfig]
      using hrun
  · exact hstate ▸ hcleanState

private theorem run_exact_of_equiv {stateCount : Nat} (L : Layout stateCount) (newHead : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) (hsuffix : HeadLocator.afterHeadWord L callerData = first :: rest) (T : Tape MachineCodeSymbol) (hinput : Tape.Equiv (Tape.input (Frame.protectedWord L callerData)) T) :
    ∃ endpoint,
      (machine L.head newHead).runConfigExact? (runSteps L newHead callerData)
        { state := (machine L.head newHead).start, tape := T } = some endpoint ∧
      endpoint.state = Control.replace (.insert (.rewind .gate)) ∧
      Tape.Equiv (Tape.input (Frame.protectedWord
        (HeadReplacement.replaceHead L newHead) callerData)) endpoint.tape := by
  have hsourceWord : Dispatch.HeadCursor.GenericPrefix.sourceWord
      L (first :: rest) = Frame.protectedWord L callerData := by
    rw [← hsuffix, protectedWord_eq_headPrefix_headSuffix]
    rfl
  have hlocatorInput : Tape.Equiv
      (Tape.input (Dispatch.HeadCursor.GenericPrefix.sourceWord
        L (first :: rest))) T := by rw [hsourceWord]; exact hinput
  rcases Dispatch.HeadCursor.Full.run_from_equiv
      L first rest T hlocatorInput with
    ⟨locatorEndpoint, hlocatorInner, hlocatorState, hlocatorTape⟩
  have hlocator := locate_run_of_some L.head newHead hlocatorInner
  have hlocatorTarget : locateConfig locatorEndpoint = replaceConfig
      { state := Edits.OptionalField.Replace.Control.markLeft
        tape := locatorEndpoint.tape } := by
    cases locatorEndpoint with
    | mk actualState tape =>
        simp only at hlocatorState
        subst actualState
        rfl
  rw [hlocatorTarget] at hlocator
  have hpositionedTape :
      (Edits.OptionalField.LayoutSpecialization.sourceConfig
        L callerData).tape =
      (Dispatch.HeadCursor.Full.positionedConfig L first rest).tape := by
    unfold Edits.OptionalField.LayoutSpecialization.sourceConfig
      Dispatch.HeadCursor.Full.positionedConfig
      Dispatch.HeadCursor.Full.postConfig
      Dispatch.HeadCursor.Post.positionedConfig
      Dispatch.HeadCursor.Post.cursorConfig
      TuringMachine.PhaseEmbedding.liftConfig
    change SerializedShift.cursorTape (headPrefix L).reverse (headSuffix L callerData) =
      SerializedShift.cursorTape (headPrefix L).reverse
        (List.append (optionalCellWord L.head) (first :: rest))
    rw [show headSuffix L callerData = List.append (optionalCellWord L.head)
      (HeadLocator.afterHeadWord L callerData) by rfl, hsuffix]
  have hreplaceSource : Tape.Equiv
      (Edits.OptionalField.LayoutSpecialization.sourceConfig
        L callerData).tape locatorEndpoint.tape := by
    rw [hpositionedTape]
    exact hlocatorTape
  rcases replace_run_exact_of_tape_equiv
      L newHead callerData locatorEndpoint.tape hreplaceSource with
    ⟨replaceEndpoint, hreplaceInner, hreplaceState, hreplaceTape⟩
  have hreplace := replace_run_of_some L.head newHead hreplaceInner
  have hrun := TuringMachine.runConfigExact?_trans hlocator hreplace
  have hstart : locateConfig
      { state := Dispatch.HeadCursor.Full.machine.start, tape := T } =
      { state := (machine L.head newHead).start, tape := T } := rfl
  rw [hstart] at hrun
  refine ⟨replaceConfig replaceEndpoint, ?_, ?_, hreplaceTape⟩
  · simpa [runSteps, Nat.add_assoc] using hrun
  · simpa [replaceConfig, replaceEmbed,
      TuringMachine.PhaseEmbedding.liftConfig] using hreplaceState
end HeadReplaceMachine
namespace LeftPrependMachine
inductive Control where
  | payload (inner : Edits.PositionedLeft.Control)
  | count (inner : Edits.PositionedLeft.Control)
deriving DecidableEq
namespace Control
def elems : List Control := List.append
  (Edits.PositionedLeft.Control.finite.elems.map Control.payload)
  (Edits.PositionedLeft.Control.finite.elems.map Control.count)
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro c
    cases c with
    | payload inner | count inner =>
        have h := Edits.PositionedLeft.Control.finite.complete inner
        simp [elems, h]
end Control
def payloadInnerMachine (write : Option MachineCodeSymbol) :=
  Edits.PositionedLeft.machine .leftPayload (InsertBlock.optionalBuffer write)
def countInnerMachine := Edits.PositionedLeft.machine .leftCountDone
  (InsertBlock.singletonBuffer MachineCodeSymbol.tick)
def payloadHalt : Edits.PositionedLeft.Control := .insert (.rewind .gate)
def payloadEmbed (inner : Edits.PositionedLeft.Control) : Control :=
  if inner = payloadHalt then .count countInnerMachine.start else .payload inner
def countEmbed : Edits.PositionedLeft.Control -> Control := Control.count
def transition (write : Option MachineCodeSymbol) : Control ->
    Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .payload inner, read =>
      match (payloadInnerMachine write).transition inner read with
      | none => none
      | some (written, direction, target) =>
          some (written, direction, payloadEmbed target)
  | .count inner, read =>
      match countInnerMachine.transition inner read with
      | none => none
      | some (written, direction, target) =>
          some (written, direction, countEmbed target)
def machine (write : Option MachineCodeSymbol) :
    TuringMachine MachineCodeSymbol Control where
  start := payloadEmbed (payloadInnerMachine write).start
  halt := countEmbed countInnerMachine.halt
  transition := transition write
  statesFinite := Control.finite
private def payloadConfig (c : TuringMachine.Configuration MachineCodeSymbol
    Edits.PositionedLeft.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig payloadEmbed c
private def countConfig (c : TuringMachine.Configuration MachineCodeSymbol
    Edits.PositionedLeft.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig countEmbed c
private theorem payload_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedLeft.Control} (hrun : (payloadInnerMachine write).runConfigExact?
      steps source = some target) : (machine write).runConfigExact? steps (payloadConfig source) =
      some (payloadConfig target) := by
  apply liftRun (payloadInnerMachine write) (machine write)
    payloadEmbed ?_ hrun
  intro state read written direction target htransition
  change (payloadInnerMachine write).transition state read =
    some (written, direction, target) at htransition
  by_cases hhalt : state = payloadHalt
  · subst state
    simp [payloadInnerMachine, payloadHalt, Edits.PositionedLeft.machine,
      Edits.PositionedLeft.transition, InsertRestagedMachine.transition,
      RewindWord.transition] at htransition
  · simp [machine, transition, payloadEmbed, hhalt, htransition]
private theorem count_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedLeft.Control} (hrun : countInnerMachine.runConfigExact? steps source = some target) : (machine write).runConfigExact? steps (countConfig source) =
      some (countConfig target) := by
  apply liftRun countInnerMachine (machine write) countEmbed ?_ hrun
  intro state read written direction target htransition
  change countInnerMachine.transition state read =
    some (written, direction, target) at htransition
  simp [machine, transition, countEmbed, htransition]
private def runSteps {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Nat :=
  Edits.PositionedLeft.payloadSteps L write callerData +
    Edits.PositionedLeft.countIncrementSteps L write callerData
private theorem run_exact_of_equiv {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) (T : Tape MachineCodeSymbol) (hsource : Tape.Equiv (Tape.input (Frame.protectedWord L callerData)) T) :
    ∃ endpoint,
      (machine write).runConfigExact? (runSteps L write callerData)
        { state := (machine write).start, tape := T } = some endpoint ∧
      endpoint.state = countEmbed countInnerMachine.halt ∧
      Tape.Equiv (Tape.input (Frame.protectedWord
        (LeftPrepend.prependedLeftLayout L write) callerData)) endpoint.tape := by
  rcases Edits.PositionedLeft.payload_insert_exact_of_tape_equiv
      L write callerData T hsource with
    ⟨payloadEndpoint, hpayloadInner, hpayloadState, hpayloadTape⟩
  have hpayload := payload_run_of_some write hpayloadInner
  have hpayloadTarget : payloadConfig payloadEndpoint = countConfig
      { state := countInnerMachine.start, tape := payloadEndpoint.tape } := by
    cases payloadEndpoint with
    | mk actualState tape =>
        simp only at hpayloadState
        subst actualState
        simp [payloadConfig, payloadEmbed, payloadHalt, countConfig, countEmbed,
          countInnerMachine, TuringMachine.PhaseEmbedding.liftConfig,
          Edits.PositionedLeft.machine]
  rw [hpayloadTarget] at hpayload
  rcases Edits.PositionedLeft.count_increment_exact_of_tape_equiv
      L write callerData payloadEndpoint.tape hpayloadTape with
    ⟨countEndpoint, hcountInner, hcountState, hcountTape⟩
  have hcount := count_run_of_some write hcountInner
  have hrun := TuringMachine.runConfigExact?_trans hpayload hcount
  refine ⟨countConfig countEndpoint, ?_, ?_, hcountTape⟩
  · simpa [runSteps, payloadInnerMachine, machine, payloadConfig,
      TuringMachine.PhaseEmbedding.liftConfig, payloadEmbed,
      payloadHalt, Edits.PositionedLeft.machine] using hrun
  · simpa [countConfig, countEmbed,
      TuringMachine.PhaseEmbedding.liftConfig, countInnerMachine,
      Edits.PositionedLeft.machine] using hcountState
end LeftPrependMachine
namespace FullMachine
inductive Control where
  | remove (inner : RightRemoval.Control)
  | replace (old new : Option MachineCodeSymbol) (inner : HeadReplaceMachine.Control)
  | prepend (inner : LeftPrependMachine.Control)
deriving DecidableEq
namespace Control
def optionalFinite : Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite
def pairFinite : Foundation.FiniteType (Option MachineCodeSymbol × Option MachineCodeSymbol) :=
  Foundation.FiniteType.prod optionalFinite optionalFinite
def replaceFinite : Foundation.FiniteType ((Option MachineCodeSymbol × Option MachineCodeSymbol) ×
      HeadReplaceMachine.Control) :=
  Foundation.FiniteType.prod pairFinite HeadReplaceMachine.Control.finite
def elems : List Control := List.append
  (RightRemoval.Control.finite.elems.map Control.remove)
  (List.append (replaceFinite.elems.map fun p => Control.replace p.1.1 p.1.2 p.2) (LeftPrependMachine.Control.finite.elems.map Control.prepend))
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro c
    cases c with
    | remove inner =>
        have h := RightRemoval.Control.finite.complete inner
        simp [elems, h]
    | replace old new inner =>
        have h := replaceFinite.complete ((old, new), inner)
        simp [elems]
        exact ⟨old, new, inner, h, rfl, rfl, rfl⟩
    | prepend inner =>
        have h := LeftPrependMachine.Control.finite.complete inner
        simp [elems, h]
end Control
def removeEmbed : RightRemoval.Control -> Control
  | .count old new (.rewind .gate) =>
      .replace old new (HeadReplaceMachine.machine old new).start
  | inner => .remove inner
def replaceEmbed (write old new : Option MachineCodeSymbol) :
    HeadReplaceMachine.Control -> Control
  | .replace (.insert (.rewind .gate)) =>
      .prepend (LeftPrependMachine.machine write).start
  | inner => .replace old new inner
def prependEmbed : LeftPrependMachine.Control -> Control := Control.prepend
def transition (write : Option MachineCodeSymbol) : Control ->
    Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .remove inner, read =>
      match RightRemoval.transition inner read with
      | none => none
      | some (written, direction, target) =>
          some (written, direction, removeEmbed target)
  | .replace old new inner, read =>
      match HeadReplaceMachine.transition old new inner read with
      | none => none
      | some (written, direction, target) =>
          some (written, direction, replaceEmbed write old new target)
  | .prepend inner, read =>
      match LeftPrependMachine.transition write inner read with
      | none => none
      | some (written, direction, target) =>
          some (written, direction, prependEmbed target)
def machine (write : Option MachineCodeSymbol) :
    TuringMachine MachineCodeSymbol Control where
  start := removeEmbed RightRemoval.machine.start
  halt := prependEmbed (LeftPrependMachine.machine write).halt
  transition := transition write
  statesFinite := Control.finite
private def removeConfig (c : TuringMachine.Configuration MachineCodeSymbol
    RightRemoval.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig removeEmbed c
private def replaceConfig (write old new : Option MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol HeadReplaceMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (replaceEmbed write old new) c
private def prependConfig (c : TuringMachine.Configuration MachineCodeSymbol
    LeftPrependMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig prependEmbed c
private theorem remove_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      RightRemoval.Control} (hrun : RightRemoval.machine.runConfigExact?
      steps source = some target) : (machine write).runConfigExact? steps (removeConfig source) =
      some (removeConfig target) := by
  apply liftRun RightRemoval.machine (machine write) removeEmbed ?_ hrun
  intro state read written direction target htransition
  change RightRemoval.transition state read =
    some (written, direction, target) at htransition
  cases state with
  | core inner | restore old new inner =>
      simp [machine, transition, removeEmbed, htransition]
  | count old new inner =>
      cases inner with
      | edit inner =>
          simp [machine, transition, removeEmbed, htransition]
      | rewind inner =>
          cases inner with
          | gate =>
              simp [RightRemoval.transition,
                DeleteRestagedMachine.transition,
                DeleteEndpointRewind.transition] at htransition
          | _ => simp [machine, transition, removeEmbed, htransition]
private theorem replace_run_of_some (write old new : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      HeadReplaceMachine.Control} (hrun : (HeadReplaceMachine.machine old new).runConfigExact?
      steps source = some target) : (machine write).runConfigExact? steps (replaceConfig write old new source) =
      some (replaceConfig write old new target) := by
  apply liftRun (HeadReplaceMachine.machine old new) (machine write) (replaceEmbed write old new) ?_ hrun
  intro state read written direction target htransition
  change HeadReplaceMachine.transition old new state read =
    some (written, direction, target) at htransition
  cases state with
  | locate inner =>
      simp [machine, transition, replaceEmbed, htransition]
  | replace inner =>
      cases inner with
      | insert inner =>
          cases inner with
          | edit inner =>
              simp [machine, transition, replaceEmbed, htransition]
          | rewind inner =>
              cases inner with
              | gate =>
                  simp [HeadReplaceMachine.transition,
                    Edits.OptionalField.Replace.transition,
                    InsertRestagedMachine.transition,
                    RewindWord.transition] at htransition
              | _ => simp [machine, transition, replaceEmbed, htransition]
      | _ =>
          simp [machine, transition, replaceEmbed, htransition]
private theorem prepend_run_of_some (write : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      LeftPrependMachine.Control} (hrun : (LeftPrependMachine.machine write).runConfigExact?
      steps source = some target) : (machine write).runConfigExact? steps (prependConfig source) =
      some (prependConfig target) := by
  apply liftRun (LeftPrependMachine.machine write) (machine write) prependEmbed ?_ hrun
  intro state read written direction target htransition
  change LeftPrependMachine.transition write state read =
    some (written, direction, target) at htransition
  simp [machine, transition, prependEmbed, htransition]
def runSteps {stateCount : Nat} (L : Layout stateCount) (write nextHead : Option MachineCodeSymbol) (remainingRight : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) : Nat :=
  (RightRemoval.runSteps
      L nextHead remainingRight callerData +
    HeadReplaceMachine.runSteps
      (MoveRightNonempty.removedRightLayout L remainingRight)
      nextHead callerData) +
    LeftPrependMachine.runSteps
      (MoveRightNonempty.headReplacedLayout L nextHead remainingRight)
      write callerData
theorem run_exact {stateCount : Nat} (L : Layout stateCount) (write nextHead : Option MachineCodeSymbol) (remainingRight : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) (hright : L.right = nextHead :: remainingRight) :
    ∃ endpoint,
      (machine write).runConfigExact?
        (runSteps L write nextHead remainingRight callerData)
        { state := (machine write).start
          tape := Tape.input (Frame.protectedWord L callerData) } = some endpoint ∧
      endpoint.state = prependEmbed (LeftPrependMachine.machine write).halt ∧
      Tape.Equiv (Tape.input (Frame.protectedWord
        (HeadActionShape.moveRightTarget L.fuel write L.state L) callerData))
        endpoint.tape := by
  rcases RightRemoval.run_exact
      L nextHead remainingRight callerData hright with
    ⟨removeEndpoint, hremoveInner, hremoveState, hremoveTape⟩
  have hremove := remove_run_of_some write hremoveInner
  have hremoveSource : removeConfig
      (RightRemoval.coreConfig
        (Dispatch.RightFirstCell.CombinedMachine.locateConfig
          (Dispatch.RightFieldLocator.OuterLocator.locateConfig
            (FieldLocator.startConfig L callerData)))) =
      { state := (machine write).start
        tape := Tape.input (Frame.protectedWord L callerData) } := rfl
  rw [hremoveSource] at hremove
  have hremoveState' : removeEndpoint.state =
      RightRemoval.Control.count
        L.head nextHead (.rewind .gate) := by
    simpa [Edits.MarkedPrefixRestorer.CountDecrement.targetConfig,
      DeleteRestagedMachine.rewindConfig,
      DeleteEndpointRewind.gateConfig] using hremoveState
  have hremoveTarget : removeConfig removeEndpoint =
      replaceConfig write L.head nextHead
        { state := (HeadReplaceMachine.machine L.head nextHead).start
          tape := removeEndpoint.tape } := by
    cases removeEndpoint with
    | mk actualState tape =>
        simp only at hremoveState'
        subst actualState
        rfl
  rw [hremoveTarget] at hremove
  have htargetGate : Tape.Equiv
      (Edits.MarkedPrefixRestorer.CountDecrement.targetConfig
        L remainingRight callerData).tape
      (Tape.input (Frame.protectedWord
        (MoveRightNonempty.removedRightLayout L remainingRight) callerData)) := by
    simpa [Edits.MarkedPrefixRestorer.CountDecrement.targetConfig,
      DeleteRestagedMachine.rewindConfig,
      DeleteEndpointRewind.gateConfig] using
      DeleteEndpointRewind.gateTape_equiv_input
        (Frame.protectedWord
          (MoveRightNonempty.removedRightLayout L remainingRight) callerData) none
  have hremoveCanonical : Tape.Equiv
      (Tape.input (Frame.protectedWord
        (MoveRightNonempty.removedRightLayout L remainingRight) callerData))
      removeEndpoint.tape :=
    Tape.Equiv.trans (Tape.Equiv.symm htargetGate) hremoveTape
  cases hsuffix : HeadLocator.afterHeadWord
      (MoveRightNonempty.removedRightLayout L remainingRight) callerData with
  | nil =>
      have hlength := congrArg List.length hsuffix
      simp [HeadLocator.afterHeadWord] at hlength
  | cons first rest =>
      rcases HeadReplaceMachine.run_exact_of_equiv
          (MoveRightNonempty.removedRightLayout L remainingRight)
          nextHead callerData first rest hsuffix removeEndpoint.tape
          hremoveCanonical with
        ⟨replaceEndpoint, hreplaceInner, hreplaceState, hreplaceTape⟩
      have hreplace := replace_run_of_some write L.head nextHead hreplaceInner
      have hreplaceTarget : replaceConfig write L.head nextHead replaceEndpoint =
          prependConfig
            { state := (LeftPrependMachine.machine write).start
              tape := replaceEndpoint.tape } := by
        cases replaceEndpoint with
        | mk actualState tape =>
            simp only at hreplaceState
            subst actualState
            rfl
      rw [hreplaceTarget] at hreplace
      have hreplaceCanonical : Tape.Equiv
          (Tape.input (Frame.protectedWord
            (MoveRightNonempty.headReplacedLayout L nextHead remainingRight)
            callerData)) replaceEndpoint.tape := by
        simpa [MoveRightNonempty.headReplacedLayout] using hreplaceTape
      rcases LeftPrependMachine.run_exact_of_equiv
          (MoveRightNonempty.headReplacedLayout L nextHead remainingRight)
          write callerData replaceEndpoint.tape hreplaceCanonical with
        ⟨prependEndpoint, hprependInner, hprependState, hprependTape⟩
      have hprepend := prepend_run_of_some write hprependInner
      have hrun := TuringMachine.runConfigExact?_trans
        (TuringMachine.runConfigExact?_trans hremove hreplace) hprepend
      refine ⟨prependConfig prependEndpoint, ?_, ?_, ?_⟩
      · simpa [runSteps, Nat.add_assoc] using hrun
      · simpa [prependConfig, prependEmbed,
          TuringMachine.PhaseEmbedding.liftConfig,
          LeftPrependMachine.machine] using hprependState
      · have hfinal : Tape.Equiv
            (Tape.input (Frame.protectedWord
              (MoveRightNonempty.reshapedLayout L write nextHead remainingRight)
              callerData)) prependEndpoint.tape := by
          simpa [MoveRightNonempty.reshapedLayout] using hprependTape
        rw [MoveRightNonempty.reshapedLayout_eq_moveRightTarget
          L write nextHead remainingRight hright] at hfinal
        exact hfinal
end FullMachine

theorem run_from_equiv {stateCount : Nat}
    (L : Layout stateCount) (write nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (hright : L.right = nextHead :: remainingRight)
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (Frame.protectedWord L callerData)) T) :
    ∃ steps endpoint,
      (FullMachine.machine write).runConfigExact? steps
          { state := (FullMachine.machine write).start, tape := T } =
        some endpoint ∧
      endpoint.state = FullMachine.prependEmbed
        (LeftPrependMachine.machine write).halt ∧
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (HeadActionShape.moveRightTarget L.fuel write L.state L)
            callerData))
        endpoint.tape := by
  rcases FullMachine.run_exact
      L write nextHead remainingRight callerData hright with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  exact
    ⟨FullMachine.runSteps L write nextHead remainingRight callerData,
      endpoint, hrun, hstate ▸ hcleanState,
      Tape.Equiv.trans hcleanTape htape⟩

end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightNonempty
