import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
open Languages
namespace FuelDecrementMachine
inductive Control where
  | header
  | update (control : DeleteOneRestagedMachine.Control)
deriving DecidableEq
namespace Control
def elems : List Control := .header :: DeleteOneRestagedMachine.Control.finite.elems.map Control.update
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | header => simp [elems]
    | update inner =>
        simp [elems]
        exact DeleteOneRestagedMachine.Control.finite.complete inner
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .header, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .update (.edit .start))
  | .header, _ => none
  | .update inner, read =>
      match DeleteOneRestagedMachine.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .update target)
def machine : TuringMachine MachineCodeSymbol Control where
  start := .header
  halt := .update (.rewind .gate)
  transition := transition
  statesFinite := Control.finite
def config (control : Control) (tape : Tape MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := tape
def startConfig (word : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control := config .header (Tape.input word)
def updateConfig (c : TuringMachine.Configuration MachineCodeSymbol DeleteOneRestagedMachine.Control) : TuringMachine.Configuration MachineCodeSymbol Control :=
  config (.update c.state) c.tape
theorem header_step (suffix : Word MachineCodeSymbol) : machine.stepConfig (startConfig (MachineCodeSymbol.header :: MachineCodeSymbol.tick :: suffix)) =
      some (updateConfig (DeleteOneRestagedMachine.editConfig (SerializedShift.Delete.startConfig [MachineCodeSymbol.header] MachineCodeSymbol.tick suffix))) := by
  cases suffix <;> rfl
theorem header_run_exact (suffix : Word MachineCodeSymbol) : machine.runConfigExact? 1 (startConfig (MachineCodeSymbol.header :: MachineCodeSymbol.tick :: suffix)) =
      some (updateConfig (DeleteOneRestagedMachine.editConfig (SerializedShift.Delete.startConfig [MachineCodeSymbol.header] MachineCodeSymbol.tick suffix))) := by
  rw [TuringMachine.runConfigExact?, header_step]
  rfl
theorem update_step (c : TuringMachine.Configuration MachineCodeSymbol DeleteOneRestagedMachine.Control) :
    machine.stepConfig (updateConfig c) = Option.map updateConfig (DeleteOneRestagedMachine.machine.stepConfig c) := by
  cases c with
  | mk state tape =>
      unfold TuringMachine.stepConfig
      simp only [updateConfig, config, machine, transition, DeleteOneRestagedMachine.machine]
      cases htransition : DeleteOneRestagedMachine.transition state (Tape.read tape) with
      | none => rfl
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rfl
theorem update_run_of_eq_some (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol DeleteOneRestagedMachine.Control)
    (hrun : DeleteOneRestagedMachine.machine.runConfigExact? steps c = some d) :
    machine.runConfigExact? steps (updateConfig c) = some (updateConfig d) := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : DeleteOneRestagedMachine.machine.stepConfig c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          rw [update_step, hstep]
          simp only [Option.map]
          exact ih next d hrun
theorem runConfigExact?_add (first second : Nat) (c : TuringMachine.Configuration MachineCodeSymbol Control) :
    machine.runConfigExact? (first + second) c = match machine.runConfigExact? first c with
      | none => none
      | some middle => machine.runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add, TuringMachine.runConfigExact?, TuringMachine.runConfigExact?]
      cases hstep : machine.stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next
def withFuel {stateCount : Nat} (fuel : Nat) (L : Layout stateCount) : Layout stateCount :=
  { L with fuel := fuel }
def suffixAfterFirstFuelTick {stateCount : Nat} (fuel : Nat) (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend fuel (stateSuffix L callerData)
theorem source_word_decomp {stateCount : Nat} (fuel : Nat) (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Frame.protectedWord (withFuel (fuel + 1) L) callerData = MachineCodeSymbol.header :: MachineCodeSymbol.tick :: suffixAfterFirstFuelTick fuel L callerData := by
  cases L
  rfl
theorem target_word_decomp {stateCount : Nat} (fuel : Nat) (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    DeleteOneRestagedMachine.output [MachineCodeSymbol.header] (suffixAfterFirstFuelTick fuel L callerData) = Frame.protectedWord (withFuel fuel L) callerData := by
  cases L
  rfl
def runSteps {stateCount : Nat} (fuel : Nat) (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Nat :=
  1 + DeleteOneRestagedMachine.runSteps [MachineCodeSymbol.header] (suffixAfterFirstFuelTick fuel L callerData)
theorem run_exact {stateCount : Nat} (fuel : Nat) (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps fuel L callerData) (startConfig (Frame.protectedWord (withFuel (fuel + 1) L) callerData)) =
      some (updateConfig (DeleteOneRestagedMachine.rewindConfig (RewindWord.gateConfig (Frame.protectedWord (withFuel fuel L) callerData) 1))) := by
  unfold runSteps
  rw [source_word_decomp, runConfigExact?_add, header_run_exact]
  simp only
  apply update_run_of_eq_some
  rw [DeleteOneRestagedMachine.run_exact, target_word_decomp]
theorem endpoint_tape_equiv_input {stateCount : Nat} (fuel : Nat) (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Tape.Equiv (RewindWord.gateConfig (Frame.protectedWord (withFuel fuel L) callerData) 1).tape (Tape.input (Frame.protectedWord (withFuel fuel L) callerData)) := by
  exact RewindWord.gateTape_equiv_input (Frame.protectedWord (withFuel fuel L) callerData) 1
end FuelDecrementMachine
namespace CarriedStateFrame
structure LoopFrame (stateCount : Nat) where
  carriedState : Fin stateCount
  physicalFrame : Layout stateCount
def physicalStatePlaceholder {stateCount : Nat} (F : LoopFrame stateCount) : Fin stateCount := F.physicalFrame.state
def semanticLayout {stateCount : Nat} (F : LoopFrame stateCount) : Layout stateCount :=
  { F.physicalFrame with state := F.carriedState }
def ofParsed {stateCount : Nat} (L : Layout stateCount) : LoopFrame stateCount where
  carriedState := L.state
  physicalFrame := L
@[simp] theorem semanticLayout_ofParsed {stateCount : Nat} (L : Layout stateCount) : semanticLayout (ofParsed L) = L := by
  cases L
  rfl
def withFuel {stateCount : Nat} (fuel : Nat) (F : LoopFrame stateCount) : LoopFrame stateCount where
  carriedState := F.carriedState
  physicalFrame := FuelDecrementMachine.withFuel fuel F.physicalFrame
@[simp] theorem withFuel_carriedState {stateCount : Nat} (fuel : Nat) (F : LoopFrame stateCount) : (withFuel fuel F).carriedState = F.carriedState := by rfl
def selectedPhysicalFrame {stateCount : Nat} (fuel : Nat) (write : Option MachineCodeSymbol) (direction : Direction) (F : LoopFrame stateCount) : Layout stateCount :=
  match direction with
  | Direction.left =>
      HeadActionShape.moveLeftTarget fuel write (physicalStatePlaceholder F) F.physicalFrame
  | Direction.right =>
      HeadActionShape.moveRightTarget fuel write (physicalStatePlaceholder F) F.physicalFrame
def afterSelected {stateCount : Nat} (fuel : Nat) (write : Option MachineCodeSymbol) (direction : Direction) (nextState : Fin stateCount)
    (F : LoopFrame stateCount) : LoopFrame stateCount where
  carriedState := nextState
  physicalFrame := selectedPhysicalFrame fuel write direction F
@[simp] theorem afterSelected_carriedState {stateCount : Nat} (fuel : Nat) (write : Option MachineCodeSymbol) (direction : Direction) (nextState : Fin stateCount)
    (F : LoopFrame stateCount) :
    (afterSelected fuel write direction nextState F).carriedState = nextState := by rfl
theorem semanticLayout_afterSelected_eq_transitionTarget
    {stateCount : Nat}
    (fuel : Nat) (write : Option MachineCodeSymbol)
    (direction : Direction) (nextState : Fin stateCount)
    (F : LoopFrame stateCount) :
    semanticLayout (afterSelected fuel write direction nextState F) = Machine.transitionTarget fuel write direction nextState (semanticLayout F) := by
  cases F with
  | mk carried physical =>
      cases physical with
      | mk layoutFuel placeholder left head right =>
          cases direction with
          | left => cases left <;> rfl
          | right => cases right <;> rfl
end CarriedStateFrame
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
