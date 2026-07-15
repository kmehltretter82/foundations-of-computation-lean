import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Rewind
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
open Languages
namespace PhysicalBranch
def deleteOutput (leftRev suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol := List.append leftRev.reverse suffix
def insertOutput (buffer : InsertBlock.Buffer) (leftRev suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol := List.append leftRev.reverse (List.append buffer.word suffix)
theorem decrementLeft_output_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (remainingLeft : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) :
    deleteOutput (MoveLeftNonempty.leftCountPrefix L).reverse (MoveLeftNonempty.afterCountTick L remainingLeft callerData) =
      Frame.protectedWord (MoveLeftNonempty.removedLeftLayout L remainingLeft)
        callerData := by
  have h := MoveLeftNonempty.countCorrectedWord_eq_protectedWord L remainingLeft callerData
  simpa [deleteOutput, MoveLeftNonempty.countCorrectedWord] using h
theorem decrementRight_output_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (remainingRight : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) :
    deleteOutput (RightPrepend.rightCountPrefix L).reverse (MoveRightNonempty.afterCountTick remainingRight callerData) =
      Frame.protectedWord (MoveRightNonempty.removedRightLayout L remainingRight)
        callerData := by
  have h := MoveRightNonempty.countCorrectedWord_eq_protectedWord L remainingRight callerData
  simpa [deleteOutput, MoveRightNonempty.countCorrectedWord] using h
theorem prependRight_output_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) :
    insertOutput (InsertBlock.singletonBuffer MachineCodeSymbol.tick) (RightPrepend.rightCountTicksPrefix L).reverse (RightPrepend.afterCountDoneSuffix L write callerData) =
      Frame.protectedWord (RightPrepend.prependedRightLayout L write) callerData := by
  have h := RightPrepend.afterIncrementWord_eq_protectedWord L write callerData
  simpa [insertOutput, InsertBlock.singletonBuffer, RightPrepend.afterIncrementWord] using h
theorem prependLeft_output_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) :
    insertOutput (InsertBlock.singletonBuffer MachineCodeSymbol.tick) (LeftPrepend.leftCountTicksPrefix L).reverse (LeftPrepend.afterCountDoneSuffix L write callerData) =
      Frame.protectedWord (LeftPrepend.prependedLeftLayout L write) callerData := by
  have h := LeftPrepend.afterIncrementWord_eq_protectedWord L write callerData
  simpa [insertOutput, InsertBlock.singletonBuffer, LeftPrepend.afterIncrementWord] using h
end PhysicalBranch
namespace InsertRestagedMachine
inductive Control where
  | edit (control : InsertBlock.Control)
  | rewind (control : RewindWord.Control)
deriving DecidableEq
namespace Control
def elems : List Control := List.append (InsertBlock.Control.finite.elems.map Control.edit) (RewindWord.Control.finite.elems.map Control.rewind)
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | edit inner =>
        simp [elems]
        exact InsertBlock.Control.finite.complete inner
    | rewind inner =>
        simp [elems]
        exact RewindWord.Control.finite.complete inner
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .edit .halt, cell =>
      match RewindWord.transition .start cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rewind target)
  | .edit inner, cell =>
      match InsertBlock.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .edit target)
  | .rewind inner, cell =>
      match RewindWord.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rewind target)
def machine (buffer : InsertBlock.Buffer) : TuringMachine MachineCodeSymbol Control where
  start := .edit (.carry buffer)
  halt := .rewind .gate
  transition := transition
  statesFinite := Control.finite
def editConfig (c : TuringMachine.Configuration MachineCodeSymbol InsertBlock.Control) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .edit c.state
  tape := c.tape
def rewindConfig (c : TuringMachine.Configuration MachineCodeSymbol RewindWord.Control) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewind c.state
  tape := c.tape
theorem edit_step_of_not_halt (buffer : InsertBlock.Buffer) (c : TuringMachine.Configuration MachineCodeSymbol InsertBlock.Control) (hnot : c.state ≠ .halt) :
    (machine buffer).stepConfig (editConfig c) = Option.map editConfig ((InsertBlock.machine buffer).stepConfig c) := by
  cases c with
  | mk state tape =>
      cases state with
      | carry current =>
          unfold TuringMachine.stepConfig
          simp only [editConfig, machine, transition, InsertBlock.machine]
          cases htransition : InsertBlock.transition (.carry current) (Tape.read tape) with
          | none => rfl
          | some action =>
              rcases action with ⟨write, direction, target⟩
              rfl
      | halt => contradiction
theorem edit_run_of_eq_some (buffer : InsertBlock.Buffer) (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol InsertBlock.Control)
    (hrun : (InsertBlock.machine buffer).runConfigExact? steps c = some d) :
    (machine buffer).runConfigExact? steps (editConfig c) = some (editConfig d) := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : (InsertBlock.machine buffer).stepConfig c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          have hnot : c.state ≠ InsertBlock.Control.halt := by
            intro hhalt
            have hnone : (InsertBlock.machine buffer).stepConfig c = none := by
              cases c with
              | mk state tape =>
                  simp only at hhalt
                  subst state
                  rfl
            rw [hnone] at hstep
            contradiction
          rw [edit_step_of_not_halt buffer c hnot, hstep]
          simp only [Option.map]
          exact ih next d hrun
theorem edit_run_exact (buffer : InsertBlock.Buffer) (leftRev suffix : Word MachineCodeSymbol) (hnonempty : buffer.word ≠ []) :
    (machine buffer).runConfigExact? (suffix.length + buffer.word.length) (editConfig (InsertBlock.config buffer leftRev suffix)) =
      some (editConfig (InsertBlock.haltConfig (InsertBlock.finalLeftRev buffer leftRev suffix))) := by
  exact edit_run_of_eq_some buffer _ _ _ (InsertBlock.run_exact buffer buffer leftRev suffix hnonempty)
theorem halt_retarget_step (buffer : InsertBlock.Buffer) (wordRev : Word MachineCodeSymbol) :
    (machine buffer).stepConfig (editConfig (InsertBlock.haltConfig wordRev)) = some (rewindConfig (RewindWord.scanConfig wordRev [] 0)) := by cases wordRev <;> rfl
theorem rewind_scan_step (buffer : InsertBlock.Buffer) (current : MachineCodeSymbol) (remainingRev crossed : Word MachineCodeSymbol) :
    (machine buffer).stepConfig (rewindConfig (RewindWord.scanConfig (current :: remainingRev) crossed 0)) =
      some (rewindConfig (RewindWord.scanConfig remainingRev (current :: crossed) 0)) := by cases remainingRev <;> rfl
theorem rewind_scan_finish (buffer : InsertBlock.Buffer) (crossed : Word MachineCodeSymbol) : (machine buffer).stepConfig (rewindConfig (RewindWord.scanConfig [] crossed 0)) =
      some (rewindConfig (RewindWord.gateConfig crossed 0)) := by cases crossed <;> rfl
theorem rewind_scan_run_exact (buffer : InsertBlock.Buffer) (remainingRev crossed : Word MachineCodeSymbol) :
    (machine buffer).runConfigExact? (remainingRev.length + 1) (rewindConfig (RewindWord.scanConfig remainingRev crossed 0)) =
      some (rewindConfig (RewindWord.gateConfig (List.append remainingRev.reverse crossed) 0)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact rewind_scan_finish buffer crossed
  | cons current remainingRev ih =>
      change (machine buffer).runConfigExact? ((remainingRev.length + 1) + 1) (rewindConfig (RewindWord.scanConfig (current :: remainingRev) crossed 0)) = _
      rw [TuringMachine.runConfigExact?, rewind_scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]
theorem rewind_run_exact (buffer : InsertBlock.Buffer) (wordRev : Word MachineCodeSymbol) :
    (machine buffer).runConfigExact? (wordRev.length + 2) (editConfig (InsertBlock.haltConfig wordRev)) = some (rewindConfig (RewindWord.gateConfig wordRev.reverse 0)) := by
  change (machine buffer).runConfigExact? ((wordRev.length + 1) + 1) (editConfig (InsertBlock.haltConfig wordRev)) = _
  rw [TuringMachine.runConfigExact?, halt_retarget_step]
  simp only
  simpa using rewind_scan_run_exact buffer wordRev ([] : Word MachineCodeSymbol)
theorem runConfigExact?_add (buffer : InsertBlock.Buffer) (first second : Nat) (c : TuringMachine.Configuration MachineCodeSymbol Control) :
    (machine buffer).runConfigExact? (first + second) c = match (machine buffer).runConfigExact? first c with
      | none => none
      | some middle =>
          (machine buffer).runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add, TuringMachine.runConfigExact?, TuringMachine.runConfigExact?]
      cases hstep : (machine buffer).stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next
def runSteps (buffer : InsertBlock.Buffer) (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  (suffix.length + buffer.word.length) + ((InsertBlock.finalLeftRev buffer leftRev suffix).length + 2)
theorem run_exact (buffer : InsertBlock.Buffer) (leftRev suffix : Word MachineCodeSymbol) (hnonempty : buffer.word ≠ []) :
    (machine buffer).runConfigExact? (runSteps buffer leftRev suffix) (editConfig (InsertBlock.config buffer leftRev suffix)) =
      some (rewindConfig (RewindWord.gateConfig (PhysicalBranch.insertOutput buffer leftRev suffix) 0)) := by
  unfold runSteps
  rw [runConfigExact?_add, edit_run_exact buffer leftRev suffix hnonempty]
  simp only
  rw [rewind_run_exact]
  rw [InsertBlock.finalLeftRev_reverse buffer leftRev suffix hnonempty]
  rfl
end InsertRestagedMachine
namespace DeleteRestagedMachine
inductive Control where
  | edit (control : DeleteBlock.Control)
  | rewind (control : DeleteEndpointRewind.Control)
deriving DecidableEq
namespace Control
def elems : List Control := List.append (DeleteBlock.Control.finite.elems.map Control.edit) (DeleteEndpointRewind.Control.finite.elems.map Control.rewind)
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | edit inner =>
        simp [elems]
        exact DeleteBlock.Control.finite.complete inner
    | rewind inner =>
        simp [elems]
        exact DeleteEndpointRewind.Control.finite.complete inner
end Control
def transition (cell : Option MachineCodeSymbol) : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .edit .halt, read =>
      match DeleteEndpointRewind.transition (DeleteEndpointRewind.startControl cell) read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rewind target)
  | .edit inner, read =>
      match DeleteBlock.transition (DeleteBlock.optionalGap cell) inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .edit target)
  | .rewind inner, read =>
      match DeleteEndpointRewind.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rewind target)
def machine (cell : Option MachineCodeSymbol) : TuringMachine MachineCodeSymbol Control where
  start := .edit (.erase (DeleteBlock.optionalGap cell))
  halt := .rewind .gate
  transition := transition cell
  statesFinite := Control.finite
def editConfig (c : TuringMachine.Configuration MachineCodeSymbol DeleteBlock.Control) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .edit c.state
  tape := c.tape
def rewindConfig (c : TuringMachine.Configuration MachineCodeSymbol DeleteEndpointRewind.Control) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewind c.state
  tape := c.tape
theorem edit_step_of_not_halt (cell : Option MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol DeleteBlock.Control) (hnot : c.state ≠ .halt) :
    (machine cell).stepConfig (editConfig c) = Option.map editConfig ((DeleteBlock.machine (DeleteBlock.optionalGap cell)).stepConfig c) := by
  cases c with
  | mk state tape =>
      cases state with
      | erase remaining =>
          unfold TuringMachine.stepConfig
          simp only [editConfig, machine, transition, DeleteBlock.machine]
          cases htransition : DeleteBlock.transition (DeleteBlock.optionalGap cell) (.erase remaining) (Tape.read tape) with
          | none => rfl
          | some action =>
              rcases action with ⟨write, direction, target⟩
              rfl
      | pull =>
          unfold TuringMachine.stepConfig
          simp only [editConfig, machine, transition, DeleteBlock.machine]
          cases htransition : DeleteBlock.transition (DeleteBlock.optionalGap cell) .pull (Tape.read tape) with
          | none => rfl
          | some action =>
              rcases action with ⟨write, direction, target⟩
              rfl
      | returnLeft carried remaining =>
          unfold TuringMachine.stepConfig
          simp only [editConfig, machine, transition, DeleteBlock.machine]
          cases htransition : DeleteBlock.transition (DeleteBlock.optionalGap cell) (.returnLeft carried remaining) (Tape.read tape) with
          | none => rfl
          | some action =>
              rcases action with ⟨write, direction, target⟩
              rfl
      | advance remaining =>
          unfold TuringMachine.stepConfig
          simp only [editConfig, machine, transition, DeleteBlock.machine]
          cases htransition : DeleteBlock.transition (DeleteBlock.optionalGap cell) (.advance remaining) (Tape.read tape) with
          | none => rfl
          | some action =>
              rcases action with ⟨write, direction, target⟩
              rfl
      | halt => contradiction
theorem edit_run_of_eq_some (cell : Option MachineCodeSymbol) (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol DeleteBlock.Control)
    (hrun : (DeleteBlock.machine (DeleteBlock.optionalGap cell)).runConfigExact? steps c = some d) :
    (machine cell).runConfigExact? steps (editConfig c) = some (editConfig d) := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : (DeleteBlock.machine (DeleteBlock.optionalGap cell)).stepConfig c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          have hnot : c.state ≠ DeleteBlock.Control.halt := by
            intro hhalt
            have hnone : (DeleteBlock.machine (DeleteBlock.optionalGap cell)).stepConfig c = none := by
              cases c with
              | mk state tape =>
                  simp only at hhalt
                  subst state
                  rfl
            rw [hnone] at hstep
            contradiction
          rw [edit_step_of_not_halt cell c hnot, hstep]
          simp only [Option.map]
          exact ih next d hrun
theorem edit_run_exact (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    (machine cell).runConfigExact? (DeleteBlock.runSteps cell suffix) (editConfig (DeleteBlock.sourceConfig cell leftRev suffix)) =
      some (editConfig (DeleteBlock.exitConfig cell (List.append suffix.reverse leftRev))) := by exact edit_run_of_eq_some cell _ _ _ (DeleteBlock.run_exact cell leftRev suffix)
theorem halt_retarget_skip_run_exact (cell : Option MachineCodeSymbol) (wordRev : Word MachineCodeSymbol) :
    (machine cell).runConfigExact? (optionalCodeSymbolTag cell + 1) (editConfig (DeleteBlock.exitConfig cell wordRev)) =
      some (rewindConfig (DeleteEndpointRewind.scanConfig wordRev [] cell)) := by
  cases cell with
  | none =>
      cases wordRev <;> rfl
  | some symbol =>
      cases symbol <;> cases wordRev <;> rfl
theorem rewind_scan_step (cell : Option MachineCodeSymbol) (current : MachineCodeSymbol) (remainingRev crossed : Word MachineCodeSymbol) :
    (machine cell).stepConfig (rewindConfig (DeleteEndpointRewind.scanConfig (current :: remainingRev) crossed cell)) =
      some (rewindConfig (DeleteEndpointRewind.scanConfig remainingRev (current :: crossed) cell)) := by cases remainingRev <;> rfl
theorem rewind_scan_finish (cell : Option MachineCodeSymbol) (crossed : Word MachineCodeSymbol) :
    (machine cell).stepConfig (rewindConfig (DeleteEndpointRewind.scanConfig [] crossed cell)) = some (rewindConfig (DeleteEndpointRewind.gateConfig crossed cell)) := by rfl
theorem rewind_scan_run_exact (cell : Option MachineCodeSymbol) (remainingRev crossed : Word MachineCodeSymbol) :
    (machine cell).runConfigExact? (remainingRev.length + 1) (rewindConfig (DeleteEndpointRewind.scanConfig remainingRev crossed cell)) =
      some (rewindConfig (DeleteEndpointRewind.gateConfig (List.append remainingRev.reverse crossed) cell)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact rewind_scan_finish cell crossed
  | cons current remainingRev ih =>
      change (machine cell).runConfigExact? ((remainingRev.length + 1) + 1) (rewindConfig (DeleteEndpointRewind.scanConfig (current :: remainingRev) crossed cell)) = _
      rw [TuringMachine.runConfigExact?, rewind_scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]
theorem runConfigExact?_add (cell : Option MachineCodeSymbol) (first second : Nat) (c : TuringMachine.Configuration MachineCodeSymbol Control) :
    (machine cell).runConfigExact? (first + second) c = match (machine cell).runConfigExact? first c with
      | none => none
      | some middle => (machine cell).runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add, TuringMachine.runConfigExact?, TuringMachine.runConfigExact?]
      cases hstep : (machine cell).stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next
theorem rewind_run_exact (cell : Option MachineCodeSymbol) (wordRev : Word MachineCodeSymbol) :
    (machine cell).runConfigExact? (DeleteEndpointRewind.runSteps cell wordRev) (editConfig (DeleteBlock.exitConfig cell wordRev)) =
      some (rewindConfig (DeleteEndpointRewind.gateConfig wordRev.reverse cell)) := by
  unfold DeleteEndpointRewind.runSteps
  rw [runConfigExact?_add, halt_retarget_skip_run_exact]
  simp only
  simpa using rewind_scan_run_exact cell wordRev ([] : Word MachineCodeSymbol)
def runSteps (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  DeleteBlock.runSteps cell suffix + DeleteEndpointRewind.runSteps cell (List.append suffix.reverse leftRev)
theorem run_exact (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    (machine cell).runConfigExact? (runSteps cell leftRev suffix) (editConfig (DeleteBlock.sourceConfig cell leftRev suffix)) =
      some (rewindConfig (DeleteEndpointRewind.gateConfig (PhysicalBranch.deleteOutput leftRev suffix) cell)) := by
  unfold runSteps
  rw [runConfigExact?_add, edit_run_exact]
  simp only
  rw [rewind_run_exact]
  simp [PhysicalBranch.deleteOutput, List.reverse_append]
end DeleteRestagedMachine
namespace FieldLocator
inductive Boundary where
  | state
  | leftCount
  | leftPayload
deriving DecidableEq
inductive Control where
  | header
  | fuel
  | state
  | leftCount
  | gate
deriving DecidableEq
namespace Control
def elems : List Control := [.header, .fuel, .state, .leftCount, .gate]
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]
end Control
def transition (boundary : Boundary) : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .header, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .fuel)
  | .fuel, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .fuel)
  | .fuel, some MachineCodeSymbol.done =>
      match boundary with
      | .state =>
          some (some MachineCodeSymbol.done, Direction.right, .gate)
      | .leftCount | .leftPayload =>
          some (some MachineCodeSymbol.done, Direction.right, .state)
  | .state, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .state)
  | .state, some MachineCodeSymbol.done =>
      match boundary with
      | .leftCount =>
          some (some MachineCodeSymbol.done, Direction.right, .gate)
      | .leftPayload =>
          some (some MachineCodeSymbol.done, Direction.right, .leftCount)
      | .state => none
  | .leftCount, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .leftCount)
  | .leftCount, some MachineCodeSymbol.done =>
      match boundary with
      | .leftPayload =>
          some (some MachineCodeSymbol.done, Direction.right, .gate)
      | .state | .leftCount => none
  | _, _ => none
def machine (boundary : Boundary) : TuringMachine MachineCodeSymbol Control where
  start := .header
  halt := .gate
  transition := transition boundary
  statesFinite := Control.finite
def config (control : Control) (leftRev rest : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest
def startConfig {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control :=
  config .header [] (Frame.protectedWord L callerData)
theorem header_step (boundary : Boundary) (suffix : Word MachineCodeSymbol) : (machine boundary).stepConfig (config .header [] (MachineCodeSymbol.header :: suffix)) =
      some (config .fuel [MachineCodeSymbol.header] suffix) := by cases suffix <;> rfl
theorem fuel_tick_step (boundary : Boundary) (leftRev suffix : Word MachineCodeSymbol) : (machine boundary).stepConfig (config .fuel leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (config .fuel (MachineCodeSymbol.tick :: leftRev) suffix) := by cases boundary <;> cases suffix <;> rfl
theorem fuel_done_later_step (boundary : Boundary) (hstate : boundary ≠ .state) (leftRev suffix : Word MachineCodeSymbol) :
    (machine boundary).stepConfig (config .fuel leftRev (MachineCodeSymbol.done :: suffix)) = some (config .state (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases boundary with
  | state => contradiction
  | leftCount => cases suffix <;> rfl
  | leftPayload => cases suffix <;> rfl
theorem fuel_run_later (boundary : Boundary) (hstate : boundary ≠ .state) (fuel : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine boundary).runConfigExact? (fuel + 1) (config .fuel leftRev (MachineDescription.encodeNatAppend fuel suffix)) =
      some (config .state (List.append (MachineDescription.encodeNat fuel).reverse leftRev) suffix) := by
  induction fuel generalizing leftRev with
  | zero =>
      have hzeroSuffix : MachineDescription.encodeNatAppend 0 suffix = MachineCodeSymbol.done :: suffix := by
        simp [MachineDescription.encodeNatAppend, MachineDescription.encodeNat]
      have hzeroRev : List.append (MachineDescription.encodeNat 0).reverse leftRev = MachineCodeSymbol.done :: leftRev := by
        simp [MachineDescription.encodeNat]
      rw [hzeroSuffix, hzeroRev, TuringMachine.runConfigExact?, fuel_done_later_step boundary hstate]
      simp only [TuringMachine.runConfigExact?]
  | succ fuel ih =>
      change (machine boundary).runConfigExact? ((fuel + 1) + 1) (config .fuel leftRev (MachineCodeSymbol.tick :: MachineDescription.encodeNatAppend fuel suffix)) = _
      rw [TuringMachine.runConfigExact?, fuel_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]
theorem state_tick_step (boundary : Boundary) (leftRev suffix : Word MachineCodeSymbol) : (machine boundary).stepConfig (config .state leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (config .state (MachineCodeSymbol.tick :: leftRev) suffix) := by cases boundary <;> cases suffix <;> rfl
theorem state_done_leftCount_step (leftRev suffix : Word MachineCodeSymbol) : (machine .leftCount).stepConfig (config .state leftRev (MachineCodeSymbol.done :: suffix)) =
      some (config .gate (MachineCodeSymbol.done :: leftRev) suffix) := by cases suffix <;> rfl
theorem state_done_leftPayload_step (leftRev suffix : Word MachineCodeSymbol) : (machine .leftPayload).stepConfig (config .state leftRev (MachineCodeSymbol.done :: suffix)) =
      some (config .leftCount (MachineCodeSymbol.done :: leftRev) suffix) := by cases suffix <;> rfl
theorem state_run_leftCount (state : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine .leftCount).runConfigExact? (state + 1) (config .state leftRev (MachineDescription.encodeNatAppend state suffix)) =
      some (config .gate (List.append (MachineDescription.encodeNat state).reverse leftRev) suffix) := by
  induction state generalizing leftRev with
  | zero =>
      exact state_done_leftCount_step leftRev suffix
  | succ state ih =>
      change (machine .leftCount).runConfigExact? ((state + 1) + 1) (config .state leftRev (MachineCodeSymbol.tick :: MachineDescription.encodeNatAppend state suffix)) = _
      rw [TuringMachine.runConfigExact?, state_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]
theorem state_run_leftPayload (state : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine .leftPayload).runConfigExact? (state + 1) (config .state leftRev (MachineDescription.encodeNatAppend state suffix)) =
      some (config .leftCount (List.append (MachineDescription.encodeNat state).reverse leftRev) suffix) := by
  induction state generalizing leftRev with
  | zero =>
      exact state_done_leftPayload_step leftRev suffix
  | succ state ih =>
      change (machine .leftPayload).runConfigExact? ((state + 1) + 1) (config .state leftRev (MachineCodeSymbol.tick :: MachineDescription.encodeNatAppend state suffix)) = _
      rw [TuringMachine.runConfigExact?, state_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]
theorem leftCount_tick_step (leftRev suffix : Word MachineCodeSymbol) : (machine .leftPayload).stepConfig (config .leftCount leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (config .leftCount (MachineCodeSymbol.tick :: leftRev) suffix) := by cases suffix <;> rfl
theorem leftCount_done_step (leftRev suffix : Word MachineCodeSymbol) : (machine .leftPayload).stepConfig (config .leftCount leftRev (MachineCodeSymbol.done :: suffix)) =
      some (config .gate (MachineCodeSymbol.done :: leftRev) suffix) := by cases suffix <;> rfl
theorem leftCount_run (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine .leftPayload).runConfigExact? (count + 1) (config .leftCount leftRev (MachineDescription.encodeNatAppend count suffix)) =
      some (config .gate (List.append (MachineDescription.encodeNat count).reverse leftRev) suffix) := by
  induction count generalizing leftRev with
  | zero =>
      exact leftCount_done_step leftRev suffix
  | succ count ih =>
      change (machine .leftPayload).runConfigExact? ((count + 1) + 1) (config .leftCount leftRev (MachineCodeSymbol.tick :: MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?, leftCount_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]
theorem runConfigExact?_add (boundary : Boundary) (first second : Nat) (c : TuringMachine.Configuration MachineCodeSymbol Control) :
    (machine boundary).runConfigExact? (first + second) c = match (machine boundary).runConfigExact? first c with
      | none => none
      | some middle =>
          (machine boundary).runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add, TuringMachine.runConfigExact?, TuringMachine.runConfigExact?]
      cases hstep : (machine boundary).stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next
def leftCountSteps {stateCount : Nat} (L : Layout stateCount) : Nat := 1 + ((L.fuel + 1) + (L.state.val + 1))
def leftPayloadSteps {stateCount : Nat} (L : Layout stateCount) : Nat := 1 + ((L.fuel + 1) + ((L.state.val + 1) + (L.left.length + 1)))
theorem locate_leftCount_exact {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    (machine .leftCount).runConfigExact? (leftCountSteps L) (startConfig L callerData) =
      some (config .gate (LeftPrepend.leftCountPrefix L).reverse (afterStateWord L callerData)) := by
  unfold leftCountSteps startConfig
  have hsource : Frame.protectedWord L callerData = MachineCodeSymbol.header :: MachineDescription.encodeNatAppend L.fuel
            (MachineDescription.encodeNatAppend L.state.val (afterStateWord L callerData)) := by
    rw [protectedWord_eq_statePrefix_stateSuffix]
    simp [statePrefix, stateSuffix, MachineDescription.encodeNatAppend]
  rw [hsource, runConfigExact?_add]
  have hheader : (machine .leftCount).runConfigExact? 1 (config .header [] (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend L.fuel (MachineDescription.encodeNatAppend L.state.val (afterStateWord L callerData)))) =
        some (config .fuel [MachineCodeSymbol.header] (MachineDescription.encodeNatAppend L.fuel (MachineDescription.encodeNatAppend L.state.val
                (afterStateWord L callerData)))) := by
    rw [TuringMachine.runConfigExact?, header_step]
    rfl
  rw [hheader]
  simp only
  rw [runConfigExact?_add, fuel_run_later .leftCount (by decide)]
  simp only
  rw [state_run_leftCount]
  simp [LeftPrepend.leftCountPrefix, MachineDescription.encodeNatAppend, List.reverse_cons, List.reverse_append, List.append_assoc]
theorem locate_leftPayload_exact {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    (machine .leftPayload).runConfigExact? (leftPayloadSteps L) (startConfig L callerData) =
      some (config .gate (LeftPrepend.leftPayloadPrefix L).reverse (LeftPrepend.leftPayloadSuffix L callerData)) := by
  unfold leftPayloadSteps startConfig
  have hsource : Frame.protectedWord L callerData = MachineCodeSymbol.header :: MachineDescription.encodeNatAppend L.fuel
            (MachineDescription.encodeNatAppend L.state.val (MachineDescription.encodeNatAppend L.left.length (LeftPrepend.leftPayloadSuffix L callerData))) := by
    rw [LeftPrepend.protectedWord_decomp]
    simp [LeftPrepend.leftPayloadPrefix, LeftPrepend.leftCountPrefix, MachineDescription.encodeNatAppend, List.append_assoc]
  rw [hsource, runConfigExact?_add]
  have hheader : (machine .leftPayload).runConfigExact? 1 (config .header [] (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend L.fuel (MachineDescription.encodeNatAppend L.state.val
                  (MachineDescription.encodeNatAppend L.left.length (LeftPrepend.leftPayloadSuffix L callerData))))) =
        some (config .fuel [MachineCodeSymbol.header] (MachineDescription.encodeNatAppend L.fuel (MachineDescription.encodeNatAppend L.state.val
                (MachineDescription.encodeNatAppend L.left.length (LeftPrepend.leftPayloadSuffix L callerData))))) := by
    rw [TuringMachine.runConfigExact?, header_step]
    rfl
  rw [hheader]
  simp only
  rw [runConfigExact?_add, fuel_run_later .leftPayload (by decide)]
  simp only
  rw [runConfigExact?_add, state_run_leftPayload]
  simp only
  rw [leftCount_run]
  simp [LeftPrepend.leftPayloadPrefix, LeftPrepend.leftCountPrefix, MachineDescription.encodeNatAppend, List.reverse_cons, List.reverse_append, List.append_assoc]
end FieldLocator
/- A genuinely lifted one-token compaction followed by a physical rewind. -/
namespace DeleteOneRestagedMachine
inductive Control where
  | edit (control : SerializedShift.Delete.Control)
  | rewind (control : RewindWord.Control)
deriving DecidableEq
namespace Control
def elems : List Control := List.append (SerializedShift.Delete.Control.finite.elems.map Control.edit) (RewindWord.Control.finite.elems.map Control.rewind)
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | edit inner =>
        simp [elems]
        exact SerializedShift.Delete.Control.finite.complete inner
    | rewind inner =>
        simp [elems]
        exact RewindWord.Control.finite.complete inner
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .edit .halt, read =>
      match RewindWord.transition .start read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rewind target)
  | .edit inner, read =>
      match SerializedShift.Delete.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .edit target)
  | .rewind inner, read =>
      match RewindWord.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rewind target)
def machine : TuringMachine MachineCodeSymbol Control where
  start := .edit .start
  halt := .rewind .gate
  transition := transition
  statesFinite := Control.finite
def editConfig (c : TuringMachine.Configuration MachineCodeSymbol SerializedShift.Delete.Control) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .edit c.state
  tape := c.tape
def rewindConfig (c : TuringMachine.Configuration MachineCodeSymbol RewindWord.Control) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewind c.state
  tape := c.tape
theorem edit_start_step (leftRev : Word MachineCodeSymbol) (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    machine.stepConfig (editConfig (SerializedShift.Delete.startConfig leftRev deleted suffix)) = some (editConfig (SerializedShift.Delete.pullConfig leftRev suffix)) := by
  cases suffix <;> rfl
theorem edit_pull_three_steps (leftRev : Word MachineCodeSymbol) (current : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 3 (editConfig (SerializedShift.Delete.pullConfig leftRev (current :: suffix))) =
      some (editConfig (SerializedShift.Delete.pullConfig (current :: leftRev) suffix)) := by cases suffix <;> rfl
theorem edit_pull_finish (leftRev : Word MachineCodeSymbol) : machine.runConfigExact? 1 (editConfig (SerializedShift.Delete.pullConfig leftRev [])) =
      some (editConfig (SerializedShift.Delete.exitConfig leftRev)) := by rfl
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
theorem edit_pull_run_exact (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (3 * suffix.length + 1) (editConfig (SerializedShift.Delete.pullConfig leftRev suffix)) = some (editConfig
          (SerializedShift.Delete.exitConfig (List.append suffix.reverse leftRev))) := by
  induction suffix generalizing leftRev with
  | nil =>
      exact edit_pull_finish leftRev
  | cons current suffix ih =>
      rw [show 3 * (current :: suffix).length + 1 = 3 + (3 * suffix.length + 1) by
        simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm]]
      rw [runConfigExact?_add, edit_pull_three_steps]
      simp only
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]
theorem edit_run_exact (leftRev : Word MachineCodeSymbol) (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (3 * suffix.length + 2) (editConfig (SerializedShift.Delete.startConfig leftRev deleted suffix)) =
      some (editConfig (SerializedShift.Delete.exitConfig (List.append suffix.reverse leftRev))) := by
  change machine.runConfigExact? ((3 * suffix.length + 1) + 1) (editConfig (SerializedShift.Delete.startConfig leftRev deleted suffix)) = _
  rw [TuringMachine.runConfigExact?, edit_start_step]
  simp only
  exact edit_pull_run_exact leftRev suffix
theorem halt_retarget_step (wordRev : Word MachineCodeSymbol) : machine.stepConfig (editConfig (SerializedShift.Delete.exitConfig wordRev)) =
      some (rewindConfig (RewindWord.scanConfig wordRev [] 1)) := by cases wordRev <;> rfl
theorem rewind_scan_step (current : MachineCodeSymbol) (remainingRev crossed : Word MachineCodeSymbol) :
    machine.stepConfig (rewindConfig (RewindWord.scanConfig (current :: remainingRev) crossed 1)) =
      some (rewindConfig (RewindWord.scanConfig remainingRev (current :: crossed) 1)) := by cases remainingRev <;> rfl
theorem rewind_scan_finish (crossed : Word MachineCodeSymbol) : machine.stepConfig (rewindConfig (RewindWord.scanConfig [] crossed 1)) =
      some (rewindConfig (RewindWord.gateConfig crossed 1)) := by cases crossed <;> rfl
theorem rewind_scan_run_exact (remainingRev crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? (remainingRev.length + 1) (rewindConfig (RewindWord.scanConfig remainingRev crossed 1)) =
      some (rewindConfig (RewindWord.gateConfig (List.append remainingRev.reverse crossed) 1)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact rewind_scan_finish crossed
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1) (rewindConfig (RewindWord.scanConfig (current :: remainingRev) crossed 1)) = _
      rw [TuringMachine.runConfigExact?, rewind_scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]
theorem rewind_run_exact (wordRev : Word MachineCodeSymbol) : machine.runConfigExact? (wordRev.length + 2) (editConfig (SerializedShift.Delete.exitConfig wordRev)) =
      some (rewindConfig (RewindWord.gateConfig wordRev.reverse 1)) := by
  change machine.runConfigExact? ((wordRev.length + 1) + 1) (editConfig (SerializedShift.Delete.exitConfig wordRev)) = _
  rw [TuringMachine.runConfigExact?, halt_retarget_step]
  simp only
  simpa using rewind_scan_run_exact wordRev ([] : Word MachineCodeSymbol)
def output (leftRev suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol := List.append leftRev.reverse suffix
def runSteps (leftRev suffix : Word MachineCodeSymbol) : Nat := (3 * suffix.length + 2) + ((List.append suffix.reverse leftRev).length + 2)
theorem run_exact (leftRev : Word MachineCodeSymbol) (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps leftRev suffix) (editConfig (SerializedShift.Delete.startConfig leftRev deleted suffix)) =
      some (rewindConfig (RewindWord.gateConfig (output leftRev suffix) 1)) := by
  unfold runSteps
  rw [runConfigExact?_add, edit_run_exact]
  simp only
  rw [rewind_run_exact]
  simp [output, List.reverse_append]
end DeleteOneRestagedMachine
/- Exact fuel decrement, including the header locator and padded rewind. -/
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
