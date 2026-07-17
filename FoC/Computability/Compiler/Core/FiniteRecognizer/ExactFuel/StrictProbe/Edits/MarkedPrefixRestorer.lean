import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.RightFirstCell
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Marked-prefix restoration

Finite restoration of the marked left/head prefix after removing the first
serialized right cell, followed by correction of the stale right count.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Edits.MarkedPrefixRestorer

open Languages

open SerializedFieldComposer
open Dispatch.RightFieldLocator
open Dispatch.RightFirstCell

def markedPrefix {stateCount : Nat}
    (L : Layout stateCount) : Word MachineCodeSymbol :=
  List.append (statePrefix L)
    (List.append (MachineDescription.encodeNat L.state.val)
      (List.append (HeadLocator.transitionMarkers L.left.length)
        (MachineCodeSymbol.blank ::
          List.append (HeadLocator.markedCellsWord L.left)
            (optionalCellWord L.head))))

def markedDeletedWord {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  PhysicalBranch.deleteOutput (markedRightPayloadLeftRev L)
    (MoveRightNonempty.afterFirstRightCell remainingRight callerData)

theorem transitionMarkers_reverse (count : Nat) :
    (HeadLocator.transitionMarkers count).reverse =
      HeadLocator.transitionMarkers count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change
        (MachineCodeSymbol.transition ::
          HeadLocator.transitionMarkers count).reverse =
        MachineCodeSymbol.transition ::
          HeadLocator.transitionMarkers count
      rw [List.reverse_cons, ih]
      simpa using HeadLocator.transitionMarkers_append_transition
        count ([] : Word MachineCodeSymbol)

theorem markedDeletedWord_decomp {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    markedDeletedWord L remainingRight callerData =
      List.append (markedPrefix L)
        (MachineDescription.encodeNatAppend L.right.length
          (MoveRightNonempty.afterFirstRightCell
            remainingRight callerData)) := by
  unfold markedDeletedWord PhysicalBranch.deleteOutput
    markedRightPayloadLeftRev markedRightCountLeftRev
    HeadDecoder.markedCountBaseLeftRev markedPrefix
    HeadLocator.countBaseLeftRev HeadLocator.topFieldsRev
    statePrefix
  simp [List.reverse_append, HeadLocator.ticks_reverse,
    transitionMarkers_reverse,
    HeadLocator.encodeNat_eq_ticks_done,
    HeadLocator.encodeNatAppend_eq_ticks_done_append,
    List.append_assoc]

inductive Control where
  | header
  | fuel
  | state
  | restoreCount
  | restoreCells
  | gate
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.header, .fuel, .state, .restoreCount, .restoreCells, .gate]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .header, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .fuel)
  | .fuel, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .fuel)
  | .fuel, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .state)
  | .state, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .state)
  | .state, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .restoreCount)
  | .restoreCount, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.tick, Direction.right, .restoreCount)
  | .restoreCount, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.done, Direction.right, .restoreCells)
  | .restoreCells, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .restoreCells)
  | .restoreCells, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.done, Direction.right, .restoreCells)
  | .restoreCells, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .gate)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .header
  halt := .gate
  transition := transition
  statesFinite := Control.finite

def config (control : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest

def sourceConfig {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .header [] (markedDeletedWord L remainingRight callerData)

def gateConfig {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .gate (RightPrepend.rightCountPrefix L).reverse
    (MachineDescription.encodeNatAppend L.right.length
      (MoveRightNonempty.afterFirstRightCell remainingRight callerData))

theorem header_step
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .header [] (MachineCodeSymbol.header :: suffix)) =
      some (config .fuel [MachineCodeSymbol.header] suffix) := by
  cases suffix <;> rfl

theorem fuel_tick_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .fuel leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (config .fuel (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem fuel_done_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .fuel leftRev (MachineCodeSymbol.done :: suffix)) =
      some (config .state (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem fuel_run_exact
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1)
        (config .fuel leftRev
          (MachineDescription.encodeNatAppend count suffix)) =
      some
        (config .state
          (List.append (MachineDescription.encodeNat count).reverse leftRev)
          suffix) := by
  induction count generalizing leftRev with
  | zero => exact fuel_done_step leftRev suffix
  | succ count ih =>
      change
        machine.runConfigExact? ((count + 1) + 1)
            (config .fuel leftRev
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [fuel_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem state_tick_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .state leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (config .state (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem state_done_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .state leftRev (MachineCodeSymbol.done :: suffix)) =
      some
        (config .restoreCount (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem state_run_exact
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1)
        (config .state leftRev
          (MachineDescription.encodeNatAppend count suffix)) =
      some
        (config .restoreCount
          (List.append (MachineDescription.encodeNat count).reverse leftRev)
          suffix) := by
  induction count generalizing leftRev with
  | zero => exact state_done_step leftRev suffix
  | succ count ih =>
      change
        machine.runConfigExact? ((count + 1) + 1)
            (config .state leftRev
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [state_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem restoreCount_marker_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .restoreCount leftRev
          (MachineCodeSymbol.transition :: suffix)) =
      some
        (config .restoreCount (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem restoreCount_blank_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .restoreCount leftRev
          (MachineCodeSymbol.blank :: suffix)) =
      some
        (config .restoreCells (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem restoreCount_run_exact
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1)
        (config .restoreCount leftRev
          (List.append (HeadLocator.transitionMarkers count)
            (MachineCodeSymbol.blank :: suffix))) =
      some
        (config .restoreCells
          (List.append (MachineDescription.encodeNat count).reverse leftRev)
          suffix) := by
  induction count generalizing leftRev with
  | zero => exact restoreCount_blank_step leftRev suffix
  | succ count ih =>
      change
        machine.runConfigExact? ((count + 1) + 1)
            (config .restoreCount leftRev
              (MachineCodeSymbol.transition ::
                List.append (HeadLocator.transitionMarkers count)
                  (MachineCodeSymbol.blank :: suffix))) = _
      rw [TuringMachine.runConfigExact?]
      rw [restoreCount_marker_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem restoreMarkedCell_run_exact
    (cell : Option MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.markedCellWord cell).length
        (config .restoreCells leftRev
          (List.append (HeadLocator.markedCellWord cell) suffix)) =
      some
        (config .restoreCells
          (List.append (optionalCellWord cell).reverse leftRev) suffix) := by
  cases cell with
  | none => cases suffix <;> rfl
  | some symbol => cases symbol <;> cases suffix <;> rfl

theorem restoreMarkedCells_run_exact
    (cells : List (Option MachineCodeSymbol))
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.markedCellsWord cells).length
        (config .restoreCells leftRev
          (List.append (HeadLocator.markedCellsWord cells) suffix)) =
      some
        (config .restoreCells
          (List.append (HeadLocator.cellsPayloadWord cells).reverse leftRev)
          suffix) := by
  induction cells generalizing leftRev with
  | nil => rfl
  | cons cell cells ih =>
      rw [HeadLocator.markedCellsWord_cons]
      rw [HeadLocator.cellsPayloadWord]
      have hlength :
          (List.append (HeadLocator.markedCellWord cell)
            (HeadLocator.markedCellsWord cells) :
              Word MachineCodeSymbol).length =
            (HeadLocator.markedCellWord cell).length +
              (HeadLocator.markedCellsWord cells).length :=
        List.length_append
      rw [hlength]
      rw [TuringMachine.runConfigExact?_add]
      have hassoc :
          List.append
              (List.append (HeadLocator.markedCellWord cell)
                (HeadLocator.markedCellsWord cells)) suffix =
            List.append (HeadLocator.markedCellWord cell)
              (List.append (HeadLocator.markedCellsWord cells) suffix) :=
        List.append_assoc _ _ _
      rw [hassoc]
      rw [restoreMarkedCell_run_exact]
      simp only
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

theorem restoreHead_run_exact
    (head : Option MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (optionalCodeSymbolTag head + 1)
        (config .restoreCells leftRev
          (List.append (optionalCellWord head) suffix)) =
      some
        (config .gate
          (List.append (optionalCellWord head).reverse leftRev) suffix) := by
  cases head with
  | none => cases suffix <;> rfl
  | some symbol => cases symbol <;> cases suffix <;> rfl

theorem markedDeletedWord_eq_fields {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    markedDeletedWord L remainingRight callerData =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend L.fuel
          (MachineDescription.encodeNatAppend L.state.val
            (List.append (HeadLocator.transitionMarkers L.left.length)
              (MachineCodeSymbol.blank ::
                List.append (HeadLocator.markedCellsWord L.left)
                  (List.append (optionalCellWord L.head)
                    (MachineDescription.encodeNatAppend L.right.length
                      (MoveRightNonempty.afterFirstRightCell
                        remainingRight callerData)))))) := by
  rw [markedDeletedWord_decomp]
  simp [markedPrefix, statePrefix,
    MachineDescription.encodeNatAppend, List.append_assoc]

theorem optionalCellsWord_eq_count_payload
    (cells : List (Option MachineCodeSymbol)) :
    optionalCellsWord cells =
      List.append (MachineDescription.encodeNat cells.length)
        (HeadLocator.cellsPayloadWord cells) := by
  simp [optionalCellsWord, encodeOptionalCodeSymbolsAppend,
    MachineDescription.encodeNatAppend,
    HeadLocator.cellsPayloadWord_eq_encode]

theorem restoredPrefix_reverse_eq_rightCountPrefix {stateCount : Nat}
    (L : Layout stateCount) :
    List.append (optionalCellWord L.head).reverse
        (List.append (HeadLocator.cellsPayloadWord L.left).reverse
          (List.append (MachineDescription.encodeNat L.left.length).reverse
            (List.append
              (MachineDescription.encodeNat L.state.val).reverse
              (statePrefix L).reverse))) =
      (RightPrepend.rightCountPrefix L).reverse := by
  unfold RightPrepend.rightCountPrefix headPrefix
  rw [optionalCellsWord_eq_count_payload]
  simp [List.reverse_append, List.append_assoc]

def runSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  1 + ((L.fuel + 1) +
    ((L.state.val + 1) +
      ((L.left.length + 1) +
        ((HeadLocator.markedCellsWord L.left).length +
          (optionalCodeSymbolTag L.head + 1)))))

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps L)
        (sourceConfig L remainingRight callerData) =
      some (gateConfig L remainingRight callerData) := by
  unfold runSteps sourceConfig gateConfig
  rw [markedDeletedWord_eq_fields]
  rw [TuringMachine.runConfigExact?_add]
  have hheader :
      machine.runConfigExact? 1
          (config .header []
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend L.fuel
                (MachineDescription.encodeNatAppend L.state.val
                  (List.append
                    (HeadLocator.transitionMarkers L.left.length)
                    (MachineCodeSymbol.blank ::
                      List.append (HeadLocator.markedCellsWord L.left)
                        (List.append (optionalCellWord L.head)
                          (MachineDescription.encodeNatAppend L.right.length
                            (MoveRightNonempty.afterFirstRightCell
                              remainingRight callerData)))))))) =
        some
          (config .fuel [MachineCodeSymbol.header]
            (MachineDescription.encodeNatAppend L.fuel
              (MachineDescription.encodeNatAppend L.state.val
                (List.append
                  (HeadLocator.transitionMarkers L.left.length)
                  (MachineCodeSymbol.blank ::
                    List.append (HeadLocator.markedCellsWord L.left)
                      (List.append (optionalCellWord L.head)
                        (MachineDescription.encodeNatAppend L.right.length
                          (MoveRightNonempty.afterFirstRightCell
                            remainingRight callerData)))))))) := by
    rw [TuringMachine.runConfigExact?]
    rw [header_step]
    rfl
  rw [hheader]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [fuel_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [state_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [restoreCount_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [restoreMarkedCells_run_exact]
  simp only
  rw [restoreHead_run_exact]
  have hprefix :
      List.append (optionalCellWord L.head).reverse
          (List.append (HeadLocator.cellsPayloadWord L.left).reverse
            (List.append
              (MachineDescription.encodeNat L.left.length).reverse
              (List.append
                (MachineDescription.encodeNat L.state.val).reverse
                (List.append
                  (MachineDescription.encodeNat L.fuel).reverse
                  [MachineCodeSymbol.header])))) =
        (RightPrepend.rightCountPrefix L).reverse := by
    simpa [statePrefix, List.reverse_cons, List.append_assoc] using
      restoredPrefix_reverse_eq_rightCountPrefix L
  rw [hprefix]

/-- The delete rewind leaves only trailing blank-window padding.  The forward
restorer therefore runs for the same exact number of steps on that physical
endpoint and reaches an equivalent stale-right-count cursor. -/
theorem run_exact_from_deleteGate {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      machine.runConfigExact? (runSteps L)
          { state := Control.header
            tape :=
              (deleteGateConfig L nextHead remainingRight callerData).tape } =
        some endpoint ∧
      endpoint.state = Control.gate ∧
      Tape.Equiv (gateConfig L remainingRight callerData).tape
        endpoint.tape := by
  have hsourceInput :
      (sourceConfig L remainingRight callerData).tape =
        Tape.input (markedDeletedWord L remainingRight callerData) := by
    unfold sourceConfig config
    cases markedDeletedWord L remainingRight callerData <;> rfl
  have hdeleteInput :
      Tape.Equiv
        (deleteGateConfig L nextHead remainingRight callerData).tape
        (Tape.input (markedDeletedWord L remainingRight callerData)) := by
    exact DeleteEndpointRewind.gateTape_equiv_input
      (markedDeletedWord L remainingRight callerData) nextHead
  have hequiv :
      Tape.Equiv (sourceConfig L remainingRight callerData).tape
        (deleteGateConfig L nextHead remainingRight callerData).tape := by
    rw [hsourceInput]
    exact Tape.Equiv.symm hdeleteInput
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (run_exact L remainingRight callerData) hequiv with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨endpoint, hrun, hstate, htape⟩

namespace CountDecrement

def suffix
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MoveRightNonempty.afterCountTick remainingRight callerData

theorem staleCount_decomp {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (hright : L.right = nextHead :: remainingRight) :
    MachineDescription.encodeNatAppend L.right.length
        (MoveRightNonempty.afterFirstRightCell remainingRight callerData) =
      MachineCodeSymbol.tick :: suffix remainingRight callerData := by
  unfold suffix MoveRightNonempty.afterCountTick
  rw [hright]
  rfl

def sourceConfig {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.editConfig
    (DeleteBlock.oneSourceConfig MachineCodeSymbol.tick
      (RightPrepend.rightCountPrefix L).reverse
      (suffix remainingRight callerData))

def targetConfig {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.rewindConfig
    (DeleteEndpointRewind.gateConfig
      (Frame.protectedWord
        (MoveRightNonempty.removedRightLayout L remainingRight)
        callerData)
      none)

def runSteps {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Nat :=
  DeleteBlock.runOneSteps (suffix remainingRight callerData) +
    DeleteEndpointRewind.runSteps none
      (List.append (suffix remainingRight callerData).reverse
        (RightPrepend.rightCountPrefix L).reverse)

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact?
        (runSteps L remainingRight callerData)
        (sourceConfig L remainingRight callerData) =
      some (targetConfig L remainingRight callerData) := by
  unfold runSteps sourceConfig targetConfig
  rw [TuringMachine.runConfigExact?_add]
  rw [DeleteRestagedMachine.edit_run_of_eq_some none _ _ _
    (DeleteBlock.run_one_exact MachineCodeSymbol.tick
      (RightPrepend.rightCountPrefix L).reverse
      (suffix remainingRight callerData))]
  simp only
  rw [DeleteRestagedMachine.rewind_run_exact]
  have hword := PhysicalBranch.decrementRight_output_eq_protectedWord
    L remainingRight callerData
  have hout :
      (List.append (suffix remainingRight callerData).reverse
        (RightPrepend.rightCountPrefix L).reverse :
          Word MachineCodeSymbol).reverse =
        Frame.protectedWord
          (MoveRightNonempty.removedRightLayout L remainingRight)
          callerData := by
    calc
      (List.append (suffix remainingRight callerData).reverse
          (RightPrepend.rightCountPrefix L).reverse :
            Word MachineCodeSymbol).reverse =
          PhysicalBranch.deleteOutput
            (RightPrepend.rightCountPrefix L).reverse
            (suffix remainingRight callerData) := by
              unfold PhysicalBranch.deleteOutput
              simp [List.reverse_append]
      _ = Frame.protectedWord
          (MoveRightNonempty.removedRightLayout L remainingRight)
          callerData := by
            simpa only [suffix] using hword
  rw [hout]

theorem source_tape_eq_restoreGate {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (hright : L.right = nextHead :: remainingRight) :
    (sourceConfig L remainingRight callerData).tape =
      (MarkedPrefixRestorer.gateConfig
        L remainingRight callerData).tape := by
  unfold sourceConfig DeleteRestagedMachine.editConfig
    DeleteBlock.oneSourceConfig MarkedPrefixRestorer.gateConfig
  rw [staleCount_decomp L nextHead remainingRight callerData hright]
  rfl

/-- Count correction also tolerates the padding left by the preceding
restoration transport. -/
theorem run_exact_of_tape_equiv {stateCount : Nat}
    (L : Layout stateCount)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol)
    (hequiv : Tape.Equiv
      (sourceConfig L remainingRight callerData).tape T) :
    exists endpoint,
      (DeleteRestagedMachine.machine none).runConfigExact?
          (runSteps L remainingRight callerData)
          { state := (sourceConfig L remainingRight callerData).state
            tape := T } = some endpoint ∧
      endpoint.state = (targetConfig L remainingRight callerData).state ∧
      Tape.Equiv (targetConfig L remainingRight callerData).tape
        endpoint.tape := by
  exact
    TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      (run_exact L remainingRight callerData) hequiv

end CountDecrement

end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Edits.MarkedPrefixRestorer
