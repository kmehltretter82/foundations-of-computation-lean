import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Contextual.Prefix

set_option doc.verso true

/-!
# Contextual product raw-tail materialization

Generalize the raw-tail loop's physical deep-left cells while reusing its
existing finite transition table.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductContextual

namespace Raw

def leftContextCells
    (remainingRev : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    List (Option MachineCodeSymbol) :=
  List.append (remainingRev.map some) (none :: deepLeft)

def gateConfigCells
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.RawTailLoopMachine.Control :=
  InitialMaterializer.RawTailLoopMachine.loopConfig
    (InitialMaterializer.OneCellMachine.rewindConfig
      (InitialMaterializer.SeparatorRewind.gateConfigCells
        (leftContextCells remainingRev deepLeft)
        (InitialMaterializer.NonemptyRightRegion.region processed)))

def restartConfigCells
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.RawTailLoopMachine.Control where
  state := .restart
  tape :=
    { left := leftContextCells remainingRev deepLeft
      head := none
      right := List.append
        ((InitialMaterializer.NonemptyRightRegion.region processed).map some)
        [none] }

def paddedIterationSourceConfigCells
    (current : MachineCodeSymbol)
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.RawTailLoopMachine.Control :=
  InitialMaterializer.RawTailLoopMachine.loopConfig
    { state := .prep .start
      tape := InitialMaterializer.SeparatorRewind.gateTapeCells
        (some current :: leftContextCells remainingRev deepLeft)
        (InitialMaterializer.NonemptyRightRegion.region processed) }

def emptyStartConfigCells
    (processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.RawTailLoopMachine.Control where
  state := .loop (.prep .start)
  tape := InitialMaterializer.SeparatorRewind.gateTapeCells
    (none :: deepLeft)
    (InitialMaterializer.NonemptyRightRegion.region processed)

def doneConfigCells
    (processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.RawTailLoopMachine.Control where
  state := .done
  tape := InitialMaterializer.SeparatorRewind.gateTapeCells
    (none :: deepLeft)
    (InitialMaterializer.NonemptyRightRegion.region processed)

theorem gate_restart_step_cells
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    InitialMaterializer.RawTailLoopMachine.machine.stepConfig
        (gateConfigCells remainingRev processed deepLeft) =
      some (restartConfigCells remainingRev processed deepLeft) := by
  cases hregion : InitialMaterializer.NonemptyRightRegion.region processed <;>
    simp [TuringMachine.stepConfig,
      InitialMaterializer.RawTailLoopMachine.machine,
      InitialMaterializer.RawTailLoopMachine.transition,
      gateConfigCells, restartConfigCells, leftContextCells,
      InitialMaterializer.RawTailLoopMachine.loopConfig,
      InitialMaterializer.OneCellMachine.rewindConfig,
      InitialMaterializer.SeparatorRewind.gateConfigCells,
      InitialMaterializer.SeparatorRewind.gateTapeCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, hregion]

theorem restart_iteration_step_of_cons_cells
    (current : MachineCodeSymbol)
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    InitialMaterializer.RawTailLoopMachine.machine.stepConfig
        (restartConfigCells (current :: remainingRev) processed deepLeft) =
      some (paddedIterationSourceConfigCells current remainingRev processed
        deepLeft) := by
  cases hregion : InitialMaterializer.NonemptyRightRegion.region processed <;>
    simp [TuringMachine.stepConfig,
      InitialMaterializer.RawTailLoopMachine.machine,
      InitialMaterializer.RawTailLoopMachine.transition,
      restartConfigCells, paddedIterationSourceConfigCells,
      leftContextCells,
      InitialMaterializer.RawTailLoopMachine.loopConfig,
      InitialMaterializer.SeparatorRewind.gateTapeCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight, hregion]

theorem paddedIterationSource_equiv_clean_cells
    (current : MachineCodeSymbol)
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    Tape.Equiv
      (paddedIterationSourceConfigCells current remainingRev processed
        deepLeft).tape
      (InitialMaterializer.RawTailLoopMachine.loopConfig
        (InitialMaterializer.OneCellMachine.sourceConfig current processed
          (leftContextCells remainingRev deepLeft))).tape := by
  have hnonempty :=
    InitialMaterializer.NonemptyRightRegion.region_ne_nil processed
  cases hregion : InitialMaterializer.NonemptyRightRegion.region processed with
  | nil => contradiction
  | cons first regionRest =>
      unfold paddedIterationSourceConfigCells
        InitialMaterializer.RawTailLoopMachine.loopConfig
      unfold InitialMaterializer.OneCellMachine.sourceConfig
        InitialMaterializer.OneCellMachine.prepConfig
      unfold InitialMaterializer.RightCellPrep.sourceConfig
      rw [hregion]
      simp [InitialMaterializer.SeparatorRewind.gateTapeCells,
        InitialMaterializer.InsertOneWithBoundary.cursorTape,
        Tape.Equiv, dropTrailingNone_append_none]

theorem clean_iteration_run_exact_cells
    (current : MachineCodeSymbol)
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    InitialMaterializer.RawTailLoopMachine.machine.runConfigExact?
        (InitialMaterializer.OneCellMachine.runSteps current processed)
        (InitialMaterializer.RawTailLoopMachine.loopConfig
          (InitialMaterializer.OneCellMachine.sourceConfig current processed
            (leftContextCells remainingRev deepLeft))) =
      some (gateConfigCells remainingRev (current :: processed) deepLeft) := by
  simpa [gateConfigCells,
      InitialMaterializer.OneCellMachine.endpointConfig] using
    InitialMaterializer.RawTailLoopMachine.loop_run_of_eq_some
      (InitialMaterializer.OneCellMachine.runSteps current processed)
      (InitialMaterializer.OneCellMachine.sourceConfig current processed
        (leftContextCells remainingRev deepLeft))
      (InitialMaterializer.OneCellMachine.endpointConfig current processed
        (leftContextCells remainingRev deepLeft))
      (InitialMaterializer.OneCellMachine.run_exact current processed
        (leftContextCells remainingRev deepLeft))

theorem padded_iteration_run_exact_cells
    (current : MachineCodeSymbol)
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    exists paddedEndpoint : TuringMachine.Configuration MachineCodeSymbol
        InitialMaterializer.RawTailLoopMachine.Control,
      InitialMaterializer.RawTailLoopMachine.machine.runConfigExact?
          (InitialMaterializer.OneCellMachine.runSteps current processed)
          (paddedIterationSourceConfigCells current remainingRev processed
            deepLeft) =
        some paddedEndpoint ∧
      (gateConfigCells remainingRev (current :: processed) deepLeft).state =
        paddedEndpoint.state ∧
      Tape.Equiv
        (gateConfigCells remainingRev (current :: processed) deepLeft).tape
        paddedEndpoint.tape := by
  exact InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
    (clean := InitialMaterializer.RawTailLoopMachine.loopConfig
      (InitialMaterializer.OneCellMachine.sourceConfig current processed
        (leftContextCells remainingRev deepLeft)))
    (padded := paddedIterationSourceConfigCells current remainingRev processed
      deepLeft)
    (cleanFinal := gateConfigCells remainingRev (current :: processed)
      deepLeft)
    InitialMaterializer.RawTailLoopMachine.machine
    (InitialMaterializer.OneCellMachine.runSteps current processed)
    rfl
    (Tape.Equiv.symm
      (paddedIterationSource_equiv_clean_cells current remainingRev processed
        deepLeft))
    (clean_iteration_run_exact_cells current remainingRev processed deepLeft)

theorem restart_empty_step_cells
    (processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    InitialMaterializer.RawTailLoopMachine.machine.stepConfig
        (restartConfigCells [] processed deepLeft) =
      some (emptyStartConfigCells processed deepLeft) := by
  cases hregion : InitialMaterializer.NonemptyRightRegion.region processed <;>
    simp [TuringMachine.stepConfig,
      InitialMaterializer.RawTailLoopMachine.machine,
      InitialMaterializer.RawTailLoopMachine.transition,
      restartConfigCells, emptyStartConfigCells, leftContextCells,
      InitialMaterializer.SeparatorRewind.gateTapeCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight, hregion]

theorem empty_finish_run_exact_cells
    (processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    InitialMaterializer.RawTailLoopMachine.machine.runConfigExact? 4
        (emptyStartConfigCells processed deepLeft) =
      some (doneConfigCells processed deepLeft) := by
  have hnonempty :=
    InitialMaterializer.NonemptyRightRegion.region_ne_nil processed
  cases hregion : InitialMaterializer.NonemptyRightRegion.region processed with
  | nil => contradiction
  | cons first rest =>
      cases rest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          InitialMaterializer.RawTailLoopMachine.machine,
          InitialMaterializer.RawTailLoopMachine.transition,
          emptyStartConfigCells, doneConfigCells,
          InitialMaterializer.OneCellMachine.transition,
          InitialMaterializer.RightCellPrep.transition,
          InitialMaterializer.SeparatorRewind.gateTapeCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          hregion]

theorem run_to_done_equiv_cells
    (remainingRev processed : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          InitialMaterializer.RawTailLoopMachine.Control),
      InitialMaterializer.RawTailLoopMachine.machine.runConfigExact? steps
          (gateConfigCells remainingRev processed deepLeft) =
        some endpoint ∧
      (doneConfigCells (List.append remainingRev.reverse processed)
        deepLeft).state = endpoint.state ∧
      Tape.Equiv
        (doneConfigCells (List.append remainingRev.reverse processed)
          deepLeft).tape
        endpoint.tape := by
  induction remainingRev generalizing processed with
  | nil =>
      refine ⟨6, doneConfigCells processed deepLeft, ?_, rfl,
        Tape.Equiv.refl _⟩
      change
        InitialMaterializer.RawTailLoopMachine.machine.runConfigExact?
            (1 + (1 + 4)) (gateConfigCells [] processed deepLeft) = _
      rw [TuringMachine.runConfigExact?]
      rw [gate_restart_step_cells]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [restart_empty_step_cells]
      simp only
      exact empty_finish_run_exact_cells processed deepLeft
  | cons current remainingRev ih =>
      rcases padded_iteration_run_exact_cells current remainingRev processed
          deepLeft with
        ⟨cellEndpoint, hcellRun, hcellState, hcellTape⟩
      rcases ih (current :: processed) with
        ⟨restSteps, restEndpoint, hrestRun, hrestState, hrestTape⟩
      rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
          (clean := gateConfigCells remainingRev (current :: processed)
            deepLeft)
          (padded := cellEndpoint)
          (cleanFinal := restEndpoint)
          InitialMaterializer.RawTailLoopMachine.machine restSteps
          hcellState hcellTape hrestRun with
        ⟨actualEndpoint, hactualRun, hactualState, hactualTape⟩
      refine
        ⟨(InitialMaterializer.OneCellMachine.runSteps current processed +
            restSteps) + 2,
          actualEndpoint, ?_, ?_, ?_⟩
      · rw [TuringMachine.runConfigExact?]
        rw [gate_restart_step_cells]
        simp only
        rw [TuringMachine.runConfigExact?]
        rw [restart_iteration_step_of_cons_cells]
        simp only
        rw [InitialMaterializer.ExactRun.append]
        rw [hcellRun]
        simp only
        exact hactualRun
      · have htarget :
            doneConfigCells
                (List.append (current :: remainingRev).reverse processed)
                deepLeft =
              doneConfigCells
                (List.append remainingRev.reverse (current :: processed))
                deepLeft := by
          simp [List.reverse_cons, List.append_assoc]
        rw [htarget]
        exact hrestState.trans hactualState
      · have htarget :
            doneConfigCells
                (List.append (current :: remainingRev).reverse processed)
                deepLeft =
              doneConfigCells
                (List.append remainingRev.reverse (current :: processed))
                deepLeft := by
          simp [List.reverse_cons, List.append_assoc]
        rw [htarget]
        exact Tape.Equiv.trans hrestTape hactualTape

def gateConfig
    (outerRev remainingRev processed fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.RawTailLoopMachine.Control :=
  gateConfigCells remainingRev processed
    (List.append (fuelRev.map some) (none :: outerRev.map some))

def doneConfig
    (outerRev processed fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.RawTailLoopMachine.Control :=
  doneConfigCells processed
    (List.append (fuelRev.map some) (none :: outerRev.map some))

theorem run_to_done_equiv
    (outerRev remainingRev processed fuelRev : Word MachineCodeSymbol) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          InitialMaterializer.RawTailLoopMachine.Control),
      InitialMaterializer.RawTailLoopMachine.machine.runConfigExact? steps
          (gateConfig outerRev remainingRev processed fuelRev) =
        some endpoint ∧
      (doneConfig outerRev
        (List.append remainingRev.reverse processed) fuelRev).state =
        endpoint.state ∧
      Tape.Equiv
        (doneConfig outerRev
          (List.append remainingRev.reverse processed) fuelRev).tape
        endpoint.tape := by
  exact run_to_done_equiv_cells remainingRev processed
    (List.append (fuelRev.map some) (none :: outerRev.map some))

end Raw

end ProductContextual
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

