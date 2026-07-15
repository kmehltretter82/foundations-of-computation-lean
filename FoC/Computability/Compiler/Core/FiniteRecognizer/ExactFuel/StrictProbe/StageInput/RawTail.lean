import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Insertion

/-!
# Exact-fuel stage-input raw-tail materialization

Iteration over the raw input tail and the fixed-prefix insertion endpoint for
nonempty canonical stage inputs.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace InitialMaterializer

namespace RawTailLoopMachine

inductive Control where
  | loop (control : OneCellMachine.Control)
  | restart
  | finishReturn
  | done
deriving DecidableEq

namespace Control
def elems : List Control :=
  List.append (OneCellMachine.Control.finite.elems.map Control.loop) [.restart, .finishReturn, .done]
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | loop inner =>
        simp [elems]
        exact OneCellMachine.Control.finite.complete inner
    | restart => simp [elems]
    | finishReturn => simp [elems]
    | done => simp [elems]
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .loop (.rewind .gate), cell =>
      some (cell, Direction.left, .restart)
  | .restart, none =>
      some (none, Direction.right, .loop (.prep .start))
  | .loop (.prep .candidate), none =>
      some (none, Direction.right, .finishReturn)
  | .finishReturn, none =>
      some (none, Direction.right, .done)
  | .loop inner, cell =>
      match OneCellMachine.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .loop target)
  | _, _ => none
def machine : TuringMachine MachineCodeSymbol Control where
  start := .loop (.rewind .gate)
  halt := .done
  transition := transition
  statesFinite := Control.finite
def loopConfig (c : TuringMachine.Configuration MachineCodeSymbol OneCellMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .loop c.state
  tape := c.tape
def gateConfig (remainingRev processed fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  loopConfig (OneCellMachine.rewindConfig (SeparatorRewind.gateConfigCells
        (List.append (remainingRev.map some) (none :: fuelRev.map some)) (NonemptyRightRegion.region processed)))
def restartConfig (remainingRev processed fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .restart
  tape :=
    { left := List.append (remainingRev.map some) (none :: fuelRev.map some)
      head := none
      right := List.append ((NonemptyRightRegion.region processed).map some) [none] }
def paddedIterationSourceConfig (current : MachineCodeSymbol)
    (remainingRev processed fuelRev : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control :=
  loopConfig
    { state := .prep .start
      tape := SeparatorRewind.gateTapeCells (some current :: List.append (remainingRev.map some)
            (none :: fuelRev.map some)) (NonemptyRightRegion.region processed) }
def emptyStartConfig (processed fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .loop (.prep .start)
  tape := SeparatorRewind.gateTapeCells (none :: fuelRev.map some) (NonemptyRightRegion.region processed)
def doneConfig (processed fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .done
  tape := SeparatorRewind.gateTapeCells (none :: fuelRev.map some) (NonemptyRightRegion.region processed)
theorem gate_restart_step (remainingRev processed fuelRev : Word MachineCodeSymbol) :
    machine.stepConfig (gateConfig remainingRev processed fuelRev) =
      some (restartConfig remainingRev processed fuelRev) := by
  cases hregion : NonemptyRightRegion.region processed <;>
    simp [TuringMachine.stepConfig, machine, transition, gateConfig, restartConfig, loopConfig,
      OneCellMachine.rewindConfig, SeparatorRewind.gateConfigCells,
      SeparatorRewind.gateTapeCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft, hregion]
theorem restart_iteration_step_of_cons (current : MachineCodeSymbol)
    (remainingRev processed fuelRev : Word MachineCodeSymbol) : machine.stepConfig
        (restartConfig (current :: remainingRev) processed fuelRev) =
      some (paddedIterationSourceConfig current remainingRev processed fuelRev) := by
  cases hregion : NonemptyRightRegion.region processed <;>
    simp [TuringMachine.stepConfig, machine, transition,
      restartConfig, paddedIterationSourceConfig, loopConfig, SeparatorRewind.gateTapeCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight, hregion, ]
theorem paddedIterationSource_equiv_clean (current : MachineCodeSymbol)
    (remainingRev processed fuelRev : Word MachineCodeSymbol) : Tape.Equiv
        (paddedIterationSourceConfig current remainingRev processed fuelRev).tape (loopConfig
          (OneCellMachine.sourceConfig current processed (List.append (remainingRev.map some)
              (none :: fuelRev.map some)))).tape := by
  have hnonempty := NonemptyRightRegion.region_ne_nil processed
  cases hregion : NonemptyRightRegion.region processed with
  | nil => contradiction
  | cons first regionRest =>
      unfold paddedIterationSourceConfig loopConfig
      unfold OneCellMachine.sourceConfig OneCellMachine.prepConfig
      unfold RightCellPrep.sourceConfig
      rw [hregion]
      simp [SeparatorRewind.gateTapeCells, InsertOneWithBoundary.cursorTape, Tape.Equiv, dropTrailingNone_append_none]
theorem loop_transition_of_eq_some (inner target : OneCellMachine.Control)
    (cell write : Option MachineCodeSymbol) (direction : Direction) (htransition :
      OneCellMachine.transition inner cell = some (write, direction, target)) :
    transition (.loop inner) cell = some (write, direction, .loop target) := by
  cases inner with
  | prep prepControl =>
      cases prepControl with
      | candidate =>
          cases cell with
          | none =>
              simp [OneCellMachine.transition, RightCellPrep.transition] at htransition
          | some symbol =>
              simp only [transition, htransition]
      | start | separator | increment | locateDone | gate =>
          simp only [transition, htransition]
  | bridge symbol =>
      simp only [transition, htransition]
  | insert symbol insertControl =>
      simp only [transition, htransition]
  | rewind rewindControl =>
      cases rewindControl with
      | gate =>
          simp [OneCellMachine.transition, SeparatorRewind.transition] at htransition
      | start | scan =>
          simp only [transition, htransition]
theorem loop_step_of_eq_some (c d : TuringMachine.Configuration MachineCodeSymbol
      OneCellMachine.Control) (hstep : OneCellMachine.machine.stepConfig c = some d) :
    machine.stepConfig (loopConfig c) = some (loopConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      unfold OneCellMachine.machine at hstep
      unfold machine
      unfold loopConfig
      dsimp only at hstep ⊢
      cases htransition : OneCellMachine.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          rw [loop_transition_of_eq_some inner target (Tape.read tape) write direction htransition]
          cases hstep
          rfl
theorem loop_run_of_eq_some (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol
      OneCellMachine.Control) (hrun : OneCellMachine.machine.runConfigExact? steps c = some d) :
    machine.runConfigExact? steps (loopConfig c) = some (loopConfig d) := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : OneCellMachine.machine.stepConfig c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          rw [loop_step_of_eq_some c next hstep]
          simp only
          exact ih next d hrun
theorem clean_iteration_run_exact (current : MachineCodeSymbol)
    (remainingRev processed fuelRev : Word MachineCodeSymbol) : machine.runConfigExact?
        (OneCellMachine.runSteps current processed) (loopConfig
          (OneCellMachine.sourceConfig current processed (List.append (remainingRev.map some)
              (none :: fuelRev.map some)))) = some (gateConfig remainingRev (current :: processed) fuelRev) := by
  simpa [gateConfig, OneCellMachine.endpointConfig] using loop_run_of_eq_some
      (OneCellMachine.runSteps current processed) (OneCellMachine.sourceConfig current processed
        (List.append (remainingRev.map some) (none :: fuelRev.map some)))
      (OneCellMachine.endpointConfig current processed (List.append (remainingRev.map some)
          (none :: fuelRev.map some))) (OneCellMachine.run_exact current processed
        (List.append (remainingRev.map some) (none :: fuelRev.map some)))
theorem padded_iteration_run_exact (current : MachineCodeSymbol)
    (remainingRev processed fuelRev : Word MachineCodeSymbol) : exists paddedEndpoint :
        TuringMachine.Configuration MachineCodeSymbol Control, machine.runConfigExact?
          (OneCellMachine.runSteps current processed) (paddedIterationSourceConfig
            current remainingRev processed fuelRev) = some paddedEndpoint ∧
      (gateConfig remainingRev (current :: processed) fuelRev).state = paddedEndpoint.state ∧
      Tape.Equiv (gateConfig remainingRev (current :: processed) fuelRev).tape paddedEndpoint.tape := by
  exact TuringExactEquiv.runConfigExact?_some_of_equiv (clean :=
      loopConfig (OneCellMachine.sourceConfig current processed
          (List.append (remainingRev.map some) (none :: fuelRev.map some))))
    (padded := paddedIterationSourceConfig current remainingRev processed fuelRev)
    (cleanFinal := gateConfig remainingRev (current :: processed) fuelRev)
    machine (OneCellMachine.runSteps current processed)
    rfl (Tape.Equiv.symm (paddedIterationSource_equiv_clean
        current remainingRev processed fuelRev)) (clean_iteration_run_exact current remainingRev processed fuelRev)
theorem restart_empty_step (processed fuelRev : Word MachineCodeSymbol) :
    machine.stepConfig (restartConfig [] processed fuelRev) = some (emptyStartConfig processed fuelRev) := by
  cases hregion : NonemptyRightRegion.region processed <;>
    simp [TuringMachine.stepConfig, machine, transition, restartConfig, emptyStartConfig,
      SeparatorRewind.gateTapeCells, Tape.read, Tape.write, Tape.move, Tape.moveRight, hregion]
theorem empty_finish_run_exact (processed fuelRev : Word MachineCodeSymbol) :
    machine.runConfigExact? 4 (emptyStartConfig processed fuelRev) = some (doneConfig processed fuelRev) := by
  have hnonempty := NonemptyRightRegion.region_ne_nil processed
  cases hregion : NonemptyRightRegion.region processed with
  | nil => contradiction
  | cons first rest =>
      cases rest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          machine, transition, emptyStartConfig, doneConfig, OneCellMachine.transition, RightCellPrep.transition,
          SeparatorRewind.gateTapeCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, hregion]
theorem run_to_done_equiv (remainingRev processed fuelRev : Word MachineCodeSymbol) : exists
        (steps : Nat) (endpoint : TuringMachine.Configuration MachineCodeSymbol Control),
      machine.runConfigExact? steps (gateConfig remainingRev processed fuelRev) =
        some endpoint ∧ (doneConfig (List.append remainingRev.reverse processed)
        fuelRev).state = endpoint.state ∧ Tape.Equiv (doneConfig
          (List.append remainingRev.reverse processed) fuelRev).tape endpoint.tape := by
  induction remainingRev generalizing processed with
  | nil =>
      refine ⟨6, doneConfig processed fuelRev, ?_, rfl, Tape.Equiv.refl _⟩
      change machine.runConfigExact? (1 + (1 + 4)) (gateConfig [] processed fuelRev) = _
      rw [TuringMachine.runConfigExact?]
      rw [gate_restart_step]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [restart_empty_step]
      simp only
      exact empty_finish_run_exact processed fuelRev
  | cons current remainingRev ih =>
      rcases padded_iteration_run_exact current remainingRev processed fuelRev with
        ⟨cellEndpoint, hcellRun, hcellState, hcellTape⟩
      rcases ih (current :: processed) with
        ⟨restSteps, restEndpoint, hrestRun, hrestState, hrestTape⟩
      rcases TuringExactEquiv.runConfigExact?_some_of_equiv
          (clean := gateConfig remainingRev (current :: processed) fuelRev)
          (padded := cellEndpoint) (cleanFinal := restEndpoint) machine restSteps hcellState hcellTape hrestRun with
        ⟨actualEndpoint, hactualRun, hactualState, hactualTape⟩
      refine ⟨(OneCellMachine.runSteps current processed + restSteps) + 2, actualEndpoint, ?_, ?_, ?_⟩
      · rw [TuringMachine.runConfigExact?]
        rw [gate_restart_step]
        simp only
        rw [TuringMachine.runConfigExact?]
        rw [restart_iteration_step_of_cons]
        simp only
        rw [ExactRun.append]
        rw [hcellRun]
        simp only
        exact hactualRun
      · have htarget : doneConfig (List.append (current :: remainingRev).reverse
                  processed) fuelRev = doneConfig (List.append remainingRev.reverse
                  (current :: processed)) fuelRev := by
          simp [List.reverse_cons, List.append_assoc]
        rw [htarget]
        exact hrestState.trans hactualState
      · have htarget : doneConfig (List.append (current :: remainingRev).reverse
                  processed) fuelRev = doneConfig (List.append remainingRev.reverse
                  (current :: processed)) fuelRev := by
          simp [List.reverse_cons, List.append_assoc]
        rw [htarget]
        exact Tape.Equiv.trans hrestTape hactualTape
end RawTailLoopMachine


namespace NonemptyFixedPrefix
def fixedPrefix {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat M.start.val) (MachineCodeSymbol.done ::
      encodeOptionalCodeSymbolAppend (some headSymbol) [])
def body {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat fuel) (List.append (fixedPrefix M headSymbol)
      (NonemptyRightRegion.region rest))
theorem fixedPrefix_ne_nil {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol) :
    fixedPrefix M headSymbol ≠ [] := by
  intro hnil
  have htail := (List.append_eq_nil_iff.mp hnil).2
  cases htail
theorem body_eq_initial_protectedWord {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    MachineCodeSymbol.header :: body M fuel headSymbol rest = Frame.protectedWord
        (Layout.initial M (headSymbol :: rest) fuel) [] := by
  rw [Layout.initial_cons_eq]
  simp [body, fixedPrefix, NonemptyRightRegion.region, Frame.protectedWord, Layout.encodeAppend,
    encodeOptionalCodeSymbolsAppend, encodeOptionalCodeSymbolsPayloadAppend,
    encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend, MachineDescription.encodeNat, List.append_assoc]
def capacityFrom {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    : List MachineCodeSymbol -> Nat
  | [] => 0
  | symbol :: rest =>
      Nat.max (fixedPrefix M symbol).length (capacityFrom M rest)
def capacity {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Nat :=
  capacityFrom M MachineCodeSymbol.finite.elems
theorem fixedPrefix_length_le_capacityFrom {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (symbols : List MachineCodeSymbol) (hmem : headSymbol ∈ symbols) :
    (fixedPrefix M headSymbol).length ≤ capacityFrom M symbols := by
  induction symbols with
  | nil => simp at hmem
  | cons first rest ih =>
      simp only [capacityFrom]
      cases List.mem_cons.mp hmem with
      | inl heq =>
          subst first
          exact Nat.le_max_left _ _
      | inr htail =>
          exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)
theorem fixedPrefix_length_le_capacity {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol) :
    (fixedPrefix M headSymbol).length ≤ capacity M := by
  exact fixedPrefix_length_le_capacityFrom M headSymbol MachineCodeSymbol.finite.elems
    (MachineCodeSymbol.finite.complete headSymbol)
def buffer {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) : VariableBlockInsert.Buffer (capacity M) :=
  ⟨fixedPrefix M headSymbol, fixedPrefix_length_le_capacity M headSymbol⟩
def sourceConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (VariableBlockInsert.Control (capacity M)) :=
  VariableBlockInsert.config (buffer M headSymbol) [] (none :: none :: fuelRev.map some)
    (NonemptyRightRegion.region rest)
def endpointConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (VariableBlockInsert.Control (capacity M)) :=
  VariableBlockInsert.haltConfig (VariableBlockInsert.finalLeftRev (buffer M headSymbol) []
      (NonemptyRightRegion.region rest)) (none :: none :: fuelRev.map some)
def runSteps {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) : Nat :=
  (NonemptyRightRegion.region rest).length + (fixedPrefix M headSymbol).length
theorem run_exact {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest fuelRev : Word MachineCodeSymbol) :
    (VariableBlockInsert.machine (capacity M) (buffer M headSymbol)).runConfigExact?
        (runSteps M headSymbol rest) (sourceConfig M headSymbol rest fuelRev) =
      some (endpointConfig M headSymbol rest fuelRev) := by
  exact VariableBlockInsert.run_exact (buffer M headSymbol) (buffer M headSymbol) []
    (NonemptyRightRegion.region rest) (none :: none :: fuelRev.map some) (fixedPrefix_ne_nil M headSymbol)
theorem endpoint_word_reverse {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) : (VariableBlockInsert.finalLeftRev (buffer M headSymbol) []
      (NonemptyRightRegion.region rest)).reverse = List.append (fixedPrefix M headSymbol)
        (NonemptyRightRegion.region rest) := by
  simpa [buffer] using VariableBlockInsert.finalLeftRev_reverse
    (buffer M headSymbol) ([] : Word MachineCodeSymbol) (NonemptyRightRegion.region rest)
    (fixedPrefix_ne_nil M headSymbol)
theorem tail_done_equiv_source {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (rest fuelRev : Word MachineCodeSymbol) : Tape.Equiv (RawTailLoopMachine.doneConfig rest fuelRev).tape
      (sourceConfig M headSymbol rest fuelRev).tape := by
  have hnonempty := NonemptyRightRegion.region_ne_nil rest
  cases hregion : NonemptyRightRegion.region rest with
  | nil => contradiction
  | cons first regionRest =>
      simp [RawTailLoopMachine.doneConfig, SeparatorRewind.gateTapeCells, sourceConfig,
        VariableBlockInsert.config, InsertOneWithBoundary.cursorTape, Tape.Equiv, dropTrailingNone_append_none, hregion]
end NonemptyFixedPrefix

end InitialMaterializer
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
