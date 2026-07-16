import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Context.Prefix

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.DirectContextUpdate

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

/-!
### Encoded-list boundary positioner

The two protected contexts are adjacent unary-counted cell lists.  After the
dynamic-state prefix has been crossed, this scanner crosses exactly one list
and stops on the first count token of the following list.  The payload scan is
lexically unambiguous: encoded cells are `blank`, `zero`, or `one`, whereas a
following unary count starts with `tick` or `done`.
-/

namespace Boundary

inductive Control where
  | locate (inner : FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.Control)
  | enter
  | payload
  | bounce
  | ready
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.Control.finite.elems.map locate ++
    [enter, payload, bounce, ready, halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.Control.finite.complete
            inner]
    | enter => simp [elems]
    | payload => simp [elems]
    | bounce => simp [elems]
    | ready => simp [elems]
    | halt => simp [elems]

end Control

def isCellSymbol : MachineCodeSymbol -> Bool
  | MachineCodeSymbol.blank
  | MachineCodeSymbol.zero
  | MachineCodeSymbol.one => true
  | _ => false

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate .gate, read => some (read, Direction.left, .enter)
  | .locate inner, read =>
      match FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .locate target)
  | .enter, read => some (read, Direction.right, .payload)
  | .payload, some symbol =>
      if isCellSymbol symbol then
        some (some symbol, Direction.right, .payload)
      else if symbol = MachineCodeSymbol.tick ∨
          symbol = MachineCodeSymbol.done then
        some (some symbol, Direction.left, .bounce)
      else
        none
  | .bounce, read => some (read, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locate .count
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def locateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .locate c.state
  tape := c.tape

theorem locate_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.Control)
    (hstep :
      FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.machine.stepConfig source =
        some target) :
    machine.stepConfig (locateConfig source) =
      some (locateConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.machine] at hstep
      cases htransition :
          FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot :
              inner ≠ FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.Control.gate := by
            intro hgate
            subst inner
            simp [FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.transition] at htransition
          simp [machine, transition, locateConfig, htransition]

theorem locate_run_of_some :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.Control),
      FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.machine.runConfigExact?
          steps source = some target ->
        machine.runConfigExact? steps (locateConfig source) =
          some (locateConfig target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using
        congrArg locateConfig (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.machine.stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [locate_step_of_some source next hstep]
          simp only
          exact ih next target hrun

theorem locate_payload_handoff_exact
    (leftHead : MachineCodeSymbol)
    (leftRev : Word MachineCodeSymbol)
    (rightHead : MachineCodeSymbol)
    (right : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.locate .gate
          tape := SerializedShift.cursorTape (leftHead :: leftRev)
            (rightHead :: right) } =
      some
        { state := Control.payload
          tape := SerializedShift.cursorTape (leftHead :: leftRev)
            (rightHead :: right) } := by
  rfl

theorem step_payload_cell
    (cell : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.payload
          tape := SerializedShift.cursorTape leftRev
            (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell :: suffix) } =
      some
        { state := Control.payload
          tape := SerializedShift.cursorTape
            (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell :: leftRev)
            suffix } := by
  cases cell with
  | none => cases suffix <;> rfl
  | some bit => cases bit <;> cases suffix <;> rfl

def payloadLeftRev
    (baseLeftRev : Word MachineCodeSymbol) :
    List (Option Bool) -> Word MachineCodeSymbol
  | [] => baseLeftRev
  | cell :: cells =>
      payloadLeftRev
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell :: baseLeftRev)
        cells

theorem run_payload_cells
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? cells.length
        { state := Control.payload
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineDescription.encodeCellsAppend cells suffix) } =
      some
        { state := Control.payload
          tape := SerializedShift.cursorTape
            (payloadLeftRev baseLeftRev cells) suffix } := by
  induction cells generalizing baseLeftRev with
  | nil => rfl
  | cons cell cells ih =>
      change machine.runConfigExact? (cells.length + 1)
        { state := Control.payload
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineDescription.encodeCellAppend cell
              (MachineDescription.encodeCellsAppend cells suffix)) } = _
      have hcell :
          MachineDescription.encodeCellAppend cell
              (MachineDescription.encodeCellsAppend cells suffix) =
            FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell ::
              MachineDescription.encodeCellsAppend cells suffix := by
        cases cell with
        | none => rfl
        | some bit => cases bit <;> rfl
      rw [hcell]
      rw [TuringMachine.runConfigExact?]
      rw [step_payload_cell]
      simp only
      simpa [payloadLeftRev] using
        ih (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell :: baseLeftRev)

theorem payload_ready_handoff_tick_exact
    (leftHead : MachineCodeSymbol)
    (leftRev right : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.payload
          tape := SerializedShift.cursorTape (leftHead :: leftRev)
            (MachineCodeSymbol.tick :: right) } =
      some
        { state := Control.ready
          tape := SerializedShift.cursorTape (leftHead :: leftRev)
            (MachineCodeSymbol.tick :: right) } := by
  rfl

theorem payload_ready_handoff_done_exact
    (leftHead : MachineCodeSymbol)
    (leftRev right : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.payload
          tape := SerializedShift.cursorTape (leftHead :: leftRev)
            (MachineCodeSymbol.done :: right) } =
      some
        { state := Control.ready
          tape := SerializedShift.cursorTape (leftHead :: leftRev)
            (MachineCodeSymbol.done :: right) } := by
  rfl

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (nextCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  locateConfig
    (FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.sourceConfig
      baseLeftRev cells.length
      (MachineDescription.encodeCellsAppend cells
        (MachineDescription.encodeNatAppend nextCount suffix)))

def targetBaseLeftRev
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) : Word MachineCodeSymbol :=
  payloadLeftRev
    (FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.targetLeftRev
      baseLeftRev cells.length)
    cells

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (nextCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready
  tape := SerializedShift.cursorTape
    (targetBaseLeftRev baseLeftRev cells)
    (MachineDescription.encodeNatAppend nextCount suffix)

theorem locate_payload_handoff_cells_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (nextCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (locateConfig
          (FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.targetConfig
            baseLeftRev cells.length
            (MachineDescription.encodeCellsAppend cells
              (MachineDescription.encodeNatAppend nextCount suffix)))) =
      some
        { state := Control.payload
          tape := SerializedShift.cursorTape
            (FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.targetLeftRev
              baseLeftRev cells.length)
            (MachineDescription.encodeCellsAppend cells
              (MachineDescription.encodeNatAppend nextCount suffix)) } := by
  cases cells with
  | nil => cases nextCount <;> rfl
  | cons cell cells =>
      cases cell with
      | none => rfl
      | some bit => cases bit <;> rfl

theorem payloadLeftRev_ne_nil
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (hbase : baseLeftRev ≠ []) :
    payloadLeftRev baseLeftRev cells ≠ [] := by
  induction cells generalizing baseLeftRev with
  | nil => exact hbase
  | cons cell cells ih =>
      exact ih
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell :: baseLeftRev)
        (by simp)

theorem targetBaseLeftRev_ne_nil
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    targetBaseLeftRev baseLeftRev cells ≠ [] := by
  apply payloadLeftRev_ne_nil
  simp [FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.targetLeftRev]

theorem payloadLeftRev_reverse
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    (payloadLeftRev baseLeftRev cells).reverse =
      List.append baseLeftRev.reverse
        (MachineDescription.encodeCells cells) := by
  have encodeCells_cons : forall
      (cell : Option Bool) (rest : List (Option Bool)),
      MachineDescription.encodeCells (cell :: rest) =
        FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell ::
          MachineDescription.encodeCells rest := by
    intro cell rest
    cases cell with
    | none => rfl
    | some bit => cases bit <;> rfl
  induction cells generalizing baseLeftRev with
  | nil =>
      simp [payloadLeftRev, MachineDescription.encodeCells,
        MachineDescription.encodeCellsAppend]
  | cons cell cells ih =>
      calc
        (payloadLeftRev baseLeftRev (cell :: cells)).reverse =
            List.append
              (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell ::
                baseLeftRev).reverse
              (MachineDescription.encodeCells cells) := by
                rw [payloadLeftRev, ih]
        _ = List.append baseLeftRev.reverse
              (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol cell ::
                MachineDescription.encodeCells cells) := by
                simp [List.append_assoc]
        _ = List.append baseLeftRev.reverse
              (MachineDescription.encodeCells (cell :: cells)) := by
                rw [encodeCells_cons]

theorem locatorTargetLeftRev_reverse
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) :
    (FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.targetLeftRev
      baseLeftRev count).reverse =
      List.append baseLeftRev.reverse
        (MachineDescription.encodeNat count) := by
  rw [runtimeKey_encodeNat_eq_replicate_tick_done]
  simp [FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.targetLeftRev,
    FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.ticks,
    List.reverse_replicate, List.append_assoc]

theorem targetBaseLeftRev_reverse
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    (targetBaseLeftRev baseLeftRev cells).reverse =
      List.append baseLeftRev.reverse
        (MachineDescription.encodeCellListAppend cells []) := by
  rw [targetBaseLeftRev, payloadLeftRev_reverse]
  rw [locatorTargetLeftRev_reverse]
  rw [show MachineDescription.encodeCellListAppend cells [] =
      List.append (MachineDescription.encodeNat cells.length)
        (MachineDescription.encodeCells cells) by
    rfl]
  simp [List.append_assoc]

theorem payload_ready_handoff_nat_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (nextCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.payload
          tape := SerializedShift.cursorTape
            (targetBaseLeftRev baseLeftRev cells)
            (MachineDescription.encodeNatAppend nextCount suffix) } =
      some (targetConfig baseLeftRev cells nextCount suffix) := by
  have hnonempty := targetBaseLeftRev_ne_nil baseLeftRev cells
  cases hleft : targetBaseLeftRev baseLeftRev cells with
  | nil => contradiction
  | cons leftHead leftRev =>
      cases nextCount with
      | zero =>
          simpa [targetConfig, hleft,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            payload_ready_handoff_done_exact leftHead leftRev suffix
      | succ nextCount =>
          simpa [targetConfig, hleft,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            payload_ready_handoff_tick_exact leftHead leftRev
              (MachineDescription.encodeNatAppend nextCount suffix)

theorem runConfigExact_trans
    {first second : Nat}
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hfirst : machine.runConfigExact? first source = some middle)
    (hsecond : machine.runConfigExact? second middle = some target) :
    machine.runConfigExact? (first + second) source = some target := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hfirst)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hsecond)

def runSteps (cells : List (Option Bool)) : Nat :=
  (((cells.length + 1) + 2) + cells.length) + 2

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (nextCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps cells)
        (sourceConfig baseLeftRev cells nextCount suffix) =
      some (targetConfig baseLeftRev cells nextCount suffix) := by
  have hlocateInner :=
    FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.run_exact
      baseLeftRev cells.length
      (MachineDescription.encodeCellsAppend cells
        (MachineDescription.encodeNatAppend nextCount suffix))
  have hlocate := locate_run_of_some _ _ _ hlocateInner
  have henter := locate_payload_handoff_cells_exact
    baseLeftRev cells nextCount suffix
  have hpref := runConfigExact_trans hlocate henter
  have hcells := run_payload_cells
    (FiniteRecognizer.Interpreter.RuntimeEncodedList.PayloadLocator.targetLeftRev
      baseLeftRev cells.length)
    cells (MachineDescription.encodeNatAppend nextCount suffix)
  have hthroughCells := runConfigExact_trans hpref hcells
  have hready := payload_ready_handoff_nat_exact
    baseLeftRev cells nextCount suffix
  have hrun := runConfigExact_trans hthroughCells hready
  simpa [runSteps, sourceConfig, targetBaseLeftRev, Nat.add_assoc] using hrun

end Boundary

end FiniteRecognizer.Interpreter.DirectContextUpdate

end Computability
end FoC
