import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.EncodedList.Locator
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.RuntimeEncodedList

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

/-!
**Encoded-list prepend.** At the payload boundary, the machine changes the old
count terminator into an additional count tick and inserts a fresh terminator
followed by the new one-token cell encoding. One restaged insertion therefore
increments the count and prepends the payload cell.
-/

namespace Prepend

def cellSymbol : Option Bool -> MachineCodeSymbol
  | none => MachineCodeSymbol.blank
  | some false => MachineCodeSymbol.zero
  | some true => MachineCodeSymbol.one

theorem encodeCell_eq_singleton (cell : Option Bool) :
    MachineDescription.encodeCell cell = [cellSymbol cell] := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl

def buffer (cell : Option Bool) : InsertBlock.Buffer where
  word := [MachineCodeSymbol.done, cellSymbol cell]
  length_le := by simp

theorem buffer_nonempty (cell : Option Bool) :
    (buffer cell).word ≠ [] := by
  simp [buffer]

inductive Control where
  | locate (inner : PayloadLocator.Control)
  | replaceCountDone
  | insert (inner : InsertRestagedMachine.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  List.append
    (PayloadLocator.Control.finite.elems.map Control.locate)
    (Control.replaceCountDone ::
      InsertRestagedMachine.Control.finite.elems.map Control.insert)

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        have h := PayloadLocator.Control.finite.complete inner
        simp [elems, h]
    | replaceCountDone => simp [elems]
    | insert inner =>
        have h := InsertRestagedMachine.Control.finite.complete inner
        simp [elems, h]

end Control

def transition (cell : Option Bool) :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate .gate, read =>
      some (read, Direction.left, .replaceCountDone)
  | .locate inner, read =>
      match PayloadLocator.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .locate target)
  | .replaceCountDone, some MachineCodeSymbol.done =>
      some
        (some MachineCodeSymbol.tick, Direction.right,
          .insert (.edit (.carry (buffer cell))))
  | .insert inner, read =>
      match InsertRestagedMachine.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .insert target)
  | _, _ => none

def machine (cell : Option Bool) :
    TuringMachine MachineCodeSymbol Control where
  start := .locate .count
  halt := .insert (.rewind .gate)
  transition := transition cell
  statesFinite := Control.finite

def locateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      PayloadLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .locate c.state
  tape := c.tape

def insertConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .insert c.state
  tape := c.tape

theorem locate_step_of_some
    (cell : Option Bool)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      PayloadLocator.Control)
    (hstep : PayloadLocator.machine.stepConfig source = some target) :
    (machine cell).stepConfig (locateConfig source) =
      some (locateConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [PayloadLocator.machine] at hstep
      cases htransition :
          PayloadLocator.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : inner ≠ PayloadLocator.Control.gate := by
            intro hgate
            subst inner
            simp [PayloadLocator.transition] at htransition
          simp [machine, transition, locateConfig, htransition]

theorem locate_run_of_some
    (cell : Option Bool) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        PayloadLocator.Control),
      PayloadLocator.machine.runConfigExact? steps source = some target ->
        (machine cell).runConfigExact? steps (locateConfig source) =
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
      cases hstep : PayloadLocator.machine.stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [locate_step_of_some cell source next hstep]
          simp only
          exact ih next target hrun

def insertLeftRev
    (baseLeftRev : Word MachineCodeSymbol) (count : Nat) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.tick ::
    List.append (PayloadLocator.ticks count) baseLeftRev

theorem locate_insert_handoff_exact
    (cell : Option Bool)
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    (machine cell).runConfigExact? 2
        (locateConfig
          (PayloadLocator.targetConfig baseLeftRev count suffix)) =
      some
        (insertConfig
          (InsertRestagedMachine.editConfig
            (InsertBlock.config (buffer cell)
              (insertLeftRev baseLeftRev count) suffix))) := by
  cases suffix <;> rfl

theorem insert_step_of_some
    (cell : Option Bool)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control)
    (hstep : (InsertRestagedMachine.machine (buffer cell)).stepConfig
      source = some target) :
    (machine cell).stepConfig (insertConfig source) =
      some (insertConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [InsertRestagedMachine.machine] at hstep
      cases htransition :
          InsertRestagedMachine.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          simp [machine, transition, insertConfig, htransition]

theorem insert_run_of_some
    (cell : Option Bool) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        InsertRestagedMachine.Control),
      (InsertRestagedMachine.machine (buffer cell)).runConfigExact?
          steps source = some target ->
        (machine cell).runConfigExact? steps (insertConfig source) =
          some (insertConfig target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using
        congrArg insertConfig (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          (InsertRestagedMachine.machine (buffer cell)).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [insert_step_of_some cell source next hstep]
          simp only
          exact ih next target hrun

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  locateConfig (PayloadLocator.sourceConfig baseLeftRev count suffix)

def targetWord
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append baseLeftRev.reverse
    (MachineDescription.encodeNatAppend (count + 1)
      (MachineDescription.encodeCellAppend cell suffix))

def runSteps
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) : Nat :=
  ((count + 1) + 2) +
    InsertRestagedMachine.runSteps (buffer cell)
      (insertLeftRev baseLeftRev count) suffix

theorem insert_output_eq_targetWord
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) :
    PhysicalBranch.insertOutput (buffer cell)
        (insertLeftRev baseLeftRev count) suffix =
      targetWord baseLeftRev count cell suffix := by
  have hcell :
      MachineDescription.encodeCellAppend cell suffix =
        cellSymbol cell :: suffix := by
    cases cell with
    | none => rfl
    | some bit => cases bit <;> rfl
  unfold PhysicalBranch.insertOutput insertLeftRev targetWord
  rw [PayloadLocator.encodeNatAppend_eq_ticks]
  rw [PayloadLocator.ticks_succ_append]
  rw [hcell]
  simp [buffer, PayloadLocator.ticks, List.reverse_replicate,
    List.reverse_append, List.append_assoc]

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) :
    exists endpoint,
      (machine cell).runConfigExact?
          (runSteps baseLeftRev count cell suffix)
          (sourceConfig baseLeftRev count suffix) = some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input (targetWord baseLeftRev count cell suffix))
        endpoint.tape := by
  have hlocateInner := PayloadLocator.run_exact
    baseLeftRev count suffix
  have hlocate := locate_run_of_some cell _ _ _ hlocateInner
  have hhandoff := locate_insert_handoff_exact
    cell baseLeftRev count suffix
  have hinsertInner := InsertRestagedMachine.run_exact
    (buffer cell) (insertLeftRev baseLeftRev count) suffix
    (buffer_nonempty cell)
  have hinsert := insert_run_of_some cell _ _ _ hinsertInner
  have hpref := TuringMachine.runConfigExact?_trans hlocate hhandoff
  have hrun := TuringMachine.runConfigExact?_trans hpref hinsert
  refine ⟨insertConfig
      (InsertRestagedMachine.rewindConfig
        (RewindWord.gateConfig
          (targetWord baseLeftRev count cell suffix) 0)),
    ?_, ?_, ?_⟩
  · simpa [runSteps, sourceConfig, Nat.add_assoc,
      insert_output_eq_targetWord] using hrun
  · rfl
  · have hgate := RewindWord.gateTape_equiv_input
      (PhysicalBranch.insertOutput (buffer cell)
        (insertLeftRev baseLeftRev count) suffix) 0
    simpa [insertConfig, InsertRestagedMachine.rewindConfig,
      RewindWord.gateConfig, insert_output_eq_targetWord] using
        Tape.Equiv.symm hgate


end Prepend

end FiniteRecognizer.Interpreter.RuntimeEncodedList

end Computability
end FoC
