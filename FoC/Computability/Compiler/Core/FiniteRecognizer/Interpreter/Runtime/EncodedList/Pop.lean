import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.DeleteTwo

namespace FoC
namespace Computability

open Languages

namespace Section53RuntimeEncodedList

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

/-!
**Encoded-list pop.** For a nonempty unary-counted Boolean-cell list, the
machine stores the first payload cell in finite control, changes the last count
tick into the new terminator, deletes the obsolete terminator and stored
payload token, rewinds, and returns the popped cell in ready control.
-/

namespace Pop

abbrev cellSymbol := Prepend.cellSymbol

def optionBools : List (Option Bool) :=
  [none, some false, some true]

theorem optionBools_complete (cell : Option Bool) :
    cell ∈ optionBools := by
  cases cell with
  | none => simp [optionBools]
  | some bit => cases bit <;> simp [optionBools]

inductive Control where
  | locate (inner : PayloadLocator.Control)
  | oldDone (cell : Option Bool)
  | lastTick (cell : Option Bool)
  | delete (cell : Option Bool) (inner : DeleteRestagedMachine.Control)
  | returnToReady (cell : Option Bool)
  | ready (cell : Option Bool)
  | halt
deriving DecidableEq

namespace Control

def cellDeleteFinite : Foundation.FiniteType
    (Option Bool × DeleteRestagedMachine.Control) :=
  Foundation.FiniteType.prod
    { elems := optionBools, complete := optionBools_complete }
    DeleteRestagedMachine.Control.finite

def elems : List Control :=
  List.append
    (PayloadLocator.Control.finite.elems.map Control.locate)
    (List.append (optionBools.map Control.oldDone)
      (List.append (optionBools.map Control.lastTick)
        (List.append
          (cellDeleteFinite.elems.map
            (fun payload => Control.delete payload.1 payload.2))
          (List.append (optionBools.map Control.returnToReady)
            (List.append (optionBools.map Control.ready) [.halt])))))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        have h := PayloadLocator.Control.finite.complete inner
        simp [elems, h]
    | oldDone cell => simp [elems, optionBools_complete cell]
    | lastTick cell => simp [elems, optionBools_complete cell]
    | delete cell inner =>
        have h := cellDeleteFinite.complete (cell, inner)
        simp [elems, h]
    | returnToReady cell => simp [elems, optionBools_complete cell]
    | ready cell => simp [elems, optionBools_complete cell]
    | halt => simp [elems]

end Control

def readCell : Option MachineCodeSymbol -> Option (Option Bool)
  | some MachineCodeSymbol.blank => some none
  | some MachineCodeSymbol.zero => some (some false)
  | some MachineCodeSymbol.one => some (some true)
  | _ => none

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate .gate, read =>
      match readCell read with
      | none => none
      | some cell => some (read, Direction.left, .oldDone cell)
  | .locate inner, read =>
      match PayloadLocator.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .locate target)
  | .oldDone cell, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .lastTick cell)
  | .lastTick cell, some MachineCodeSymbol.tick =>
      some
        (some MachineCodeSymbol.done, Direction.right,
          .delete cell
            (.edit (.erase (DeleteBlock.optionalGap DeleteTwo.gapCell))))
  | .delete cell (.rewind .gate), read =>
      some (read, Direction.right, .returnToReady cell)
  | .delete cell inner, read =>
      match DeleteRestagedMachine.transition DeleteTwo.gapCell inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .delete cell target)
  | .returnToReady cell, read =>
      some (read, Direction.left, .ready cell)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locate .count
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def locateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      PayloadLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .locate c.state
  tape := c.tape

def deleteConfig
    (cell : Option Bool)
    (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .delete cell c.state
  tape := c.tape

theorem locate_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      PayloadLocator.Control)
    (hstep : PayloadLocator.machine.stepConfig source = some target) :
    machine.stepConfig (locateConfig source) =
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

theorem locate_run_of_some :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        PayloadLocator.Control),
      PayloadLocator.machine.runConfigExact? steps source = some target ->
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
      cases hstep : PayloadLocator.machine.stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [locate_step_of_some source next hstep]
          simp only
          exact ih next target hrun

def shortenedLeftRev
    (baseLeftRev : Word MachineCodeSymbol) (remaining : Nat) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    List.append (PayloadLocator.ticks remaining) baseLeftRev

theorem locate_delete_handoff_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (remaining : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 3
        (locateConfig
          (PayloadLocator.targetConfig baseLeftRev (remaining + 1)
            (cellSymbol cell :: suffix))) =
      some
        (deleteConfig cell
          (DeleteTwo.sourceConfig
            (shortenedLeftRev baseLeftRev remaining)
            MachineCodeSymbol.done (cellSymbol cell) suffix)) := by
  cases cell with
  | none =>
      cases suffix <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          machine, transition, readCell,
          locateConfig, deleteConfig, DeleteTwo.sourceConfig,
          DeleteTwo.rawSourceConfig, DeleteRestagedMachine.editConfig,
          PayloadLocator.targetConfig,
          PayloadLocator.targetLeftRev, shortenedLeftRev,
          PayloadLocator.ticks, List.replicate_succ,
          Prepend.cellSymbol, SerializedShift.cursorTape,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.append_assoc]
  | some bit =>
      cases bit <;> cases suffix <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          machine, transition, readCell,
          locateConfig, deleteConfig, DeleteTwo.sourceConfig,
          DeleteTwo.rawSourceConfig, DeleteRestagedMachine.editConfig,
          PayloadLocator.targetConfig,
          PayloadLocator.targetLeftRev, shortenedLeftRev,
          PayloadLocator.ticks, List.replicate_succ,
          Prepend.cellSymbol, SerializedShift.cursorTape,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.append_assoc]

theorem delete_step_of_some
    (cell : Option Bool)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine DeleteTwo.gapCell).stepConfig
      source = some target)
    (hnotGate : source.state ≠
      DeleteRestagedMachine.Control.rewind .gate) :
    machine.stepConfig (deleteConfig cell source) =
      some (deleteConfig cell target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [DeleteRestagedMachine.machine] at hstep
      cases htransition :
          DeleteRestagedMachine.transition DeleteTwo.gapCell inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          simp [machine, transition, deleteConfig, htransition]

theorem delete_run_of_some
    (cell : Option Bool) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        DeleteRestagedMachine.Control),
      (DeleteRestagedMachine.machine DeleteTwo.gapCell).runConfigExact?
          steps source = some target ->
      target.state = DeleteRestagedMachine.Control.rewind .gate ->
        machine.runConfigExact? steps (deleteConfig cell source) =
          some (deleteConfig cell target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun htarget
      simpa [TuringMachine.runConfigExact?] using
        congrArg (deleteConfig cell) (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun htarget
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          (DeleteRestagedMachine.machine DeleteTwo.gapCell).stepConfig
            source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          have hnotGate :
              source.state ≠ DeleteRestagedMachine.Control.rewind .gate := by
            intro hgate
            have hnone :
                (DeleteRestagedMachine.machine DeleteTwo.gapCell).stepConfig
                    source = none := by
              cases source with
              | mk inner tape =>
                  simp only at hgate
                  subst inner
                  rfl
            rw [hnone] at hstep
            contradiction
          rw [delete_step_of_some cell source next hstep hnotGate]
          simp only
          exact ih next target hrun htarget

def roundTripTape (tape : Tape MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right tape)

theorem roundTripTape_equiv (tape : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape tape) tape :=
  Machine.moveLeft_moveRight_equiv_self tape

private theorem write_read_eq_self (tape : Tape MachineCodeSymbol) :
    Tape.write (Tape.read tape) tape = tape := by
  cases tape
  rfl

theorem delete_ready_handoff_exact
    (cell : Option Bool) (tape : Tape MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.delete cell (.rewind .gate), tape := tape } =
      some
        { state := Control.ready cell,
          tape := roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, roundTripTape, write_read_eq_self]

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

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (remaining : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  locateConfig
    (PayloadLocator.sourceConfig baseLeftRev (remaining + 1)
      (cellSymbol cell :: suffix))

def targetWord
    (baseLeftRev : Word MachineCodeSymbol)
    (remaining : Nat) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append baseLeftRev.reverse
    (MachineDescription.encodeNatAppend remaining suffix)

def runSteps
    (baseLeftRev : Word MachineCodeSymbol)
    (remaining : Nat) (suffix : Word MachineCodeSymbol) : Nat :=
  (((remaining + 1) + 1) + 3) +
    (DeleteTwo.runSteps
      (shortenedLeftRev baseLeftRev remaining) suffix + 2)

theorem delete_output_eq_targetWord
    (baseLeftRev : Word MachineCodeSymbol)
    (remaining : Nat) (suffix : Word MachineCodeSymbol) :
    DeleteTwo.output (shortenedLeftRev baseLeftRev remaining) suffix =
      targetWord baseLeftRev remaining suffix := by
  unfold DeleteTwo.output shortenedLeftRev targetWord
  rw [PayloadLocator.encodeNatAppend_eq_ticks]
  simp [PayloadLocator.ticks, List.reverse_replicate,
    List.reverse_append, List.append_assoc]

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (remaining : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) :
    exists endpoint,
      machine.runConfigExact?
          (runSteps baseLeftRev remaining suffix)
          (sourceConfig baseLeftRev remaining cell suffix) = some endpoint ∧
      endpoint.state = Control.ready cell ∧
      Tape.Equiv
        (Tape.input (targetWord baseLeftRev remaining suffix))
        endpoint.tape := by
  have hlocateInner := PayloadLocator.run_exact
    baseLeftRev (remaining + 1) (cellSymbol cell :: suffix)
  have hlocate := locate_run_of_some _ _ _ hlocateInner
  have hhandoff := locate_delete_handoff_exact
    baseLeftRev remaining cell suffix
  have hdeleteInner := DeleteTwo.run_exact
    (shortenedLeftRev baseLeftRev remaining)
    MachineCodeSymbol.done (cellSymbol cell) suffix
  have hdelete := delete_run_of_some cell _ _ _ hdeleteInner rfl
  have hpref := runConfigExact_trans hlocate hhandoff
  have hthroughDelete := runConfigExact_trans hpref hdelete
  have hready := delete_ready_handoff_exact cell
    (DeleteRestagedMachine.rewindConfig
      (DeleteEndpointRewind.gateConfig
        (DeleteTwo.output (shortenedLeftRev baseLeftRev remaining) suffix)
        DeleteTwo.gapCell)).tape
  have hrun := runConfigExact_trans hthroughDelete hready
  refine ⟨
    { state := Control.ready cell
      tape := roundTripTape
        (DeleteRestagedMachine.rewindConfig
          (DeleteEndpointRewind.gateConfig
            (DeleteTwo.output
              (shortenedLeftRev baseLeftRev remaining) suffix)
            DeleteTwo.gapCell)).tape },
    ?_, rfl, ?_⟩
  · simpa [runSteps, sourceConfig, Nat.add_assoc] using hrun
  · have hdeleteEquiv := DeleteTwo.target_tape_equiv_input
      (shortenedLeftRev baseLeftRev remaining) suffix
    have htarget :
        Tape.Equiv
          (Tape.input (targetWord baseLeftRev remaining suffix))
          (DeleteRestagedMachine.rewindConfig
            (DeleteEndpointRewind.gateConfig
              (DeleteTwo.output
                (shortenedLeftRev baseLeftRev remaining) suffix)
              DeleteTwo.gapCell)).tape := by
      rw [← delete_output_eq_targetWord]
      exact Tape.Equiv.symm hdeleteEquiv
    exact Tape.Equiv.trans htarget
      (Tape.Equiv.symm
        (roundTripTape_equiv
          (DeleteRestagedMachine.rewindConfig
            (DeleteEndpointRewind.gateConfig
              (DeleteTwo.output
                (shortenedLeftRev baseLeftRev remaining) suffix)
              DeleteTwo.gapCell)).tape))


end Pop

end Section53RuntimeEncodedList

end Computability
end FoC
