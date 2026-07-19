import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.CodeAlphabetLowering
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorBooleanCloseout
import FoC.Computability.Compiler.StuckExecution

set_option doc.verso true

/-!
# Missing-only rejecting completion

This campaign-local wrapper preserves every successful run and its physical
output tape.  Only a missing transition at a nonhalt base state enters a
left-rewind, right-erase, one-bit rejecting tail.  Building the wrapper as a
finite Boolean Turing machine and using the checked finite-machine enumerator
keeps the structural proof independent of a generated transition table.
-/

namespace FoC
namespace Computability
namespace PairHaltingReduction
namespace MissingRejectCompletion

open Languages
open MachineDescription

inductive Control (stateCount : Nat) where
  | base (inner : Fin (stateCount + 1))
  | rejectRewind
  | rejectErase
deriving DecidableEq

namespace Control

private def elems (stateCount : Nat) : List (Control stateCount) :=
  ((Foundation.FiniteType.fin (stateCount + 1)).elems.map Control.base) ++
    [.rejectRewind, .rejectErase]

def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | base inner =>
        have h := (Foundation.FiniteType.fin (stateCount + 1)).complete inner
        simp [elems, h]
    | rejectRewind => simp [elems]
    | rejectErase => simp [elems]

end Control

private def mapBaseAction {stateCount : Nat} :
    Option (Option Bool × Direction × Fin (stateCount + 1)) ->
      Option (Option Bool × Direction × Control stateCount)
  | none => none
  | some (write, move, target) => some (write, move, .base target)

def transition (D : MachineDescription) (reject : Bool) :
    Control D.stateCount -> Option Bool ->
      Option (Option Bool × Direction × Control D.stateCount)
  | .base state, read =>
      if state = D.toTuringMachine.halt then
        none
      else
        match D.toTuringMachine.transition state read with
        | some action => mapBaseAction (some action)
        | none => some (read, Direction.left, .rejectRewind)
  | .rejectRewind, none =>
      some (none, Direction.right, .rejectErase)
  | .rejectRewind, some bit =>
      some (some bit, Direction.left, .rejectRewind)
  | .rejectErase, none =>
      some (some reject, Direction.right, .base D.toTuringMachine.halt)
  | .rejectErase, some _ =>
      some (none, Direction.right, .rejectErase)

def machine (D : MachineDescription) (reject : Bool) :
    TuringMachine Bool (Control D.stateCount) where
  start := .base D.toTuringMachine.start
  halt := .base D.toTuringMachine.halt
  transition := transition D reject
  statesFinite := Control.finite D.stateCount

theorem machine_haltingTransitionsDisabled
    (D : MachineDescription) (reject : Bool) :
    TuringMachine.HaltingTransitionsDisabled (machine D reject) := by
  intro read
  simp [machine, transition]

def Description (D : MachineDescription) (reject : Bool) :
    MachineDescription :=
  SelfHaltingRecognizer.CodeAlphabetLowering.finiteBoolMachineDescription
    (machine D reject)

theorem description_subroutineReady
    (D : MachineDescription) (reject : Bool) :
    (Description D reject).SubroutineReady :=
  SelfHaltingRecognizer.CodeAlphabetLowering.finiteBoolMachineDescription_subroutineReady
    (machine D reject)

private def baseConfig (D : MachineDescription)
    (configuration : TuringMachine.Configuration Bool
      (Fin (D.stateCount + 1))) :
    TuringMachine.Configuration Bool (Control D.stateCount) where
  state := .base configuration.state
  tape := configuration.tape

private theorem step_base
    {D : MachineDescription} (hD : D.SubroutineReady) (reject : Bool)
    {source target : TuringMachine.Configuration Bool
      (Fin (D.stateCount + 1))}
    (hstep : TuringMachine.Step D.toTuringMachine source target) :
    TuringMachine.Step (machine D reject)
      (baseConfig D source) (baseConfig D target) := by
  cases hstep with
  | mk htransition =>
      have hsource : source.state ≠ D.toTuringMachine.halt := by
        intro hhalt
        have hdisabled :=
          MachineDescription.toTuringMachine_haltingTransitionsDisabled
            hD.1 hD.2 (Tape.read source.tape)
        rw [hhalt, hdisabled] at htransition
        cases htransition
      apply TuringMachine.Step.mk
      simp [machine, transition, baseConfig, hsource, htransition,
        mapBaseAction]

private theorem computes_base
    {D : MachineDescription} (hD : D.SubroutineReady) (reject : Bool)
    {source target : TuringMachine.Configuration Bool
      (Fin (D.stateCount + 1))}
    (hcomputes : TuringMachine.Computes D.toTuringMachine source target) :
    TuringMachine.Computes (machine D reject)
      (baseConfig D source) (baseConfig D target) := by
  induction hcomputes with
  | refl configuration => exact TuringMachine.Computes.refl _
  | step hstep _ ih =>
      exact TuringMachine.Computes.step
        (step_base hD reject hstep) ih

private theorem description_haltsFromTape_of_machine_computes
    {D : MachineDescription} (reject : Bool) {source : Tape Bool}
    {final : TuringMachine.Configuration Bool (Control D.stateCount)}
    (hcomputes : TuringMachine.Computes (machine D reject)
      { state := (machine D reject).start, tape := source } final)
    (hhalt : TuringMachine.Halted (machine D reject) final) :
    (Description D reject).HaltsFromTape source final.tape := by
  rcases SelfHaltingRecognizer.original_haltsFrom_to_haltStoppedMachine
      (M := machine D reject) ⟨final, hcomputes, hhalt⟩ with
    ⟨stoppedFinal, hstoppedComputes, hstoppedHalt⟩
  have hstoppedOriginal :=
    SelfHaltingRecognizer.haltStoppedMachine_computes_to_original
      hstoppedComputes
  have hfinalEq : stoppedFinal = final :=
    TuringMachine.computes_to_halted_unique
      (machine_haltingTransitionsDisabled D reject)
      hstoppedOriginal hstoppedHalt hcomputes hhalt
  subst stoppedFinal
  exact SelfHaltingRecognizer.CodeAlphabetLowering.finiteBoolMachineDescription_haltsFromTape_of_stopped_computes
    (machine D reject) source final hstoppedComputes hhalt

/-- Successful base execution is preserved with its exact physical output
tape. -/
theorem description_haltsFromTape_of_haltsFromTape
    {D : MachineDescription} (hD : D.SubroutineReady) (reject : Bool)
    {input output : Tape Bool}
    (hhalts : D.HaltsFromTape input output) :
    (Description D reject).HaltsFromTape input output := by
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalts with
    ⟨steps, hrun⟩
  let source : MachineDescription.Configuration :=
    { state := D.start, tape := input }
  have hinner := MachineDescription.runConfig_toTuringMachine_computes
    (D := D) hD.1 (n := steps) (c := source) hD.1.2.1
  have hinner' : TuringMachine.Computes D.toTuringMachine
      (D.toTMConfig source)
      (D.toTMConfig { state := D.halt, tape := output }) := by
    simpa [source, hrun] using hinner
  have houter := computes_base hD reject hinner'
  have houter' : TuringMachine.Computes (machine D reject)
      { state := (machine D reject).start, tape := input }
      { state := (machine D reject).halt, tape := output } := by
    simpa [source, baseConfig, machine, MachineDescription.toTMConfig,
      MachineDescription.toTuringMachine]
      using houter
  exact description_haltsFromTape_of_machine_computes reject houter' rfl

/-- Successful normalized base output is preserved unchanged. -/
theorem description_haltsFromTapeWithOutput_of_haltsFromTapeWithOutput
    {D : MachineDescription} (hD : D.SubroutineReady) (reject : Bool)
    {input : Tape Bool} {out : Word Bool}
    (hhalts : D.HaltsFromTapeWithOutput input out) :
    (Description D reject).HaltsFromTapeWithOutput input out := by
  rcases hhalts with ⟨steps, hstate, houtput⟩
  let output :=
    (D.runConfig steps { state := D.start, tape := input }).tape
  have hbase : D.HaltsFromTape input output :=
    ⟨steps, hstate, rfl⟩
  rcases description_haltsFromTape_of_haltsFromTape hD reject hbase with
    ⟨completedSteps, hcompletedState, hcompletedTape⟩
  refine ⟨completedSteps, hcompletedState, ?_⟩
  rw [hcompletedTape]
  exact houtput

private def rewindConfig (D : MachineDescription) (tape : Tape Bool) :
    TuringMachine.Configuration Bool (Control D.stateCount) :=
  { state := .rejectRewind, tape := tape }

private def eraseConfig (D : MachineDescription) (tape : Tape Bool) :
    TuringMachine.Configuration Bool (Control D.stateCount) :=
  { state := .rejectErase, tape := tape }

private def haltConfig (D : MachineDescription) (tape : Tape Bool) :
    TuringMachine.Configuration Bool (Control D.stateCount) :=
  { state := .base D.toTuringMachine.halt, tape := tape }

private theorem step_rewind_blank
    (D : MachineDescription) (reject : Bool) (tape : Tape Bool)
    (hread : Tape.read tape = none) :
    TuringMachine.Step (machine D reject) (rewindConfig D tape)
      (eraseConfig D (Tape.move Direction.right tape)) := by
  have hhead : tape.head = none := by simpa [Tape.read] using hread
  apply TuringMachine.Step.mk
  simp [machine, transition, rewindConfig, hread, hhead]

private theorem step_rewind_bit
    (D : MachineDescription) (reject bit : Bool) (tape : Tape Bool)
    (hread : Tape.read tape = some bit) :
    TuringMachine.Step (machine D reject) (rewindConfig D tape)
      (rewindConfig D (Tape.move Direction.left tape)) := by
  have hhead : tape.head = some bit := by simpa [Tape.read] using hread
  apply TuringMachine.Step.mk
  simp [machine, transition, rewindConfig, hread, hhead]

private theorem step_erase_blank
    (D : MachineDescription) (reject : Bool) (tape : Tape Bool)
    (hread : Tape.read tape = none) :
    TuringMachine.Step (machine D reject) (eraseConfig D tape)
      (haltConfig D
        (Tape.move Direction.right (Tape.write (some reject) tape))) := by
  apply TuringMachine.Step.mk
  simp [machine, transition, eraseConfig, hread]

private theorem step_erase_bit
    (D : MachineDescription) (reject bit : Bool) (tape : Tape Bool)
    (hread : Tape.read tape = some bit) :
    TuringMachine.Step (machine D reject) (eraseConfig D tape)
      (eraseConfig D
        (Tape.move Direction.right (Tape.write none tape))) := by
  apply TuringMachine.Step.mk
  simp [machine, transition, eraseConfig, hread]

private def eraseTape
    (erased : Nat) (right : Word Bool) (padding : Nat) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append
      (List.replicate erased (none : Option Bool)) [none])
    (List.append (right.map some)
      (List.replicate (padding + 1) (none : Option Bool)))

private theorem rewind_computes
    (D : MachineDescription) (reject : Bool)
    (leftRev right : Word Bool) (padding : Nat) :
    TuringMachine.Computes (machine D reject)
      (rewindConfig D
        (Tape.move Direction.left (splitTape leftRev right padding)))
      (eraseConfig D
        (splitTape [] (List.append leftRev.reverse right) padding)) := by
  induction leftRev generalizing right with
  | nil =>
      have hread : Tape.read
          (Tape.move Direction.left (splitTape [] right padding)) = none := by
        cases right <;>
          simp [splitTape, Tape.read, Tape.move, Tape.moveLeft,
            List.replicate_succ]
      have hstep := step_rewind_blank D reject
        (Tape.move Direction.left (splitTape [] right padding)) hread
      have hrun := TuringMachine.Computes.step hstep
        (TuringMachine.Computes.refl _)
      cases right <;>
        simpa [splitTape, DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight, List.replicate_succ]
          using hrun
  | cons bit rest ih =>
      have hread : Tape.read
          (Tape.move Direction.left
            (splitTape (bit :: rest) right padding)) = some bit := by
        cases right <;>
          simp [splitTape, Tape.read, Tape.move, Tape.moveLeft,
            List.replicate_succ]
      have hstep := step_rewind_bit D reject bit
        (Tape.move Direction.left
          (splitTape (bit :: rest) right padding)) hread
      have htail := ih (bit :: right)
      have htail' : TuringMachine.Computes (machine D reject)
          (rewindConfig D (Tape.move Direction.left
            (Tape.move Direction.left
              (splitTape (bit :: rest) right padding))))
          (eraseConfig D (splitTape []
            (List.append (bit :: rest).reverse right) padding)) := by
        cases right <;>
          simpa [splitTape, DovetailInitialLayoutInitializer.tapeAtCells,
            Tape.move, Tape.moveLeft, List.reverse_cons,
            List.append_assoc, List.replicate_succ] using htail
      exact TuringMachine.Computes.step hstep htail'

private theorem erase_computes
    (D : MachineDescription) (reject : Bool)
    (erased : Nat) (right : Word Bool) (padding : Nat) :
    TuringMachine.Computes (machine D reject)
      (eraseConfig D (eraseTape erased right padding))
      (haltConfig D
        (SelfHaltingRecognizer.ValidatorBooleanCloseout.answerTape
          reject (erased + right.length) padding)) := by
  induction right generalizing erased with
  | nil =>
      have hread : Tape.read (eraseTape erased [] padding) = none := by
        simp [eraseTape, DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.read, List.replicate_succ]
      have hstep := step_erase_blank D reject
        (eraseTape erased [] padding) hread
      have hrun := TuringMachine.Computes.step hstep
        (TuringMachine.Computes.refl _)
      cases padding <;>
        simpa [eraseTape,
          SelfHaltingRecognizer.ValidatorBooleanCloseout.answerTape,
          DovetailInitialLayoutInitializer.tapeAtCells, Tape.move,
          Tape.moveRight, Tape.write, List.replicate_succ,
          List.append_assoc] using hrun
  | cons bit rest ih =>
      have hread : Tape.read
          (eraseTape erased (bit :: rest) padding) = some bit := by
        simp [eraseTape, DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.read, List.replicate_succ]
      have hstep := step_erase_bit D reject bit
        (eraseTape erased (bit :: rest) padding) hread
      have htail := ih (erased + 1)
      have herased : erased + 1 + rest.length =
          erased + (rest.length + 1) := by lia
      rw [herased] at htail
      have htail' : TuringMachine.Computes (machine D reject)
          (eraseConfig D (Tape.move Direction.right
            (Tape.write none (eraseTape erased (bit :: rest) padding))))
          (haltConfig D
            (SelfHaltingRecognizer.ValidatorBooleanCloseout.answerTape
              reject (erased + (bit :: rest).length) padding)) := by
        cases rest <;>
          simpa [eraseTape, DovetailInitialLayoutInitializer.tapeAtCells,
            Tape.move, Tape.moveRight, Tape.write, List.replicate_succ,
            List.append_assoc] using htail
      exact TuringMachine.Computes.step hstep htail'

private theorem rejectTail_computes
    (D : MachineDescription) (reject : Bool)
    (leftRev right : Word Bool) (padding : Nat) :
    TuringMachine.Computes (machine D reject)
      (rewindConfig D
        (Tape.move Direction.left (splitTape leftRev right padding)))
      (haltConfig D
        (SelfHaltingRecognizer.ValidatorBooleanCloseout.answerTape reject
          (List.append leftRev.reverse right).length padding)) := by
  have hrewind := rewind_computes D reject leftRev right padding
  have htape : splitTape [] (List.append leftRev.reverse right) padding =
      eraseTape 0 (List.append leftRev.reverse right) padding := by
    cases List.append leftRev.reverse right with
    | nil => cases padding <;> rfl
    | cons bit rest =>
        simp [splitTape, eraseTape,
          DovetailInitialLayoutInitializer.tapeAtCells]
  rw [htape] at hrewind
  have herase := erase_computes D reject 0
    (List.append leftRev.reverse right) padding
  exact TuringMachine.computes_trans hrewind (by
    simpa [List.length_append, List.length_reverse] using herase)

private theorem step_reject_of_missing
    {D : MachineDescription} (hD : D.SubroutineReady)
    (reject : Bool) {state : Nat}
    {tape : Tape Bool} (hbound : state < D.stateCount)
    (hstate : state ≠ D.halt)
    (hstep : D.stepConfig { state := state, tape := tape } = none) :
    TuringMachine.Step (machine D reject)
      (baseConfig D (D.toTMConfig { state := state, tape := tape }))
      (rewindConfig D (Tape.move Direction.left tape)) := by
  have hlookup : D.lookupTransition state (Tape.read tape) = none := by
    cases hlookup : D.lookupTransition state (Tape.read tape) with
    | none => rfl
    | some row =>
        rw [MachineDescription.stepConfig, hlookup] at hstep
        cases hstep
  have hsource : D.stateOfNat state ≠ D.toTuringMachine.halt := by
    change D.stateOfNat state ≠ D.stateOfNat D.halt
    intro heq
    apply hstate
    have hval := congrArg Fin.val heq
    simpa [MachineDescription.stateOfNat_val_of_lt
      (Nat.lt_trans hbound (Nat.lt_succ_self D.stateCount)),
      MachineDescription.stateOfNat_val_of_lt
        (Nat.lt_trans hD.1.2.2.1
          (Nat.lt_succ_self D.stateCount))] using hval
  have htransition : D.toTuringMachine.transition
      (D.stateOfNat state) (Tape.read tape) = none := by
    simp [MachineDescription.toTuringMachine,
      MachineDescription.stateOfNat_val_of_lt
        (Nat.lt_trans hbound (Nat.lt_succ_self D.stateCount)), hlookup]
  have htransition' : D.toTuringMachine.transition
      (D.stateOfNat state) tape.head = none := by
    simpa [Tape.read] using htransition
  apply TuringMachine.Step.mk
  simp [machine, transition, baseConfig,
    MachineDescription.toTMConfig, hsource, htransition', Tape.read]

/-- A finite base run ending at a contiguous missing-transition endpoint takes
the rejecting tail and returns exactly the requested normalized answer bit. -/
theorem description_haltsFromTapeWithOutput_reject_of_stuck
    {D : MachineDescription} (hD : D.SubroutineReady) (reject : Bool)
    {input stuck : Tape Bool} (hstuck : D.StuckFromTape input stuck)
    (hcontiguous : ContiguousTape stuck) :
    (Description D reject).HaltsFromTapeWithOutput input [reject] := by
  rcases hcontiguous with ⟨leftRev, right, padding, rfl⟩
  rcases hstuck with ⟨steps, state, hrun, hstep, hstate⟩
  have hbound : state < D.stateCount := by
    have hrunBound := MachineDescription.runConfig_state_bound
      (D := D) hD.1 (n := steps)
      (c := { state := D.start, tape := input }) hD.1.2.1
    simpa [hrun] using hrunBound
  let source : MachineDescription.Configuration :=
    { state := D.start, tape := input }
  have hinner := MachineDescription.runConfig_toTuringMachine_computes
    (D := D) hD.1 (n := steps) (c := source) hD.1.2.1
  have hinner' : TuringMachine.Computes D.toTuringMachine
      (D.toTMConfig source)
      (D.toTMConfig
        { state := state, tape := splitTape leftRev right padding }) := by
    simpa [source, hrun] using hinner
  have hbase := computes_base hD reject hinner'
  have hbase' : TuringMachine.Computes (machine D reject)
      { state := (machine D reject).start, tape := input }
      (baseConfig D (D.toTMConfig
        { state := state, tape := splitTape leftRev right padding })) := by
    simpa [source, baseConfig, machine, MachineDescription.toTMConfig,
      MachineDescription.toTuringMachine] using hbase
  have hentry := step_reject_of_missing hD reject hbound hstate hstep
  have hentryRun : TuringMachine.Computes (machine D reject)
      (baseConfig D (D.toTMConfig
        { state := state, tape := splitTape leftRev right padding }))
      (rewindConfig D
        (Tape.move Direction.left (splitTape leftRev right padding))) :=
    TuringMachine.Computes.step hentry (TuringMachine.Computes.refl _)
  have htail := rejectTail_computes D reject leftRev right padding
  have hfull := TuringMachine.computes_trans hbase'
    (TuringMachine.computes_trans hentryRun htail)
  have hfull' : TuringMachine.Computes (machine D reject)
      { state := (machine D reject).start, tape := input }
      { state := (machine D reject).halt
        tape := SelfHaltingRecognizer.ValidatorBooleanCloseout.answerTape
          reject (List.append leftRev.reverse right).length padding } := by
    simpa [haltConfig, machine] using hfull
  have hhalts := description_haltsFromTape_of_machine_computes reject
    hfull' rfl
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape hhalts
  simpa [SelfHaltingRecognizer.ValidatorBooleanCloseout.answerTape_normalizedOutput]
    using houtput

end MissingRejectCompletion
end PairHaltingReduction
end Computability
end FoC
