import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

/-!
**Unary-field duplicator.** This suffix-preserving machine duplicates a
canonical unary natural-number field while preserving an arbitrary suffix.
Its exact action maps {lit}`MachineDescription.encodeNatAppend n suffix` to
{lit}`MachineDescription.encodeNatAppend n (MachineDescription.encodeNatAppend n suffix)`.

The machine first inserts the second {lit}`done`, then repeatedly changes one
source {lit}`tick` to {lit}`blank`, inserts one {lit}`tick` before the second
terminator with the restaged insertion core, and rewinds.  Once the first
terminator is reached, the marked source prefix is restored.  Scans do not
inspect the arbitrary suffix beyond the second terminator.
-/

inductive InsertPhase where
  | initial
  | copy
deriving DecidableEq

namespace InsertPhase

def elems : List InsertPhase := [.initial, .copy]

def finite : Foundation.FiniteType InsertPhase where
  elems := elems
  complete := by
    intro phase
    cases phase <;> simp [elems]

end InsertPhase

def initialBuffer : InsertBlock.Buffer where
  word := [MachineCodeSymbol.done]
  length_le := by simp

def copyBuffer : InsertBlock.Buffer where
  word := [MachineCodeSymbol.tick]
  length_le := by simp

def phaseBuffer : InsertPhase -> InsertBlock.Buffer
  | .initial => initialBuffer
  | .copy => copyBuffer

theorem phaseBuffer_nonempty (phase : InsertPhase) :
    (phaseBuffer phase).word ≠ [] := by
  cases phase <;> simp [phaseBuffer, initialBuffer, copyBuffer]

inductive Control where
  | initSeek
  | scan
  | seekSourceDone
  | seekCopyDone
  | copyBounce
  | insert (phase : InsertPhase)
      (inner : InsertRestagedMachine.Control)
  | insertReturn
  | restore
  | halt
deriving DecidableEq

namespace Control

def phaseInnerFinite : Foundation.FiniteType
    (InsertPhase × InsertRestagedMachine.Control) :=
  Foundation.FiniteType.prod InsertPhase.finite
    InsertRestagedMachine.Control.finite

def elems : List Control :=
  [initSeek, scan, seekSourceDone, seekCopyDone, copyBounce,
    insertReturn, restore, halt] ++
  phaseInnerFinite.elems.map
    (fun payload => insert payload.1 payload.2)

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | initSeek => simp [elems]
    | scan => simp [elems]
    | seekSourceDone => simp [elems]
    | seekCopyDone => simp [elems]
    | copyBounce => simp [elems]
    | insert phase inner =>
        apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨(phase, inner), phaseInnerFinite.complete (phase, inner), rfl⟩
    | insertReturn => simp [elems]
    | restore => simp [elems]
    | halt => simp [elems]

end Control

def mapInsertAction (phase : InsertPhase) :
    Option MachineCodeSymbol × Direction ×
        InsertRestagedMachine.Control ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) =>
      (write, direction, .insert phase target)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .initSeek, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .initSeek)
  | .initSeek, some MachineCodeSymbol.done =>
      some
        (some MachineCodeSymbol.done, Direction.right,
          .insert .initial
            (InsertRestagedMachine.machine initialBuffer).start)
  | .scan, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .scan)
  | .scan, some MachineCodeSymbol.tick =>
      some
        (some MachineCodeSymbol.blank, Direction.right, .seekSourceDone)
  | .scan, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .restore)
  | .seekSourceDone, some MachineCodeSymbol.tick =>
      some
        (some MachineCodeSymbol.tick, Direction.right, .seekSourceDone)
  | .seekSourceDone, some MachineCodeSymbol.done =>
      some
        (some MachineCodeSymbol.done, Direction.right, .seekCopyDone)
  | .seekCopyDone, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .seekCopyDone)
  | .seekCopyDone, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .copyBounce)
  | .copyBounce, read =>
      some
        (read, Direction.right,
          .insert .copy
            (InsertRestagedMachine.machine copyBuffer).start)
  | .insert phase inner, read =>
      if inner = (InsertRestagedMachine.machine
          (phaseBuffer phase)).halt then
        some (read, Direction.right, .insertReturn)
      else
        Option.map (mapInsertAction phase)
          (InsertRestagedMachine.transition inner read)
  | .insertReturn, read =>
      some (read, Direction.left, .scan)
  | .restore, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.tick, Direction.left, .restore)
  | .restore, none =>
      some (none, Direction.right, .halt)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .initSeek
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def insertConfig
    (phase : InsertPhase)
    (config : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .insert phase config.state
  tape := config.tape

def roundTripTape (tape : Tape MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right tape)

private theorem write_read_eq_self (tape : Tape MachineCodeSymbol) :
    Tape.write (Tape.read tape) tape = tape := by
  cases tape
  rfl

theorem insert_step_of_some
    (phase : InsertPhase)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control)
    (hstep :
      (InsertRestagedMachine.machine (phaseBuffer phase)).stepConfig
          source = some target) :
    machine.stepConfig (insertConfig phase source) =
      some (insertConfig phase target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [InsertRestagedMachine.machine] at hstep
      cases htransition :
          InsertRestagedMachine.transition inner (Tape.read tape) with
      | none =>
          simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : inner ≠
              (InsertRestagedMachine.machine
                (phaseBuffer phase)).halt := by
            intro hhalt
            subst inner
            cases phase <;> cases tape <;>
              simp [InsertRestagedMachine.machine,
                InsertRestagedMachine.transition,
                RewindWord.transition] at htransition
          simp [machine, transition, insertConfig, hnot,
            htransition, mapInsertAction]

theorem insert_run_of_some
    (phase : InsertPhase) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        InsertRestagedMachine.Control),
      (InsertRestagedMachine.machine (phaseBuffer phase)).runConfigExact?
          steps source = some target ->
        machine.runConfigExact? steps (insertConfig phase source) =
          some (insertConfig phase target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using
        congrArg (insertConfig phase) (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          (InsertRestagedMachine.machine
            (phaseBuffer phase)).stepConfig source with
      | none =>
          simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [insert_step_of_some phase source next hstep]
          simp only
          exact ih next target hrun

theorem insert_return_run_exact
    (phase : InsertPhase) (tape : Tape MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := .insert phase
            (InsertRestagedMachine.machine (phaseBuffer phase)).halt
          tape := tape } =
      some { state := .scan, tape := roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, roundTripTape, write_read_eq_self]

theorem roundTrip_gateTape
    (word : Word MachineCodeSymbol) (hword : word ≠ []) :
    roundTripTape (RewindWord.gateTape word 0) =
      RewindWord.gateTape word 0 := by
  cases word with
  | nil => contradiction
  | cons first rest =>
      cases rest <;> rfl

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

def sourceWord
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend value suffix

def targetWord
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend value
    (MachineDescription.encodeNatAppend value suffix)

def sourceConfig
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .initSeek
  tape := Tape.input (sourceWord value suffix)

def targetConfig
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := Tape.input (targetWord value suffix)

theorem encodeNat_eq_ticks_done (value : Nat) :
    MachineDescription.encodeNat value =
      List.append (List.replicate value MachineCodeSymbol.tick)
        [MachineCodeSymbol.done] := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [MachineDescription.encodeNat, List.replicate_succ, ih]

theorem sourceWord_eq
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    sourceWord value suffix =
      List.append (List.replicate value MachineCodeSymbol.tick)
        (MachineCodeSymbol.done :: suffix) := by
  simp [sourceWord, MachineDescription.encodeNatAppend,
    encodeNat_eq_ticks_done, List.append_assoc]

theorem targetWord_eq
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    targetWord value suffix =
      List.append (List.replicate value MachineCodeSymbol.tick)
        (MachineCodeSymbol.done ::
          List.append (List.replicate value MachineCodeSymbol.tick)
            (MachineCodeSymbol.done :: suffix)) := by
  simp [targetWord, MachineDescription.encodeNatAppend,
    encodeNat_eq_ticks_done, List.append_assoc]

theorem init_tick_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .initSeek
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: suffix) } =
      some
        { state := .initSeek
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem init_done_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .initSeek
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: suffix) } =
      some
        { state := .insert .initial
            (InsertRestagedMachine.machine initialBuffer).start
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem ticks_append_cons
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    List.append (List.replicate count MachineCodeSymbol.tick)
        (MachineCodeSymbol.tick :: suffix) =
      MachineCodeSymbol.tick ::
        List.append (List.replicate count MachineCodeSymbol.tick)
          suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ] using
        congrArg (fun word => MachineCodeSymbol.tick :: word) ih

theorem init_seek_run
    (remaining : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (remaining + 1)
        { state := .initSeek
          tape := SerializedShift.cursorTape leftRev
            (List.append
              (List.replicate remaining MachineCodeSymbol.tick)
              (MachineCodeSymbol.done :: suffix)) } =
      some
        (insertConfig .initial
          (InsertRestagedMachine.editConfig
            (InsertBlock.config initialBuffer
              (MachineCodeSymbol.done ::
                List.append
                  (List.replicate remaining MachineCodeSymbol.tick)
                  leftRev)
              suffix))) := by
  induction remaining generalizing leftRev with
  | zero =>
      change machine.runConfigExact? 1
        { state := .initSeek
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: suffix) } =
        some
          (insertConfig .initial
            (InsertRestagedMachine.editConfig
              (InsertBlock.config initialBuffer
                (MachineCodeSymbol.done :: leftRev) suffix)))
      rw [TuringMachine.runConfigExact?]
      rw [init_done_step]
      rfl
  | succ remaining ih =>
      rw [List.replicate_succ]
      change machine.runConfigExact? ((remaining + 1) + 1)
        { state := .initSeek
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick ::
              List.append
                (List.replicate remaining MachineCodeSymbol.tick)
                (MachineCodeSymbol.done :: suffix)) } = _
      rw [TuringMachine.runConfigExact?]
      rw [init_tick_step]
      simp only
      have hrun := ih (MachineCodeSymbol.tick :: leftRev)
      rw [ticks_append_cons remaining leftRev] at hrun
      simpa [List.replicate_succ] using hrun

def workWord
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (List.replicate marked MachineCodeSymbol.blank)
    (List.append
      (List.replicate remaining MachineCodeSymbol.tick)
      (MachineCodeSymbol.done ::
        List.append
          (List.replicate marked MachineCodeSymbol.tick)
          (MachineCodeSymbol.done :: suffix)))

def workConfig
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan
  tape := RewindWord.gateTape (workWord marked remaining suffix) 0

def inputWorkConfig
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan
  tape := Tape.input (workWord marked remaining suffix)

def initialLeftRev (value : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    List.replicate value MachineCodeSymbol.tick

theorem initial_insert_output_eq_workWord
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    PhysicalBranch.insertOutput initialBuffer
        (initialLeftRev value) suffix =
      workWord 0 value suffix := by
  simp [PhysicalBranch.insertOutput, initialBuffer, initialLeftRev,
    workWord, List.reverse_replicate, List.append_assoc]
  done

def initialRunSteps
    (value : Nat) (suffix : Word MachineCodeSymbol) : Nat :=
  (value + 1) +
    InsertRestagedMachine.runSteps initialBuffer
      (initialLeftRev value) suffix + 2

theorem sourceConfig_eq_cursor
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    sourceConfig value suffix =
      { state := .initSeek
        tape := SerializedShift.cursorTape []
          (List.append
            (List.replicate value MachineCodeSymbol.tick)
            (MachineCodeSymbol.done :: suffix)) } := by
  cases value <;>
    simp [sourceConfig, sourceWord_eq, List.replicate_succ,
      SerializedShift.cursorTape, Tape.input]
  done

theorem initial_run_exact
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (initialRunSteps value suffix)
        (sourceConfig value suffix) =
      some (workConfig 0 value suffix) := by
  have hseek := init_seek_run value
    ([] : Word MachineCodeSymbol) suffix
  have hseek' : machine.runConfigExact? (value + 1)
        (sourceConfig value suffix) =
      some
        (insertConfig .initial
          (InsertRestagedMachine.editConfig
            (InsertBlock.config initialBuffer
              (initialLeftRev value) suffix))) := by
    rw [sourceConfig_eq_cursor]
    simpa [initialLeftRev] using hseek
  have hinsertInner := InsertRestagedMachine.run_exact initialBuffer
    (initialLeftRev value) suffix (by simp [initialBuffer])
  have hinsert := insert_run_of_some .initial _ _ _ hinsertInner
  have hreturn := insert_return_run_exact .initial
    (RewindWord.gateTape
      (PhysicalBranch.insertOutput initialBuffer
        (initialLeftRev value) suffix) 0)
  have houtput : PhysicalBranch.insertOutput initialBuffer
      (initialLeftRev value) suffix ≠ [] := by
    rw [initial_insert_output_eq_workWord]
    cases value <;> simp [workWord, List.replicate_succ]
  have hreturn' : machine.runConfigExact? 2
      (insertConfig .initial
        (InsertRestagedMachine.rewindConfig
          (RewindWord.gateConfig
            (PhysicalBranch.insertOutput initialBuffer
              (initialLeftRev value) suffix) 0))) =
      some (workConfig 0 value suffix) := by
    rw [roundTrip_gateTape _ houtput] at hreturn
    simpa [insertConfig, InsertRestagedMachine.rewindConfig,
      InsertRestagedMachine.machine, RewindWord.gateConfig,
      phaseBuffer, workConfig,
      initial_insert_output_eq_workWord] using hreturn
  have hpref := runConfigExact_trans hseek' hinsert
  have hrun := runConfigExact_trans hpref hreturn'
  simpa [initialRunSteps] using hrun
  done

theorem scan_mark_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .scan
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: suffix) } =
      some
        { state := .seekSourceDone
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.blank :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem scan_blank_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .scan
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.blank :: suffix) } =
      some
        { state := .scan
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.blank :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem computes_scan_blanks
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
        { state := .scan
          tape := SerializedShift.cursorTape leftRev
            (List.append
              (List.replicate count MachineCodeSymbol.blank) suffix) }
        { state := .scan
          tape := SerializedShift.cursorTape
            (List.append
              (List.replicate count MachineCodeSymbol.blank).reverse
              leftRev) suffix } := by
  induction count generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ count ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [List.replicate_succ] using
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (scan_blank_step leftRev
                (List.append
                  (List.replicate count MachineCodeSymbol.blank)
                  suffix)))
        (by
          simpa [List.replicate_succ, List.reverse_cons,
            List.append_assoc] using
              ih (MachineCodeSymbol.blank :: leftRev))
  done

theorem seekSource_tick_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .seekSourceDone
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: suffix) } =
      some
        { state := .seekSourceDone
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem computes_seekSource_ticks
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .seekSourceDone
        tape := SerializedShift.cursorTape leftRev
          (List.append
            (List.replicate count MachineCodeSymbol.tick) suffix) }
      { state := .seekSourceDone
        tape := SerializedShift.cursorTape
          (List.append
            (List.replicate count MachineCodeSymbol.tick).reverse
            leftRev) suffix } := by
  induction count generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ count ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [List.replicate_succ] using
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (seekSource_tick_step leftRev
                (List.append
                  (List.replicate count MachineCodeSymbol.tick)
                  suffix)))
        (by
          simpa [List.replicate_succ, List.reverse_cons,
            List.append_assoc] using
              ih (MachineCodeSymbol.tick :: leftRev))
  done

theorem seekSource_done_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .seekSourceDone
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: suffix) } =
      some
        { state := .seekCopyDone
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem seekCopy_tick_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .seekCopyDone
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: suffix) } =
      some
        { state := .seekCopyDone
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem computes_seekCopy_ticks
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .seekCopyDone
        tape := SerializedShift.cursorTape leftRev
          (List.append
            (List.replicate count MachineCodeSymbol.tick) suffix) }
      { state := .seekCopyDone
        tape := SerializedShift.cursorTape
          (List.append
            (List.replicate count MachineCodeSymbol.tick).reverse
            leftRev) suffix } := by
  induction count generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ count ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [List.replicate_succ] using
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (seekCopy_tick_step leftRev
                (List.append
                  (List.replicate count MachineCodeSymbol.tick)
                  suffix)))
        (by
          simpa [List.replicate_succ, List.reverse_cons,
            List.append_assoc] using
              ih (MachineCodeSymbol.tick :: leftRev))
  done

theorem seekCopy_done_step
    (current : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .seekCopyDone
          tape := SerializedShift.cursorTape (current :: leftTail)
            (MachineCodeSymbol.done :: suffix) } =
      some
        { state := .copyBounce
          tape := SerializedShift.cursorTape leftTail
            (current :: MachineCodeSymbol.done :: suffix) } := by
  cases suffix <;> rfl

theorem copyBounce_step
    (current : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .copyBounce
          tape := SerializedShift.cursorTape leftTail
            (current :: MachineCodeSymbol.done :: suffix) } =
      some
        { state := .insert .copy
            (InsertRestagedMachine.machine copyBuffer).start
          tape := SerializedShift.cursorTape (current :: leftTail)
            (MachineCodeSymbol.done :: suffix) } := by
  cases suffix <;> rfl

def copyLeftRev (marked remaining : Nat) : Word MachineCodeSymbol :=
  List.append
    (List.replicate marked MachineCodeSymbol.tick)
    (MachineCodeSymbol.done ::
      List.append
        (List.replicate remaining MachineCodeSymbol.tick)
        (List.replicate (marked + 1) MachineCodeSymbol.blank))

def copyInsertConfig
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .insert .copy
    (InsertRestagedMachine.machine copyBuffer).start
  tape := SerializedShift.cursorTape
    (copyLeftRev marked remaining)
    (MachineCodeSymbol.done :: suffix)

theorem inputWorkConfig_succ_eq_cursor
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    inputWorkConfig marked (remaining + 1) suffix =
      { state := .scan
        tape := SerializedShift.cursorTape []
          (workWord marked (remaining + 1) suffix) } := by
  cases marked <;>
    simp [inputWorkConfig, workWord, Tape.input,
      SerializedShift.cursorTape, List.replicate_succ]
  done

theorem copyLeftRev_ne_nil
    (marked remaining : Nat) :
    copyLeftRev marked remaining ≠ [] := by
  cases marked <;>
    simp [copyLeftRev, List.replicate_succ]
  done

theorem computes_copy_done_bounce
    (current : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .seekCopyDone
        tape := SerializedShift.cursorTape (current :: leftTail)
          (MachineCodeSymbol.done :: suffix) }
      { state := .insert .copy
          (InsertRestagedMachine.machine copyBuffer).start
        tape := SerializedShift.cursorTape (current :: leftTail)
          (MachineCodeSymbol.done :: suffix) } := by
  exact TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (seekCopy_done_step current leftTail suffix))
    (TuringMachine.Computes.step
      (TuringMachine.stepConfig_eq_some_iff_step.mp
        (copyBounce_step current leftTail suffix))
      (TuringMachine.Computes.refl _))
  done

theorem computes_copy_prelude
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (inputWorkConfig marked (remaining + 1) suffix)
      (copyInsertConfig marked remaining suffix) := by
  let sourceTail : Word MachineCodeSymbol :=
    List.append
      (List.replicate remaining MachineCodeSymbol.tick)
      (MachineCodeSymbol.done ::
        List.append
          (List.replicate marked MachineCodeSymbol.tick)
          (MachineCodeSymbol.done :: suffix))
  have hscan : TuringMachine.Computes machine
      (inputWorkConfig marked (remaining + 1) suffix)
      { state := .scan
        tape := SerializedShift.cursorTape
          (List.replicate marked MachineCodeSymbol.blank)
          (MachineCodeSymbol.tick :: sourceTail) } := by
    rw [inputWorkConfig_succ_eq_cursor]
    simpa [workWord, sourceTail, List.replicate_succ,
      List.reverse_replicate, List.append_assoc] using
        computes_scan_blanks marked ([] : Word MachineCodeSymbol)
          (MachineCodeSymbol.tick :: sourceTail)
  let markedLeft : Word MachineCodeSymbol :=
    List.replicate (marked + 1) MachineCodeSymbol.blank
  have hmark : TuringMachine.Step machine
      { state := .scan
        tape := SerializedShift.cursorTape
          (List.replicate marked MachineCodeSymbol.blank)
          (MachineCodeSymbol.tick :: sourceTail) }
      { state := .seekSourceDone
        tape := SerializedShift.cursorTape markedLeft sourceTail } := by
    simpa [markedLeft, List.replicate_succ] using
      TuringMachine.stepConfig_eq_some_iff_step.mp
        (scan_mark_step
          (List.replicate marked MachineCodeSymbol.blank) sourceTail)
  let copyTail : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      List.append
        (List.replicate marked MachineCodeSymbol.tick)
        (MachineCodeSymbol.done :: suffix)
  let sourceLeft : Word MachineCodeSymbol :=
    List.append
      (List.replicate remaining MachineCodeSymbol.tick).reverse
      markedLeft
  have hsourceTicks : TuringMachine.Computes machine
      { state := .seekSourceDone
        tape := SerializedShift.cursorTape markedLeft sourceTail }
      { state := .seekSourceDone
        tape := SerializedShift.cursorTape sourceLeft copyTail } := by
    simpa [sourceTail, copyTail, sourceLeft] using
      computes_seekSource_ticks remaining markedLeft copyTail
  let copiedTail : Word MachineCodeSymbol :=
    List.append
      (List.replicate marked MachineCodeSymbol.tick)
      (MachineCodeSymbol.done :: suffix)
  let doneLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.done :: sourceLeft
  have hsourceDone : TuringMachine.Step machine
      { state := .seekSourceDone
        tape := SerializedShift.cursorTape sourceLeft copyTail }
      { state := .seekCopyDone
        tape := SerializedShift.cursorTape doneLeft copiedTail } := by
    simpa [copyTail, copiedTail, doneLeft] using
      TuringMachine.stepConfig_eq_some_iff_step.mp
        (seekSource_done_step sourceLeft copiedTail)
  have hcopyTicks : TuringMachine.Computes machine
      { state := .seekCopyDone
        tape := SerializedShift.cursorTape doneLeft copiedTail }
      { state := .seekCopyDone
        tape := SerializedShift.cursorTape
          (copyLeftRev marked remaining)
          (MachineCodeSymbol.done :: suffix) } := by
    simpa [copiedTail, copyLeftRev, doneLeft, sourceLeft,
      markedLeft, List.reverse_replicate, List.append_assoc] using
        computes_seekCopy_ticks marked doneLeft
          (MachineCodeSymbol.done :: suffix)
  have hbounce : TuringMachine.Computes machine
      { state := .seekCopyDone
        tape := SerializedShift.cursorTape
          (copyLeftRev marked remaining)
          (MachineCodeSymbol.done :: suffix) }
      (copyInsertConfig marked remaining suffix) := by
    cases hleft : copyLeftRev marked remaining with
    | nil => exact (copyLeftRev_ne_nil marked remaining hleft).elim
    | cons current leftTail =>
        simpa [copyInsertConfig, hleft] using
          computes_copy_done_bounce current leftTail suffix
  exact TuringMachine.computes_trans hscan
    (TuringMachine.Computes.step hmark
      (TuringMachine.computes_trans hsourceTicks
        (TuringMachine.Computes.step hsourceDone
          (TuringMachine.computes_trans hcopyTicks hbounce))))
  done

theorem replicate_append_singleton
    (count : Nat) (symbol : MachineCodeSymbol) :
    List.append (List.replicate count symbol) [symbol] =
      List.replicate (count + 1) symbol := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ] using
        congrArg (fun word => symbol :: word) ih
  done

theorem replicate_append_cons_same
    (count : Nat) (symbol : MachineCodeSymbol)
    (suffix : List MachineCodeSymbol) :
    List.append (List.replicate count symbol) (symbol :: suffix) =
      List.append (List.replicate (count + 1) symbol) suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ] using
        congrArg (fun word => symbol :: word) ih
  done

theorem copy_insert_output_eq_workWord
    (marked remaining : Nat)
    (suffix : List MachineCodeSymbol) :
    PhysicalBranch.insertOutput copyBuffer
        (copyLeftRev marked remaining)
        (MachineCodeSymbol.done :: suffix) =
      workWord (marked + 1) remaining suffix := by
  simp [PhysicalBranch.insertOutput, copyBuffer, copyLeftRev,
    workWord, List.reverse_append, List.reverse_replicate,
    List.append_assoc]
  exact congrArg
    (fun tail : List MachineCodeSymbol =>
      List.append
        (List.replicate (marked + 1) MachineCodeSymbol.blank)
        (List.append
          (List.replicate remaining MachineCodeSymbol.tick)
          (MachineCodeSymbol.done :: tail)))
    (replicate_append_cons_same marked MachineCodeSymbol.tick
      (MachineCodeSymbol.done :: suffix))
  done

theorem computes_copy_round_canonical
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (inputWorkConfig marked (remaining + 1) suffix)
      (workConfig (marked + 1) remaining suffix) := by
  have hprelude := computes_copy_prelude marked remaining suffix
  have hinsertInner := InsertRestagedMachine.run_exact copyBuffer
    (copyLeftRev marked remaining)
    (MachineCodeSymbol.done :: suffix) (by simp [copyBuffer])
  have hinsert := insert_run_of_some .copy _ _ _ hinsertInner
  have hinsertComp : TuringMachine.Computes machine
      (copyInsertConfig marked remaining suffix)
      (insertConfig .copy
        (InsertRestagedMachine.rewindConfig
          (RewindWord.gateConfig
            (PhysicalBranch.insertOutput copyBuffer
              (copyLeftRev marked remaining)
              (MachineCodeSymbol.done :: suffix)) 0))) := by
    simpa [copyInsertConfig, insertConfig,
      InsertRestagedMachine.editConfig,
      InsertRestagedMachine.machine, InsertBlock.config] using
        TuringMachine.computesIn_to_computes
          (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hinsert)
  have houtputEq := copy_insert_output_eq_workWord marked remaining
    (show List MachineCodeSymbol from suffix)
  have houtput : PhysicalBranch.insertOutput copyBuffer
      (copyLeftRev marked remaining)
      (MachineCodeSymbol.done :: suffix) ≠ [] := by
    rw [houtputEq]
    simp [workWord, List.replicate_succ]
  have hreturn := insert_return_run_exact .copy
    (RewindWord.gateTape
      (PhysicalBranch.insertOutput copyBuffer
        (copyLeftRev marked remaining)
        (MachineCodeSymbol.done :: suffix)) 0)
  have hreturnRun : machine.runConfigExact? 2
      (insertConfig .copy
        (InsertRestagedMachine.rewindConfig
          (RewindWord.gateConfig
            (PhysicalBranch.insertOutput copyBuffer
              (copyLeftRev marked remaining)
              (MachineCodeSymbol.done :: suffix)) 0))) =
      some (workConfig (marked + 1) remaining suffix) := by
    rw [roundTrip_gateTape _ houtput] at hreturn
    have htarget :
        { state := Control.scan
          tape := RewindWord.gateTape
            (PhysicalBranch.insertOutput copyBuffer
              (copyLeftRev marked remaining)
              (MachineCodeSymbol.done :: suffix)) 0 } =
          workConfig (marked + 1) remaining suffix := by
      rw [houtputEq]
      rfl
    rw [← htarget]
    simpa [insertConfig, InsertRestagedMachine.rewindConfig,
      InsertRestagedMachine.machine, RewindWord.gateConfig,
      phaseBuffer] using hreturn
  have hreturnComp := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hreturnRun)
  exact TuringMachine.computes_trans hprelude
    (TuringMachine.computes_trans hinsertComp hreturnComp)
  done

theorem computes_copy_round_of_tape_equiv
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input (workWord marked (remaining + 1) suffix)) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .scan, tape := tape }
        { state := .scan, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input (workWord (marked + 1) remaining suffix))
        targetTape := by
  rcases TuringMachine.computes_to_computesIn
      (computes_copy_round_canonical marked remaining suffix) with
    ⟨steps, hcanonical⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonical (by simpa [inputWorkConfig] using htape) with
    ⟨targetConfig', hrun, hstate, htarget⟩
  rcases targetConfig' with ⟨targetState, targetTape⟩
  simp only [workConfig] at hstate
  subst targetState
  refine ⟨targetTape, ?_, ?_⟩
  · simpa [inputWorkConfig] using
      TuringMachine.computesIn_to_computes hrun
  · exact Tape.Equiv.trans
      (Tape.Equiv.symm
        (RewindWord.gateTape_equiv_input
          (workWord (marked + 1) remaining suffix) 0))
      htarget
  done

theorem computes_copy_remaining
    (marked remaining : Nat)
    (suffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input (workWord marked remaining suffix)) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .scan, tape := tape }
        { state := .scan, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input (workWord (marked + remaining) 0 suffix))
        targetTape := by
  induction remaining generalizing marked tape with
  | zero =>
      refine ⟨tape, TuringMachine.Computes.refl _, ?_⟩
      simpa using htape
  | succ remaining ih =>
      rcases computes_copy_round_of_tape_equiv
          marked remaining suffix tape (by
            simpa [Nat.add_eq, Nat.succ_eq_add_one] using htape) with
        ⟨middleTape, hround, hmiddle⟩
      rcases ih (marked + 1) middleTape hmiddle with
        ⟨targetTape, hremaining, htarget⟩
      refine ⟨targetTape,
        TuringMachine.computes_trans hround hremaining, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htarget
  done

def restoreTail
    (copied : Nat) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    List.append
      (List.replicate copied MachineCodeSymbol.tick)
      (MachineCodeSymbol.done :: suffix)

def restoreTape
    (remaining restored : Nat)
    (tail : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remaining with
  | 0 =>
      { left := []
        head := none
        right :=
          (List.append
            (List.replicate restored MachineCodeSymbol.tick)
            tail).map some }
  | remaining + 1 =>
      SerializedShift.cursorTape
        (List.replicate remaining MachineCodeSymbol.blank)
        (MachineCodeSymbol.blank ::
          List.append
            (List.replicate restored MachineCodeSymbol.tick)
            tail)

def restoreConfig
    (remaining restored : Nat)
    (tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .restore
  tape := restoreTape remaining restored tail

theorem restoreConfig_step
    (remaining restored : Nat)
    (tail : Word MachineCodeSymbol) :
    machine.stepConfig (restoreConfig (remaining + 1) restored tail) =
      some (restoreConfig remaining (restored + 1) tail) := by
  cases remaining <;> cases restored <;> cases tail <;> rfl
  done

theorem computes_restore_markers
    (remaining restored : Nat)
    (tail : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (restoreConfig remaining restored tail)
      (restoreConfig 0 (restored + remaining) tail) := by
  induction remaining generalizing restored with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ remaining ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (by simpa [Nat.succ_eq_add_one] using
            restoreConfig_step remaining restored tail))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (restored + 1))
  done

def restoredOutputTape
    (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.right
    { left := []
      head := none
      right := word.map some }

theorem restore_finish_step
    (restored : Nat) (tail : Word MachineCodeSymbol) :
    machine.stepConfig (restoreConfig 0 restored tail) =
      some
        { state := .halt
          tape := restoredOutputTape
            (List.append
              (List.replicate restored MachineCodeSymbol.tick)
              tail) } := by
  rfl

theorem restoredOutputTape_equiv_input
    (word : Word MachineCodeSymbol) :
    Tape.Equiv (Tape.input word) (restoredOutputTape word) := by
  cases word <;>
    simp [restoredOutputTape, Tape.input, Tape.blank, Tape.move,
      Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]
  done

theorem inputWorkConfig_zero_eq_cursor
    (marked : Nat) (suffix : Word MachineCodeSymbol) :
    inputWorkConfig marked 0 suffix =
      { state := .scan
        tape := SerializedShift.cursorTape []
          (workWord marked 0 suffix) } := by
  cases marked <;>
    simp [inputWorkConfig, workWord, Tape.input,
      SerializedShift.cursorTape, List.replicate_succ]
  done

theorem scan_done_restore_step
    (marked copied : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .scan
          tape := SerializedShift.cursorTape
            (List.replicate marked MachineCodeSymbol.blank)
            (restoreTail copied suffix) } =
      some (restoreConfig marked 0 (restoreTail copied suffix)) := by
  cases marked <;> cases copied <;> cases suffix <;> rfl
  done

theorem computes_to_restore
    (marked : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (inputWorkConfig marked 0 suffix)
      (restoreConfig marked 0 (restoreTail marked suffix)) := by
  have hscan : TuringMachine.Computes machine
      (inputWorkConfig marked 0 suffix)
      { state := .scan
        tape := SerializedShift.cursorTape
          (List.replicate marked MachineCodeSymbol.blank)
          (restoreTail marked suffix) } := by
    rw [inputWorkConfig_zero_eq_cursor]
    simpa [workWord, restoreTail, List.reverse_replicate,
      List.append_assoc] using
        computes_scan_blanks marked ([] : Word MachineCodeSymbol)
          (restoreTail marked suffix)
  exact TuringMachine.computes_trans hscan
    (TuringMachine.Computes.step
      (TuringMachine.stepConfig_eq_some_iff_step.mp
        (scan_done_restore_step marked marked suffix))
      (TuringMachine.Computes.refl _))
  done

theorem computes_restore_canonical
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (inputWorkConfig value 0 suffix)
      { state := .halt
        tape := restoredOutputTape (targetWord value suffix) } := by
  have henter := computes_to_restore value suffix
  have hmarkers := computes_restore_markers value 0
    (restoreTail value suffix)
  have hfinish : TuringMachine.Computes machine
      (restoreConfig 0 value (restoreTail value suffix))
      { state := .halt
        tape := restoredOutputTape (targetWord value suffix) } := by
    exact TuringMachine.Computes.step
      (by
        simpa [restoreTail, targetWord_eq, List.append_assoc] using
          TuringMachine.stepConfig_eq_some_iff_step.mp
            (restore_finish_step value (restoreTail value suffix)))
      (TuringMachine.Computes.refl _)
  exact TuringMachine.computes_trans henter
    (TuringMachine.computes_trans (by simpa using hmarkers) hfinish)
  done

theorem computes_restore_of_tape_equiv
    (value : Nat) (suffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input (workWord value 0 suffix)) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .scan, tape := tape }
        { state := .halt, tape := targetTape } ∧
      Tape.Equiv (targetConfig value suffix).tape targetTape := by
  rcases TuringMachine.computes_to_computesIn
      (computes_restore_canonical value suffix) with
    ⟨steps, hcanonical⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonical (by simpa [inputWorkConfig] using htape) with
    ⟨targetConfig', hrun, hstate, htarget⟩
  rcases targetConfig' with ⟨targetState, targetTape⟩
  simp only at hstate
  subst targetState
  refine ⟨targetTape, ?_, ?_⟩
  · simpa [inputWorkConfig] using
      TuringMachine.computesIn_to_computes hrun
  · exact Tape.Equiv.trans
      (by
        simpa [targetConfig] using
          restoredOutputTape_equiv_input (targetWord value suffix))
      htarget
  done

theorem computes_suffix_preserving
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (sourceConfig value suffix)
        { state := .halt, tape := targetTape } ∧
      Tape.Equiv (targetConfig value suffix).tape targetTape := by
  have hinitial : TuringMachine.Computes machine
      (sourceConfig value suffix) (workConfig 0 value suffix) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (initial_run_exact value suffix))
  have hinitialTape : Tape.Equiv
      (Tape.input (workWord 0 value suffix))
      (workConfig 0 value suffix).tape :=
    Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input (workWord 0 value suffix) 0)
  rcases computes_copy_remaining 0 value suffix
      (workConfig 0 value suffix).tape hinitialTape with
    ⟨copiedTape, hcopy, hcopiedTape⟩
  have hcopiedTape' : Tape.Equiv
      (Tape.input (workWord value 0 suffix)) copiedTape := by
    simpa using hcopiedTape
  rcases computes_restore_of_tape_equiv value suffix
      copiedTape hcopiedTape' with
    ⟨targetTape, hrestore, htarget⟩
  exact ⟨targetTape,
    TuringMachine.computes_trans hinitial
      (TuringMachine.computes_trans hcopy hrestore),
    htarget⟩
  done

theorem restore_mark_step
    (leftCurrent : MachineCodeSymbol)
    (leftTail rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .restore
          tape := SerializedShift.cursorTape (leftCurrent :: leftTail)
            (MachineCodeSymbol.blank :: rest) } =
      some
        { state := .restore
          tape := SerializedShift.cursorTape leftTail
            (leftCurrent :: MachineCodeSymbol.tick :: rest) } := by
  cases rest <;> rfl

end FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator

end Computability
end FoC
