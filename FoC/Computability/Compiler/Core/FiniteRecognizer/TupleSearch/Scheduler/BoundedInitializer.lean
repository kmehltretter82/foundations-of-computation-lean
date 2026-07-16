import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.SplitLayout

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace TupleSearch
namespace Scheduler.BoundedInitializer

open ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

abbrev Frame := Scheduler.Layout.Frame

def initialFrame
    (budget : Nat) (input : Word MachineCodeSymbol) : Frame where
  geometry := .bounded budget
  cursor := Scheduler.Layout.Cursor.initial
  input := input

theorem initialFrame_valid
    (budget : Nat) (input : Word MachineCodeSymbol) :
    (initialFrame budget input).cursor.Valid
      (initialFrame budget input).geometry := by
  exact Scheduler.Layout.Cursor.initial_valid (.bounded budget)
  done

inductive DuplicatePhase where
  | first
  | second
deriving DecidableEq

namespace DuplicatePhase

def finite : Foundation.FiniteType DuplicatePhase where
  elems := [.first, .second]
  complete := by
    intro phase
    cases phase <;> simp

end DuplicatePhase

inductive InsertPhase where
  | candidateTail
  | innerSplit
  | outerPrefix
  | leading
deriving DecidableEq

namespace InsertPhase

def elems : List InsertPhase :=
  [.candidateTail, .innerSplit, .outerPrefix, .leading]

def finite : Foundation.FiniteType InsertPhase where
  elems := elems
  complete := by
    intro phase
    cases phase <;> simp [elems]

def word : InsertPhase -> Word MachineCodeSymbol
  | .candidateTail =>
      [.moveLeft, .done, .done, .done]
  | .innerSplit =>
      [.done, .transition]
  | .outerPrefix =>
      [.done, .done, .transition, .done, .done, .transition]
  | .leading =>
      [.header, .zero]

def buffer (phase : InsertPhase) : InsertBlock.Buffer where
  word := phase.word
  length_le := by
    cases phase <;> decide

theorem word_nonempty (phase : InsertPhase) : phase.word ≠ [] := by
  cases phase <;> decide
  done

end InsertPhase

inductive ScanFields where
  | one
  | two
  | three
deriving DecidableEq

namespace ScanFields

def finite : Foundation.FiniteType ScanFields where
  elems := [.one, .two, .three]
  complete := by
    intro fields
    cases fields <;> simp

end ScanFields

inductive Control where
  | duplicate (phase : DuplicatePhase)
      (inner : FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.Control)
  | duplicateBounce (phase : DuplicatePhase)
  | scan (phase : InsertPhase) (fields : ScanFields)
  | insert (phase : InsertPhase)
      (inner : InsertRestagedMachine.Control)
  | insertBounce (phase : InsertPhase)
deriving DecidableEq

namespace Control

def duplicateFinite : Foundation.FiniteType
    (DuplicatePhase × FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.Control) :=
  Foundation.FiniteType.prod DuplicatePhase.finite
    FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.Control.finite

def scanFinite : Foundation.FiniteType (InsertPhase × ScanFields) :=
  Foundation.FiniteType.prod InsertPhase.finite ScanFields.finite

def insertFinite : Foundation.FiniteType
    (InsertPhase × InsertRestagedMachine.Control) :=
  Foundation.FiniteType.prod InsertPhase.finite
    InsertRestagedMachine.Control.finite

def elems : List Control :=
  duplicateFinite.elems.map
      (fun payload => duplicate payload.1 payload.2) ++
    DuplicatePhase.finite.elems.map duplicateBounce ++
    scanFinite.elems.map
      (fun payload => scan payload.1 payload.2) ++
    insertFinite.elems.map
      (fun payload => insert payload.1 payload.2) ++
    InsertPhase.finite.elems.map insertBounce

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | duplicate phase inner =>
        simp [elems]
        exact duplicateFinite.complete (phase, inner)
    | duplicateBounce phase =>
        simp [elems]
        exact DuplicatePhase.finite.complete phase
    | scan phase fields =>
        simp [elems]
        exact scanFinite.complete (phase, fields)
    | insert phase inner =>
        simp [elems]
        exact insertFinite.complete (phase, inner)
    | insertBounce phase =>
        simp [elems]
        exact InsertPhase.finite.complete phase

end Control

def mapDuplicateAction (phase : DuplicatePhase) :
    Option MachineCodeSymbol × Direction ×
        FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.Control ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) =>
      (write, direction, .duplicate phase target)

def mapInsertAction (phase : InsertPhase) :
    Option MachineCodeSymbol × Direction ×
        InsertRestagedMachine.Control ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) =>
      (write, direction, .insert phase target)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .duplicate phase inner, read =>
      if inner = FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.halt then
        some (read, Direction.left, .duplicateBounce phase)
      else
        Option.map (mapDuplicateAction phase)
          (FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.transition inner read)
  | .duplicateBounce .first, read =>
      some
        (read, Direction.right,
          .duplicate .second FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.start)
  | .duplicateBounce .second, read =>
      some (read, Direction.right, .scan .candidateTail .three)
  | .scan phase fields, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right,
        .scan phase fields)
  | .scan phase .three, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right,
        .scan phase .two)
  | .scan phase .two, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right,
        .scan phase .one)
  | .scan phase .one, some MachineCodeSymbol.done =>
      some
        (some MachineCodeSymbol.done, Direction.right,
          .insert phase
            (InsertRestagedMachine.machine phase.buffer).start)
  | .insert .leading inner, read =>
      Option.map (mapInsertAction .leading)
        (InsertRestagedMachine.transition inner read)
  | .insert phase inner, read =>
      if inner = (InsertRestagedMachine.machine phase.buffer).halt then
        some (read, Direction.left, .insertBounce phase)
      else
        Option.map (mapInsertAction phase)
          (InsertRestagedMachine.transition inner read)
  | .insertBounce .candidateTail, read =>
      some (read, Direction.right, .scan .innerSplit .two)
  | .insertBounce .innerSplit, read =>
      some (read, Direction.right, .scan .outerPrefix .one)
  | .insertBounce .outerPrefix, read =>
      some
        (read, Direction.right,
          .insert .leading
            (InsertRestagedMachine.machine
              (InsertPhase.buffer .leading)).start)
  | .insertBounce .leading, _ => none
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .duplicate .first FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.start
  halt := .insert .leading
    (InsertRestagedMachine.machine (InsertPhase.buffer .leading)).halt
  transition := transition
  statesFinite := Control.finite

def sourceConfig
    (budget : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := machine.start
  tape := Tape.input (GeneratedCode.stageCode input budget)

def targetConfig
    (budget : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := machine.halt
  tape := Tape.input
    (Scheduler.SplitLayout.encode (initialFrame budget input))

def tripleBudgetWord
    (budget : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend budget
    (MachineDescription.encodeNatAppend budget
      (MachineDescription.encodeNatAppend budget input))

def candidateTailWord
    (budget : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend budget
    (MachineDescription.encodeNatAppend budget
      (MachineDescription.encodeNatAppend budget
        (List.append InsertPhase.candidateTail.word input)))

def innerSplitWord
    (budget : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend budget
    (MachineDescription.encodeNatAppend budget
      (List.append InsertPhase.innerSplit.word
        (MachineDescription.encodeNatAppend budget
          (List.append InsertPhase.candidateTail.word input))))

def outerPrefixWord
    (budget : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend budget
    (List.append InsertPhase.outerPrefix.word
      (MachineDescription.encodeNatAppend budget
        (List.append InsertPhase.innerSplit.word
          (MachineDescription.encodeNatAppend budget
            (List.append InsertPhase.candidateTail.word input)))))

def assembledWord
    (budget : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append InsertPhase.leading.word (outerPrefixWord budget input)

theorem assembledWord_eq_encode_initialFrame
    (budget : Nat) (input : Word MachineCodeSymbol) :
    assembledWord budget input =
      Scheduler.SplitLayout.encode (initialFrame budget input) := by
  simp [assembledWord, outerPrefixWord, initialFrame, InsertPhase.word,
    Scheduler.SplitLayout.encode,
    Scheduler.SplitLayout.encodeSplitAppend,
    Scheduler.SplitLayout.candidateWord,
    Scheduler.SplitLayout.candidateMarker,
    Scheduler.SplitLayout.splitMarker,
    Scheduler.Layout.encodeGeometryAppend,
    Scheduler.Layout.Geometry.pairBound,
    Scheduler.Layout.Cursor.initial,
    GeneratedCode.nestedStageCode, GeneratedCode.stageCode,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat]
  done

def duplicateConfig
    (phase : DuplicatePhase)
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .duplicate phase config.state
  tape := config.tape

def insertConfig
    (phase : InsertPhase)
    (config : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .insert phase config.state
  tape := config.tape

theorem duplicate_step_of_some
    (phase : DuplicatePhase)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.Control)
    (hstep : FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.stepConfig source =
      some target) :
    machine.stepConfig (duplicateConfig phase source) =
      some (duplicateConfig phase target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine] at hstep
      cases htransition :
          FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.transition inner
            (Tape.read tape) with
      | none =>
          simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : inner ≠
              FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.halt := by
            intro hhalt
            subst inner
            simp [FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine,
              FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.transition] at htransition
          simp [machine, transition, duplicateConfig, hnot,
            htransition, mapDuplicateAction]
  done

theorem duplicate_computes
    (phase : DuplicatePhase)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.Control}
    (hcomp : TuringMachine.Computes
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine source target) :
    TuringMachine.Computes machine
      (duplicateConfig phase source) (duplicateConfig phase target) := by
  induction hcomp with
  | refl config =>
      exact TuringMachine.Computes.refl _
  | step hstep _ ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (duplicate_step_of_some phase _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih
  done

theorem insert_step_of_some
    (phase : InsertPhase)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control)
    (hstep : (InsertRestagedMachine.machine phase.buffer).stepConfig
      source = some target) :
    machine.stepConfig (insertConfig phase source) =
      some (insertConfig phase target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [InsertRestagedMachine.machine] at hstep
      cases htransition : InsertRestagedMachine.transition inner
          (Tape.read tape) with
      | none =>
          simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          cases phase with
          | leading =>
              simp [machine, transition, insertConfig, htransition,
                mapInsertAction]
          | candidateTail =>
              have hnot : inner ≠
                  (InsertRestagedMachine.machine
                    InsertPhase.candidateTail.buffer).halt := by
                intro hhalt
                subst inner
                simp [InsertRestagedMachine.machine,
                  InsertRestagedMachine.transition,
                  RewindWord.transition] at htransition
              simp [machine, transition, insertConfig, hnot, htransition,
                mapInsertAction]
          | innerSplit =>
              have hnot : inner ≠
                  (InsertRestagedMachine.machine
                    InsertPhase.innerSplit.buffer).halt := by
                intro hhalt
                subst inner
                simp [InsertRestagedMachine.machine,
                  InsertRestagedMachine.transition,
                  RewindWord.transition] at htransition
              simp [machine, transition, insertConfig, hnot, htransition,
                mapInsertAction]
          | outerPrefix =>
              have hnot : inner ≠
                  (InsertRestagedMachine.machine
                    InsertPhase.outerPrefix.buffer).halt := by
                intro hhalt
                subst inner
                simp [InsertRestagedMachine.machine,
                  InsertRestagedMachine.transition,
                  RewindWord.transition] at htransition
              simp [machine, transition, insertConfig, hnot, htransition,
                mapInsertAction]
  done

theorem insert_computes
    (phase : InsertPhase)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control}
    (hcomp : TuringMachine.Computes
      (InsertRestagedMachine.machine phase.buffer) source target) :
    TuringMachine.Computes machine
      (insertConfig phase source) (insertConfig phase target) := by
  induction hcomp with
  | refl config =>
      exact TuringMachine.Computes.refl _
  | step hstep _ ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (insert_step_of_some phase _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih
  done

def sameHeadRoundTrip
    (tape : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.right (Tape.move Direction.left tape)

theorem sameHeadRoundTrip_equiv
    (tape : Tape MachineCodeSymbol) :
    Tape.Equiv tape (sameHeadRoundTrip tape) := by
  cases tape with
  | mk left head right =>
      cases left <;>
        simp [sameHeadRoundTrip, Tape.move, Tape.moveLeft,
          Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]
  done

private theorem write_read_eq_self
    (tape : Tape MachineCodeSymbol) :
    Tape.write (Tape.read tape) tape = tape := by
  cases tape
  rfl

theorem first_duplicate_handoff
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .duplicate .first
          FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.halt
        tape := tape }
      { state := .duplicate .second
          FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.start
        tape := sameHeadRoundTrip tape } := by
  let middle : TuringMachine.Configuration MachineCodeSymbol Control :=
    { state := .duplicateBounce .first
      tape := Tape.move Direction.left tape }
  have hfirst : machine.stepConfig
      { state := .duplicate .first
          FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.halt
        tape := tape } = some middle := by
    simp [middle, machine, TuringMachine.stepConfig, transition,
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine, write_read_eq_self]
  have hsecond : machine.stepConfig middle =
      some
        { state := .duplicate .second
            FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.start
          tape := sameHeadRoundTrip tape } := by
    simp [middle, machine, TuringMachine.stepConfig, transition,
      sameHeadRoundTrip, write_read_eq_self]
  exact TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp hfirst)
    (TuringMachine.Computes.step
      (TuringMachine.stepConfig_eq_some_iff_step.mp hsecond)
      (TuringMachine.Computes.refl _))
  done

theorem second_duplicate_handoff
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .duplicate .second
          FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.halt
        tape := tape }
      { state := .scan .candidateTail .three
        tape := sameHeadRoundTrip tape } := by
  let middle : TuringMachine.Configuration MachineCodeSymbol Control :=
    { state := .duplicateBounce .second
      tape := Tape.move Direction.left tape }
  have hfirst : machine.stepConfig
      { state := .duplicate .second
          FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.halt
        tape := tape } = some middle := by
    simp [middle, machine, TuringMachine.stepConfig, transition,
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine, write_read_eq_self]
  have hsecond : machine.stepConfig middle =
      some
        { state := .scan .candidateTail .three
          tape := sameHeadRoundTrip tape } := by
    simp [middle, machine, TuringMachine.stepConfig, transition,
      sameHeadRoundTrip, write_read_eq_self]
  exact TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp hfirst)
    (TuringMachine.Computes.step
      (TuringMachine.stepConfig_eq_some_iff_step.mp hsecond)
      (TuringMachine.Computes.refl _))
  done

def scanConfig
    (phase : InsertPhase) (fields : ScanFields)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan phase fields
  tape := SerializedShift.cursorTape leftRev rest

theorem scan_tick_step
    (phase : InsertPhase) (fields : ScanFields)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (scanConfig phase fields leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (scanConfig phase fields
          (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl
  done

theorem scan_done_three_step
    (phase : InsertPhase)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (scanConfig phase .three leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some
        (scanConfig phase .two
          (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl
  done

theorem scan_done_two_step
    (phase : InsertPhase)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (scanConfig phase .two leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some
        (scanConfig phase .one
          (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl
  done

theorem scan_done_one_step
    (phase : InsertPhase)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (scanConfig phase .one leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some
        (insertConfig phase
          (InsertRestagedMachine.editConfig
            (InsertBlock.config phase.buffer
              (MachineCodeSymbol.done :: leftRev) suffix))) := by
  cases phase <;> cases suffix <;> rfl
  done

theorem computes_scan_ticks
    (phase : InsertPhase) (fields : ScanFields)
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (scanConfig phase fields leftRev
        (List.append
          (List.replicate count MachineCodeSymbol.tick) suffix))
      (scanConfig phase fields
        (List.append
          (List.replicate count MachineCodeSymbol.tick).reverse
          leftRev) suffix) := by
  induction count generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ count ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [List.replicate_succ] using
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (scan_tick_step phase fields leftRev
                (List.append
                  (List.replicate count MachineCodeSymbol.tick)
                  suffix)))
        (by
          simpa [List.replicate_succ, List.reverse_cons,
            List.append_assoc] using
              ih (MachineCodeSymbol.tick :: leftRev))
  done

def fieldLeftRev
    (value : Nat) (leftRev : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat value).reverse leftRev

theorem computes_scan_field_three
    (phase : InsertPhase) (value : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (scanConfig phase .three leftRev
        (MachineDescription.encodeNatAppend value suffix))
      (scanConfig phase .two (fieldLeftRev value leftRev) suffix) := by
  have hticks := computes_scan_ticks phase .three value leftRev
    (MachineCodeSymbol.done :: suffix)
  have hdone := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (scan_done_three_step phase
        (List.append
          (List.replicate value MachineCodeSymbol.tick).reverse leftRev)
        suffix))
    (TuringMachine.Computes.refl _)
  exact TuringMachine.computes_trans
    (by
      simpa [MachineDescription.encodeNatAppend,
        FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.encodeNat_eq_ticks_done] using hticks)
    (by
      simpa [fieldLeftRev,
        FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.encodeNat_eq_ticks_done,
        List.reverse_append, List.append_assoc] using hdone)
  done

theorem computes_scan_field_two
    (phase : InsertPhase) (value : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (scanConfig phase .two leftRev
        (MachineDescription.encodeNatAppend value suffix))
      (scanConfig phase .one (fieldLeftRev value leftRev) suffix) := by
  have hticks := computes_scan_ticks phase .two value leftRev
    (MachineCodeSymbol.done :: suffix)
  have hdone := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (scan_done_two_step phase
        (List.append
          (List.replicate value MachineCodeSymbol.tick).reverse leftRev)
        suffix))
    (TuringMachine.Computes.refl _)
  exact TuringMachine.computes_trans
    (by
      simpa [MachineDescription.encodeNatAppend,
        FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.encodeNat_eq_ticks_done] using hticks)
    (by
      simpa [fieldLeftRev,
        FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.encodeNat_eq_ticks_done,
        List.reverse_append, List.append_assoc] using hdone)
  done

theorem computes_scan_field_one
    (phase : InsertPhase) (value : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (scanConfig phase .one leftRev
        (MachineDescription.encodeNatAppend value suffix))
      (insertConfig phase
        (InsertRestagedMachine.editConfig
          (InsertBlock.config phase.buffer
            (fieldLeftRev value leftRev) suffix))) := by
  have hticks := computes_scan_ticks phase .one value leftRev
    (MachineCodeSymbol.done :: suffix)
  have hdone := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (scan_done_one_step phase
        (List.append
          (List.replicate value MachineCodeSymbol.tick).reverse leftRev)
        suffix))
    (TuringMachine.Computes.refl _)
  exact TuringMachine.computes_trans
    (by
      simpa [MachineDescription.encodeNatAppend,
        FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.encodeNat_eq_ticks_done] using hticks)
    (by
      simpa [fieldLeftRev,
        FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.encodeNat_eq_ticks_done,
        List.reverse_append, List.append_assoc] using hdone)
  done

def insertHaltConfig
    (phase : InsertPhase) (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .insert phase
    (InsertRestagedMachine.machine phase.buffer).halt
  tape := RewindWord.gateTape word 0

theorem computes_insert_from_cursor
    (phase : InsertPhase)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (insertConfig phase
        (InsertRestagedMachine.editConfig
          (InsertBlock.config phase.buffer leftRev suffix)))
      (insertHaltConfig phase
        (PhysicalBranch.insertOutput phase.buffer leftRev suffix)) := by
  have hinsertInner := InsertRestagedMachine.run_exact phase.buffer
    leftRev suffix (InsertPhase.word_nonempty phase)
  have hinsert := insert_computes phase
    (TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        hinsertInner))
  simpa [insertHaltConfig, insertConfig,
    InsertRestagedMachine.rewindConfig, InsertRestagedMachine.machine,
    RewindWord.gateConfig] using hinsert
  done

theorem computes_insert_after_one
    (phase : InsertPhase) (value : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .scan phase .one
        tape := Tape.input
          (MachineDescription.encodeNatAppend value suffix) }
      (insertHaltConfig phase
        (MachineDescription.encodeNatAppend value
          (List.append phase.word suffix))) := by
  have hsource :
      { state := Control.scan phase ScanFields.one
        tape := Tape.input
          (MachineDescription.encodeNatAppend value suffix) } =
        scanConfig phase .one []
          (MachineDescription.encodeNatAppend value suffix) := by
    cases value <;> rfl
  have hscan := computes_scan_field_one phase value
    ([] : Word MachineCodeSymbol) suffix
  have hinsertInner := InsertRestagedMachine.run_exact phase.buffer
    (fieldLeftRev value []) suffix (InsertPhase.word_nonempty phase)
  have hinsert := insert_computes phase
    (TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        hinsertInner))
  have houtput : PhysicalBranch.insertOutput phase.buffer
      (fieldLeftRev value []) suffix =
        MachineDescription.encodeNatAppend value
          (List.append phase.word suffix) := by
    simp [PhysicalBranch.insertOutput, fieldLeftRev,
      InsertPhase.buffer, MachineDescription.encodeNatAppend]
  rw [hsource]
  exact TuringMachine.computes_trans hscan (by
    simpa [insertHaltConfig, insertConfig,
      InsertRestagedMachine.rewindConfig, InsertRestagedMachine.machine,
      RewindWord.gateConfig,
      houtput] using hinsert)
  done

theorem computes_insert_after_two
    (phase : InsertPhase) (first second : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .scan phase .two
        tape := Tape.input
          (MachineDescription.encodeNatAppend first
            (MachineDescription.encodeNatAppend second suffix)) }
      (insertHaltConfig phase
        (MachineDescription.encodeNatAppend first
          (MachineDescription.encodeNatAppend second
            (List.append phase.word suffix)))) := by
  have hsource :
      { state := Control.scan phase ScanFields.two
        tape := Tape.input
          (MachineDescription.encodeNatAppend first
            (MachineDescription.encodeNatAppend second suffix)) } =
        scanConfig phase .two []
          (MachineDescription.encodeNatAppend first
            (MachineDescription.encodeNatAppend second suffix)) := by
    cases first <;> rfl
  have hfirst := computes_scan_field_two phase first
    ([] : Word MachineCodeSymbol)
    (MachineDescription.encodeNatAppend second suffix)
  have hsecond := computes_scan_field_one phase second
    (fieldLeftRev first []) suffix
  have hinsert := computes_insert_from_cursor phase
    (fieldLeftRev second (fieldLeftRev first [])) suffix
  have houtput : PhysicalBranch.insertOutput phase.buffer
      (fieldLeftRev second (fieldLeftRev first [])) suffix =
        MachineDescription.encodeNatAppend first
          (MachineDescription.encodeNatAppend second
            (List.append phase.word suffix)) := by
    simp [PhysicalBranch.insertOutput, fieldLeftRev,
      InsertPhase.buffer, MachineDescription.encodeNatAppend,
      List.reverse_append, List.append_assoc]
  rw [hsource]
  exact TuringMachine.computes_trans hfirst
    (TuringMachine.computes_trans hsecond (by
      simpa [houtput] using hinsert))
  done

theorem computes_insert_after_three
    (phase : InsertPhase) (first second third : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .scan phase .three
        tape := Tape.input
          (MachineDescription.encodeNatAppend first
            (MachineDescription.encodeNatAppend second
              (MachineDescription.encodeNatAppend third suffix))) }
      (insertHaltConfig phase
        (MachineDescription.encodeNatAppend first
          (MachineDescription.encodeNatAppend second
            (MachineDescription.encodeNatAppend third
              (List.append phase.word suffix))))) := by
  have hsource :
      { state := Control.scan phase ScanFields.three
        tape := Tape.input
          (MachineDescription.encodeNatAppend first
            (MachineDescription.encodeNatAppend second
              (MachineDescription.encodeNatAppend third suffix))) } =
        scanConfig phase .three []
          (MachineDescription.encodeNatAppend first
            (MachineDescription.encodeNatAppend second
              (MachineDescription.encodeNatAppend third suffix))) := by
    cases first <;> rfl
  have hfirst := computes_scan_field_three phase first
    ([] : Word MachineCodeSymbol)
    (MachineDescription.encodeNatAppend second
      (MachineDescription.encodeNatAppend third suffix))
  have hsecond := computes_scan_field_two phase second
    (fieldLeftRev first [])
    (MachineDescription.encodeNatAppend third suffix)
  have hthird := computes_scan_field_one phase third
    (fieldLeftRev second (fieldLeftRev first [])) suffix
  have hinsert := computes_insert_from_cursor phase
    (fieldLeftRev third
      (fieldLeftRev second (fieldLeftRev first []))) suffix
  have houtput : PhysicalBranch.insertOutput phase.buffer
      (fieldLeftRev third
        (fieldLeftRev second (fieldLeftRev first []))) suffix =
        MachineDescription.encodeNatAppend first
          (MachineDescription.encodeNatAppend second
            (MachineDescription.encodeNatAppend third
              (List.append phase.word suffix))) := by
    simp [PhysicalBranch.insertOutput, fieldLeftRev,
      InsertPhase.buffer, MachineDescription.encodeNatAppend,
      List.reverse_append, List.append_assoc]
  rw [hsource]
  exact TuringMachine.computes_trans hfirst
    (TuringMachine.computes_trans hsecond
      (TuringMachine.computes_trans hthird (by
        simpa [houtput] using hinsert)))
  done

theorem computes_insert_at_start
    (phase : InsertPhase) (word : Word MachineCodeSymbol)
    (hword : word ≠ []) :
    TuringMachine.Computes machine
      { state := .insert phase
          (InsertRestagedMachine.machine phase.buffer).start
        tape := Tape.input word }
      (insertHaltConfig phase (List.append phase.word word)) := by
  have hsource :
      { state := Control.insert phase
          (InsertRestagedMachine.machine phase.buffer).start
        tape := Tape.input word } =
        insertConfig phase
          (InsertRestagedMachine.editConfig
            (InsertBlock.config phase.buffer [] word)) := by
    cases word with
    | nil => contradiction
    | cons first rest => rfl
  have hinsert := computes_insert_from_cursor phase
    ([] : Word MachineCodeSymbol) word
  rw [hsource]
  simpa [PhysicalBranch.insertOutput, InsertPhase.buffer] using hinsert
  done

theorem computes_of_tape_equiv
    (sourceState targetState : Control)
    (sourceTape canonicalSource canonicalTarget : Tape MachineCodeSymbol)
    (hcomp : TuringMachine.Computes machine
      { state := sourceState, tape := canonicalSource }
      { state := targetState, tape := canonicalTarget })
    (hsource : Tape.Equiv canonicalSource sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := sourceState, tape := sourceTape }
        { state := targetState, tape := targetTape } ∧
      Tape.Equiv canonicalTarget targetTape := by
  rcases TuringMachine.computes_to_computesIn hcomp with
    ⟨steps, hcanonical⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonical hsource with
    ⟨targetConfig', hrun, hstate, htarget⟩
  rcases targetConfig' with ⟨actualState, actualTape⟩
  simp only at hstate
  subst actualState
  exact ⟨actualTape, TuringMachine.computesIn_to_computes hrun,
    htarget⟩
  done

theorem candidateTail_handoff
    (word : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := (insertHaltConfig .candidateTail word).state
        tape := tape }
      { state := .scan .innerSplit .two
        tape := sameHeadRoundTrip tape } := by
  let middle : TuringMachine.Configuration MachineCodeSymbol Control :=
    { state := .insertBounce .candidateTail
      tape := Tape.move Direction.left tape }
  have hfirst : machine.stepConfig
      { state := (insertHaltConfig .candidateTail word).state
        tape := tape } = some middle := by
    simp [middle, insertHaltConfig, machine,
      TuringMachine.stepConfig, transition,
      InsertRestagedMachine.machine, write_read_eq_self]
  have hsecond : machine.stepConfig middle =
      some
        { state := .scan .innerSplit .two
          tape := sameHeadRoundTrip tape } := by
    simp [middle, machine, TuringMachine.stepConfig, transition,
      sameHeadRoundTrip, write_read_eq_self]
  exact TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp hfirst)
    (TuringMachine.Computes.step
      (TuringMachine.stepConfig_eq_some_iff_step.mp hsecond)
      (TuringMachine.Computes.refl _))
  done

theorem innerSplit_handoff
    (word : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := (insertHaltConfig .innerSplit word).state
        tape := tape }
      { state := .scan .outerPrefix .one
        tape := sameHeadRoundTrip tape } := by
  let middle : TuringMachine.Configuration MachineCodeSymbol Control :=
    { state := .insertBounce .innerSplit
      tape := Tape.move Direction.left tape }
  have hfirst : machine.stepConfig
      { state := (insertHaltConfig .innerSplit word).state
        tape := tape } = some middle := by
    simp [middle, insertHaltConfig, machine,
      TuringMachine.stepConfig, transition,
      InsertRestagedMachine.machine, write_read_eq_self]
  have hsecond : machine.stepConfig middle =
      some
        { state := .scan .outerPrefix .one
          tape := sameHeadRoundTrip tape } := by
    simp [middle, machine, TuringMachine.stepConfig, transition,
      sameHeadRoundTrip, write_read_eq_self]
  exact TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp hfirst)
    (TuringMachine.Computes.step
      (TuringMachine.stepConfig_eq_some_iff_step.mp hsecond)
      (TuringMachine.Computes.refl _))
  done

theorem outerPrefix_handoff
    (word : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := (insertHaltConfig .outerPrefix word).state
        tape := tape }
      { state := .insert .leading
          (InsertRestagedMachine.machine
            (InsertPhase.buffer .leading)).start
        tape := sameHeadRoundTrip tape } := by
  let middle : TuringMachine.Configuration MachineCodeSymbol Control :=
    { state := .insertBounce .outerPrefix
      tape := Tape.move Direction.left tape }
  have hfirst : machine.stepConfig
      { state := (insertHaltConfig .outerPrefix word).state
        tape := tape } = some middle := by
    simp [middle, insertHaltConfig, machine,
      TuringMachine.stepConfig, transition,
      InsertRestagedMachine.machine, write_read_eq_self]
  have hsecond : machine.stepConfig middle =
      some
        { state := .insert .leading
            (InsertRestagedMachine.machine
              (InsertPhase.buffer .leading)).start
          tape := sameHeadRoundTrip tape } := by
    simp [middle, machine, TuringMachine.stepConfig, transition,
      sameHeadRoundTrip, write_read_eq_self]
  exact TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp hfirst)
    (TuringMachine.Computes.step
      (TuringMachine.stepConfig_eq_some_iff_step.mp hsecond)
      (TuringMachine.Computes.refl _))
  done

theorem computes_two_budget_duplications
    (budget : Nat) (input : Word MachineCodeSymbol) :
    exists tripleTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (sourceConfig budget input)
        { state := .scan .candidateTail .three
          tape := tripleTape } ∧
      Tape.Equiv (Tape.input (tripleBudgetWord budget input))
        tripleTape := by
  rcases FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.computes_suffix_preserving
      budget input with
    ⟨firstTape, hfirstInner, hfirstTape⟩
  have hfirst := duplicate_computes .first hfirstInner
  have hfirst' : TuringMachine.Computes machine
      (sourceConfig budget input)
      { state := .duplicate .first
          FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.halt
        tape := firstTape } := by
    simpa [sourceConfig, duplicateConfig,
      machine,
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.sourceConfig,
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.sourceWord,
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine,
      GeneratedCode.stageCode] using hfirst
  have hdouble : Tape.Equiv
      (Tape.input
        (MachineDescription.encodeNatAppend budget
          (MachineDescription.encodeNatAppend budget input)))
      firstTape := by
    simpa [FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.targetConfig,
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.targetWord] using hfirstTape
  have hfirstHandoff := first_duplicate_handoff firstTape
  have hsecondSource : Tape.Equiv
      (Tape.input
        (MachineDescription.encodeNatAppend budget
          (MachineDescription.encodeNatAppend budget input)))
      (sameHeadRoundTrip firstTape) :=
    Tape.Equiv.trans hdouble (sameHeadRoundTrip_equiv firstTape)
  rcases FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.computes_suffix_preserving
      budget (MachineDescription.encodeNatAppend budget input) with
    ⟨secondCanonicalTape, hsecondInner, hsecondCanonicalTape⟩
  have hsecondCanonical := duplicate_computes .second hsecondInner
  rcases computes_of_tape_equiv
      (.duplicate .second FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.start)
      (.duplicate .second FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.machine.halt)
      (sameHeadRoundTrip firstTape)
      (Tape.input
        (MachineDescription.encodeNatAppend budget
          (MachineDescription.encodeNatAppend budget input)))
      secondCanonicalTape hsecondCanonical hsecondSource with
    ⟨secondTape, hsecond, hsecondTape⟩
  have htripleCanonical : Tape.Equiv
      (Tape.input (tripleBudgetWord budget input))
      secondCanonicalTape := by
    simpa [tripleBudgetWord,
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.targetConfig,
      FiniteRecognizer.TupleSearch.Scheduler.UnaryFieldDuplicator.targetWord] using
        hsecondCanonicalTape
  have htriple : Tape.Equiv
      (Tape.input (tripleBudgetWord budget input)) secondTape :=
    Tape.Equiv.trans htripleCanonical hsecondTape
  have hsecondHandoff := second_duplicate_handoff secondTape
  refine ⟨sameHeadRoundTrip secondTape, ?_, ?_⟩
  · exact TuringMachine.computes_trans hfirst'
      (TuringMachine.computes_trans hfirstHandoff
        (TuringMachine.computes_trans hsecond hsecondHandoff))
  · exact Tape.Equiv.trans htriple
      (sameHeadRoundTrip_equiv secondTape)
  done

theorem computes_layout_assembly
    (budget : Nat) (input : Word MachineCodeSymbol)
    (tripleTape : Tape MachineCodeSymbol)
    (htriple : Tape.Equiv
      (Tape.input (tripleBudgetWord budget input)) tripleTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .scan .candidateTail .three
          tape := tripleTape }
        { state := machine.halt, tape := targetTape } ∧
      Tape.Equiv (targetConfig budget input).tape targetTape := by
  have hcandidateCanonical : TuringMachine.Computes machine
      { state := .scan .candidateTail .three
        tape := Tape.input (tripleBudgetWord budget input) }
      (insertHaltConfig .candidateTail
        (candidateTailWord budget input)) := by
    simpa [tripleBudgetWord, candidateTailWord] using
      computes_insert_after_three .candidateTail
        budget budget budget input
  rcases computes_of_tape_equiv
      (.scan .candidateTail .three)
      (insertHaltConfig .candidateTail
        (candidateTailWord budget input)).state
      tripleTape
      (Tape.input (tripleBudgetWord budget input))
      (insertHaltConfig .candidateTail
        (candidateTailWord budget input)).tape
      hcandidateCanonical htriple with
    ⟨candidateTape, hcandidate, hcandidateTape⟩
  have hcandidateHandoff := candidateTail_handoff
    (candidateTailWord budget input) candidateTape
  have hinnerSource : Tape.Equiv
      (Tape.input (candidateTailWord budget input))
      (sameHeadRoundTrip candidateTape) :=
    Tape.Equiv.trans
      (Tape.Equiv.trans
        (Tape.Equiv.symm
          (RewindWord.gateTape_equiv_input
            (candidateTailWord budget input) 0))
        hcandidateTape)
      (sameHeadRoundTrip_equiv candidateTape)
  let candidateSuffix : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend budget
      (List.append InsertPhase.candidateTail.word input)
  have hinnerCanonical : TuringMachine.Computes machine
      { state := .scan .innerSplit .two
        tape := Tape.input (candidateTailWord budget input) }
      (insertHaltConfig .innerSplit
        (innerSplitWord budget input)) := by
    simpa [candidateTailWord, innerSplitWord, candidateSuffix] using
      computes_insert_after_two .innerSplit budget budget candidateSuffix
  rcases computes_of_tape_equiv
      (.scan .innerSplit .two)
      (insertHaltConfig .innerSplit
        (innerSplitWord budget input)).state
      (sameHeadRoundTrip candidateTape)
      (Tape.input (candidateTailWord budget input))
      (insertHaltConfig .innerSplit
        (innerSplitWord budget input)).tape
      hinnerCanonical hinnerSource with
    ⟨innerTape, hinner, hinnerTape⟩
  have hinnerHandoff := innerSplit_handoff
    (innerSplitWord budget input) innerTape
  have houterSource : Tape.Equiv
      (Tape.input (innerSplitWord budget input))
      (sameHeadRoundTrip innerTape) :=
    Tape.Equiv.trans
      (Tape.Equiv.trans
        (Tape.Equiv.symm
          (RewindWord.gateTape_equiv_input
            (innerSplitWord budget input) 0))
        hinnerTape)
      (sameHeadRoundTrip_equiv innerTape)
  let outerSuffix : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend budget
      (List.append InsertPhase.innerSplit.word candidateSuffix)
  have houterCanonical : TuringMachine.Computes machine
      { state := .scan .outerPrefix .one
        tape := Tape.input (innerSplitWord budget input) }
      (insertHaltConfig .outerPrefix
        (outerPrefixWord budget input)) := by
    simpa [innerSplitWord, outerPrefixWord, outerSuffix,
      candidateSuffix] using
        computes_insert_after_one .outerPrefix budget outerSuffix
  rcases computes_of_tape_equiv
      (.scan .outerPrefix .one)
      (insertHaltConfig .outerPrefix
        (outerPrefixWord budget input)).state
      (sameHeadRoundTrip innerTape)
      (Tape.input (innerSplitWord budget input))
      (insertHaltConfig .outerPrefix
        (outerPrefixWord budget input)).tape
      houterCanonical houterSource with
    ⟨outerTape, houter, houterTape⟩
  have houterHandoff := outerPrefix_handoff
    (outerPrefixWord budget input) outerTape
  have hleadingSource : Tape.Equiv
      (Tape.input (outerPrefixWord budget input))
      (sameHeadRoundTrip outerTape) :=
    Tape.Equiv.trans
      (Tape.Equiv.trans
        (Tape.Equiv.symm
          (RewindWord.gateTape_equiv_input
            (outerPrefixWord budget input) 0))
        houterTape)
      (sameHeadRoundTrip_equiv outerTape)
  have houterWord : outerPrefixWord budget input ≠ [] := by
    cases budget <;>
      simp [outerPrefixWord, MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat]
  have hleadingCanonical := computes_insert_at_start .leading
    (outerPrefixWord budget input) houterWord
  rcases computes_of_tape_equiv
      (.insert .leading
        (InsertRestagedMachine.machine
          (InsertPhase.buffer .leading)).start)
      (insertHaltConfig .leading
        (assembledWord budget input)).state
      (sameHeadRoundTrip outerTape)
      (Tape.input (outerPrefixWord budget input))
      (insertHaltConfig .leading
        (assembledWord budget input)).tape
      (by simpa [assembledWord] using hleadingCanonical)
      hleadingSource with
    ⟨targetTape, hleading, htargetTape⟩
  refine ⟨targetTape, ?_, ?_⟩
  · simpa [insertHaltConfig, machine,
      InsertRestagedMachine.machine] using
      TuringMachine.computes_trans hcandidate
        (TuringMachine.computes_trans hcandidateHandoff
          (TuringMachine.computes_trans hinner
            (TuringMachine.computes_trans hinnerHandoff
              (TuringMachine.computes_trans houter
                (TuringMachine.computes_trans houterHandoff hleading)))))
  · exact Tape.Equiv.trans
      (U := RewindWord.gateTape (assembledWord budget input) 0)
      (by
        simpa [targetConfig, assembledWord_eq_encode_initialFrame] using
          Tape.Equiv.symm
            (RewindWord.gateTape_equiv_input
              (assembledWord budget input) 0))
      (by
        simpa [insertHaltConfig] using htargetTape)
  done

theorem computes_stageCode_to_initialFrame
    (budget : Nat) (input : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input (GeneratedCode.stageCode input budget) }
        { state := machine.halt, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.SplitLayout.encode
            (initialFrame budget input)))
        targetTape ∧
      (initialFrame budget input).cursor.Valid
        (initialFrame budget input).geometry := by
  rcases computes_two_budget_duplications budget input with
    ⟨tripleTape, hduplicate, htriple⟩
  rcases computes_layout_assembly budget input tripleTape htriple with
    ⟨targetTape, hassembly, htarget⟩
  refine ⟨targetTape, ?_, ?_, initialFrame_valid budget input⟩
  · simpa [sourceConfig] using
      TuringMachine.computes_trans hduplicate hassembly
  · simpa [targetConfig] using htarget
  done

theorem computes_sourceConfig_to_target_equiv
    (budget : Nat) (input : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (sourceConfig budget input)
        { state := machine.halt, tape := targetTape } ∧
      Tape.Equiv (targetConfig budget input).tape targetTape := by
  rcases computes_stageCode_to_initialFrame budget input with
    ⟨targetTape, hrun, htape, _⟩
  exact ⟨targetTape, by simpa [sourceConfig] using hrun,
    by simpa [targetConfig] using htape⟩
  done

end Scheduler.BoundedInitializer
end TupleSearch
end FiniteRecognizer

end Computability
end FoC
