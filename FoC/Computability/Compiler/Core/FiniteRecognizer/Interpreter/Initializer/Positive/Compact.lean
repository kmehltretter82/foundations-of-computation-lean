import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Positive.CopyDriver

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.PositiveInitializerPhase

open FiniteRecognizer ExactFuel StrictProbe
open FiniteRecognizer.Interpreter.InitializerFrontier
open FiniteRecognizer.Interpreter.InitializerPersistentCopy
open FiniteRecognizer.Interpreter.InitializerPersistentCopy.PersistentMasterCopier
open FiniteRecognizer.Interpreter.InitializerRepeatedCopy
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.BoundedLoopInduction
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair

namespace GapCompactor

/-! The marker is always the first nonblank cell to the right of the compacted
prefix.  It therefore remains unambiguous even though the protected source
word itself may contain `header`. -/

inductive Control where
  | enter
  | seekOutput (carried : MachineCodeSymbol)
  | writeOutput (carried : MachineCodeSymbol)
  | seekMarker
  | readNext
  | finishSeek
  | rewindPrefix
  | ready
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.enter, .seekMarker, .readNext, .finishSeek, .rewindPrefix, .ready,
    .halt] ++
  MachineCodeSymbol.finite.elems.map seekOutput ++
  MachineCodeSymbol.finite.elems.map writeOutput

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | enter => simp [elems]
    | seekOutput carried =>
        simp [elems, MachineCodeSymbol.finite.complete carried]
    | writeOutput carried =>
        simp [elems, MachineCodeSymbol.finite.complete carried]
    | seekMarker => simp [elems]
    | readNext => simp [elems]
    | finishSeek => simp [elems]
    | rewindPrefix => simp [elems]
    | ready => simp [elems]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .enter, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.header, Direction.left,
        .seekOutput MachineCodeSymbol.transition)
  | .seekOutput carried, none =>
      some (none, Direction.left, .seekOutput carried)
  | .seekOutput carried, some current =>
      some (some current, Direction.right, .writeOutput carried)
  | .writeOutput carried, none =>
      some (some carried, Direction.right, .seekMarker)
  | .seekMarker, none =>
      some (none, Direction.right, .seekMarker)
  | .seekMarker, some MachineCodeSymbol.header =>
      some (none, Direction.right, .readNext)
  | .readNext, some next =>
      some (some MachineCodeSymbol.header, Direction.left,
        .seekOutput next)
  | .readNext, none =>
      some (none, Direction.left, .finishSeek)
  | .finishSeek, none =>
      some (none, Direction.left, .finishSeek)
  | .finishSeek, some current =>
      some (some current, Direction.left, .rewindPrefix)
  | .rewindPrefix, some current =>
      some (some current, Direction.left, .rewindPrefix)
  | .rewindPrefix, none =>
      some (none, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .enter
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceTape
    (baseWord : Word MachineCodeSymbol)
    (gap : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := List.replicate (gap + 1) none ++ baseWord.reverse.map some
    head := some first
    right := rest.map some ++ [none] }

def sourceConfig
    (baseWord : Word MachineCodeSymbol)
    (gap : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .enter
    tape := sourceTape baseWord gap first rest }

def targetConfig
    (baseWord active : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .ready
    tape := Tape.input (List.append baseWord active) }

def markerConfig
    (compacted : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .seekOutput carried
    tape :=
      { left := List.replicate gap none ++ compacted.reverse.map some
        head := none
        right := some MachineCodeSymbol.header ::
          (remaining.map some ++ [none]) } }

def outputConfig
    (compacted : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .writeOutput carried
    tape :=
      { left := compacted.reverse.map some
        head := none
        right := List.replicate gap none ++
          some MachineCodeSymbol.header ::
            (remaining.map some ++ [none]) } }

def seekMarkerConfig
    (compacted : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .seekMarker
    tape :=
      PersistentMasterCopier.tapeAtCells
        (some carried :: compacted.reverse.map some)
        (List.replicate gap none ++
          some MachineCodeSymbol.header ::
            (remaining.map some ++ [none])) }

def readNextConfig
    (compacted : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .readNext
    tape :=
      PersistentMasterCopier.tapeAtCells
        (none :: List.replicate gap none ++
          some carried :: compacted.reverse.map some)
        (remaining.map some ++ [none]) }

theorem enter_step
    (baseWord : Word MachineCodeSymbol)
    (gap : Nat)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (sourceConfig baseWord gap MachineCodeSymbol.transition rest) =
      some
        (markerConfig baseWord gap MachineCodeSymbol.transition rest) := by
  cases gap <;> cases rest <;> rfl

theorem seekOutput_blank_step
    (carried : MachineCodeSymbol)
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := Control.seekOutput carried
          tape := { left := none :: leftRev, head := none, right := right } } =
      some
        { state := Control.seekOutput carried
          tape := { left := leftRev, head := none, right := none :: right } } := by
  cases leftRev <;> cases right <;> rfl

theorem seekOutput_left_step
    (carried : MachineCodeSymbol)
    (cell : Option MachineCodeSymbol)
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := Control.seekOutput carried
          tape := { left := cell :: leftRev, head := none, right := right } } =
      some
        { state := Control.seekOutput carried
          tape := { left := leftRev, head := cell, right := none :: right } } := by
  cases cell <;> cases leftRev <;> cases right <;> rfl

theorem seekOutput_found_step
    (carried current : MachineCodeSymbol)
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := Control.seekOutput carried
          tape :=
            { left := leftRev, head := some current,
              right := none :: right } } =
      some
        { state := Control.writeOutput carried
          tape :=
            { left := some current :: leftRev, head := none,
              right := right } } := by
  cases leftRev <;> cases right <;> rfl

theorem replicate_append_none
    (count : Nat)
    (tail : List (Option MachineCodeSymbol)) :
    List.replicate count none ++ none :: tail =
      List.replicate (count + 1) none ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ] using congrArg (fun cells => none :: cells) ih

theorem seekOutput_run_aux
    (current : MachineCodeSymbol)
    (leftRev right : List (Option MachineCodeSymbol))
    (gap : Nat)
    (carried : MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .seekOutput carried
        tape :=
          { left := List.replicate gap none ++ some current :: leftRev
            head := none
            right := right } }
      { state := .writeOutput carried
        tape :=
          { left := some current :: leftRev
            head := none
            right := List.replicate gap none ++ right } } := by
  induction gap generalizing right with
  | zero =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa using seekOutput_left_step carried (some current)
            leftRev right))
        (TuringMachine.Computes.step
          (TuringMachine.stepConfig_eq_some_iff_step.mp (by
            simpa using seekOutput_found_step carried current leftRev right))
          (TuringMachine.Computes.refl _))
  | succ gap ih =>
      have hstep : TuringMachine.Step machine
          { state := .seekOutput carried
            tape :=
              { left := List.replicate (gap + 1) none ++
                  some current :: leftRev
                head := none
                right := right } }
          { state := .seekOutput carried
            tape :=
              { left := List.replicate gap none ++ some current :: leftRev
                head := none
                right := none :: right } } := by
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [List.replicate_succ, List.append_assoc] using
            seekOutput_blank_step carried
              (List.replicate gap none ++
                some current :: leftRev) right)
      have htail := ih (none :: right)
      have hrun := TuringMachine.Computes.step hstep htail
      rw [replicate_append_none] at hrun
      simpa [List.replicate_succ, List.append_assoc] using hrun

theorem seekOutput_run
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (markerConfig (first :: rest) gap carried remaining)
      (outputConfig (first :: rest) gap carried remaining) := by
  cases hrev : (first :: rest).reverse with
  | nil =>
      have hlength := congrArg List.length hrev
      simp at hlength
  | cons current leftRev =>
      have h := seekOutput_run_aux current (leftRev.map some)
        (some MachineCodeSymbol.header ::
          (remaining.map some ++ [none])) gap carried
      simpa [markerConfig, outputConfig, hrev] using h

theorem writeOutput_step
    (compacted : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    machine.stepConfig (outputConfig compacted gap carried remaining) =
      some (seekMarkerConfig compacted gap carried remaining) := by
  cases gap <;> cases remaining <;> rfl

theorem seekMarker_blank_step
    (leftRev : List (Option MachineCodeSymbol))
    (right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := Control.seekMarker
          tape := { left := leftRev, head := none, right := right } } =
      some
        { state := Control.seekMarker
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem seekMarker_run_aux
    (leftRev tail : List (Option MachineCodeSymbol))
    (gap : Nat) :
    TuringMachine.Computes machine
      { state := .seekMarker
        tape := PersistentMasterCopier.tapeAtCells leftRev
          (List.replicate gap none ++
            some MachineCodeSymbol.header :: tail) }
      { state := .readNext
        tape := PersistentMasterCopier.tapeAtCells
          (none :: List.replicate gap none ++ leftRev) tail } := by
  induction gap generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp (by
          cases leftRev <;> cases tail <;> rfl))
        (TuringMachine.Computes.refl _)
  | succ gap ih =>
      have hstep : TuringMachine.Step machine
          { state := .seekMarker
            tape := PersistentMasterCopier.tapeAtCells leftRev
              (List.replicate (gap + 1) none ++
                some MachineCodeSymbol.header :: tail) }
          { state := .seekMarker
            tape := PersistentMasterCopier.tapeAtCells
              (none :: leftRev)
              (List.replicate gap none ++
                some MachineCodeSymbol.header :: tail) } := by
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [PersistentMasterCopier.tapeAtCells,
            List.replicate_succ, List.append_assoc] using
            seekMarker_blank_step leftRev
              (List.replicate gap none ++
                some MachineCodeSymbol.header :: tail))
      have htail := ih (none :: leftRev)
      have hrun := TuringMachine.Computes.step hstep htail
      simpa [replicate_append_none, List.append_assoc] using hrun

theorem seekMarker_run
    (compacted : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (seekMarkerConfig compacted gap carried remaining)
      (readNextConfig compacted gap carried remaining) := by
  exact seekMarker_run_aux
    (some carried :: compacted.reverse.map some)
    (remaining.map some ++ [none]) gap

theorem round_cons
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (gap : Nat)
    (carried next : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (markerConfig (first :: rest) gap carried (next :: remaining))
      (markerConfig
        (List.append (first :: rest) [carried]) gap next remaining) := by
  have hseek := seekOutput_run first rest gap carried (next :: remaining)
  have hwrite : TuringMachine.Step machine
      (outputConfig (first :: rest) gap carried (next :: remaining))
      (seekMarkerConfig (first :: rest) gap carried (next :: remaining)) :=
    TuringMachine.stepConfig_eq_some_iff_step.mp
      (writeOutput_step (first :: rest) gap carried (next :: remaining))
  have hmarker := seekMarker_run (first :: rest) gap carried
    (next :: remaining)
  have readNext_symbol_step
      (leftRev : List (Option MachineCodeSymbol))
      (right : List (Option MachineCodeSymbol)) :
      machine.stepConfig
          { state := Control.readNext
            tape :=
              { left := none :: leftRev, head := some next,
                right := right } } =
        some
          { state := Control.seekOutput next
            tape :=
              { left := leftRev, head := none,
                right := some MachineCodeSymbol.header :: right } } := by
    cases leftRev <;> cases right <;> rfl
  have hnext : TuringMachine.Step machine
      (readNextConfig (first :: rest) gap carried (next :: remaining))
      (markerConfig (List.append (first :: rest) [carried]) gap next
        remaining) := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      simpa [readNextConfig, markerConfig,
        PersistentMasterCopier.tapeAtCells,
        List.reverse_append, List.reverse_cons, List.map_append,
        List.append_assoc] using
        readNext_symbol_step
          (List.replicate gap none ++
            some carried :: (first :: rest).reverse.map some)
          (remaining.map some ++ [none]))
  exact TuringMachine.computes_trans hseek
    (TuringMachine.Computes.step hwrite
      (TuringMachine.computes_trans hmarker
        (TuringMachine.Computes.step hnext
          (TuringMachine.Computes.refl _))))

theorem finishSeek_left_step
    (cell : Option MachineCodeSymbol)
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := Control.finishSeek
          tape := { left := cell :: leftRev, head := none, right := right } } =
      some
        { state := Control.finishSeek
          tape := { left := leftRev, head := cell, right := none :: right } } := by
  cases cell <;> cases leftRev <;> cases right <;> rfl

theorem finishSeek_blanks_run
    (current : MachineCodeSymbol)
    (leftRev right : List (Option MachineCodeSymbol))
    (gap : Nat) :
    TuringMachine.Computes machine
      { state := .finishSeek
        tape :=
          { left := List.replicate gap none ++ some current :: leftRev
            head := none
            right := right } }
      { state := .finishSeek
        tape :=
          { left := leftRev
            head := some current
            right := List.replicate (gap + 1) none ++ right } } := by
  induction gap generalizing right with
  | zero =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa using finishSeek_left_step (some current) leftRev right))
        (TuringMachine.Computes.refl _)
  | succ gap ih =>
      have hstep : TuringMachine.Step machine
          { state := .finishSeek
            tape :=
              { left := List.replicate (gap + 1) none ++
                  some current :: leftRev
                head := none
                right := right } }
          { state := .finishSeek
            tape :=
              { left := List.replicate gap none ++ some current :: leftRev
                head := none
                right := none :: right } } := by
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [List.replicate_succ, List.append_assoc] using
            finishSeek_left_step none
              (List.replicate gap none ++ some current :: leftRev) right)
      have htail := ih (none :: right)
      have hrun := TuringMachine.Computes.step hstep htail
      rw [replicate_append_none] at hrun
      simpa [List.replicate_succ, List.append_assoc] using hrun

theorem rewindPrefix_symbol_step
    (current : MachineCodeSymbol)
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := Control.rewindPrefix
          tape :=
            { left := leftRev, head := some current, right := right } } =
      some
        { state := Control.rewindPrefix
          tape := Tape.move Direction.left
            { left := leftRev, head := some current, right := right } } := by
  cases leftRev <;> cases right <;> rfl

def paddedReadyTape
    (word : Word MachineCodeSymbol)
    (padding : Nat) : Tape MachineCodeSymbol :=
  match word with
  | [] => Tape.blank
  | first :: rest =>
      { left := [none]
        head := some first
        right := rest.map some ++ List.replicate padding none }

theorem rewindPrefix_run
    (first : MachineCodeSymbol)
    (beforeRev after : Word MachineCodeSymbol)
    (padding : Nat) :
    TuringMachine.Computes machine
      { state := .rewindPrefix
        tape :=
          { left := beforeRev.map some
            head := some first
            right := after.map some ++ List.replicate padding none } }
      { state := .ready
        tape := paddedReadyTape
          (List.append beforeRev.reverse (first :: after)) padding } := by
  induction beforeRev generalizing first after with
  | nil =>
      have hleft : TuringMachine.Step machine
          { state := .rewindPrefix
            tape :=
              { left := []
                head := some first
                right := after.map some ++ List.replicate padding none } }
          { state := .rewindPrefix
            tape :=
              { left := []
                head := none
                right := some first ::
                  (after.map some ++ List.replicate padding none) } } := by
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          cases after <;> cases padding <;> rfl)
      have hright : TuringMachine.Step machine
          { state := .rewindPrefix
            tape :=
              { left := []
                head := none
                right := some first ::
                  (after.map some ++ List.replicate padding none) } }
          { state := .ready
            tape := paddedReadyTape (first :: after) padding } := by
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          cases after <;> cases padding <;> rfl)
      exact TuringMachine.Computes.step hleft
        (TuringMachine.Computes.step hright
          (TuringMachine.Computes.refl _))
  | cons previous more ih =>
      have hstep : TuringMachine.Step machine
          { state := .rewindPrefix
            tape :=
              { left := (previous :: more).map some
                head := some first
                right := after.map some ++ List.replicate padding none } }
          { state := .rewindPrefix
            tape :=
              { left := more.map some
                head := some previous
                right := (first :: after).map some ++
                  List.replicate padding none } } := by
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          cases more <;> cases after <;> cases padding <;> rfl)
      have htail := ih previous (first :: after)
      simpa [List.reverse_cons, List.append_assoc] using
        TuringMachine.Computes.step hstep htail

theorem finish_from_readNext
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol) :
    TuringMachine.Computes machine
      (readNextConfig (first :: rest) gap carried [])
      { state := .ready
        tape := paddedReadyTape
          (List.append (first :: rest) [carried]) (gap + 2) } := by
  have readNext_none_step
      (leftRev right : List (Option MachineCodeSymbol)) :
      machine.stepConfig
          { state := Control.readNext
            tape := { left := none :: leftRev, head := none, right := right } } =
        some
          { state := Control.finishSeek
            tape := { left := leftRev, head := none, right := none :: right } } := by
    cases leftRev <;> cases right <;> rfl
  have hterminal : TuringMachine.Step machine
      (readNextConfig (first :: rest) gap carried [])
      { state := .finishSeek
        tape :=
          { left := List.replicate gap none ++
              some carried :: (first :: rest).reverse.map some
            head := none
            right := [none] } } := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      simpa [readNextConfig, PersistentMasterCopier.tapeAtCells,
        List.append_assoc] using
        readNext_none_step
          (List.replicate gap none ++
            some carried :: (first :: rest).reverse.map some) [])
  have hseek := finishSeek_blanks_run carried
    ((first :: rest).reverse.map some) [none] gap
  have hseek' : TuringMachine.Computes machine
      { state := .finishSeek
        tape :=
          { left := List.replicate gap none ++
              some carried :: (first :: rest).reverse.map some
            head := none
            right := [none] } }
      { state := .finishSeek
        tape :=
          { left := (first :: rest).reverse.map some
            head := some carried
            right := List.replicate (gap + 2) none } } := by
    simpa [replicate_append_none, List.append_assoc] using hseek
  cases hrev : (first :: rest).reverse with
  | nil =>
      have hlength := congrArg List.length hrev
      simp at hlength
  | cons last beforeRev =>
      have hfound : TuringMachine.Step machine
          { state := .finishSeek
            tape :=
              { left := (first :: rest).reverse.map some
                head := some carried
                right := List.replicate (gap + 2) none } }
          { state := .rewindPrefix
            tape :=
              { left := beforeRev.map some
                head := some last
                right := some carried ::
                  List.replicate (gap + 2) none } } := by
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          rw [hrev]
          cases beforeRev <;> cases gap <;> rfl)
      have hrewind := rewindPrefix_run last beforeRev [carried] (gap + 2)
      have hword :
          List.append beforeRev.reverse [last, carried] =
            List.append (first :: rest) [carried] := by
        have hreverse := congrArg List.reverse hrev
        simp at hreverse
        simp [hreverse, List.append_assoc]
      rw [hword] at hrewind
      exact TuringMachine.Computes.step hterminal
        (TuringMachine.computes_trans hseek'
          (TuringMachine.Computes.step hfound hrewind))

theorem from_marker_computes
    (baseFirst : MachineCodeSymbol)
    (baseRest : Word MachineCodeSymbol)
    (gap : Nat)
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (markerConfig (baseFirst :: baseRest) gap carried remaining)
      { state := .ready
        tape := paddedReadyTape
          (List.append (baseFirst :: baseRest) (carried :: remaining))
          (gap + 2) } := by
  induction remaining generalizing baseRest carried with
  | nil =>
      have hseek := seekOutput_run baseFirst baseRest gap carried []
      have hwrite : TuringMachine.Step machine
          (outputConfig (baseFirst :: baseRest) gap carried [])
          (seekMarkerConfig (baseFirst :: baseRest) gap carried []) :=
        TuringMachine.stepConfig_eq_some_iff_step.mp
          (writeOutput_step (baseFirst :: baseRest) gap carried [])
      have hmarker := seekMarker_run (baseFirst :: baseRest) gap carried []
      have hfinish := finish_from_readNext baseFirst baseRest gap carried
      simpa using TuringMachine.computes_trans hseek
        (TuringMachine.Computes.step hwrite
          (TuringMachine.computes_trans hmarker hfinish))
  | cons next remaining ih =>
      have hround := round_cons baseFirst baseRest gap carried next remaining
      have htail := ih (List.append baseRest [carried]) next
      simpa [List.append_assoc] using
        TuringMachine.computes_trans hround htail

theorem paddedReadyTape_equiv_input
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (padding : Nat) :
    Tape.Equiv (paddedReadyTape (first :: rest) padding)
      (Tape.input (first :: rest)) := by
  exact
    ⟨FoC.Computability.dropTrailingNone_append_none [], rfl,
      FoC.Computability.dropTrailingNone_append_replicate_none
        (rest.map some) padding⟩

theorem canonical_computes
    (baseFirst : MachineCodeSymbol)
    (baseRest rest : Word MachineCodeSymbol)
    (gap : Nat) :
    TuringMachine.Computes machine
      (sourceConfig (baseFirst :: baseRest) gap
        MachineCodeSymbol.transition rest)
      { state := .ready
        tape := paddedReadyTape
          (List.append (baseFirst :: baseRest)
            (MachineCodeSymbol.transition :: rest)) (gap + 2) } := by
  have henter : TuringMachine.Step machine
      (sourceConfig (baseFirst :: baseRest) gap
        MachineCodeSymbol.transition rest)
      (markerConfig (baseFirst :: baseRest) gap
        MachineCodeSymbol.transition rest) :=
    TuringMachine.stepConfig_eq_some_iff_step.mp
      (enter_step (baseFirst :: baseRest) gap rest)
  exact TuringMachine.Computes.step henter
    (from_marker_computes baseFirst baseRest gap
      MachineCodeSymbol.transition rest)

theorem computes_of_tape_equiv
    (baseFirst : MachineCodeSymbol)
    (baseRest rest : Word MachineCodeSymbol)
    (gap : Nat)
    (tape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (sourceConfig (baseFirst :: baseRest) gap
        MachineCodeSymbol.transition rest).tape tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .enter, tape := tape }
        { state := .ready, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (List.append (baseFirst :: baseRest)
            (MachineCodeSymbol.transition :: rest))) targetTape := by
  rcases TuringMachine.computes_to_computesIn
      (canonical_computes baseFirst baseRest rest gap) with
    ⟨steps, hcanonical⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonical hsource with
    ⟨target, hrun, hstate, htape⟩
  rcases target with ⟨targetState, targetTape⟩
  simp only at hstate
  subst targetState
  refine ⟨targetTape, TuringMachine.computesIn_to_computes hrun, ?_⟩
  have hpadded := paddedReadyTape_equiv_input baseFirst
    (List.append baseRest (MachineCodeSymbol.transition :: rest))
    (gap + 2)
  exact Tape.Equiv.trans
    (Tape.Equiv.symm (by
      simpa [List.append_assoc] using hpadded))
    (by
      simpa using htape)

def cleanupGap
    (D : MachineDescription)
    (master : Word MachineCodeSymbol) : Nat :=
  master.length + (CopyDriver.nearStart D).length

theorem finalCompactTape_equiv_source
    (D : MachineDescription)
    (masterRest suffix : Word MachineCodeSymbol) :
    Tape.Equiv
      (sourceConfig
        (List.append (MachineDescription.encodeNat D.start)
          [MachineCodeSymbol.header])
        (cleanupGap D (MachineCodeSymbol.transition :: masterRest))
        MachineCodeSymbol.transition
        (List.append masterRest suffix)).tape
      (CopyDriver.finalCompactTape D
        (MachineCodeSymbol.transition :: masterRest)
        (List.append (MachineCodeSymbol.transition :: masterRest)
          suffix)) := by
  let master := MachineCodeSymbol.transition :: masterRest
  let gap := cleanupGap D master
  have hprefix :
      List.replicate (gap + 1) (none : Option MachineCodeSymbol) =
        List.replicate (master.length + 1) none ++
          List.replicate (CopyDriver.nearStart D).length none := by
    rw [List.replicate_append_replicate]
    congr 1
    simp [gap, cleanupGap, master]
    lia
  have hpadding :
      List.replicate (D.stateCount + 1)
          (none : Option MachineCodeSymbol) ++
        [none, none, none, none] =
      List.replicate (D.stateCount + 5) none := by
    change List.replicate (D.stateCount + 1) none ++
        List.replicate 4 none = _
    rw [List.replicate_append_replicate]
  have hleft : CopyDriver.finalCompactLeftRev D master =
      (List.replicate (gap + 1) none ++
        (List.append (MachineDescription.encodeNat D.start)
          [MachineCodeSymbol.header]).reverse.map some) ++
          List.replicate (D.stateCount + 5) none := by
    simp only [CopyDriver.finalCompactLeftRev]
    rw [← hprefix]
    simp only [List.append_assoc]
    rw [hpadding]
    simp [List.reverse_append]
  change Tape.Equiv
    { left := List.replicate (gap + 1) none ++
        (List.append (MachineDescription.encodeNat D.start)
          [MachineCodeSymbol.header]).reverse.map some
      head := some MachineCodeSymbol.transition
      right := (List.append masterRest suffix).map some ++ [none] }
    { left := CopyDriver.finalCompactLeftRev D master
      head := some MachineCodeSymbol.transition
      right := (List.append masterRest suffix).map some ++ [none] }
  refine ⟨?_, rfl, rfl⟩
  change Tape.dropTrailingNone
      (List.replicate (gap + 1) none ++
        (List.append (MachineDescription.encodeNat D.start)
          [MachineCodeSymbol.header]).reverse.map some) =
    Tape.dropTrailingNone (CopyDriver.finalCompactLeftRev D master)
  rw [hleft]
  exact
    (FoC.Computability.dropTrailingNone_append_replicate_none _ _).symm

end GapCompactor

end FiniteRecognizer.Interpreter.PositiveInitializerPhase

end Computability
end FoC
