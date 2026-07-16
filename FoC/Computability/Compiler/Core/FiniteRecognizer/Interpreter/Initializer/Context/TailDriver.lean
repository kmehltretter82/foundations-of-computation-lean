import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.SymbolRound

namespace FoC
namespace Computability

open Languages

namespace Section53BooleanContextRawTailDriver

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Section53InitializerFrontier
open Section53RuntimeEncodedList
open Section53BooleanContextMaterializer
open Section53BooleanContextLocator
open Section53BooleanContextRawTail
open Section53BooleanContextOneSymbolRound

namespace Driver

inductive Control where
  | round (inner : Section53BooleanContextOneSymbolRound.Machine.Control)
  | loopBounce
  | restart (inner : Section53BooleanContextLocator.Control)
  | restartBounce
  | finish (inner : RewindWord.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  Section53BooleanContextOneSymbolRound.Machine.Control.finite.elems.map
      Control.round ++
    [Control.loopBounce] ++
    Section53BooleanContextLocator.Control.finite.elems.map
      Control.restart ++
    [Control.restartBounce] ++
    RewindWord.Control.finite.elems.map Control.finish

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | round inner =>
        simp [elems,
          Section53BooleanContextOneSymbolRound.Machine.Control.finite.complete
            inner]
    | loopBounce => simp [elems]
    | restart inner =>
        simp [elems,
          Section53BooleanContextLocator.Control.finite.complete inner]
    | restartBounce => simp [elems]
    | finish inner =>
        simp [elems, RewindWord.Control.finite.complete inner]

end Control

def mapRoundAction :
    (Option MachineCodeSymbol × Direction ×
      Section53BooleanContextOneSymbolRound.Machine.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, .round next)

def mapFinishAction :
    (Option MachineCodeSymbol × Direction × RewindWord.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, .finish next)

def mapRestartAction :
    (Option MachineCodeSymbol × Direction ×
      Section53BooleanContextLocator.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, .restart next)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .round Section53BooleanContextOneSymbolRound.Machine.Control.ready, read =>
      some (read, Direction.left, .loopBounce)
  | .round
      (Section53BooleanContextOneSymbolRound.Machine.Control.pop
        RawTailPop.Control.empty), read =>
      some (read, Direction.left, .finish .scan)
  | .round inner, read =>
      Option.map mapRoundAction
        (Section53BooleanContextOneSymbolRound.Machine.transition inner read)
  | .loopBounce, read =>
      some (read, Direction.right,
        .restart .fuel)
  | .restart .ready, read =>
      some (read, Direction.left, .restartBounce)
  | .restart inner, read =>
      Option.map mapRestartAction
        (Section53BooleanContextLocator.transition inner read)
  | .restartBounce, read =>
      some (read, Direction.right,
        .round Section53BooleanContextOneSymbolRound.Machine.machine.start)
  | .finish inner, read =>
      Option.map mapFinishAction (RewindWord.transition inner read)

def machine : TuringMachine MachineCodeSymbol Control where
  start := .round Section53BooleanContextOneSymbolRound.Machine.machine.start
  halt := .finish .gate
  transition := transition
  statesFinite := Control.finite

def roundConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextOneSymbolRound.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .round config.state
    tape := config.tape }

def finishConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      RewindWord.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .finish config.state
    tape := config.tape }

def restartConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .restart config.state
    tape := config.tape }

theorem round_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextOneSymbolRound.Machine.Control)
    (hstep :
      Section53BooleanContextOneSymbolRound.Machine.machine.stepConfig source =
        some target) :
    machine.stepConfig (roundConfig source) =
      some (roundConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextOneSymbolRound.Machine.machine] at hstep
      cases htransition :
          Section53BooleanContextOneSymbolRound.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnotReady :
              inner ≠
                Section53BooleanContextOneSymbolRound.Machine.Control.ready := by
            intro heq
            subst inner
            simp [Section53BooleanContextOneSymbolRound.Machine.transition]
              at htransition
          have hnotEmpty :
              inner ≠
                Section53BooleanContextOneSymbolRound.Machine.Control.pop
                  RawTailPop.Control.empty := by
            intro heq
            subst inner
            simp [Section53BooleanContextOneSymbolRound.Machine.transition,
              RawTailPop.transition] at htransition
          simp [machine, transition, roundConfig, mapRoundAction,
            htransition]

theorem round_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextOneSymbolRound.Machine.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextOneSymbolRound.Machine.machine source target) :
    TuringMachine.Computes machine
      (roundConfig source) (roundConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (round_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem restart_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextLocator.Control)
    (hstep : Section53BooleanContextLocator.machine.stepConfig source =
      some target) :
    machine.stepConfig (restartConfig source) =
      some (restartConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextLocator.machine] at hstep
      cases htransition :
          Section53BooleanContextLocator.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnotReady :
              inner ≠ Section53BooleanContextLocator.Control.ready := by
            intro heq
            subst inner
            simp [Section53BooleanContextLocator.transition] at htransition
          simp [machine, transition, restartConfig, mapRestartAction,
            htransition]

theorem restart_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextLocator.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextLocator.machine source target) :
    TuringMachine.Computes machine
      (restartConfig source) (restartConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (restart_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem finish_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      RewindWord.Control)
    (hstep : RewindWord.machine.stepConfig source = some target) :
    machine.stepConfig (finishConfig source) =
      some (finishConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [RewindWord.machine] at hstep
      cases htransition : RewindWord.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          simp [machine, transition, finishConfig, mapFinishAction,
            htransition]

theorem finish_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RewindWord.Control}
    (hrun : TuringMachine.Computes RewindWord.machine source target) :
    TuringMachine.Computes machine
      (finishConfig source) (finishConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (finish_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem computes_of_tape_equiv
    {source target : TuringMachine.Configuration MachineCodeSymbol Control}
    {sourceTape : Tape MachineCodeSymbol}
    (hrun : TuringMachine.Computes machine source target)
    (hsource : Tape.Equiv source.tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := source.state, tape := sourceTape }
        { state := target.state, tape := targetTape } ∧
      Tape.Equiv target.tape targetTape := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hrunIn hsource with
    ⟨target, htargetRun, htargetState, htargetTape⟩
  rcases target with ⟨state, tape⟩
  simp only at htargetState
  subst state
  exact ⟨tape, TuringMachine.computesIn_to_computes htargetRun,
    htargetTape⟩

theorem loop_run_exact
    (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.round
            Section53BooleanContextOneSymbolRound.Machine.Control.ready
          tape := Tape.input word } =
      some
        { state := Control.restart .fuel
          tape := Section53BooleanContextOneSymbolRound.Machine.bounceTape
            (Tape.input word) } := by
  cases word <;> rfl

theorem loop_computes_of_tape_equiv
    (word : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input word) sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.round
            Section53BooleanContextOneSymbolRound.Machine.Control.ready
          tape := sourceTape }
        { state := Control.restart .fuel
          tape := targetTape } ∧
      Tape.Equiv (Tape.input word) targetTape := by
  have hrunExact := loop_run_exact word
  have hrun := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrunExact)
  rcases computes_of_tape_equiv hrun hsource with
    ⟨targetTape, htransport, htransportTarget⟩
  refine ⟨targetTape, htransport, ?_⟩
  exact Tape.Equiv.trans
    (Section53BooleanContextOneSymbolRound.Machine.bounceTape_input_equiv word)
    htransportTarget

theorem restart_to_round_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol)
    (hbase : baseLeftRev ≠ []) :
    machine.runConfigExact? 2
        { state := Control.restart .ready
          tape := (Prepend.sourceConfig baseLeftRev count suffix).tape } =
      some
        { state := Control.round
            Section53BooleanContextOneSymbolRound.Machine.machine.start
          tape := (Prepend.sourceConfig baseLeftRev count suffix).tape } := by
  cases hbaseEq : baseLeftRev with
  | nil => contradiction
  | cons first rest =>
      cases count <;> cases suffix <;> rfl

theorem restart_round_computes_of_tape_equiv
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hnoHeader : Section53BooleanContextLocator.noHeader table)
    (hsource : Tape.Equiv
      (Tape.input
        (Section53BooleanContextOneSymbolRound.Machine.layoutWord
          fuel stateCount start halt rowCount table cells raw))
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.round
            Section53BooleanContextOneSymbolRound.Machine.Control.ready
          tape := sourceTape }
        { state := Control.round
            Section53BooleanContextOneSymbolRound.Machine.machine.start
          tape := targetTape } ∧
      Tape.Equiv
        (RawTailPop.sourceConfig
          (Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
            fuel stateCount start halt rowCount table)
          cells raw).tape
        targetTape := by
  let baseLeftRev :=
    Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
      fuel stateCount start halt rowCount table
  let suffix := MachineDescription.encodeCellsAppend cells
    (MachineCodeSymbol.header :: raw)
  rcases loop_computes_of_tape_equiv
      (Section53BooleanContextOneSymbolRound.Machine.layoutWord
        fuel stateCount start halt rowCount table cells raw)
      sourceTape hsource with
    ⟨tape0, hloop, htape0⟩
  have hlocatorSource : Tape.Equiv
      (Section53BooleanContextOneSymbolRound.Machine.locatorSource
        fuel stateCount start halt rowCount table cells raw).tape
      tape0 := by
    rw [Section53BooleanContextOneSymbolRound.Machine.locatorSource_tape_eq_input]
    exact htape0
  have hlocatorInner :=
    Section53BooleanContextLocator.computes_to_right_count
      fuel stateCount start halt rowCount table cells.length suffix hnoHeader
  have hlocator := restart_computes_lift hlocatorInner
  rcases computes_of_tape_equiv hlocator hlocatorSource with
    ⟨tape1, hlocatorTransport, htape1⟩
  have hbase : baseLeftRev ≠ [] := by
    exact
      Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev_ne_nil
        fuel stateCount start halt rowCount table
  have hhandoffExact := restart_to_round_run_exact
    baseLeftRev cells.length suffix hbase
  have hhandoff := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hhandoffExact)
  rcases computes_of_tape_equiv hhandoff htape1 with
    ⟨targetTape, hhandoffTransport, htarget⟩
  refine ⟨targetTape, ?_, ?_⟩
  · exact TuringMachine.computes_trans hloop
      (TuringMachine.computes_trans hlocatorTransport hhandoffTransport)
  · simpa [baseLeftRev, suffix,
      RawTailPop.sourceConfig, Prepend.sourceConfig,
      RawTailPop.locateConfig, Prepend.locateConfig,
      Section53BooleanContextOneSymbolRound.Machine.locatorTarget,
      Section53BooleanContextLocator.targetConfig,
      Section53BooleanContextLocator.rightCountBaseLeftRev] using htarget

theorem rewind_scan_step
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol)
    (padding : Nat) :
    RewindWord.machine.stepConfig
        (RewindWord.scanConfig (current :: remainingRev) crossed padding) =
      some
        (RewindWord.scanConfig remainingRev (current :: crossed) padding) := by
  cases remainingRev <;> cases crossed <;> rfl

theorem rewind_scan_finish
    (crossed : Word MachineCodeSymbol)
    (padding : Nat) :
    RewindWord.machine.stepConfig
        (RewindWord.scanConfig [] crossed padding) =
      some (RewindWord.gateConfig crossed padding) := by
  cases crossed <;> rfl

theorem rewind_scan_run_exact
    (remainingRev crossed : Word MachineCodeSymbol)
    (padding : Nat) :
    RewindWord.machine.runConfigExact? (remainingRev.length + 1)
        (RewindWord.scanConfig remainingRev crossed padding) =
      some
        (RewindWord.gateConfig
          (Word.Concat remainingRev.reverse crossed) padding) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact rewind_scan_finish crossed padding
  | cons current remainingRev ih =>
      change
        RewindWord.machine.runConfigExact? ((remainingRev.length + 1) + 1)
            (RewindWord.scanConfig (current :: remainingRev) crossed padding) =
          _
      rw [TuringMachine.runConfigExact?, rewind_scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [Word.Concat, List.reverse_cons, List.append_assoc]

theorem empty_handoff_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    machine.runConfigExact? 1
        (roundConfig
          (Section53BooleanContextOneSymbolRound.Machine.popConfig
            (RawTailPop.emptyConfig baseLeftRev cells))) =
      some
        (finishConfig
          (RewindWord.scanConfig
            (RawTailPop.payloadBaseLeftRev baseLeftRev cells)
            [MachineCodeSymbol.header] 0)) := by
  cases hbase : RawTailPop.payloadBaseLeftRev baseLeftRev cells <;>
    simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine,
      Section53BooleanContextRawTailDriver.Driver.transition,
      roundConfig, Section53BooleanContextOneSymbolRound.Machine.popConfig,
      RawTailPop.emptyConfig, RawTailPop.rawBaseLeftRev,
      finishConfig, RewindWord.scanConfig, RewindWord.scanTape, hbase,
      RewindWord.paddingCells, SerializedShift.cursorTape,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem empty_tail_finishes
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (roundConfig
          (Section53BooleanContextOneSymbolRound.Machine.popConfig
            (RawTailPop.sourceConfig
              (Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
                fuel stateCount start halt rowCount table)
              cells [])))
        { state := Control.finish .gate
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table cells []))
        targetTape := by
  let baseLeftRev :=
    Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
      fuel stateCount start halt rowCount table
  let word := RawTailPop.wordBeforeRaw baseLeftRev cells
  have hraw := RawTailPop.empty_computes baseLeftRev cells
  have hone :=
    Section53BooleanContextOneSymbolRound.Machine.pop_computes_lift hraw
  have hround := round_computes_lift hone
  have hhandoffExact := empty_handoff_run_exact baseLeftRev cells
  have hhandoff := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hhandoffExact)
  have hrewindExact := rewind_scan_run_exact
    (RawTailPop.payloadBaseLeftRev baseLeftRev cells)
    [MachineCodeSymbol.header] 0
  have hrewindInner := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrewindExact)
  have hrewind := finish_computes_lift hrewindInner
  have hrun := TuringMachine.computes_trans hround
    (TuringMachine.computes_trans hhandoff hrewind)
  let targetTape := RewindWord.gateTape word 0
  refine ⟨targetTape, ?_, ?_⟩
  · have hword : Word.Concat
        (RawTailPop.payloadBaseLeftRev baseLeftRev cells).reverse
        [MachineCodeSymbol.header] = word := by
      have hreverse := RawTailPop.rawBaseLeftRev_reverse
        baseLeftRev cells
      rw [RawTailPop.rawBaseLeftRev] at hreverse
      rw [List.reverse_cons] at hreverse
      change Word.Concat
        (RawTailPop.payloadBaseLeftRev baseLeftRev cells).reverse
          [MachineCodeSymbol.header] =
        RawTailPop.wordBeforeRaw baseLeftRev cells at hreverse
      exact hreverse
    simpa [baseLeftRev, word, targetTape, hword, finishConfig,
      RewindWord.gateConfig] using hrun
  · have hlayout :
        Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table cells [] = word := by
      have hshape :=
        Section53BooleanContextOneSymbolRound.Machine.popTargetWord_eq_layoutWord
          fuel stateCount start halt rowCount table cells []
      calc
        _ = List.append
              (RawTailPop.wordBeforeRaw baseLeftRev cells) [] := by
            simpa [baseLeftRev] using hshape.symm
        _ = word := by simp [word]
    rw [hlayout]
    exact Tape.Equiv.symm (RewindWord.gateTape_equiv_input word 0)

def reverseWord
    (symbols : List MachineCodeSymbol) : Word MachineCodeSymbol :=
  symbols.reverse

theorem reverseWord_cons
    (last : MachineCodeSymbol)
    (symbols : List MachineCodeSymbol) :
    reverseWord (last :: symbols) =
      Word.Concat (reverseWord symbols) [last] := by
  simp [reverseWord, Word.Concat, List.reverse_cons]

theorem reverseWord_reverse
    (word : Word MachineCodeSymbol) :
    reverseWord (List.reverse word) = word := by
  unfold reverseWord
  exact List.reverse_reverse word

theorem full_tail_reverse_computes
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (revRaw : List MachineCodeSymbol)
    (hnoHeader : Section53BooleanContextLocator.noHeader table) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (roundConfig
          (Section53BooleanContextOneSymbolRound.Machine.popConfig
            (RawTailPop.sourceConfig
              (Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
                fuel stateCount start halt rowCount table)
              cells (reverseWord revRaw))))
        { state := Control.finish .gate
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table
            (List.append
              ((MachineDescription.encodeCodeWordAsInput
                (reverseWord revRaw)).map
                some)
              cells)
            []))
        targetTape := by
  induction revRaw generalizing cells with
  | nil =>
      simpa [reverseWord, MachineDescription.encodeCodeWordAsInput] using
        empty_tail_finishes fuel stateCount start halt rowCount table cells
  | cons last revRaw ih =>
      let raw : Word MachineCodeSymbol := reverseWord revRaw
      let nextCells : List (Option Bool) :=
        List.append
          ((MachineDescription.encodeCodeSymbolAsInput last).map some)
          cells
      rcases
          Section53BooleanContextOneSymbolRound.Machine.nonempty_raw_symbol_round_computes
            fuel stateCount start halt rowCount table cells raw last hnoHeader with
        ⟨tape1, honeRound, htape1⟩
      have hround := round_computes_lift honeRound
      rcases restart_round_computes_of_tape_equiv
          fuel stateCount start halt rowCount table nextCells raw tape1
          hnoHeader (by simpa [nextCells] using htape1) with
        ⟨tape2, hrestart, htape2⟩
      have hrecursiveSource : Tape.Equiv
          (roundConfig
            (Section53BooleanContextOneSymbolRound.Machine.popConfig
              (RawTailPop.sourceConfig
                (Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
                  fuel stateCount start halt rowCount table)
                nextCells raw))).tape
          tape2 := by
        simpa [roundConfig,
          Section53BooleanContextOneSymbolRound.Machine.popConfig] using
            htape2
      rcases ih nextCells with
        ⟨recursiveTargetTape, hrecursive, hrecursiveShape⟩
      rcases computes_of_tape_equiv hrecursive hrecursiveSource with
        ⟨targetTape, hrecursiveTransport, hrecursiveTarget⟩
      refine ⟨targetTape, ?_, ?_⟩
      · have hrun := TuringMachine.computes_trans hround
          (TuringMachine.computes_trans hrestart hrecursiveTransport)
        rw [reverseWord_cons]
        simpa [raw] using hrun
      · have hshape := Tape.Equiv.trans
          hrecursiveShape hrecursiveTarget
        have hcells :
            List.append
                ((MachineDescription.encodeCodeWordAsInput
                  (Word.Concat raw
                    ([last] : Word MachineCodeSymbol))).map some)
                cells =
              List.append
                ((MachineDescription.encodeCodeWordAsInput
                  raw).map some)
                (List.append
                  ((MachineDescription.encodeCodeSymbolAsInput last).map some)
                  cells) := by
          have hencode :=
            MachineDescription.encodeCodeWordAsInput_append
              raw ([last] : Word MachineCodeSymbol)
          change
            MachineDescription.encodeCodeWordAsInput
                (Word.Concat raw ([last] : Word MachineCodeSymbol)) =
              Word.Concat
                (MachineDescription.encodeCodeWordAsInput raw)
                (MachineDescription.encodeCodeWordAsInput
                  ([last] : Word MachineCodeSymbol)) at hencode
          rw [hencode]
          simp [MachineDescription.encodeCodeWordAsInput, Word.Concat,
            List.map_append, List.append_assoc]
        rw [reverseWord_cons]
        have hinput := congrArg
          (fun theseCells : List (Option Bool) =>
            Tape.input
              (Section53BooleanContextOneSymbolRound.Machine.layoutWord
                fuel stateCount start halt rowCount table theseCells []))
          hcells
        rw [hinput]
        simpa [raw, nextCells, List.append_assoc] using hshape

theorem full_tail_computes
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol)
    (hnoHeader : Section53BooleanContextLocator.noHeader table) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (roundConfig
          (Section53BooleanContextOneSymbolRound.Machine.popConfig
            (RawTailPop.sourceConfig
              (Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
                fuel stateCount start halt rowCount table)
              cells raw)))
        { state := Control.finish .gate
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table
            (List.append
              ((MachineDescription.encodeCodeWordAsInput raw).map some)
              cells)
            []))
        targetTape := by
  have hrun :=
    full_tail_reverse_computes fuel stateCount start halt rowCount table
      cells raw.reverse hnoHeader
  rw [reverseWord_reverse] at hrun
  exact hrun


end Driver

end Section53BooleanContextRawTailDriver

end Computability
end FoC
