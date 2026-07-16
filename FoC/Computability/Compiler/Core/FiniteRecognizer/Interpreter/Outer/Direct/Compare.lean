import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.Direct.Extract

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.ParserAssembly
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

def headerBuffer : InsertBlock.Buffer :=
  ⟨[MachineCodeSymbol.header], by decide⟩

def separatorBuffer : InsertBlock.Buffer :=
  ⟨[MachineCodeSymbol.blank, MachineCodeSymbol.transition], by decide⟩

def headerInsertedWord (start halt : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header :: extractedWord start halt

def headerInsertSourceConfig
    (leftPadding start halt rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control where
  state := .edit (.carry headerBuffer)
  tape :=
    (readyConfig leftPadding
      (extractedWord start halt) rightPadding).tape

theorem cursorTape_nil_eq_input (word : Word MachineCodeSymbol) :
    SerializedShift.cursorTape [] word = Tape.input word := by
  cases word <;> rfl

theorem header_insert_from_ready
    (leftPadding start halt rightPadding : Nat) :
    exists targetTape : Tape MachineCodeSymbol,
      (InsertRestagedMachine.machine headerBuffer).runConfigExact?
          (InsertRestagedMachine.runSteps headerBuffer []
            (extractedWord start halt))
          (headerInsertSourceConfig
            leftPadding start halt rightPadding) =
        some
          { state := InsertRestagedMachine.Control.rewind
              RewindWord.Control.gate
            tape := targetTape } ∧
      Tape.Equiv targetTape
        (Tape.input (headerInsertedWord start halt)) := by
  have hcanonical := InsertRestagedMachine.run_exact
    headerBuffer [] (extractedWord start halt) (by decide)
  have hsource : Tape.Equiv
      (InsertRestagedMachine.editConfig
        (InsertBlock.config headerBuffer []
          (extractedWord start halt))).tape
      (headerInsertSourceConfig
        leftPadding start halt rightPadding).tape := by
    simpa [InsertRestagedMachine.editConfig, InsertBlock.config,
      cursorTape_nil_eq_input, headerInsertSourceConfig] using
      Tape.Equiv.symm
        (ready_tape_equiv_extracted
          leftPadding start halt rightPadding)
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hcanonical hsource with
    ⟨target, hrun, hstate, htape⟩
  rcases target with ⟨targetState, targetTape⟩
  simp only [InsertRestagedMachine.rewindConfig] at hstate
  subst targetState
  refine ⟨targetTape, ?_, ?_⟩
  · simpa [headerInsertSourceConfig,
      InsertRestagedMachine.editConfig, InsertBlock.config,
      InsertRestagedMachine.rewindConfig,
      RewindWord.gateConfig] using hrun
  · have hgate := RewindWord.gateTape_equiv_input
      (headerInsertedWord start halt) 0
    exact (Tape.Equiv.symm htape).trans (by
      simpa [headerInsertedWord, headerBuffer,
        PhysicalBranch.insertOutput,
        InsertRestagedMachine.rewindConfig,
        RewindWord.gateConfig] using hgate)

namespace StartBoundaryLocator

inductive Control where
  | needHeader
  | scanStart
  | ready
deriving DecidableEq

namespace Control

def elems : List Control := [.needHeader, .scanStart, .ready]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .needHeader, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .scanStart)
  | .scanStart, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .scanStart)
  | .scanStart, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .needHeader
  halt := .ready
  transition := transition
  statesFinite := Control.finite

def sourceConfig (start halt : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .needHeader
  tape := Tape.input (headerInsertedWord start halt)

def scanConfig
    (remaining processed halt : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scanStart
  tape := SerializedShift.cursorTape
    (List.replicate processed MachineCodeSymbol.tick ++
      [MachineCodeSymbol.header])
    (MachineDescription.encodeNatAppend remaining
      (MachineDescription.encodeNatAppend halt
        [MachineCodeSymbol.blank]))

def boundaryLeftRev (start : Nat) : Word MachineCodeSymbol :=
  (MachineDescription.encodeNat start).reverse ++
    [MachineCodeSymbol.header]

def readyConfig (start halt : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready
  tape := SerializedShift.cursorTape
    (boundaryLeftRev start)
    (MachineDescription.encodeNatAppend halt
      [MachineCodeSymbol.blank])

theorem header_step (start halt : Nat) :
    machine.stepConfig (sourceConfig start halt) =
      some (scanConfig start 0 halt) := by
  cases start <;> cases halt <;> rfl

theorem tick_step
    (remaining processed halt : Nat) :
    machine.stepConfig
        (scanConfig remaining.succ processed halt) =
      some (scanConfig remaining processed.succ halt) := by
  cases remaining <;> cases processed <;> cases halt <;>
    simp [scanConfig, machine, transition,
      TuringMachine.stepConfig, SerializedShift.cursorTape,
      MachineDescription.encodeNat,
      MachineDescription.encodeNatAppend,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ, List.append_assoc]

theorem scan_run_exact
    (remaining processed halt : Nat) :
    machine.runConfigExact? remaining
        (scanConfig remaining processed halt) =
      some (scanConfig 0 (remaining + processed) halt) := by
  induction remaining generalizing processed with
  | zero =>
      simp only [TuringMachine.runConfigExact?, Nat.zero_add]
  | succ remaining ih =>
      rw [TuringMachine.runConfigExact?]
      rw [tick_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih processed.succ

theorem done_step (start halt : Nat) :
    machine.stepConfig (scanConfig 0 start halt) =
      some (readyConfig start halt) := by
  cases start <;> cases halt <;>
    simp [scanConfig, readyConfig, boundaryLeftRev,
      machine, transition, TuringMachine.stepConfig,
      SerializedShift.cursorTape, MachineDescription.encodeNat,
      MachineDescription.encodeNatAppend,
      encodeNat_reverse_eq_done_ticks,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.map_reverse, List.map_append,
      List.replicate_succ, List.append_assoc,
      replicate_append_self_cons]

theorem computes (start halt : Nat) :
    TuringMachine.Computes machine
      (sourceConfig start halt) (readyConfig start halt) := by
  apply TuringMachine.computes_trans
    (TuringMachine.computes_of_step
      (TuringMachine.stepConfig_eq_some_iff_step.mp
        (header_step start halt)))
  apply TuringMachine.computes_trans
    (TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (scan_run_exact start 0 halt)))
  exact TuringMachine.computes_of_step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (by simpa using done_step start halt))

end StartBoundaryLocator

theorem locate_start_boundary_from_equiv
    (start halt : Nat) (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv sourceTape
      (Tape.input (headerInsertedWord start halt))) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes StartBoundaryLocator.machine
        { state := StartBoundaryLocator.Control.needHeader
          tape := sourceTape }
        { state := StartBoundaryLocator.Control.ready
          tape := targetTape } ∧
      Tape.Equiv targetTape
        (StartBoundaryLocator.readyConfig start halt).tape := by
  rcases TuringMachine.computes_to_computesIn
      (StartBoundaryLocator.computes start halt) with
    ⟨steps, hrun⟩
  have hcanonical : Tape.Equiv
      (StartBoundaryLocator.sourceConfig start halt).tape sourceTape := by
    simpa [StartBoundaryLocator.sourceConfig] using
      Tape.Equiv.symm hsource
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hrun hcanonical with
    ⟨target, hrun', hstate, htape⟩
  rcases target with ⟨targetState, targetTape⟩
  simp only [StartBoundaryLocator.readyConfig] at hstate
  subst targetState
  refine ⟨targetTape, ?_, Tape.Equiv.symm htape⟩
  exact TuringMachine.computesIn_to_computes
    (by simpa [StartBoundaryLocator.sourceConfig] using hrun')

def separatorSuffix (halt : Nat) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend halt [MachineCodeSymbol.blank]

def separatorInsertSourceConfig
    (sourceTape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control where
  state := .edit (.carry separatorBuffer)
  tape := sourceTape

def finalInsertedWord (start halt : Nat) : Word MachineCodeSymbol :=
  PhysicalBranch.insertOutput separatorBuffer
    (StartBoundaryLocator.boundaryLeftRev start)
    (separatorSuffix halt)

theorem finalInsertedWord_eq_runtime_word
    (start halt : Nat) :
    finalInsertedWord start halt =
      MachineCodeSymbol.header ::
        runtimeKeyComparatorBody
          (List.replicate start MachineCodeSymbol.tick) none
          (List.replicate halt MachineCodeSymbol.tick) none [] := by
  cases start <;> cases halt <;>
    simp [finalInsertedWord, PhysicalBranch.insertOutput,
      separatorBuffer, StartBoundaryLocator.boundaryLeftRev,
      separatorSuffix, runtimeKeyComparatorBody,
      runtimeKeyCellSymbol, MachineDescription.encodeNat,
      MachineDescription.encodeNatAppend,
      encodeNat_eq_ticks_done,
      List.reverse_append, List.replicate_succ,
      List.append_assoc, replicate_append_self_cons]

theorem finalComparatorSource_tape_eq_input_inserted
    (start halt : Nat) :
    (finalComparatorSourceConfig start halt []).tape =
      Tape.input (finalInsertedWord start halt) := by
  rw [finalInsertedWord_eq_runtime_word]
  rfl

theorem separator_insert_from_locator
    (start halt : Nat) (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv sourceTape
      (StartBoundaryLocator.readyConfig start halt).tape) :
    exists targetTape : Tape MachineCodeSymbol,
      (InsertRestagedMachine.machine separatorBuffer).runConfigExact?
          (InsertRestagedMachine.runSteps separatorBuffer
            (StartBoundaryLocator.boundaryLeftRev start)
            (separatorSuffix halt))
          (separatorInsertSourceConfig sourceTape) =
        some
          { state := InsertRestagedMachine.Control.rewind
              RewindWord.Control.gate
            tape := targetTape } ∧
      Tape.Equiv targetTape
        (finalComparatorSourceConfig start halt []).tape := by
  have hcanonical := InsertRestagedMachine.run_exact
    separatorBuffer (StartBoundaryLocator.boundaryLeftRev start)
      (separatorSuffix halt) (by decide)
  have hcanonicalSource : Tape.Equiv
      (InsertRestagedMachine.editConfig
        (InsertBlock.config separatorBuffer
          (StartBoundaryLocator.boundaryLeftRev start)
          (separatorSuffix halt))).tape sourceTape := by
    simpa [InsertRestagedMachine.editConfig, InsertBlock.config,
      StartBoundaryLocator.readyConfig, separatorSuffix] using
      Tape.Equiv.symm hsource
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hcanonical hcanonicalSource with
    ⟨target, hrun, hstate, htape⟩
  rcases target with ⟨targetState, targetTape⟩
  simp only [InsertRestagedMachine.rewindConfig] at hstate
  subst targetState
  refine ⟨targetTape, ?_, ?_⟩
  · simpa [separatorInsertSourceConfig,
      InsertRestagedMachine.editConfig, InsertBlock.config,
      InsertRestagedMachine.rewindConfig,
      RewindWord.gateConfig] using hrun
  · have hgate := RewindWord.gateTape_equiv_input
      (finalInsertedWord start halt) 0
    have hout : Tape.Equiv targetTape
        (Tape.input (finalInsertedWord start halt)) :=
      (Tape.Equiv.symm htape).trans (by
        simpa [finalInsertedWord,
          InsertRestagedMachine.rewindConfig,
          RewindWord.gateConfig] using hgate)
    rw [finalComparatorSource_tape_eq_input_inserted]
    exact hout

theorem haltsFrom_iff_of_tape_equiv
    {symbol state : Type}
    {M : TuringMachine symbol state}
    {canonical : TuringMachine.Configuration symbol state}
    {physicalTape : Tape symbol}
    (htape : Tape.Equiv physicalTape canonical.tape) :
    TuringMachine.HaltsFrom M
        { state := canonical.state, tape := physicalTape } ↔
      TuringMachine.HaltsFrom M canonical := by
  constructor
  · intro hhalt
    rcases TuringMachine.halts_from_to_halts_from_in hhalt with
      ⟨steps, final, hrun, hfinal⟩
    rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
        hrun htape with
      ⟨final', hrun', hstate, hfinalTape⟩
    refine ⟨final', TuringMachine.computesIn_to_computes hrun', ?_⟩
    exact hstate.trans hfinal
  · intro hhalt
    rcases TuringMachine.halts_from_to_halts_from_in hhalt with
      ⟨steps, final, hrun, hfinal⟩
    rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
        hrun (Tape.Equiv.symm htape) with
      ⟨final', hrun', hstate, hfinalTape⟩
    refine ⟨final', TuringMachine.computesIn_to_computes hrun', ?_⟩
    exact hstate.trans hfinal

def physicalFinalComparatorSourceConfig
    (sourceTape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeyComparatorState where
  state := RuntimeKeyComparatorState.needHeader
  tape := sourceTape

theorem physical_finalComparator_haltsFrom_iff
    (start halt : Nat) (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv sourceTape
      (finalComparatorSourceConfig start halt []).tape) :
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (physicalFinalComparatorSourceConfig sourceTape) ↔
      start = halt := by
  calc
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (physicalFinalComparatorSourceConfig sourceTape) ↔
      TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (finalComparatorSourceConfig start halt []) := by
          simpa [physicalFinalComparatorSourceConfig,
            finalComparatorSourceConfig] using
            (haltsFrom_iff_of_tape_equiv hsource)
    _ ↔ start = halt := finalComparator_haltsFrom_iff start halt []

namespace SavedParserFinalHandoff

inductive Control where
  | parser (fuelZero : Bool)
      (state : FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control)
  | final (state : FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control)
  | positiveReady (saved : Option MachineCodeSymbol)
  | finalReady
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.elems.map
      (Control.parser false) ++
    FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.elems.map
      (Control.parser true) ++
    FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.elems.map Control.final ++
    TransitionListParserState.optionCells.map Control.positiveReady ++
    [Control.finalReady, Control.halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro state
    cases state with
    | parser fuelZero parserState =>
        have hparser :=
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.finite.complete
            parserState
        change parserState ∈
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.elems at hparser
        cases fuelZero <;> simp [elems, hparser]
    | final finalState =>
        have hfinal :=
          FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.finite.complete
            finalState
        change finalState ∈
          FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.elems at hfinal
        simp [elems, hfinal]
    | positiveReady saved =>
        have hsaved :=
          TransitionListParserState.optionCells_complete saved
        simp [elems, hsaved]
    | finalReady => simp [elems]
    | halt => simp [elems]

end Control

def parserTarget
    (fuelZero : Bool) :
    FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control -> Control
  | .parser TransitionListParserState.halt =>
      .final .preserveNoBarrierBlank
  | .ready saved =>
      if fuelZero then .final .preserveContextBlank
      else .positiveReady saved
  | .halt => .halt
  | state => .parser fuelZero state

def finalTarget :
    FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control -> Control
  | .ready => .finalReady
  | .halt => .halt
  | state => .final state

def mapAction {state : Type}
    (mapState : state -> Control) :
    (Option MachineCodeSymbol × Direction × state) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, mapState next)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .parser fuelZero state, cell =>
      Option.map (mapAction (parserTarget fuelZero))
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.transition state cell)
  | .final state, cell =>
      Option.map (mapAction finalTarget)
        (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.transition state cell)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .parser false FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine.start
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def parserConfig
    (fuelZero : Bool)
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (parserTarget fuelZero) config

def finalConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig finalTarget config

theorem parserTarget_eq_parser_of_step
    (fuelZero : Bool)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    (hstep : FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine.stepConfig source =
      some target) :
    parserTarget fuelZero source.state =
      .parser fuelZero source.state := by
  cases source with
  | mk state tape =>
      cases state with
      | parser parserState =>
          cases parserState <;> try rfl
          cases hcell : Tape.read tape <;>
            simp [FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine,
              FiniteRecognizer.Interpreter.SavedCellTransitionParser.transition,
              transitionListParserMachine,
              TuringMachine.stepConfig, hcell] at hstep
      | ready saved =>
          simp [FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine,
            FiniteRecognizer.Interpreter.SavedCellTransitionParser.transition,
            TuringMachine.stepConfig] at hstep
      | halt =>
          simp [FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine,
            FiniteRecognizer.Interpreter.SavedCellTransitionParser.transition,
            TuringMachine.stepConfig] at hstep

theorem parser_step_lift_active
    (fuelZero : Bool)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    (hstep : FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine.stepConfig source =
      some target) :
    machine.stepConfig (parserConfig fuelZero source) =
      some (parserConfig fuelZero target) := by
  have hsource := parserTarget_eq_parser_of_step fuelZero hstep
  cases source with
  | mk state tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      simp only [parserConfig, TuringMachine.PhaseEmbedding.liftConfig]
      rw [hsource]
      cases haction :
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.transition state
            (Tape.read tape) with
      | none =>
          simp [FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine, haction]
            at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp [FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine, haction]
            at hstep
          cases hstep
          simp [machine, transition, haction, mapAction]

theorem parser_computes_lift
    (fuelZero : Bool)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine source target) :
    TuringMachine.Computes machine
      (parserConfig fuelZero source) (parserConfig fuelZero target) := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    (parserTarget fuelZero)
  · intro source target hstep
    exact parser_step_lift_active fuelZero hstep
  · exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem finalTarget_eq_final_of_step
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control}
    (hstep : FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine.stepConfig source =
      some target) :
    finalTarget source.state = .final source.state := by
  cases source with
  | mk state tape =>
      cases state <;> try rfl
      all_goals
        cases hcell : Tape.read tape <;>
          simp [FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine,
            FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.transition,
            TuringMachine.stepConfig, hcell] at hstep

theorem final_step_lift_active
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control}
    (hstep : FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine.stepConfig source =
      some target) :
    machine.stepConfig (finalConfig source) =
      some (finalConfig target) := by
  have hsource := finalTarget_eq_final_of_step hstep
  cases source with
  | mk state tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      simp only [finalConfig, TuringMachine.PhaseEmbedding.liftConfig]
      rw [hsource]
      cases haction :
          FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.transition state
            (Tape.read tape) with
      | none =>
          simp [FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine, haction]
            at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp [FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine, haction]
            at hstep
          cases hstep
          simp [machine, transition, haction, mapAction]

theorem final_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine source target) :
    TuringMachine.Computes machine
      (finalConfig source) (finalConfig target) := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    finalTarget
  · intro source target hstep
    exact final_step_lift_active hstep
  · exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem parserConfig_parser_halt
    (fuelZero : Bool) (tape : Tape MachineCodeSymbol) :
    parserConfig fuelZero
        { state :=
            FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.parser
              TransitionListParserState.halt
          tape := tape } =
      finalConfig
        { state :=
            FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.preserveNoBarrierBlank
          tape := tape } := by
  rfl

theorem parserConfig_ready_fuelZero
    (saved : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    parserConfig true
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.readyConfig saved tape) =
      finalConfig
        { state :=
            FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.preserveContextBlank
          tape := tape } := by
  rfl

theorem zero_count_halt_retarget_computes
    (fuelZero : Bool)
    {source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    {targetTape : Tape MachineCodeSymbol}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine source
        { state :=
            FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.parser
              TransitionListParserState.halt
          tape := targetTape }) :
    TuringMachine.Computes machine
      (parserConfig fuelZero source)
      (finalConfig
        { state :=
            FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.preserveNoBarrierBlank
          tape := targetTape }) := by
  simpa [parserConfig_parser_halt] using
    parser_computes_lift fuelZero hrun

theorem positive_fuelZero_ready_retarget_computes
    {source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    {saved : Option MachineCodeSymbol}
    {targetTape : Tape MachineCodeSymbol}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine source
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.readyConfig saved targetTape)) :
    TuringMachine.Computes machine
      (parserConfig true source)
      (finalConfig
        { state :=
            FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.preserveContextBlank
          tape := targetTape }) := by
  simpa [parserConfig_ready_fuelZero] using
    parser_computes_lift true hrun

def savedContextualParserSourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat)
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control :=
  FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
    { state :=
        TransitionListParserState.findCount
          TransitionListParserMarker.initial
      tape :=
        transitionListParserOptionTape
          (baseLeftRev.map some)
          ((MachineDescription.encodeNatAppend count tokens).map some) }

def savedZeroTransitionHaltConfig
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control :=
  FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
    (contextualZeroTransitionHaltConfig baseLeftRev input)

theorem savedParser_zero_context_step
    (baseLeftRev input : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine.stepConfig
        (savedContextualParserSourceConfig baseLeftRev 0 input) =
      some (savedZeroTransitionHaltConfig baseLeftRev input) := by
  cases baseLeftRev <;> cases input <;> rfl

theorem savedParser_zero_context_computes
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Computes FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
      (savedContextualParserSourceConfig baseLeftRev 0 input)
      (savedZeroTransitionHaltConfig baseLeftRev input) := by
  exact TuringMachine.computes_of_step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (savedParser_zero_context_step baseLeftRev input))

theorem contextualZeroTransitionHalt_tape_eq_noBarrierSource
    (baseLeftRev input : Word MachineCodeSymbol) :
    (contextualZeroTransitionHaltConfig baseLeftRev input).tape =
      (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.noBarrierSourceConfig
        baseLeftRev input).tape := by
  cases input <;> rfl

theorem zero_count_parser_retarget_computes
    (fuelZero : Bool)
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (parserConfig fuelZero
        (savedContextualParserSourceConfig baseLeftRev 0 input))
      (finalConfig
        (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.noBarrierSourceConfig
          baseLeftRev input)) := by
  have hrun := savedParser_zero_context_computes baseLeftRev input
  have hretarget := zero_count_halt_retarget_computes fuelZero
    (by
      simpa [savedZeroTransitionHaltConfig,
        contextualZeroTransitionHaltConfig,
        FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig,
        TuringMachine.PhaseEmbedding.liftConfig] using hrun)
  cases input <;>
    simpa [FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.noBarrierSourceConfig,
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextCursorTape,
      transitionListParserOptionTape] using hretarget

theorem zero_count_computes_to_finalReady
    (fuelZero : Bool)
    (fuel stateCount start halt : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (parserConfig fuelZero
        (savedContextualParserSourceConfig
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
            fuel stateCount start halt)
          0 input))
      { state := Control.finalReady
        tape :=
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.readyConfig
            ((FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.olderMetadataLeftRev
              fuel stateCount).length + 2)
            (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.extractedWord start halt)
            (((FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.noBarrierPayloadTail
              input).length + 1).succ)).tape } := by
  apply TuringMachine.computes_trans
    (zero_count_parser_retarget_computes fuelZero
      (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
        fuel stateCount start halt) input)
  have hfinal := final_computes_lift
    (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.noBarrier_extractor_computes
      fuel stateCount start halt input)
  simpa [finalConfig, finalTarget,
    FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.readyConfig,
    TuringMachine.PhaseEmbedding.liftConfig] using hfinal

theorem positive_canonical_ready_retarget_computes
    (baseLeftRev symbols suffix : Word MachineCodeSymbol)
    (rowCount : Nat)
    (saved : Option MachineCodeSymbol)
    {source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (hpayload :
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.parserPayloadWord symbols suffix =
        first :: rest)
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine source
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.readyConfig saved
          (FiniteRecognizer.Interpreter.ParserAssembly.TransitionParserContextTransport.appendLeftContext
            baseLeftRev
            (parsedTransitionHaltConfig rowCount symbols suffix).tape))) :
    TuringMachine.Computes machine
      (parserConfig true source)
      (finalConfig
        (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
          (parsedTableLeftRev rowCount ++ baseLeftRev.map some)
          first rest)) := by
  have hretarget := positive_fuelZero_ready_retarget_computes hrun
  have htape :=
    FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextual_parser_endpoint_tape
      baseLeftRev symbols suffix rowCount first rest hpayload
  rw [htape] at hretarget
  exact hretarget

theorem positive_canonical_ready_retarget_exists
    (baseLeftRev symbols suffix : Word MachineCodeSymbol)
    (rowCount : Nat)
    (saved : Option MachineCodeSymbol)
    {source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine source
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.readyConfig saved
          (FiniteRecognizer.Interpreter.ParserAssembly.TransitionParserContextTransport.appendLeftContext
            baseLeftRev
            (parsedTransitionHaltConfig rowCount symbols suffix).tape))) :
    exists first : MachineCodeSymbol,
    exists rest : Word MachineCodeSymbol,
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.parserPayloadWord symbols suffix =
          first :: rest ∧
        TuringMachine.Computes machine
          (parserConfig true source)
          (finalConfig
            (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
              (parsedTableLeftRev rowCount ++ baseLeftRev.map some)
              first rest)) := by
  cases hpayload :
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.parserPayloadWord symbols suffix with
  | nil =>
      exact False.elim
        (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.parserPayloadWord_ne_nil
          symbols suffix hpayload)
  | cons first rest =>
      exact ⟨first, rest, rfl,
        positive_canonical_ready_retarget_computes
          baseLeftRev symbols suffix rowCount saved first rest
          hpayload hrun⟩

theorem positive_canonical_computes_to_finalReady
    (fuel stateCount start halt rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol)
    (saved : Option MachineCodeSymbol)
    {source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine source
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.readyConfig saved
          (FiniteRecognizer.Interpreter.ParserAssembly.TransitionParserContextTransport.appendLeftContext
            (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
              fuel stateCount start halt)
            (parsedTransitionHaltConfig rowCount symbols suffix).tape))) :
    exists first : MachineCodeSymbol,
    exists rest : Word MachineCodeSymbol,
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.parserPayloadWord symbols suffix =
          first :: rest ∧
        TuringMachine.Computes machine
          (parserConfig true source)
          { state := Control.finalReady
            tape :=
              (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.readyConfig
                ((FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.olderMetadataLeftRev
                  fuel stateCount).length + 2)
                (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.extractedWord start halt)
                ((MachineCodeSymbol.done ::
                  List.replicate rowCount MachineCodeSymbol.blank).length +
                  (rest.length + 1)).succ).tape } := by
  rcases positive_canonical_ready_retarget_exists
      (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
        fuel stateCount start halt)
      symbols suffix rowCount saved hrun with
    ⟨first, rest, hpayload, hretarget⟩
  refine ⟨first, rest, hpayload, ?_⟩
  apply TuringMachine.computes_trans hretarget
  have hfinal := final_computes_lift
    (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextual_extractor_computes
      fuel stateCount start halt rowCount first rest)
  simpa [finalConfig, finalTarget,
    FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.readyConfig,
    TuringMachine.PhaseEmbedding.liftConfig] using hfinal

end SavedParserFinalHandoff

def FinalComparatorMaterialization
    (leftPadding start halt rightPadding : Nat) : Prop :=
  exists headerTape boundaryTape comparatorTape : Tape MachineCodeSymbol,
    (InsertRestagedMachine.machine headerBuffer).runConfigExact?
        (InsertRestagedMachine.runSteps headerBuffer []
          (extractedWord start halt))
        (headerInsertSourceConfig
          leftPadding start halt rightPadding) =
      some
        { state := InsertRestagedMachine.Control.rewind
            RewindWord.Control.gate
          tape := headerTape } ∧
    Tape.Equiv headerTape
      (Tape.input (headerInsertedWord start halt)) ∧
    TuringMachine.Computes StartBoundaryLocator.machine
      { state := StartBoundaryLocator.Control.needHeader
        tape := headerTape }
      { state := StartBoundaryLocator.Control.ready
        tape := boundaryTape } ∧
    Tape.Equiv boundaryTape
      (StartBoundaryLocator.readyConfig start halt).tape ∧
    (InsertRestagedMachine.machine separatorBuffer).runConfigExact?
        (InsertRestagedMachine.runSteps separatorBuffer
          (StartBoundaryLocator.boundaryLeftRev start)
          (separatorSuffix halt))
        (separatorInsertSourceConfig boundaryTape) =
      some
        { state := InsertRestagedMachine.Control.rewind
            RewindWord.Control.gate
          tape := comparatorTape } ∧
    Tape.Equiv comparatorTape
      (finalComparatorSourceConfig start halt []).tape ∧
    (TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (physicalFinalComparatorSourceConfig comparatorTape) ↔
      start = halt)

theorem finalComparator_materialization
    (leftPadding start halt rightPadding : Nat) :
    FinalComparatorMaterialization
      leftPadding start halt rightPadding := by
  rcases header_insert_from_ready leftPadding start halt rightPadding with
    ⟨headerTape, hheader, hheaderEquiv⟩
  rcases locate_start_boundary_from_equiv
      start halt headerTape hheaderEquiv with
    ⟨boundaryTape, hboundary, hboundaryEquiv⟩
  rcases separator_insert_from_locator
      start halt boundaryTape hboundaryEquiv with
    ⟨comparatorTape, hseparator, hcomparatorEquiv⟩
  exact
    ⟨headerTape, boundaryTape, comparatorTape,
      hheader, hheaderEquiv, hboundary, hboundaryEquiv,
      hseparator, hcomparatorEquiv,
      physical_finalComparator_haltsFrom_iff
        start halt comparatorTape hcomparatorEquiv⟩

theorem empty_table_finalComparator_bundle
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (_hempty : D.transitions = []) :
    TuringMachine.Computes SavedParserFinalHandoff.machine
        (SavedParserFinalHandoff.parserConfig false
          (SavedParserFinalHandoff.savedContextualParserSourceConfig
            (metadataLeftRev fuel D.stateCount D.start D.halt)
            0 input))
        { state := SavedParserFinalHandoff.Control.finalReady
          tape :=
            (readyConfig
              ((olderMetadataLeftRev fuel D.stateCount).length + 2)
              (extractedWord D.start D.halt)
              (((noBarrierPayloadTail input).length + 1).succ)).tape } ∧
      FinalComparatorMaterialization
        ((olderMetadataLeftRev fuel D.stateCount).length + 2)
        D.start D.halt
        (((noBarrierPayloadTail input).length + 1).succ) := by
  exact
    ⟨SavedParserFinalHandoff.zero_count_computes_to_finalReady
        false fuel D.stateCount D.start D.halt input,
      finalComparator_materialization
        ((olderMetadataLeftRev fuel D.stateCount).length + 2)
        D.start D.halt
        (((noBarrierPayloadTail input).length + 1).succ)⟩

theorem positive_fuelZero_finalComparator_bundle
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (firstTransition : TransitionDescription)
    (remainingTransitions : List TransitionDescription)
    (_htransitions :
      D.transitions = firstTransition :: remainingTransitions)
    (_hfuelZero : fuel = 0)
    {source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine source
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.readyConfig
          (transitionListParserSavedHead input)
          (FiniteRecognizer.Interpreter.ParserAssembly.TransitionParserContextTransport.appendLeftContext
            (metadataLeftRev fuel D.stateCount D.start D.halt)
            (parsedTransitionHaltConfig
              (firstTransition :: remainingTransitions).length
              (MachineDescription.encodeTransitions
                (firstTransition :: remainingTransitions))
              input).tape))) :
    exists payloadFirst : MachineCodeSymbol,
    exists payloadRest : Word MachineCodeSymbol,
      parserPayloadWord
          (MachineDescription.encodeTransitions
            (firstTransition :: remainingTransitions)) input =
        payloadFirst :: payloadRest ∧
      TuringMachine.Computes SavedParserFinalHandoff.machine
        (SavedParserFinalHandoff.parserConfig true source)
        { state := SavedParserFinalHandoff.Control.finalReady
          tape :=
            (readyConfig
              ((olderMetadataLeftRev fuel D.stateCount).length + 2)
              (extractedWord D.start D.halt)
              ((MachineCodeSymbol.done ::
                List.replicate
                  (firstTransition :: remainingTransitions).length
                  MachineCodeSymbol.blank).length +
                (payloadRest.length + 1)).succ).tape } ∧
      FinalComparatorMaterialization
        ((olderMetadataLeftRev fuel D.stateCount).length + 2)
        D.start D.halt
        ((MachineCodeSymbol.done ::
          List.replicate
            (firstTransition :: remainingTransitions).length
            MachineCodeSymbol.blank).length +
          (payloadRest.length + 1)).succ := by
  rcases
      SavedParserFinalHandoff.positive_canonical_computes_to_finalReady
        fuel D.stateCount D.start D.halt
        (firstTransition :: remainingTransitions).length
        (MachineDescription.encodeTransitions
          (firstTransition :: remainingTransitions))
        input (transitionListParserSavedHead input) hrun with
    ⟨payloadFirst, payloadRest, hpayload, hfinal⟩
  exact
    ⟨payloadFirst, payloadRest, hpayload, hfinal,
      finalComparator_materialization
        ((olderMetadataLeftRev fuel D.stateCount).length + 2)
        D.start D.halt
        ((MachineCodeSymbol.done ::
          List.replicate
            (firstTransition :: remainingTransitions).length
            MachineCodeSymbol.blank).length +
          (payloadRest.length + 1)).succ⟩

end FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal
end Computability
end FoC
