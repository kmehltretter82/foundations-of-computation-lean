import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.FinalCompare
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.PersistentCopy
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.SavedCell.Handoff
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Insertion
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.StuckSink
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.MarkerRestore.Runs

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.InitializerFrontier

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.InitialMaterializer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.InitializerPersistentCopy

/-!
# Initializer contract boundary

This module fixes the semantic currency on both sides of the Boolean-context
materializer. The Boolean tape is exactly
`Tape.input (encodeCodeWordAsInput input)`: its first bit is stored in the
lookup key and its input tail forms the encoded right context.
-/

def inputBits (input : Word MachineCodeSymbol) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput input

def initialTape (input : Word MachineCodeSymbol) : Tape Bool :=
  Tape.input (inputBits input)

def initialConfiguration
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) : MachineDescription.Configuration :=
  D.initial (inputBits input)

def loopCallerSuffix
    (D : MachineDescription)
    (remainingFuel : Nat)
    (callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend D.halt
    (MachineDescription.encodeNatAppend remainingFuel callerSuffix)

def initialProtectedSuffix
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  protectedTapeContextsAppend (initialTape input)
    (loopCallerSuffix D remainingFuel callerSuffix)

def initialActiveTableSuffix
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    initialProtectedSuffix D remainingFuel input callerSuffix

def initialActiveWord
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeTransitionsAppend D.transitions
    (initialActiveTableSuffix D remainingFuel input callerSuffix)

def initialScanConfig
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol) :=
  canonicalScanRowsConfig (initialConfiguration D input) [] D.transitions
    (initialProtectedSuffix D remainingFuel input callerSuffix)

theorem initialConfiguration_exact
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    initialConfiguration D input =
      { state := D.start
        tape := Tape.input
          (MachineDescription.encodeCodeWordAsInput input) } := by
  rfl

theorem initialConfiguration_state
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (initialConfiguration D input).state = D.start := by
  rfl

theorem initialConfiguration_tape
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (initialConfiguration D input).tape =
      Tape.input (MachineDescription.encodeCodeWordAsInput input) := by
  rfl

def codeSymbolFirstBit : MachineCodeSymbol -> Bool
  | MachineCodeSymbol.moveRight => true
  | _ => false

def codeSymbolTailBits : MachineCodeSymbol -> Word Bool
  | MachineCodeSymbol.header => [false, false, false]
  | MachineCodeSymbol.transition => [false, false, true]
  | MachineCodeSymbol.tick => [false, true, false]
  | MachineCodeSymbol.done => [false, true, true]
  | MachineCodeSymbol.blank => [true, false, false]
  | MachineCodeSymbol.zero => [true, false, true]
  | MachineCodeSymbol.one => [true, true, false]
  | MachineCodeSymbol.moveLeft => [true, true, true]
  | MachineCodeSymbol.moveRight => [false, false, false]

theorem encodeCodeSymbolAsInput_eq_head_tail
    (symbol : MachineCodeSymbol) :
    MachineDescription.encodeCodeSymbolAsInput symbol =
      codeSymbolFirstBit symbol :: codeSymbolTailBits symbol := by
  cases symbol <;> rfl

theorem inputBits_cons
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    inputBits (symbol :: rest) =
      codeSymbolFirstBit symbol ::
        List.append (codeSymbolTailBits symbol) (inputBits rest) := by
  rw [inputBits, MachineDescription.encodeCodeWordAsInput]
  rw [encodeCodeSymbolAsInput_eq_head_tail]
  rfl

theorem initialTape_nil :
    initialTape [] = Tape.blank := by
  rfl

theorem initialTape_cons
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    initialTape (symbol :: rest) =
      { left := []
        head := some (codeSymbolFirstBit symbol)
        right :=
          (List.append (codeSymbolTailBits symbol)
            (inputBits rest)).map some } := by
  rw [initialTape, inputBits_cons]
  rfl

theorem initialProtectedSuffix_nil
    (D : MachineDescription)
    (remainingFuel : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    initialProtectedSuffix D remainingFuel [] callerSuffix =
      MachineDescription.encodeCellListAppend []
        (MachineDescription.encodeCellListAppend []
          (loopCallerSuffix D remainingFuel callerSuffix)) := by
  rfl

theorem initialProtectedSuffix_cons
    (D : MachineDescription)
    (remainingFuel : Nat)
    (symbol : MachineCodeSymbol)
    (rest callerSuffix : Word MachineCodeSymbol) :
    initialProtectedSuffix D remainingFuel (symbol :: rest) callerSuffix =
      MachineDescription.encodeCellListAppend []
        (MachineDescription.encodeCellListAppend
          ((List.append (codeSymbolTailBits symbol)
            (inputBits rest)).map some)
          (loopCallerSuffix D remainingFuel callerSuffix)) := by
  rw [initialProtectedSuffix, initialTape_cons]
  rfl

theorem initialScanConfig_exact
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol) :
    initialScanConfig D remainingFuel input callerSuffix =
      canonicalScanRowsConfig
        { state := D.start
          tape := Tape.input
            (MachineDescription.encodeCodeWordAsInput input) }
        [] D.transitions
        (protectedTapeContextsAppend
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput input))
          (MachineDescription.encodeNatAppend D.halt
            (MachineDescription.encodeNatAppend remainingFuel
              callerSuffix))) := by
  rfl

theorem initialScanConfig_first_row
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest) :
    TuringMachine.Computes comparatorMachine
      (initialScanConfig D remainingFuel input callerSuffix)
      (canonicalSeparatedRowTarget (initialConfiguration D input) []
        first rest
        (initialProtectedSuffix D remainingFuel input callerSuffix)) := by
  simpa [initialScanConfig, htransitions] using
    (comparator_computes_scan_head
      (initialConfiguration D input) [] first rest
      (initialProtectedSuffix D remainingFuel input callerSuffix))

/-!
### Concrete bounded Boolean-cell insertion

Each raw code symbol expands to four Boolean cells. `VariableBlockInsert`
therefore gives a finite, suffix-preserving insertion phase with capacity
four, which serves as the symbol-expansion action of the raw-tail loop.
-/

def encodedBoolCell (bit : Bool) : MachineCodeSymbol :=
  if bit then MachineCodeSymbol.one else MachineCodeSymbol.zero

def encodedCodeSymbolCellBlock
    (symbol : MachineCodeSymbol) : Word MachineCodeSymbol :=
  (MachineDescription.encodeCodeSymbolAsInput symbol).map encodedBoolCell

def encodedCodeSymbolTailCellBlock
    (symbol : MachineCodeSymbol) : Word MachineCodeSymbol :=
  (codeSymbolTailBits symbol).map encodedBoolCell

theorem encodedCodeSymbolCellBlock_length
    (symbol : MachineCodeSymbol) :
    (encodedCodeSymbolCellBlock symbol).length = 4 := by
  cases symbol <;> rfl

theorem encodedCodeSymbolTailCellBlock_length
    (symbol : MachineCodeSymbol) :
    (encodedCodeSymbolTailCellBlock symbol).length = 3 := by
  cases symbol <;> rfl

theorem encodedCodeSymbolCellBlock_ne_nil
    (symbol : MachineCodeSymbol) :
    encodedCodeSymbolCellBlock symbol ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  rw [encodedCodeSymbolCellBlock_length] at hlength
  simp at hlength

def encodedCodeSymbolCellBuffer
    (symbol : MachineCodeSymbol) : VariableBlockInsert.Buffer 4 :=
  ⟨encodedCodeSymbolCellBlock symbol, by
    rw [encodedCodeSymbolCellBlock_length]
    exact Nat.le_refl 4⟩

theorem encodedCodeSymbolCellBuffer_nonempty
    (symbol : MachineCodeSymbol) :
    (encodedCodeSymbolCellBuffer symbol).word ≠ [] :=
  encodedCodeSymbolCellBlock_ne_nil symbol

def encodedCodeSymbolInsertSource
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol)) :=
  VariableBlockInsert.config (encodedCodeSymbolCellBuffer symbol)
    leftRev baseCells suffix

def encodedCodeSymbolInsertTarget
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol)) :=
  VariableBlockInsert.haltConfig (capacity := 4)
    (VariableBlockInsert.finalLeftRev
      (encodedCodeSymbolCellBuffer symbol) leftRev suffix)
    baseCells

theorem encodedCodeSymbolInsert_run_exact
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol)) :
    (VariableBlockInsert.machine 4
      (encodedCodeSymbolCellBuffer symbol)).runConfigExact?
        (suffix.length +
          (encodedCodeSymbolCellBuffer symbol).word.length)
        (encodedCodeSymbolInsertSource symbol leftRev suffix baseCells) =
      some
        (encodedCodeSymbolInsertTarget symbol leftRev suffix baseCells) := by
  exact VariableBlockInsert.run_exact
    (encodedCodeSymbolCellBuffer symbol)
    (encodedCodeSymbolCellBuffer symbol)
    leftRev suffix baseCells
    (encodedCodeSymbolCellBuffer_nonempty symbol)

theorem encodedCodeSymbolInsert_target_word
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    (VariableBlockInsert.finalLeftRev
      (encodedCodeSymbolCellBuffer symbol) leftRev suffix).reverse =
      List.append leftRev.reverse
        (List.append (encodedCodeSymbolCellBlock symbol) suffix) := by
  exact VariableBlockInsert.finalLeftRev_reverse
    (encodedCodeSymbolCellBuffer symbol) leftRev suffix
    (encodedCodeSymbolCellBuffer_nonempty symbol)


/-!
### Persistent table copy instantiated with the explicit contexts
-/

def initialPersistentCopySource
    (baseLeftRev : Word MachineCodeSymbol)
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol) :=
  PersistentMasterCopier.sourceConfig baseLeftRev
    (MachineDescription.encodeTransitions D.transitions)
    (initialProtectedSuffix D remainingFuel input callerSuffix)

def initialPersistentCopyTarget
    (baseLeftRev : Word MachineCodeSymbol)
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol) :=
  PersistentMasterCopier.readyConfig baseLeftRev
    (MachineDescription.encodeTransitions D.transitions)
    (initialActiveTableSuffix D remainingFuel input callerSuffix)

theorem initialPersistentCopy_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest) :
    PersistentMasterCopier.machine.runConfigExact?
        (PersistentMasterCopier.runSteps
          (MachineDescription.encodeTransitions D.transitions)
          (initialProtectedSuffix D remainingFuel input callerSuffix))
        (initialPersistentCopySource baseLeftRev D remainingFuel input
          callerSuffix) =
      some
        (initialPersistentCopyTarget baseLeftRev D remainingFuel input
          callerSuffix) := by
  simpa [initialPersistentCopySource, initialPersistentCopyTarget,
      initialActiveTableSuffix, htransitions] using
    (PersistentMasterCopier.raw_transition_table_run_exact
      baseLeftRev first rest
      (initialProtectedSuffix D remainingFuel input callerSuffix))

theorem initialPersistentCopy_active_word
    (baseLeftRev : Word MachineCodeSymbol)
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input callerSuffix : Word MachineCodeSymbol) :
    (initialPersistentCopyTarget baseLeftRev D remainingFuel input
      callerSuffix).tape =
      PersistentMasterCopier.readyTape baseLeftRev
        (MachineDescription.encodeTransitions D.transitions)
        (MachineCodeSymbol.header ::
          RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
            (Tape.input
              (MachineDescription.encodeCodeWordAsInput input))
            (MachineDescription.encodeNatAppend D.halt
              (MachineDescription.encodeNatAppend remainingFuel
                callerSuffix))) := by
  rfl

/-!
### Zero-fuel and empty-table final comparison
-/

def finalCallerSuffix
    (input callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  protectedTapeContextsAppend (initialTape input) callerSuffix

def initialFinalComparatorSource
    (D : MachineDescription)
    (input callerSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RuntimeKeyComparatorState :=
  { state := RuntimeKeyComparatorState.needHeader
    tape := runtimeKeyComparatorTape []
      (MachineCodeSymbol.header ::
        runtimeKeyComparatorBody
          (List.replicate D.halt MachineCodeSymbol.tick) none
          (List.replicate D.start MachineCodeSymbol.tick) none
          (finalCallerSuffix input callerSuffix)) }

def initialFinalComparatorTarget
    (D : MachineDescription)
    (input callerSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RuntimeKeyComparatorState :=
  { state :=
      if D.halt = D.start then
        RuntimeKeyComparatorState.matched
      else RuntimeKeyComparatorState.missed
    tape := runtimeKeyComparatorTape
      (runtimeKeyComparatorRestoredLeft
        (List.replicate D.halt MachineCodeSymbol.tick) none
        (List.replicate D.start MachineCodeSymbol.tick) none
        [MachineCodeSymbol.header])
      (finalCallerSuffix input callerSuffix) }

theorem initialFinalComparator_computes
    (D : MachineDescription)
    (input callerSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      (initialFinalComparatorSource D input callerSuffix)
      (initialFinalComparatorTarget D input callerSuffix) := by
  by_cases heq : D.halt = D.start
  · simpa [initialFinalComparatorSource, initialFinalComparatorTarget,
      runtimeKeyComparatorRowOutcome, runtimeKeyComparatorReadOutcome,
      runtimeKeyComparatorOutcomeState, heq] using
      (runtimeKeyComparatorMachine_computes_one_row_from_header
        D.halt none D.start none (finalCallerSuffix input callerSuffix))
  · simpa [initialFinalComparatorSource, initialFinalComparatorTarget,
      runtimeKeyComparatorRowOutcome, runtimeKeyComparatorReadOutcome,
      runtimeKeyComparatorOutcomeState, heq] using
      (runtimeKeyComparatorMachine_computes_one_row_from_header
        D.halt none D.start none (finalCallerSuffix input callerSuffix))

theorem initialFinalComparator_haltsFrom_iff
    (D : MachineDescription)
    (input callerSuffix : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (initialFinalComparatorSource D input callerSuffix) <->
      D.start = D.halt := by
  constructor
  · intro hhalt
    by_cases heq : D.halt = D.start
    · exact heq.symm
    · have hrun :=
        runtimeKeyComparatorMachine_computes_one_row_from_header
          D.halt none D.start none (finalCallerSuffix input callerSuffix)
      have hnot :=
        TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          (M := runtimeKeyComparatorMachine)
          (by intro read; rfl)
          (by
            simpa [initialFinalComparatorSource] using hrun)
          (by
            simp [TuringMachine.Halted, runtimeKeyComparatorMachine,
              runtimeKeyComparatorRowOutcome, heq,
              runtimeKeyComparatorOutcomeState])
          (by
            intro next
            apply TuringMachine.not_step_of_transition_eq_none
            simp [runtimeKeyComparatorMachine,
              runtimeKeyComparatorRowOutcome, heq,
              runtimeKeyComparatorOutcomeState])
      exact False.elim (hnot hhalt)
  · intro heq
    have hrun :=
      runtimeKeyComparatorMachine_computes_one_row_from_header
        D.halt none D.start none (finalCallerSuffix input callerSuffix)
    apply TuringMachine.halts_from_of_computes
      (by
        simpa [initialFinalComparatorSource] using hrun)
    simp [TuringMachine.Halted, runtimeKeyComparatorMachine,
      runtimeKeyComparatorRowOutcome, runtimeKeyComparatorReadOutcome,
      runtimeKeyComparatorOutcomeState, heq]

theorem runConfig_zero
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    D.runConfig 0 (initialConfiguration D input) =
      initialConfiguration D input := by
  rfl

theorem runConfig_empty_transitions
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    ({ D with transitions := [] }).runConfig fuel
        (initialConfiguration D input) =
      initialConfiguration D input := by
  cases fuel with
  | zero => rfl
  | succ remaining =>
      apply runConfig_fullScanNoMatch
      intro transition hmem
      simp at hmem

theorem zeroFuel_final_state_iff
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (D.runConfig 0 (initialConfiguration D input)).state = D.halt <->
      D.start = D.halt := by
  rw [runConfig_zero]
  rfl

theorem emptyTransitions_final_state_iff
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    (({ D with transitions := [] }).runConfig fuel
      (initialConfiguration D input)).state = D.halt <->
      D.start = D.halt := by
  rw [runConfig_empty_transitions]
  rfl

/-!
### Positive-branch materializer frontier

The parser endpoint replaces the first input symbol by `header`, so its
physical tape does not determine the initial Boolean configuration for
singleton inputs. The saved-cell parser wrapper carries that erased symbol in
finite control. The executable frontier fixes the public caller suffix to the
empty word, reads fuel from parsed metadata and the table-copy count, and
applies to the positive-fuel, nonempty-table branch.
-/

def appendParsedLeftContext
    (baseLeftRev : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := List.append tape.left (baseLeftRev.map some)
    head := tape.head
    right := tape.right }

def markedParserMaterializerSourceTape
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  appendParsedLeftContext baseLeftRev
    (parsedTransitionHaltConfig (first :: rest).length
      (MachineDescription.encodeTransitions (first :: rest)) input).tape

theorem markedParserMaterializerSourceTape_singleton_collision
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription) :
    markedParserMaterializerSourceTape baseLeftRev first rest
        [MachineCodeSymbol.header] =
      markedParserMaterializerSourceTape baseLeftRev first rest
        [MachineCodeSymbol.transition] := by
  rfl

theorem singleton_inputBits_ne :
    inputBits [MachineCodeSymbol.header] ≠
      inputBits [MachineCodeSymbol.transition] := by
  decide

def savedParserMaterializerSourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control :=
  { state :=
      .ready (transitionListParserSavedHead input)
    tape :=
      markedParserMaterializerSourceTape baseLeftRev first rest input }

/-- The saved wrapper distinguishes the two singleton inputs even though its
physical tapes coincide. -/
theorem savedParserMaterializerSourceConfig_singletons_ne
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription) :
    savedParserMaterializerSourceConfig baseLeftRev first rest
        [MachineCodeSymbol.header] ≠
      savedParserMaterializerSourceConfig baseLeftRev first rest
        [MachineCodeSymbol.transition] := by
  intro heq
  have hstate := congrArg
    (fun config => config.state) heq
  simp [savedParserMaterializerSourceConfig,
    transitionListParserSavedHead] at hstate

/-- Parameter-recovery guardrail. This source shape demonstrates that fuel and
the caller suffix are not recoverable when neither parameter occurs in the
physical source. -/
def underSpecifiedMaterializerSourceTape
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol)
    (_remainingFuel : Nat)
    (_callerSuffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  markedParserMaterializerSourceTape baseLeftRev first rest input

theorem underSpecifiedMaterializerSourceTape_ignores_fuel_and_caller
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol)
    (fuelA fuelB : Nat)
    (callerA callerB : Word MachineCodeSymbol) :
    underSpecifiedMaterializerSourceTape baseLeftRev first rest input
        fuelA callerA =
      underSpecifiedMaterializerSourceTape baseLeftRev first rest input
        fuelB callerB := by
  rfl

/-- The only context payload needed by the copier loop invariant. Fuel is not
duplicated here; it is represented by the number of table-stack copies. -/
def positiveInitialContextTail
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  protectedTapeContextsAppend (initialTape input)
    (MachineDescription.encodeNatAppend D.halt [])

/-- At zero completed copies the stack already contains its final sentinel. -/
def positiveInitialStackSuffix
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header :: positiveInitialContextTail D input

theorem positiveInitialStackSuffix_exact
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    positiveInitialStackSuffix D input =
      MachineCodeSymbol.header :: positiveInitialContextTail D input := by
  rfl

/-- Reversed left word retained behind the copier's older separator.  During
Boolean materialization the counter `done` stays encoded.  The older physical
separator is first rewritten to encoded `blank`; only after all prepend phases
does the counter become the physical separator immediately left of the raw
table. -/
def positiveMaterializerCopierBaseLeftRev
    (D : MachineDescription)
    (fuel : Nat) : Word MachineCodeSymbol :=
  List.append
    (List.replicate D.transitions.length MachineCodeSymbol.blank)
    (MachineCodeSymbol.blank ::
      FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel)

def positiveMaterializerTargetConfig
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription) :=
  PersistentMasterCopier.sourceConfig
    (positiveMaterializerCopierBaseLeftRev D (remainingFuel + 1))
    (MachineDescription.encodeTransitions (first :: rest))
    (positiveInitialStackSuffix D input)

/-- Boolean-context materializer contract. Every target parameter is
recoverable from the source configuration: entry stores the first input cell,
parsed left metadata stores fuel and description fields, the raw input tail
lies to the right of its marker, and the public caller suffix is empty.

The endpoint uses `Tape.Equiv` because rewind gates may preserve harmless
far-blank padding. The persistent copier and runtime loop transport their runs
across the same equivalence, so physical tape equality would expose an
unobservable window-size choice. -/
def SavedPositiveBooleanContextMaterializerContract
    {materializerState : Type}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (entry : Option MachineCodeSymbol -> materializerState)
    (halt : materializerState) : Prop :=
  forall
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription),
    D.transitions = first :: rest ->
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes materializer
        { state := entry (transitionListParserSavedHead input)
          tape :=
            markedParserMaterializerSourceTape
              (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
                (remainingFuel + 1))
              first rest input }
        { state := halt, tape := targetTape } ∧
      Tape.Equiv
        (positiveMaterializerTargetConfig D remainingFuel input
          first rest).tape
        targetTape


end FiniteRecognizer.Interpreter.InitializerFrontier

end Computability
end FoC
