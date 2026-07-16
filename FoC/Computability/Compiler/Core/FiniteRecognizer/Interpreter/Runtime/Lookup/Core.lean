import FoC.Computability.MachineBuilder.Encoding
import FoC.Computability.Compiler.Core.EncodingLemmas
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Duplicator
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Basic

namespace FoC
namespace Computability

open Languages

namespace Section53UniformInterpreterOneStep

theorem findTransition_none_of_everyRowMisses
    (source : Nat) (read : Option Bool)
    (transitions : List TransitionDescription)
    (hmiss :
      forall transition : TransitionDescription,
        transition ∈ transitions ->
          MachineDescription.Matches source read transition = false) :
    transitions.find? (MachineDescription.Matches source read) = none := by
  induction transitions with
  | nil =>
      rfl
  | cons transition rest ih =>
      have hhead :
          MachineDescription.Matches source read transition = false :=
        hmiss transition (by simp)
      have htail :
          forall candidate : TransitionDescription,
            candidate ∈ rest ->
              MachineDescription.Matches source read candidate = false := by
        intro candidate hmem
        exact hmiss candidate (by simp [hmem])
      simp [hhead, ih htail]
  done
theorem runConfig_fullScanNoMatch
    (D : MachineDescription) (remaining : Nat)
    (config : MachineDescription.Configuration)
    (hmiss :
      forall transition : TransitionDescription,
        transition ∈ D.transitions ->
          MachineDescription.Matches config.state (Tape.read config.tape)
            transition = false) :
    D.runConfig (remaining + 1) config = config := by
  have hlookup :
      D.lookupTransition config.state (Tape.read config.tape) = none := by
    unfold MachineDescription.lookupTransition
    exact
      findTransition_none_of_everyRowMisses
        config.state (Tape.read config.tape) D.transitions hmiss
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookup]
  done
inductive RuntimeKeyComparatorOutcome where
  | isMatch : RuntimeKeyComparatorOutcome
  | isMiss : RuntimeKeyComparatorOutcome
deriving DecidableEq

inductive RuntimeKeyComparatorState where
  | needHeader : RuntimeKeyComparatorState
  | scanQuery : RuntimeKeyComparatorState
  | seekQueryEnd : RuntimeKeyComparatorState
  | skipQueryRead : RuntimeKeyComparatorState
  | needTransition : RuntimeKeyComparatorState
  | scanRow : RuntimeKeyComparatorState
  | rewind : RuntimeKeyComparatorState
  | rememberQueryRead : RuntimeKeyComparatorState
  | finishNeedTransition
      (read : Option Bool) : RuntimeKeyComparatorState
  | finishScanRow
      (read : Option Bool) : RuntimeKeyComparatorState
  | compareRead
      (read : Option Bool) : RuntimeKeyComparatorState
  | rewindOutcome
      (outcome : RuntimeKeyComparatorOutcome) : RuntimeKeyComparatorState
  | restoreQuery
      (outcome : RuntimeKeyComparatorOutcome) : RuntimeKeyComparatorState
  | restoreSkipQueryRead
      (outcome : RuntimeKeyComparatorOutcome) : RuntimeKeyComparatorState
  | restoreNeedTransition
      (outcome : RuntimeKeyComparatorOutcome) : RuntimeKeyComparatorState
  | restoreRow
      (outcome : RuntimeKeyComparatorOutcome) : RuntimeKeyComparatorState
  | restoreSkipRowRead
      (outcome : RuntimeKeyComparatorOutcome) : RuntimeKeyComparatorState
  | matched : RuntimeKeyComparatorState
  | missed : RuntimeKeyComparatorState
deriving DecidableEq

namespace RuntimeKeyComparatorState

def optionBools : List (Option Bool) :=
  [none, some false, some true]

def outcomes : List RuntimeKeyComparatorOutcome :=
  [RuntimeKeyComparatorOutcome.isMatch,
    RuntimeKeyComparatorOutcome.isMiss]

theorem outcomes_complete (outcome : RuntimeKeyComparatorOutcome) :
    outcome ∈ outcomes := by
  cases outcome <;> simp [outcomes]

theorem optionBools_complete (read : Option Bool) :
    read ∈ optionBools := by
  cases read with
  | none => simp [optionBools]
  | some bit =>
      cases bit <;> simp [optionBools]

def elems : List RuntimeKeyComparatorState :=
  [needHeader, scanQuery, seekQueryEnd, skipQueryRead,
    needTransition, scanRow, rewind, rememberQueryRead] ++
    optionBools.map finishNeedTransition ++
    optionBools.map finishScanRow ++
    optionBools.map compareRead ++
    outcomes.map rewindOutcome ++
    outcomes.map restoreQuery ++
    outcomes.map restoreSkipQueryRead ++
    outcomes.map restoreNeedTransition ++
    outcomes.map restoreRow ++
    outcomes.map restoreSkipRowRead ++
    [matched, missed]

def finite : Foundation.FiniteType RuntimeKeyComparatorState where
  elems := elems
  complete := by
    intro state
    cases state with
    | needHeader => simp [elems]
    | scanQuery => simp [elems]
    | seekQueryEnd => simp [elems]
    | skipQueryRead => simp [elems]
    | needTransition => simp [elems]
    | scanRow => simp [elems]
    | rewind => simp [elems]
    | rememberQueryRead => simp [elems]
    | finishNeedTransition read =>
        simp [elems, optionBools_complete read]
    | finishScanRow read =>
        simp [elems, optionBools_complete read]
    | compareRead read =>
        simp [elems, optionBools_complete read]
    | rewindOutcome outcome =>
        simp [elems, outcomes_complete outcome]
    | restoreQuery outcome =>
        simp [elems, outcomes_complete outcome]
    | restoreSkipQueryRead outcome =>
        simp [elems, outcomes_complete outcome]
    | restoreNeedTransition outcome =>
        simp [elems, outcomes_complete outcome]
    | restoreRow outcome =>
        simp [elems, outcomes_complete outcome]
    | restoreSkipRowRead outcome =>
        simp [elems, outcomes_complete outcome]
    | matched => simp [elems]
    | missed => simp [elems]

end RuntimeKeyComparatorState

def runtimeKeyComparatorTape
    (leftRev rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := leftRev.map some
        head := none
        right := [] }
  | symbol :: suffix =>
      { left := leftRev.map some
        head := some symbol
        right := suffix.map some }

def runtimeKeyCellSymbol : Option Bool -> MachineCodeSymbol
  | none => MachineCodeSymbol.blank
  | some false => MachineCodeSymbol.zero
  | some true => MachineCodeSymbol.one

def runtimeKeyComparatorOutcomeState :
    RuntimeKeyComparatorOutcome -> RuntimeKeyComparatorState
  | RuntimeKeyComparatorOutcome.isMatch =>
      RuntimeKeyComparatorState.matched
  | RuntimeKeyComparatorOutcome.isMiss =>
      RuntimeKeyComparatorState.missed

def runtimeKeyComparatorReadOutcome
    (queryRead rowRead : Option Bool) : RuntimeKeyComparatorOutcome :=
  if queryRead = rowRead then
    RuntimeKeyComparatorOutcome.isMatch
  else
    RuntimeKeyComparatorOutcome.isMiss

def runtimeKeyComparatorRowOutcome
    (queryState : Nat) (queryRead : Option Bool)
    (rowState : Nat) (rowRead : Option Bool) :
    RuntimeKeyComparatorOutcome :=
  if queryState = rowState then
    runtimeKeyComparatorReadOutcome queryRead rowRead
  else
    RuntimeKeyComparatorOutcome.isMiss

def runtimeKeyComparatorBody
    (queryCells : Word MachineCodeSymbol)
    (queryRead : Option Bool)
    (rowCells : Word MachineCodeSymbol)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append queryCells
    (MachineCodeSymbol.done ::
      runtimeKeyCellSymbol queryRead ::
      MachineCodeSymbol.transition ::
      List.append rowCells
        (MachineCodeSymbol.done ::
          runtimeKeyCellSymbol rowRead :: actionSuffix))

def runtimeKeyComparatorRestoredLeft
    (queryCells : Word MachineCodeSymbol)
    (queryRead : Option Bool)
    (rowCells : Word MachineCodeSymbol)
    (rowRead : Option Bool)
    (leftRev : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  runtimeKeyCellSymbol rowRead ::
    MachineCodeSymbol.done ::
    List.append
      (rowCells.map (fun _ => MachineCodeSymbol.tick)).reverse
      (MachineCodeSymbol.transition ::
        runtimeKeyCellSymbol queryRead ::
        MachineCodeSymbol.done ::
        List.append
          (queryCells.map (fun _ => MachineCodeSymbol.tick)).reverse
          leftRev)

def runtimeKeyComparatorComparisonPrefix
    (queryCells : Word MachineCodeSymbol)
    (queryRead : Option Bool)
    (rowCells : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append rowCells.reverse
    (MachineCodeSymbol.transition ::
      runtimeKeyCellSymbol queryRead ::
      MachineCodeSymbol.done :: queryCells.reverse)

def runtimeKeyComparatorCycleSource
    (marked queryRemaining : Nat)
    (queryRead : Option Bool)
    (rowRemaining : Nat)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append
    (List.replicate marked MachineCodeSymbol.blank)
    (MachineCodeSymbol.tick ::
      List.append
        (List.replicate queryRemaining MachineCodeSymbol.tick)
        (MachineCodeSymbol.done ::
          runtimeKeyCellSymbol queryRead ::
          MachineCodeSymbol.transition ::
          List.append
            (List.replicate marked MachineCodeSymbol.blank)
            (MachineCodeSymbol.tick ::
              List.append
                (List.replicate rowRemaining MachineCodeSymbol.tick)
                (MachineCodeSymbol.done ::
                  runtimeKeyCellSymbol rowRead :: actionSuffix))))

def runtimeKeyComparatorCycleTarget
    (marked queryRemaining : Nat)
    (queryRead : Option Bool)
    (rowRemaining : Nat)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append
    (List.replicate marked MachineCodeSymbol.blank)
    (MachineCodeSymbol.blank ::
      List.append
        (List.replicate queryRemaining MachineCodeSymbol.tick)
        (MachineCodeSymbol.done ::
          runtimeKeyCellSymbol queryRead ::
          MachineCodeSymbol.transition ::
          List.append
            (List.replicate marked MachineCodeSymbol.blank)
            (MachineCodeSymbol.blank ::
              List.append
                (List.replicate rowRemaining MachineCodeSymbol.tick)
                (MachineCodeSymbol.done ::
                  runtimeKeyCellSymbol rowRead :: actionSuffix))))

def runtimeKeyComparatorPairedBody
    (marked remaining : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  runtimeKeyComparatorBody
    (List.append
      (List.replicate marked MachineCodeSymbol.blank)
      (List.replicate remaining MachineCodeSymbol.tick))
    queryRead
    (List.append
      (List.replicate marked MachineCodeSymbol.blank)
      (List.replicate remaining MachineCodeSymbol.tick))
    rowRead actionSuffix

def runtimeKeyComparatorComparedBody
    (marked queryRemaining rowRemaining : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  runtimeKeyComparatorBody
    (List.append
      (List.replicate marked MachineCodeSymbol.blank)
      (List.replicate queryRemaining MachineCodeSymbol.tick))
    queryRead
    (List.append
      (List.replicate marked MachineCodeSymbol.blank)
      (List.replicate rowRemaining MachineCodeSymbol.tick))
    rowRead actionSuffix

theorem replicate_succ_eq_append_singleton
    {alpha : Type} (n : Nat) (value : alpha) :
    List.replicate (n + 1) value =
      List.append (List.replicate n value) [value] := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [List.replicate_succ] using
        congrArg (fun cells => value :: cells) ih
  done

theorem cons_replicate_eq_append_singleton
    {alpha : Type} (n : Nat) (value : alpha) :
    value :: List.replicate n value =
      List.append (List.replicate n value) [value] := by
  simpa only [List.replicate_succ] using
    replicate_succ_eq_append_singleton n value
  done

theorem cons_replicate_append_eq_replicate_append_cons
    {alpha : Type} (n : Nat) (value : alpha) (suffix : List alpha) :
    value :: List.append (List.replicate n value) suffix =
      List.append (List.replicate n value) (value :: suffix) := by
  simpa [List.append_assoc] using
    congrArg (fun cells => List.append cells suffix)
      (cons_replicate_eq_append_singleton n value)
  done

theorem replicate_add_eq_append
    {alpha : Type} (left right : Nat) (value : alpha) :
    List.replicate (left + right) value =
      List.append (List.replicate left value)
        (List.replicate right value) := by
  induction left with
  | zero => simp
  | succ left ih =>
      rw [Nat.succ_add, List.replicate_succ, List.replicate_succ]
      exact congrArg (fun cells => value :: cells) ih
  done

theorem runtimeKeyComparatorTape_move_right
    (leftRev : Word MachineCodeSymbol)
    (symbol write : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write (some write)
          (runtimeKeyComparatorTape leftRev (symbol :: suffix))) =
      runtimeKeyComparatorTape (write :: leftRev) suffix := by
  cases suffix <;>
    simp [runtimeKeyComparatorTape, Tape.move,
      Tape.moveRight, Tape.write]

theorem runtimeKeyComparatorTape_move_left
    (leftTail suffix : Word MachineCodeSymbol)
    (leftHead old write : MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.write (some write)
          (runtimeKeyComparatorTape
            (leftHead :: leftTail) (old :: suffix))) =
      runtimeKeyComparatorTape leftTail
        (leftHead :: write :: suffix) := by
  cases suffix <;>
    simp [runtimeKeyComparatorTape, Tape.move,
      Tape.moveLeft, Tape.write]

def runtimeKeyComparatorMachine :
    TuringMachine MachineCodeSymbol RuntimeKeyComparatorState where
  start := RuntimeKeyComparatorState.needHeader
  halt := RuntimeKeyComparatorState.matched
  transition := fun state cell =>
    match state, cell with
    | RuntimeKeyComparatorState.needHeader,
        some MachineCodeSymbol.header =>
        some
          (some MachineCodeSymbol.header, Direction.right,
            RuntimeKeyComparatorState.scanQuery)
    | RuntimeKeyComparatorState.scanQuery,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            RuntimeKeyComparatorState.scanQuery)
    | RuntimeKeyComparatorState.scanQuery,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            RuntimeKeyComparatorState.seekQueryEnd)
    | RuntimeKeyComparatorState.scanQuery,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            RuntimeKeyComparatorState.rememberQueryRead)
    | RuntimeKeyComparatorState.seekQueryEnd,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            RuntimeKeyComparatorState.seekQueryEnd)
    | RuntimeKeyComparatorState.seekQueryEnd,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            RuntimeKeyComparatorState.skipQueryRead)
    | RuntimeKeyComparatorState.skipQueryRead, some symbol =>
        some
          (some symbol, Direction.right,
            RuntimeKeyComparatorState.needTransition)
    | RuntimeKeyComparatorState.needTransition,
        some MachineCodeSymbol.transition =>
        some
          (some MachineCodeSymbol.transition, Direction.right,
            RuntimeKeyComparatorState.scanRow)
    | RuntimeKeyComparatorState.scanRow,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            RuntimeKeyComparatorState.scanRow)
    | RuntimeKeyComparatorState.scanRow,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.blank, Direction.left,
            RuntimeKeyComparatorState.rewind)
    | RuntimeKeyComparatorState.scanRow,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.left,
            RuntimeKeyComparatorState.rewindOutcome
              RuntimeKeyComparatorOutcome.isMiss)
    | RuntimeKeyComparatorState.rewind,
        some MachineCodeSymbol.header =>
        some
          (some MachineCodeSymbol.header, Direction.right,
            RuntimeKeyComparatorState.scanQuery)
    | RuntimeKeyComparatorState.rewind, some symbol =>
        some
          (some symbol, Direction.left,
            RuntimeKeyComparatorState.rewind)
    | RuntimeKeyComparatorState.rememberQueryRead,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            RuntimeKeyComparatorState.finishNeedTransition none)
    | RuntimeKeyComparatorState.rememberQueryRead,
        some MachineCodeSymbol.zero =>
        some
          (some MachineCodeSymbol.zero, Direction.right,
            RuntimeKeyComparatorState.finishNeedTransition (some false))
    | RuntimeKeyComparatorState.rememberQueryRead,
        some MachineCodeSymbol.one =>
        some
          (some MachineCodeSymbol.one, Direction.right,
            RuntimeKeyComparatorState.finishNeedTransition (some true))
    | RuntimeKeyComparatorState.finishNeedTransition read,
        some MachineCodeSymbol.transition =>
        some
          (some MachineCodeSymbol.transition, Direction.right,
            RuntimeKeyComparatorState.finishScanRow read)
    | RuntimeKeyComparatorState.finishScanRow read,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            RuntimeKeyComparatorState.finishScanRow read)
    | RuntimeKeyComparatorState.finishScanRow _,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.left,
            RuntimeKeyComparatorState.rewindOutcome
              RuntimeKeyComparatorOutcome.isMiss)
    | RuntimeKeyComparatorState.finishScanRow read,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            RuntimeKeyComparatorState.compareRead read)
    | RuntimeKeyComparatorState.compareRead none,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.blank, Direction.left,
            RuntimeKeyComparatorState.rewindOutcome
              RuntimeKeyComparatorOutcome.isMatch)
    | RuntimeKeyComparatorState.compareRead (some false),
        some MachineCodeSymbol.zero =>
        some
          (some MachineCodeSymbol.zero, Direction.left,
            RuntimeKeyComparatorState.rewindOutcome
              RuntimeKeyComparatorOutcome.isMatch)
    | RuntimeKeyComparatorState.compareRead (some true),
        some MachineCodeSymbol.one =>
        some
          (some MachineCodeSymbol.one, Direction.left,
            RuntimeKeyComparatorState.rewindOutcome
              RuntimeKeyComparatorOutcome.isMatch)
    | RuntimeKeyComparatorState.compareRead _, some symbol =>
        some
          (some symbol, Direction.left,
            RuntimeKeyComparatorState.rewindOutcome
              RuntimeKeyComparatorOutcome.isMiss)
    | RuntimeKeyComparatorState.rewindOutcome outcome,
        some MachineCodeSymbol.header =>
        some
          (some MachineCodeSymbol.header, Direction.right,
            RuntimeKeyComparatorState.restoreQuery outcome)
    | RuntimeKeyComparatorState.rewindOutcome outcome, some symbol =>
        some
          (some symbol, Direction.left,
            RuntimeKeyComparatorState.rewindOutcome outcome)
    | RuntimeKeyComparatorState.restoreQuery outcome,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            RuntimeKeyComparatorState.restoreQuery outcome)
    | RuntimeKeyComparatorState.restoreQuery outcome,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            RuntimeKeyComparatorState.restoreQuery outcome)
    | RuntimeKeyComparatorState.restoreQuery outcome,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            RuntimeKeyComparatorState.restoreSkipQueryRead outcome)
    | RuntimeKeyComparatorState.restoreSkipQueryRead outcome,
        some symbol =>
        some
          (some symbol, Direction.right,
            RuntimeKeyComparatorState.restoreNeedTransition outcome)
    | RuntimeKeyComparatorState.restoreNeedTransition outcome,
        some MachineCodeSymbol.transition =>
        some
          (some MachineCodeSymbol.transition, Direction.right,
            RuntimeKeyComparatorState.restoreRow outcome)
    | RuntimeKeyComparatorState.restoreRow outcome,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            RuntimeKeyComparatorState.restoreRow outcome)
    | RuntimeKeyComparatorState.restoreRow outcome,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            RuntimeKeyComparatorState.restoreRow outcome)
    | RuntimeKeyComparatorState.restoreRow outcome,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            RuntimeKeyComparatorState.restoreSkipRowRead outcome)
    | RuntimeKeyComparatorState.restoreSkipRowRead
        RuntimeKeyComparatorOutcome.isMatch,
        some symbol =>
        some
          (some symbol, Direction.right,
            RuntimeKeyComparatorState.matched)
    | RuntimeKeyComparatorState.restoreSkipRowRead
        RuntimeKeyComparatorOutcome.isMiss,
        some symbol =>
        some
          (some symbol, Direction.right,
            RuntimeKeyComparatorState.missed)
    | _, _ => none
  statesFinite := RuntimeKeyComparatorState.finite

theorem runtimeKeyComparatorMachine_step_header
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.needHeader
        tape :=
          runtimeKeyComparatorTape []
            (MachineCodeSymbol.header :: suffix) }
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header] suffix } := by
  rw [← runtimeKeyComparatorTape_move_right []
    MachineCodeSymbol.header MachineCodeSymbol.header suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])
theorem runtimeKeyComparatorMachine_step_rewind_outcome_symbol
    (outcome : RuntimeKeyComparatorOutcome)
    (leftHead current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.rewindOutcome outcome
        tape :=
          runtimeKeyComparatorTape (leftHead :: leftTail)
            (current :: suffix) }
      { state := RuntimeKeyComparatorState.rewindOutcome outcome
        tape :=
          runtimeKeyComparatorTape leftTail
            (leftHead :: current :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead current current]
  exact TuringMachine.Step.mk (by
    cases current <;>
      simp [runtimeKeyComparatorMachine,
        runtimeKeyComparatorTape, Tape.read] at hcurrent ⊢)

theorem runtimeKeyComparatorMachine_computes_rewind_outcome_to_header
    (outcome : RuntimeKeyComparatorOutcome)
    (leftSymbols : Word MachineCodeSymbol)
    (hleftSymbols :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol leftSymbols ->
          symbol ≠ MachineCodeSymbol.header)
    (current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.rewindOutcome outcome
        tape :=
          runtimeKeyComparatorTape
            (List.append leftSymbols [MachineCodeSymbol.header])
            (current :: suffix) }
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (List.append leftSymbols.reverse (current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      have hsymbol :=
        runtimeKeyComparatorMachine_step_rewind_outcome_symbol
          outcome MachineCodeSymbol.header current hcurrent [] suffix
      have hheader :
          TuringMachine.Step runtimeKeyComparatorMachine
            { state := RuntimeKeyComparatorState.rewindOutcome outcome
              tape :=
                runtimeKeyComparatorTape []
                  (MachineCodeSymbol.header :: current :: suffix) }
            { state := RuntimeKeyComparatorState.restoreQuery outcome
              tape :=
                runtimeKeyComparatorTape [MachineCodeSymbol.header]
                  (current :: suffix) } := by
        rw [← runtimeKeyComparatorTape_move_right []
          MachineCodeSymbol.header MachineCodeSymbol.header
          (current :: suffix)]
        exact TuringMachine.Step.mk (by
          simp [runtimeKeyComparatorMachine,
            runtimeKeyComparatorTape, Tape.read])
      exact
        TuringMachine.Computes.step
          (by simpa using hsymbol)
          (TuringMachine.Computes.step hheader
            (TuringMachine.Computes.refl _))
  | cons leftHead leftTail ih =>
      have hleftHead : leftHead ≠ MachineCodeSymbol.header :=
        hleftSymbols leftHead (List.Mem.head leftTail)
      have hleftTail :
          forall symbol : MachineCodeSymbol,
            List.Mem symbol leftTail ->
              symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hleftSymbols symbol (List.Mem.tail leftHead hmem)
      have hstep :=
        runtimeKeyComparatorMachine_step_rewind_outcome_symbol
          outcome leftHead current hcurrent
          (List.append leftTail [MachineCodeSymbol.header]) suffix
      have hrest :=
        ih hleftTail leftHead hleftHead (current :: suffix)
      exact
        TuringMachine.Computes.step
          (by simpa using hstep)
          (by
            simpa [List.reverse_cons, List.append_assoc]
              using hrest)

theorem runtimeKeyComparatorMachine_step_restore_query_blank
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.blank :: suffix) }
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.blank MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_step_restore_query_tick
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.tick MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_computes_restore_query_unary
    (outcome : RuntimeKeyComparatorOutcome)
    (cells : Word MachineCodeSymbol)
    (hcells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol cells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (List.append cells suffix) }
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape
            (List.append
              (cells.map (fun _ => MachineCodeSymbol.tick)).reverse
              leftRev)
            suffix } := by
  induction cells generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons head tail ih =>
      have hhead := hcells head (List.Mem.head tail)
      have htail :
          forall symbol : MachineCodeSymbol,
            List.Mem symbol tail ->
              symbol = MachineCodeSymbol.blank ∨
                symbol = MachineCodeSymbol.tick := by
        intro symbol hmem
        exact hcells symbol (List.Mem.tail head hmem)
      have hrest :=
        ih htail (MachineCodeSymbol.tick :: leftRev)
      rcases hhead with hblank | htick
      · subst head
        exact
          TuringMachine.Computes.step
            (by
              simpa using
                runtimeKeyComparatorMachine_step_restore_query_blank
                  outcome leftRev (List.append tail suffix))
            (by
              simpa [List.map, List.reverse_cons, List.append_assoc]
                using hrest)
      · subst head
        exact
          TuringMachine.Computes.step
            (by
              simpa using
                runtimeKeyComparatorMachine_step_restore_query_tick
                  outcome leftRev (List.append tail suffix))
            (by
              simpa [List.map, List.reverse_cons, List.append_assoc]
                using hrest)

theorem runtimeKeyComparatorMachine_step_restore_query_done
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state :=
          RuntimeKeyComparatorState.restoreSkipQueryRead outcome
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.done MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_step_restore_query_read
    (outcome : RuntimeKeyComparatorOutcome)
    (read : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state :=
          RuntimeKeyComparatorState.restoreSkipQueryRead outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (runtimeKeyCellSymbol read :: suffix) }
      { state :=
          RuntimeKeyComparatorState.restoreNeedTransition outcome
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyCellSymbol read :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    (runtimeKeyCellSymbol read) (runtimeKeyCellSymbol read) suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_step_restore_transition
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state :=
          RuntimeKeyComparatorState.restoreNeedTransition outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.transition :: suffix) }
      { state := RuntimeKeyComparatorState.restoreRow outcome
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.transition :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.transition MachineCodeSymbol.transition suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_step_restore_row_blank
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreRow outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.blank :: suffix) }
      { state := RuntimeKeyComparatorState.restoreRow outcome
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.blank MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_step_restore_row_tick
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreRow outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := RuntimeKeyComparatorState.restoreRow outcome
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.tick MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_computes_restore_row_unary
    (outcome : RuntimeKeyComparatorOutcome)
    (cells : Word MachineCodeSymbol)
    (hcells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol cells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreRow outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (List.append cells suffix) }
      { state := RuntimeKeyComparatorState.restoreRow outcome
        tape :=
          runtimeKeyComparatorTape
            (List.append
              (cells.map (fun _ => MachineCodeSymbol.tick)).reverse
              leftRev)
            suffix } := by
  induction cells generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons head tail ih =>
      have hhead := hcells head (List.Mem.head tail)
      have htail :
          forall symbol : MachineCodeSymbol,
            List.Mem symbol tail ->
              symbol = MachineCodeSymbol.blank ∨
                symbol = MachineCodeSymbol.tick := by
        intro symbol hmem
        exact hcells symbol (List.Mem.tail head hmem)
      have hrest :=
        ih htail (MachineCodeSymbol.tick :: leftRev)
      rcases hhead with hblank | htick
      · subst head
        exact
          TuringMachine.Computes.step
            (by
              simpa using
                runtimeKeyComparatorMachine_step_restore_row_blank
                  outcome leftRev (List.append tail suffix))
            (by
              simpa [List.map, List.reverse_cons, List.append_assoc]
                using hrest)
      · subst head
        exact
          TuringMachine.Computes.step
            (by
              simpa using
                runtimeKeyComparatorMachine_step_restore_row_tick
                  outcome leftRev (List.append tail suffix))
            (by
              simpa [List.map, List.reverse_cons, List.append_assoc]
                using hrest)

theorem runtimeKeyComparatorMachine_step_restore_row_done
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreRow outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := RuntimeKeyComparatorState.restoreSkipRowRead outcome
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.done MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_step_restore_row_read
    (outcome : RuntimeKeyComparatorOutcome)
    (read : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state :=
          RuntimeKeyComparatorState.restoreSkipRowRead outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (runtimeKeyCellSymbol read :: suffix) }
      { state := runtimeKeyComparatorOutcomeState outcome
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyCellSymbol read :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    (runtimeKeyCellSymbol read) (runtimeKeyCellSymbol read) suffix]
  cases outcome <;>
    exact TuringMachine.Step.mk (by
      simp [runtimeKeyComparatorMachine,
        runtimeKeyComparatorOutcomeState,
        runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_computes_restore_outcome_exact
    (outcome : RuntimeKeyComparatorOutcome)
    (queryCells : Word MachineCodeSymbol)
    (hqueryCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (queryRead : Option Bool)
    (rowCells : Word MachineCodeSymbol)
    (hrowCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (rowRead : Option Bool)
    (leftRev actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.restoreQuery outcome
        tape :=
          runtimeKeyComparatorTape leftRev
            (runtimeKeyComparatorBody
              queryCells queryRead rowCells rowRead actionSuffix) }
      { state := runtimeKeyComparatorOutcomeState outcome
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              queryCells queryRead rowCells rowRead leftRev)
            actionSuffix } := by
  let queryLeft : Word MachineCodeSymbol :=
    List.append
      (queryCells.map (fun _ => MachineCodeSymbol.tick)).reverse
      leftRev
  let afterQueryReadLeft : Word MachineCodeSymbol :=
    runtimeKeyCellSymbol queryRead ::
      MachineCodeSymbol.done :: queryLeft
  let rowEntryLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.transition :: afterQueryReadLeft
  let rowLeft : Word MachineCodeSymbol :=
    List.append
      (rowCells.map (fun _ => MachineCodeSymbol.tick)).reverse
      rowEntryLeft
  have hquery :=
    runtimeKeyComparatorMachine_computes_restore_query_unary
      outcome queryCells hqueryCells leftRev
      (MachineCodeSymbol.done ::
        runtimeKeyCellSymbol queryRead ::
        MachineCodeSymbol.transition ::
        List.append rowCells
          (MachineCodeSymbol.done ::
            runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hqueryDone :=
    runtimeKeyComparatorMachine_step_restore_query_done
      outcome queryLeft
      (runtimeKeyCellSymbol queryRead ::
        MachineCodeSymbol.transition ::
        List.append rowCells
          (MachineCodeSymbol.done ::
            runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hqueryRead :=
    runtimeKeyComparatorMachine_step_restore_query_read
      outcome queryRead (MachineCodeSymbol.done :: queryLeft)
      (MachineCodeSymbol.transition ::
        List.append rowCells
          (MachineCodeSymbol.done ::
            runtimeKeyCellSymbol rowRead :: actionSuffix))
  have htransition :=
    runtimeKeyComparatorMachine_step_restore_transition
      outcome afterQueryReadLeft
      (List.append rowCells
        (MachineCodeSymbol.done ::
          runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hrow :=
    runtimeKeyComparatorMachine_computes_restore_row_unary
      outcome rowCells hrowCells rowEntryLeft
      (MachineCodeSymbol.done ::
        runtimeKeyCellSymbol rowRead :: actionSuffix)
  have hrowDone :=
    runtimeKeyComparatorMachine_step_restore_row_done
      outcome rowLeft
      (runtimeKeyCellSymbol rowRead :: actionSuffix)
  have hrowRead :=
    runtimeKeyComparatorMachine_step_restore_row_read
      outcome rowRead (MachineCodeSymbol.done :: rowLeft)
      actionSuffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorBody, queryLeft]
          using hquery)
      (TuringMachine.Computes.step
        (by simpa [queryLeft] using hqueryDone)
        (TuringMachine.Computes.step
          (by
            simpa [queryLeft, afterQueryReadLeft]
              using hqueryRead)
          (TuringMachine.Computes.step
            (by
              simpa [afterQueryReadLeft, rowEntryLeft, queryLeft]
                using htransition)
            (TuringMachine.computes_trans
              (by
                simpa [rowEntryLeft, rowLeft,
                  afterQueryReadLeft, queryLeft]
                  using hrow)
              (TuringMachine.Computes.step
                (by
                  simpa [rowLeft, rowEntryLeft,
                    afterQueryReadLeft, queryLeft]
                    using hrowDone)
                (TuringMachine.Computes.step
                  (by
                    simpa [rowLeft,
                      runtimeKeyComparatorRestoredLeft,
                      rowEntryLeft, afterQueryReadLeft, queryLeft]
                      using hrowRead)
                  (TuringMachine.Computes.refl _)))))))

end Section53UniformInterpreterOneStep
end Computability
end FoC
