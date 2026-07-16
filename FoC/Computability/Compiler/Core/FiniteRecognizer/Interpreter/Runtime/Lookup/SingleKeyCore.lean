import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup.Shapes

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.UniformInterpreterOneStep
namespace RuntimeKeySingleKeyRepair

open FiniteRecognizer ExactFuel StrictProbe

/-- A rejected row with its leading `transition` marker changed to `done`. -/
def processedRow
    (row : TransitionDescription) : Word MachineCodeSymbol :=
  MachineCodeSymbol.done :: RuntimeKeySelectedExtractor.rowTail row

/-- Compact prefix of rows already rejected by the ordered scan. -/
def processedRows :
    List TransitionDescription -> Word MachineCodeSymbol
  | [] => []
  | row :: rest =>
      List.append (processedRow row) (processedRows rest)

theorem rowTail_no_header
    (row : TransitionDescription) :
    transitionListParserNoHeader
      (RuntimeKeySelectedExtractor.rowTail row) := by
  have hraw := transitionListParser_encodeTransition_noHeader row
  intro symbol hmem
  apply hraw symbol
  change symbol ∈
    MachineCodeSymbol.transition ::
      RuntimeKeySelectedExtractor.rowTail row
  exact List.Mem.tail MachineCodeSymbol.transition hmem
  done

theorem processedRow_no_transition
    (row : TransitionDescription) :
    RuntimeKeySelectedExtractor.NoTransition (processedRow row) := by
  intro symbol hmem
  rcases List.mem_cons.mp hmem with hdone | htail
  · subst symbol
    simp
  · exact RuntimeKeySelectedExtractor.rowTail_no_transition row
      symbol htail
  done

theorem processedRow_no_header
    (row : TransitionDescription) :
    transitionListParserNoHeader (processedRow row) := by
  intro symbol hmem
  rcases List.mem_cons.mp hmem with hdone | htail
  · subst symbol
    simp
  · exact rowTail_no_header row symbol htail
  done

theorem processedRows_no_transition
    (rows : List TransitionDescription) :
    RuntimeKeySelectedExtractor.NoTransition (processedRows rows) := by
  induction rows with
  | nil =>
      intro symbol hmem
      simp [processedRows] at hmem
  | cons row rest ih =>
      simpa [processedRows] using
        RuntimeKeySelectedExtractor.noTransition_append
          (processedRow_no_transition row) ih
  done

theorem processedRows_no_header
    (rows : List TransitionDescription) :
    transitionListParserNoHeader (processedRows rows) := by
  induction rows with
  | nil =>
      intro symbol hmem
      simp [processedRows] at hmem
  | cons row rest ih =>
      simpa [processedRows] using
        transitionListParserNoHeader_append
          (processedRow_no_header row) ih
  done
/-- The mutable tape data not already represented by the runtime lookup key. -/
def protectedTapeContextsAppend
    (tape : Tape Bool) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeCellListAppend tape.left
    (MachineDescription.encodeCellListAppend tape.right suffix)
inductive ComparatorState where
  | inner (state : RuntimeKeyComparatorState) : ComparatorState
  | seek : ComparatorState
  | restoreSeek
      (outcome : RuntimeKeyComparatorOutcome) : ComparatorState
  | selected : ComparatorState
  | missed : ComparatorState
  | rewindRejected : ComparatorState
  | exhaustedRewind : ComparatorState
  | exhausted : ComparatorState
deriving DecidableEq

namespace ComparatorState

def elems : List ComparatorState :=
  RuntimeKeyComparatorState.elems.map inner ++
    [seek, selected, missed, rewindRejected, exhaustedRewind,
      exhausted] ++
    RuntimeKeyComparatorState.outcomes.map restoreSeek

def finite : Foundation.FiniteType ComparatorState where
  elems := elems
  complete := by
    intro state
    cases state with
    | inner innerState =>
      exact List.mem_append_left _
          (List.mem_append_left _
            (List.mem_map.mpr
              ⟨innerState,
                RuntimeKeyComparatorState.finite.complete innerState,
                rfl⟩))
    | seek => simp [elems]
    | restoreSeek outcome =>
        apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨outcome,
            RuntimeKeyComparatorState.outcomes_complete outcome,
            rfl⟩
    | selected => simp [elems]
    | missed => simp [elems]
    | rewindRejected => simp [elems]
    | exhaustedRewind => simp [elems]
    | exhausted => simp [elems]

end ComparatorState

def embedComparatorState :
    RuntimeKeyComparatorState -> ComparatorState
  | RuntimeKeyComparatorState.matched => .selected
  | RuntimeKeyComparatorState.missed => .missed
  | state => .inner state

def comparatorMachine :
    TuringMachine MachineCodeSymbol ComparatorState where
  start := .inner RuntimeKeyComparatorState.needHeader
  halt := .selected
  transition := fun state cell =>
    match state with
    | .inner RuntimeKeyComparatorState.needTransition =>
        match cell with
        | some MachineCodeSymbol.transition =>
            some
              (some MachineCodeSymbol.transition, Direction.right,
                .inner RuntimeKeyComparatorState.scanRow)
        | some MachineCodeSymbol.header =>
            some
              (some MachineCodeSymbol.header, Direction.left,
                .exhaustedRewind)
        | some symbol =>
            some
              (some symbol, Direction.right,
                .inner RuntimeKeyComparatorState.needTransition)
        | none => none
    | .inner (RuntimeKeyComparatorState.finishNeedTransition read) =>
        match cell with
        | some MachineCodeSymbol.transition =>
            some
              (some MachineCodeSymbol.transition, Direction.right,
                .inner (RuntimeKeyComparatorState.finishScanRow read))
        | some MachineCodeSymbol.header =>
            some
              (some MachineCodeSymbol.header, Direction.left,
                .exhaustedRewind)
        | some symbol =>
            some
              (some symbol, Direction.right,
                .inner
                  (RuntimeKeyComparatorState.finishNeedTransition read))
        | none => none
    | .inner
        (RuntimeKeyComparatorState.restoreNeedTransition outcome) =>
        match cell with
        | some MachineCodeSymbol.transition =>
            some
              (some MachineCodeSymbol.transition, Direction.right,
                .inner (RuntimeKeyComparatorState.restoreRow outcome))
        | some MachineCodeSymbol.header =>
            some
              (some MachineCodeSymbol.header, Direction.right,
                .exhausted)
        | some symbol =>
            some
              (some symbol, Direction.right,
                .inner
                  (RuntimeKeyComparatorState.restoreNeedTransition
                    outcome))
        | none => none
    | .inner innerState =>
        match runtimeKeyComparatorMachine.transition innerState cell with
        | none => none
        | some (write, move, next) =>
            some (write, move, embedComparatorState next)
    | .seek =>
        match cell with
        | some MachineCodeSymbol.transition =>
            some
              (some MachineCodeSymbol.transition, Direction.right,
                .inner RuntimeKeyComparatorState.scanRow)
        | some MachineCodeSymbol.header =>
            some
              (some MachineCodeSymbol.header, Direction.right,
                .exhausted)
        | some symbol =>
            some (some symbol, Direction.right, .seek)
        | none => none
    | .restoreSeek outcome =>
        match cell with
        | some MachineCodeSymbol.transition =>
            some
              (some MachineCodeSymbol.transition, Direction.right,
                .inner (RuntimeKeyComparatorState.restoreRow outcome))
        | some MachineCodeSymbol.header =>
            some
              (some MachineCodeSymbol.header, Direction.right,
                .exhausted)
        | some symbol =>
            some (some symbol, Direction.right, .restoreSeek outcome)
        | none => none
    | .selected => none
    | .missed =>
        match cell with
        | some MachineCodeSymbol.transition =>
            some
              (some MachineCodeSymbol.done, Direction.left,
                .rewindRejected)
        | some symbol =>
            some (some symbol, Direction.left, .missed)
        | none => none
    | .rewindRejected =>
        match cell with
        | some MachineCodeSymbol.header =>
            some
              (some MachineCodeSymbol.header, Direction.right,
                .inner RuntimeKeyComparatorState.scanQuery)
        | some symbol =>
            some (some symbol, Direction.left, .rewindRejected)
        | none => none
    | .exhaustedRewind =>
        match cell with
        | some MachineCodeSymbol.header =>
            some
              (some MachineCodeSymbol.header, Direction.right,
                .inner
                  (RuntimeKeyComparatorState.restoreQuery
                    RuntimeKeyComparatorOutcome.isMiss))
        | some symbol =>
            some (some symbol, Direction.left, .exhaustedRewind)
        | none => none
    | .exhausted => none
  statesFinite := ComparatorState.finite

def liftComparatorConfig
    (config :
      TuringMachine.Configuration MachineCodeSymbol
        RuntimeKeyComparatorState) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := embedComparatorState config.state
    tape := config.tape }

theorem comparator_transition_lift
    (state next : RuntimeKeyComparatorState)
    (cell written : Option MachineCodeSymbol)
    (move : Direction)
    (haction :
      runtimeKeyComparatorMachine.transition state cell =
        some (written, move, next)) :
    comparatorMachine.transition (embedComparatorState state) cell =
      some (written, move, embedComparatorState next) := by
  cases state <;> cases cell <;>
    simp [runtimeKeyComparatorMachine, comparatorMachine,
      embedComparatorState] at haction ⊢
  all_goals
    split at *
  all_goals
    rcases haction with ⟨hwrite, hmove, hnext⟩ <;> simp_all
  done

theorem comparator_step_lift
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        RuntimeKeyComparatorState}
    (hstep :
      TuringMachine.Step runtimeKeyComparatorMachine source target) :
    TuringMachine.Step comparatorMachine
      (liftComparatorConfig source)
      (liftComparatorConfig target) := by
  cases hstep with
  | @mk write move nextState haction =>
      apply TuringMachine.Step.mk
      exact comparator_transition_lift source.state nextState
        (Tape.read source.tape) write move haction
  done

theorem comparator_computes_lift
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        RuntimeKeyComparatorState}
    (hrun :
      TuringMachine.Computes runtimeKeyComparatorMachine source target) :
    TuringMachine.Computes comparatorMachine
      (liftComparatorConfig source)
      (liftComparatorConfig target) := by
  induction hrun with
  | refl config =>
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (comparator_step_lift hstep) ih
  done

def comparatorSeekConfig
    (leftRev scanned suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := .inner RuntimeKeyComparatorState.needTransition
    tape := runtimeKeyComparatorTape leftRev
      (List.append scanned suffix) }

def comparatorRestoreSeekConfig
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev scanned suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := .inner
      (RuntimeKeyComparatorState.restoreNeedTransition outcome)
    tape := runtimeKeyComparatorTape leftRev
      (List.append scanned suffix) }

def comparatorFinishSeekConfig
    (read : Option Bool)
    (leftRev scanned suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := .inner
      (RuntimeKeyComparatorState.finishNeedTransition read)
    tape := runtimeKeyComparatorTape leftRev
      (List.append scanned suffix) }

theorem comparator_step_seek_symbol
    (leftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (htransition : current ≠ MachineCodeSymbol.transition)
    (hheader : current ≠ MachineCodeSymbol.header) :
    TuringMachine.Step comparatorMachine
      (comparatorSeekConfig leftRev [current] rest)
      (comparatorSeekConfig (current :: leftRev) [] rest) := by
  change TuringMachine.Step comparatorMachine
    { state := .inner RuntimeKeyComparatorState.needTransition
      tape := runtimeKeyComparatorTape leftRev (current :: rest) }
    { state := .inner RuntimeKeyComparatorState.needTransition
      tape := runtimeKeyComparatorTape (current :: leftRev) rest }
  rw [← runtimeKeyComparatorTape_move_right leftRev
    current current rest]
  apply TuringMachine.Step.mk
  cases current <;>
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read] at htransition hheader ⊢
  done

theorem comparator_step_restore_seek_symbol
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (htransition : current ≠ MachineCodeSymbol.transition)
    (hheader : current ≠ MachineCodeSymbol.header) :
    TuringMachine.Step comparatorMachine
      (comparatorRestoreSeekConfig outcome leftRev [current] rest)
      (comparatorRestoreSeekConfig outcome
        (current :: leftRev) [] rest) := by
  change TuringMachine.Step comparatorMachine
    { state := .inner
        (RuntimeKeyComparatorState.restoreNeedTransition outcome)
      tape := runtimeKeyComparatorTape leftRev (current :: rest) }
    { state := .inner
        (RuntimeKeyComparatorState.restoreNeedTransition outcome)
      tape := runtimeKeyComparatorTape (current :: leftRev) rest }
  rw [← runtimeKeyComparatorTape_move_right leftRev
    current current rest]
  apply TuringMachine.Step.mk
  cases current <;>
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read] at htransition hheader ⊢
  done

theorem comparator_step_finish_seek_symbol
    (read : Option Bool)
    (leftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (htransition : current ≠ MachineCodeSymbol.transition)
    (hheader : current ≠ MachineCodeSymbol.header) :
    TuringMachine.Step comparatorMachine
      (comparatorFinishSeekConfig read leftRev [current] rest)
      (comparatorFinishSeekConfig read
        (current :: leftRev) [] rest) := by
  change TuringMachine.Step comparatorMachine
    { state := .inner
        (RuntimeKeyComparatorState.finishNeedTransition read)
      tape := runtimeKeyComparatorTape leftRev (current :: rest) }
    { state := .inner
        (RuntimeKeyComparatorState.finishNeedTransition read)
      tape := runtimeKeyComparatorTape (current :: leftRev) rest }
  rw [← runtimeKeyComparatorTape_move_right leftRev
    current current rest]
  apply TuringMachine.Step.mk
  cases current <;>
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read] at htransition hheader ⊢
  done

theorem comparator_computes_seek_prefix
    (leftRev scanned suffix : Word MachineCodeSymbol)
    (htransition : RuntimeKeySelectedExtractor.NoTransition scanned)
    (hheader : transitionListParserNoHeader scanned) :
    TuringMachine.Computes comparatorMachine
      (comparatorSeekConfig leftRev scanned suffix)
      (comparatorSeekConfig
        (List.append scanned.reverse leftRev) [] suffix) := by
  induction scanned generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons current rest ih =>
      have hcurrentTransition :
          current ≠ MachineCodeSymbol.transition :=
        htransition current (by simp)
      have hcurrentHeader : current ≠ MachineCodeSymbol.header :=
        hheader current (by simp)
      have hrestTransition :
          RuntimeKeySelectedExtractor.NoTransition rest := by
        intro symbol hmem
        exact htransition symbol (by simp [hmem])
      have hrestHeader : transitionListParserNoHeader rest := by
        intro symbol hmem
        exact hheader symbol (by simp [hmem])
      exact TuringMachine.Computes.step
        (by
          simpa [comparatorSeekConfig, List.append_assoc] using
            comparator_step_seek_symbol leftRev current
              (List.append rest suffix)
              hcurrentTransition hcurrentHeader)
        (by
          simpa [comparatorSeekConfig, List.reverse_cons,
            List.append_assoc] using
              ih (current :: leftRev)
                hrestTransition hrestHeader)
  done

theorem comparator_computes_restore_seek_prefix
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev scanned suffix : Word MachineCodeSymbol)
    (htransition : RuntimeKeySelectedExtractor.NoTransition scanned)
    (hheader : transitionListParserNoHeader scanned) :
    TuringMachine.Computes comparatorMachine
      (comparatorRestoreSeekConfig outcome leftRev scanned suffix)
      (comparatorRestoreSeekConfig outcome
        (List.append scanned.reverse leftRev) [] suffix) := by
  induction scanned generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons current rest ih =>
      have hcurrentTransition :
          current ≠ MachineCodeSymbol.transition :=
        htransition current (by simp)
      have hcurrentHeader : current ≠ MachineCodeSymbol.header :=
        hheader current (by simp)
      have hrestTransition :
          RuntimeKeySelectedExtractor.NoTransition rest := by
        intro symbol hmem
        exact htransition symbol (by simp [hmem])
      have hrestHeader : transitionListParserNoHeader rest := by
        intro symbol hmem
        exact hheader symbol (by simp [hmem])
      exact TuringMachine.Computes.step
        (by
          simpa [comparatorRestoreSeekConfig,
            List.append_assoc] using
              comparator_step_restore_seek_symbol outcome leftRev
                current (List.append rest suffix)
                hcurrentTransition hcurrentHeader)
        (by
          simpa [comparatorRestoreSeekConfig, List.reverse_cons,
            List.append_assoc] using
              ih (current :: leftRev)
                hrestTransition hrestHeader)
  done

theorem comparator_computes_finish_seek_prefix
    (read : Option Bool)
    (leftRev scanned suffix : Word MachineCodeSymbol)
    (htransition : RuntimeKeySelectedExtractor.NoTransition scanned)
    (hheader : transitionListParserNoHeader scanned) :
    TuringMachine.Computes comparatorMachine
      (comparatorFinishSeekConfig read leftRev scanned suffix)
      (comparatorFinishSeekConfig read
        (List.append scanned.reverse leftRev) [] suffix) := by
  induction scanned generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons current rest ih =>
      have hcurrentTransition :
          current ≠ MachineCodeSymbol.transition :=
        htransition current (by simp)
      have hcurrentHeader : current ≠ MachineCodeSymbol.header :=
        hheader current (by simp)
      have hrestTransition :
          RuntimeKeySelectedExtractor.NoTransition rest := by
        intro symbol hmem
        exact htransition symbol (by simp [hmem])
      have hrestHeader : transitionListParserNoHeader rest := by
        intro symbol hmem
        exact hheader symbol (by simp [hmem])
      exact TuringMachine.Computes.step
        (by
          simpa [comparatorFinishSeekConfig,
            List.append_assoc] using
              comparator_step_finish_seek_symbol read leftRev
                current (List.append rest suffix)
                hcurrentTransition hcurrentHeader)
        (by
          simpa [comparatorFinishSeekConfig, List.reverse_cons,
            List.append_assoc] using
              ih (current :: leftRev)
                hrestTransition hrestHeader)
  done

theorem comparator_step_select_transition
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      (comparatorSeekConfig leftRev []
        (MachineCodeSymbol.transition :: suffix))
      { state := .inner RuntimeKeyComparatorState.scanRow
        tape := runtimeKeyComparatorTape
          (MachineCodeSymbol.transition :: leftRev) suffix } := by
  change TuringMachine.Step comparatorMachine
    { state := .inner RuntimeKeyComparatorState.needTransition
      tape := runtimeKeyComparatorTape leftRev
        (MachineCodeSymbol.transition :: suffix) }
    { state := .inner RuntimeKeyComparatorState.scanRow
      tape := runtimeKeyComparatorTape
        (MachineCodeSymbol.transition :: leftRev) suffix }
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.transition MachineCodeSymbol.transition suffix]
  exact TuringMachine.Step.mk (by
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read])
  done

theorem comparator_step_restore_transition
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      (comparatorRestoreSeekConfig outcome leftRev []
        (MachineCodeSymbol.transition :: suffix))
      { state := .inner
          (RuntimeKeyComparatorState.restoreRow outcome)
        tape := runtimeKeyComparatorTape
          (MachineCodeSymbol.transition :: leftRev) suffix } := by
  change TuringMachine.Step comparatorMachine
    { state := .inner
        (RuntimeKeyComparatorState.restoreNeedTransition outcome)
      tape := runtimeKeyComparatorTape leftRev
        (MachineCodeSymbol.transition :: suffix) }
    { state := .inner
        (RuntimeKeyComparatorState.restoreRow outcome)
      tape := runtimeKeyComparatorTape
        (MachineCodeSymbol.transition :: leftRev) suffix }
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.transition MachineCodeSymbol.transition suffix]
  exact TuringMachine.Step.mk (by
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read])
  done

theorem comparator_step_finish_transition
    (read : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      (comparatorFinishSeekConfig read leftRev []
        (MachineCodeSymbol.transition :: suffix))
      { state := .inner
          (RuntimeKeyComparatorState.finishScanRow read)
        tape := runtimeKeyComparatorTape
          (MachineCodeSymbol.transition :: leftRev) suffix } := by
  change TuringMachine.Step comparatorMachine
    { state := .inner
        (RuntimeKeyComparatorState.finishNeedTransition read)
      tape := runtimeKeyComparatorTape leftRev
        (MachineCodeSymbol.transition :: suffix) }
    { state := .inner
        (RuntimeKeyComparatorState.finishScanRow read)
      tape := runtimeKeyComparatorTape
        (MachineCodeSymbol.transition :: leftRev) suffix }
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.transition MachineCodeSymbol.transition suffix]
  exact TuringMachine.Step.mk (by
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read])
  done

def separatedComparatorBody
    (queryCells : Word MachineCodeSymbol)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (rowCells : Word MachineCodeSymbol)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append queryCells
    (MachineCodeSymbol.done ::
      runtimeKeyCellSymbol queryRead ::
      List.append processed
        (MachineCodeSymbol.transition ::
          List.append rowCells
            (MachineCodeSymbol.done ::
              runtimeKeyCellSymbol rowRead :: actionSuffix)))

def separatedComparatorRestoredLeft
    (queryCells : Word MachineCodeSymbol)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (rowCells : Word MachineCodeSymbol)
    (rowRead : Option Bool)
    (leftRev : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  runtimeKeyCellSymbol rowRead ::
    MachineCodeSymbol.done ::
    List.append
      (rowCells.map (fun _ => MachineCodeSymbol.tick)).reverse
      (MachineCodeSymbol.transition ::
        List.append processed.reverse
          (runtimeKeyCellSymbol queryRead ::
            MachineCodeSymbol.done ::
            List.append
              (queryCells.map (fun _ => MachineCodeSymbol.tick)).reverse
              leftRev))

def separatedComparatorComparisonPrefix
    (queryCells : Word MachineCodeSymbol)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (rowCells : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append rowCells.reverse
    (MachineCodeSymbol.transition ::
      List.append processed.reverse
        (runtimeKeyCellSymbol queryRead ::
          MachineCodeSymbol.done :: queryCells.reverse))

theorem separatedComparatorComparisonPrefix_no_header
    (queryCells : Word MachineCodeSymbol)
    (hqueryCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessed : transitionListParserNoHeader processed)
    (rowCells : Word MachineCodeSymbol)
    (hrowCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick) :
    transitionListParserNoHeader
      (separatedComparatorComparisonPrefix queryCells queryRead
        processed rowCells) := by
  intro symbol hmem hsymbol
  subst symbol
  simp only [separatedComparatorComparisonPrefix] at hmem
  rcases List.mem_append.mp hmem with hrow | hrest
  · have hrow' : List.Mem MachineCodeSymbol.header rowCells := by
      change MachineCodeSymbol.header ∈
        (show List MachineCodeSymbol from rowCells.reverse) at hrow
      have hrow' := List.mem_reverse.mp hrow
      change List.Mem MachineCodeSymbol.header rowCells at hrow'
      exact hrow'
    rcases hrowCells MachineCodeSymbol.header hrow' with hblank | htick
    · cases hblank
    · cases htick
  · rcases List.mem_cons.mp hrest with htransition | hrest
    · cases htransition
    · rcases List.mem_append.mp hrest with hprocessed' | hrest
      · apply hprocessed MachineCodeSymbol.header
          (List.mem_reverse.mp hprocessed')
        rfl
      · rcases List.mem_cons.mp hrest with hread | hrest
        · cases queryRead with
          | none => cases hread
          | some bit => cases bit <;> cases hread
        · rcases List.mem_cons.mp hrest with hdone | hquery
          · cases hdone
          · have hquery' : List.Mem MachineCodeSymbol.header queryCells := by
              change MachineCodeSymbol.header ∈
                (show List MachineCodeSymbol from queryCells.reverse) at hquery
              have hquery' := List.mem_reverse.mp hquery
              change List.Mem MachineCodeSymbol.header queryCells at hquery'
              exact hquery'
            rcases hqueryCells MachineCodeSymbol.header hquery' with
              hblank | htick
            · cases hblank
            · cases htick
  done

theorem comparator_computes_restore_outcome_separated
    (outcome : RuntimeKeyComparatorOutcome)
    (queryCells : Word MachineCodeSymbol)
    (hqueryCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowCells : Word MachineCodeSymbol)
    (hrowCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (rowRead : Option Bool)
    (leftRev actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner (RuntimeKeyComparatorState.restoreQuery outcome)
        tape := runtimeKeyComparatorTape leftRev
          (separatedComparatorBody queryCells queryRead processed
            rowCells rowRead actionSuffix) }
      { state := embedComparatorState
          (runtimeKeyComparatorOutcomeState outcome)
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft queryCells queryRead processed
            rowCells rowRead leftRev)
          actionSuffix } := by
  let queryLeft : Word MachineCodeSymbol :=
    List.append
      (queryCells.map (fun _ => MachineCodeSymbol.tick)).reverse
      leftRev
  let afterQueryReadLeft : Word MachineCodeSymbol :=
    runtimeKeyCellSymbol queryRead ::
      MachineCodeSymbol.done :: queryLeft
  let rowEntryLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.transition ::
      List.append processed.reverse afterQueryReadLeft
  let rowLeft : Word MachineCodeSymbol :=
    List.append
      (rowCells.map (fun _ => MachineCodeSymbol.tick)).reverse
      rowEntryLeft
  have hquery := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_restore_query_unary
      outcome queryCells hqueryCells leftRev
      (MachineCodeSymbol.done ::
        runtimeKeyCellSymbol queryRead ::
        List.append processed
          (MachineCodeSymbol.transition ::
            List.append rowCells
              (MachineCodeSymbol.done ::
                runtimeKeyCellSymbol rowRead :: actionSuffix))))
  have hqueryDone := comparator_step_lift
    (runtimeKeyComparatorMachine_step_restore_query_done
      outcome queryLeft
      (runtimeKeyCellSymbol queryRead ::
        List.append processed
          (MachineCodeSymbol.transition ::
            List.append rowCells
              (MachineCodeSymbol.done ::
                runtimeKeyCellSymbol rowRead :: actionSuffix))))
  have hqueryRead := comparator_step_lift
    (runtimeKeyComparatorMachine_step_restore_query_read
      outcome queryRead (MachineCodeSymbol.done :: queryLeft)
      (List.append processed
        (MachineCodeSymbol.transition ::
          List.append rowCells
            (MachineCodeSymbol.done ::
              runtimeKeyCellSymbol rowRead :: actionSuffix))))
  have hseek := comparator_computes_restore_seek_prefix outcome
    afterQueryReadLeft processed
    (MachineCodeSymbol.transition ::
      List.append rowCells
        (MachineCodeSymbol.done ::
          runtimeKeyCellSymbol rowRead :: actionSuffix))
    hprocessedTransition hprocessedHeader
  have htransition := comparator_step_restore_transition outcome
    (List.append processed.reverse afterQueryReadLeft)
    (List.append rowCells
      (MachineCodeSymbol.done ::
        runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hrow := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_restore_row_unary
      outcome rowCells hrowCells rowEntryLeft
      (MachineCodeSymbol.done ::
        runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hrowDone := comparator_step_lift
    (runtimeKeyComparatorMachine_step_restore_row_done
      outcome rowLeft
      (runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hrowRead := comparator_step_lift
    (runtimeKeyComparatorMachine_step_restore_row_read
      outcome rowRead (MachineCodeSymbol.done :: rowLeft)
      actionSuffix)
  exact
    TuringMachine.computes_trans
      (by
        simpa [separatedComparatorBody, queryLeft,
          liftComparatorConfig, embedComparatorState] using hquery)
      (TuringMachine.Computes.step
        (by
          simpa [queryLeft, liftComparatorConfig,
            embedComparatorState] using hqueryDone)
        (TuringMachine.Computes.step
          (by
            simpa [queryLeft, afterQueryReadLeft,
              liftComparatorConfig, embedComparatorState] using hqueryRead)
          (TuringMachine.computes_trans
            (by
              simpa [comparatorRestoreSeekConfig,
                afterQueryReadLeft, queryLeft,
                embedComparatorState, List.append_assoc] using hseek)
            (TuringMachine.Computes.step
              (by
                simpa [comparatorRestoreSeekConfig,
                  rowEntryLeft, afterQueryReadLeft, queryLeft,
                  List.append_assoc] using htransition)
              (TuringMachine.computes_trans
                (by
                  simpa [rowEntryLeft, afterQueryReadLeft,
                    queryLeft, liftComparatorConfig,
                    embedComparatorState,
                    List.append_assoc] using hrow)
                (TuringMachine.Computes.step
                  (by
                    simpa [rowLeft, rowEntryLeft,
                      afterQueryReadLeft, queryLeft,
                      liftComparatorConfig, embedComparatorState,
                      List.append_assoc]
                      using hrowDone)
                  (TuringMachine.Computes.step
                    (by
                      simpa [rowLeft, rowEntryLeft,
                        afterQueryReadLeft, queryLeft,
                        separatedComparatorRestoredLeft,
                        liftComparatorConfig, embedComparatorState,
                        List.append_assoc]
                        using hrowRead)
                    (TuringMachine.Computes.refl _))))))))
  done

theorem comparator_computes_paired_tick_cycle_separated
    (marked queryRemaining : Nat)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowRemaining : Nat)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorBody
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              (MachineCodeSymbol.tick ::
                List.replicate queryRemaining MachineCodeSymbol.tick))
            queryRead processed
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              (MachineCodeSymbol.tick ::
                List.replicate rowRemaining MachineCodeSymbol.tick))
            rowRead actionSuffix) }
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorBody
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              (MachineCodeSymbol.blank ::
                List.replicate queryRemaining MachineCodeSymbol.tick))
            queryRead processed
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              (MachineCodeSymbol.blank ::
                List.replicate rowRemaining MachineCodeSymbol.tick))
            rowRead actionSuffix) } := by
  let queryMarks : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let queryTail : Word MachineCodeSymbol :=
    List.replicate queryRemaining MachineCodeSymbol.tick
  let rowMarks : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let rowTail : Word MachineCodeSymbol :=
    List.replicate rowRemaining MachineCodeSymbol.tick
  let queryMarkedCells : Word MachineCodeSymbol :=
    List.append queryMarks
      (MachineCodeSymbol.blank :: queryTail)
  let afterRow : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      runtimeKeyCellSymbol rowRead :: actionSuffix
  let rowSource : Word MachineCodeSymbol :=
    List.append rowMarks
      (MachineCodeSymbol.tick :: List.append rowTail afterRow)
  let afterQuery : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      runtimeKeyCellSymbol queryRead ::
      List.append processed
        (MachineCodeSymbol.transition :: rowSource)
  let queryMarkedBody : Word MachineCodeSymbol :=
    MachineCodeSymbol.blank :: queryMarks.reverse
  let queryMarkedLeft : Word MachineCodeSymbol :=
    List.append queryMarkedBody [MachineCodeSymbol.header]
  let queryTailLeft : Word MachineCodeSymbol :=
    List.append queryTail.reverse queryMarkedLeft
  let queryDoneLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.done :: queryTailLeft
  let queryReadLeft : Word MachineCodeSymbol :=
    runtimeKeyCellSymbol queryRead :: queryDoneLeft
  let processedLeft : Word MachineCodeSymbol :=
    List.append processed.reverse queryReadLeft
  let transitionLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.transition :: processedLeft
  let rowPrefix : Word MachineCodeSymbol :=
    separatedComparatorComparisonPrefix
      queryMarkedCells queryRead processed rowMarks
  have hqueryMarkedCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryMarkedCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick := by
    intro symbol hmem
    simp only [queryMarkedCells] at hmem
    rcases List.mem_append.mp hmem with hmarks | htail
    · left
      exact (List.mem_replicate.mp hmarks).2
    · rcases List.mem_cons.mp htail with hblank | htick
      · left
        exact hblank
      · right
        exact (List.mem_replicate.mp htick).2
  have hrowMarks :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowMarks ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick := by
    intro symbol hmem
    left
    exact (List.mem_replicate.mp hmem).2
  have hrowPrefixNoHeader : transitionListParserNoHeader rowPrefix :=
    separatedComparatorComparisonPrefix_no_header
      queryMarkedCells hqueryMarkedCells queryRead
      processed hprocessedHeader rowMarks hrowMarks
  have hrowPrefixNonempty : rowPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [rowPrefix, separatedComparatorComparisonPrefix] at hlen
  have hqueryMarks := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_scan_query_blanks
      marked [MachineCodeSymbol.header]
      (MachineCodeSymbol.tick :: List.append queryTail afterQuery))
  have hqueryMark := comparator_step_lift
    (runtimeKeyComparatorMachine_step_mark_query_tick
      (List.append queryMarks.reverse [MachineCodeSymbol.header])
      (List.append queryTail afterQuery))
  have hqueryTail := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_seek_query_ticks
      queryRemaining queryMarkedLeft afterQuery)
  have hqueryDone := comparator_step_lift
    (runtimeKeyComparatorMachine_step_seek_query_done
      queryTailLeft
      (runtimeKeyCellSymbol queryRead ::
        List.append processed
          (MachineCodeSymbol.transition :: rowSource)))
  have hqueryRead := comparator_step_lift
    (runtimeKeyComparatorMachine_step_skip_query_read
      queryRead queryDoneLeft
      (List.append processed
        (MachineCodeSymbol.transition :: rowSource)))
  have hseek := comparator_computes_seek_prefix
    queryReadLeft processed
    (MachineCodeSymbol.transition :: rowSource)
    hprocessedTransition hprocessedHeader
  have htransition := comparator_step_select_transition
    processedLeft rowSource
  have hrowScan := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_scan_row_blanks
      marked transitionLeft
      (MachineCodeSymbol.tick :: List.append rowTail afterRow))
  have hrowMarkRewind := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_mark_row_tick_and_rewind
      rowPrefix hrowPrefixNoHeader hrowPrefixNonempty
      (List.append rowTail afterRow))
  exact
    TuringMachine.computes_trans
      (by
        simpa [separatedComparatorBody, queryMarks, queryTail,
          rowMarks, rowTail, afterRow, rowSource, afterQuery,
          liftComparatorConfig, embedComparatorState,
          List.append_assoc] using hqueryMarks)
      (TuringMachine.Computes.step
        (by
          simpa [queryMarks, queryTail, rowMarks, rowTail,
            afterRow, rowSource, afterQuery, queryMarkedBody,
            queryMarkedLeft, liftComparatorConfig,
            embedComparatorState, List.append_assoc]
            using hqueryMark)
        (TuringMachine.computes_trans
          (by
            simpa [queryMarks, queryTail, rowMarks, rowTail,
              afterRow, rowSource, afterQuery, queryMarkedBody,
              queryMarkedLeft, queryTailLeft,
              liftComparatorConfig, embedComparatorState,
              List.append_assoc] using hqueryTail)
          (TuringMachine.Computes.step
            (by
              simpa [queryMarks, queryTail, rowMarks, rowTail,
                afterRow, rowSource, queryMarkedBody,
                queryMarkedLeft, queryTailLeft, queryDoneLeft,
                liftComparatorConfig, embedComparatorState,
                List.append_assoc] using hqueryDone)
            (TuringMachine.Computes.step
              (by
                simpa [queryMarks, queryTail, rowMarks, rowTail,
                  afterRow, rowSource, queryMarkedBody,
                  queryMarkedLeft, queryTailLeft, queryDoneLeft,
                  queryReadLeft, liftComparatorConfig,
                  embedComparatorState, List.append_assoc]
                  using hqueryRead)
              (TuringMachine.computes_trans
                (by
                  simpa [comparatorSeekConfig, queryReadLeft,
                    queryDoneLeft, queryTailLeft, queryMarkedLeft,
                    queryMarkedBody, queryMarks, queryTail,
                    rowSource, rowMarks, rowTail, afterRow,
                    List.append_assoc] using hseek)
                (TuringMachine.Computes.step
                  (by
                    simpa [comparatorSeekConfig, processedLeft,
                      queryReadLeft, queryDoneLeft, queryTailLeft,
                      queryMarkedLeft, queryMarkedBody,
                      queryMarks, queryTail, rowSource, rowMarks,
                      rowTail, afterRow, List.append_assoc]
                      using htransition)
                  (TuringMachine.computes_trans
                    (by
                      simpa [transitionLeft, processedLeft,
                        queryReadLeft, queryDoneLeft, queryTailLeft,
                        queryMarkedLeft, queryMarkedBody,
                        queryMarks, queryTail, rowSource, rowMarks,
                        rowTail, afterRow, liftComparatorConfig,
                        embedComparatorState, List.append_assoc]
                        using hrowScan)
                    (by
                      simpa [separatedComparatorBody, rowPrefix,
                        separatedComparatorComparisonPrefix,
                        queryMarkedCells, transitionLeft,
                        processedLeft, queryReadLeft, queryDoneLeft,
                        queryTailLeft, queryMarkedLeft,
                        queryMarkedBody, queryMarks, queryTail,
                        rowMarks, rowTail, afterRow, rowSource,
                        afterQuery, liftComparatorConfig,
                        embedComparatorState,
                        List.reverse_append, List.reverse_cons,
                        List.reverse_reverse, List.reverse_replicate,
                        List.append_assoc]
                        using hrowMarkRewind))))))))
  done

def separatedComparatorPairedBody
    (marked remaining : Nat)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  separatedComparatorBody
    (List.append
      (List.replicate marked MachineCodeSymbol.blank)
      (List.replicate remaining MachineCodeSymbol.tick))
    queryRead processed
    (List.append
      (List.replicate marked MachineCodeSymbol.blank)
      (List.replicate remaining MachineCodeSymbol.tick))
    rowRead actionSuffix

def separatedComparatorComparedBody
    (marked queryRemaining rowRemaining : Nat)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  separatedComparatorBody
    (List.append
      (List.replicate marked MachineCodeSymbol.blank)
      (List.replicate queryRemaining MachineCodeSymbol.tick))
    queryRead processed
    (List.append
      (List.replicate marked MachineCodeSymbol.blank)
      (List.replicate rowRemaining MachineCodeSymbol.tick))
    rowRead actionSuffix

theorem comparator_computes_paired_body_cycle_separated
    (marked remaining : Nat)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorPairedBody marked (remaining + 1)
            queryRead processed rowRead actionSuffix) }
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorPairedBody (marked + 1) remaining
            queryRead processed rowRead actionSuffix) } := by
  have hrun := comparator_computes_paired_tick_cycle_separated
    marked remaining queryRead processed
    hprocessedTransition hprocessedHeader remaining rowRead actionSuffix
  simpa [separatedComparatorPairedBody,
    replicate_succ_eq_append_singleton,
    cons_replicate_eq_append_singleton,
    cons_replicate_append_eq_replicate_append_cons,
    List.append_assoc] using hrun
  done

theorem comparator_computes_equal_unary_prefixes_separated
    (marked remaining : Nat)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorPairedBody marked remaining
            queryRead processed rowRead actionSuffix) }
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorPairedBody (marked + remaining) 0
            queryRead processed rowRead actionSuffix) } := by
  induction remaining generalizing marked with
  | zero =>
      simpa using TuringMachine.Computes.refl
        ({ state := .inner RuntimeKeyComparatorState.scanQuery
           tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
             (separatedComparatorPairedBody marked 0
               queryRead processed rowRead actionSuffix) } :
          TuringMachine.Configuration MachineCodeSymbol ComparatorState)
  | succ remaining ih =>
      have hcycle := comparator_computes_paired_body_cycle_separated
        marked remaining queryRead processed
        hprocessedTransition hprocessedHeader rowRead actionSuffix
      have hrest := ih (marked + 1)
      exact TuringMachine.computes_trans hcycle
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hrest)
  done

theorem comparator_computes_compared_body_cycle_separated
    (marked queryRemaining rowRemaining : Nat)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorComparedBody marked
            (queryRemaining + 1) (rowRemaining + 1)
            queryRead processed rowRead actionSuffix) }
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorComparedBody (marked + 1)
            queryRemaining rowRemaining queryRead processed
            rowRead actionSuffix) } := by
  have hrun := comparator_computes_paired_tick_cycle_separated
    marked queryRemaining queryRead processed
    hprocessedTransition hprocessedHeader rowRemaining rowRead actionSuffix
  simpa [separatedComparatorComparedBody,
    replicate_succ_eq_append_singleton,
    cons_replicate_eq_append_singleton,
    cons_replicate_append_eq_replicate_append_cons,
    List.append_assoc] using hrun
  done

theorem comparator_computes_common_unary_prefix_separated
    (marked common queryExtra rowExtra : Nat)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorComparedBody marked
            (queryExtra + common) (rowExtra + common)
            queryRead processed rowRead actionSuffix) }
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorComparedBody (marked + common)
            queryExtra rowExtra queryRead processed
            rowRead actionSuffix) } := by
  induction common generalizing marked with
  | zero =>
      simpa using TuringMachine.Computes.refl
        ({ state := .inner RuntimeKeyComparatorState.scanQuery
           tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
             (separatedComparatorComparedBody marked
               queryExtra rowExtra queryRead processed
               rowRead actionSuffix) } :
          TuringMachine.Configuration MachineCodeSymbol ComparatorState)
  | succ common ih =>
      have hcycle := comparator_computes_compared_body_cycle_separated
        marked (queryExtra + common) (rowExtra + common)
        queryRead processed hprocessedTransition hprocessedHeader
        rowRead actionSuffix
      have hrest := ih (marked + 1)
      exact TuringMachine.computes_trans
        (by simpa [Nat.add_assoc] using hcycle)
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hrest)
  done

theorem comparator_computes_rewind_restore_separated
    (outcome : RuntimeKeyComparatorOutcome)
    (queryCells : Word MachineCodeSymbol)
    (hqueryCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowCells : Word MachineCodeSymbol)
    (hrowCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner (RuntimeKeyComparatorState.rewindOutcome outcome)
        tape := runtimeKeyComparatorTape
          (List.append
            (separatedComparatorComparisonPrefix queryCells queryRead
              processed rowCells)
            [MachineCodeSymbol.header])
          (MachineCodeSymbol.done ::
            runtimeKeyCellSymbol rowRead :: actionSuffix) }
      { state := embedComparatorState
          (runtimeKeyComparatorOutcomeState outcome)
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft queryCells queryRead processed
            rowCells rowRead [MachineCodeSymbol.header])
          actionSuffix } := by
  have hprefix := separatedComparatorComparisonPrefix_no_header
    queryCells hqueryCells queryRead processed hprocessedHeader
    rowCells hrowCells
  have hrewind := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_rewind_outcome_to_header
      outcome
      (separatedComparatorComparisonPrefix queryCells queryRead
        processed rowCells)
      hprefix MachineCodeSymbol.done (by simp)
      (runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hrestore := comparator_computes_restore_outcome_separated
    outcome queryCells hqueryCells queryRead processed
    hprocessedTransition hprocessedHeader rowCells hrowCells
    rowRead [MachineCodeSymbol.header] actionSuffix
  exact TuringMachine.computes_trans
    (by
      simpa [liftComparatorConfig, embedComparatorState] using hrewind)
    (by
      simpa [separatedComparatorComparisonPrefix,
        separatedComparatorBody,
        List.reverse_append, List.reverse_cons,
        List.reverse_reverse, List.append_assoc] using hrestore)
  done

theorem comparator_computes_equal_state_finish_separated
    (marked : Nat)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorComparedBody marked 0 0
            queryRead processed rowRead actionSuffix) }
      { state := embedComparatorState
          (runtimeKeyComparatorOutcomeState
            (runtimeKeyComparatorReadOutcome queryRead rowRead))
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft
            (List.replicate marked MachineCodeSymbol.blank)
            queryRead processed
            (List.replicate marked MachineCodeSymbol.blank)
            rowRead [MachineCodeSymbol.header])
          actionSuffix } := by
  let queryCells : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let rowCells : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let afterRow : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      runtimeKeyCellSymbol rowRead :: actionSuffix
  let afterQuery : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      runtimeKeyCellSymbol queryRead ::
      List.append processed
        (MachineCodeSymbol.transition ::
          List.append rowCells afterRow)
  let queryLeft : Word MachineCodeSymbol :=
    List.append queryCells.reverse [MachineCodeSymbol.header]
  let queryDoneLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.done :: queryLeft
  let queryReadLeft : Word MachineCodeSymbol :=
    runtimeKeyCellSymbol queryRead :: queryDoneLeft
  let processedLeft : Word MachineCodeSymbol :=
    List.append processed.reverse queryReadLeft
  let transitionLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.transition :: processedLeft
  let rowLeft : Word MachineCodeSymbol :=
    List.append rowCells.reverse transitionLeft
  let comparisonPrefix : Word MachineCodeSymbol :=
    separatedComparatorComparisonPrefix queryCells queryRead
      processed rowCells
  have hqueryCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick := by
    intro symbol hmem
    left
    exact (List.mem_replicate.mp hmem).2
  have hrowCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick := by
    intro symbol hmem
    left
    exact (List.mem_replicate.mp hmem).2
  have hquery := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_scan_query_blanks
      marked [MachineCodeSymbol.header] afterQuery)
  have hqueryDone := comparator_step_lift
    (runtimeKeyComparatorMachine_step_scan_query_done
      queryLeft
      (runtimeKeyCellSymbol queryRead ::
        List.append processed
          (MachineCodeSymbol.transition ::
            List.append rowCells afterRow)))
  have hqueryRead := comparator_step_lift
    (runtimeKeyComparatorMachine_step_remember_query_read
      queryRead queryDoneLeft
      (List.append processed
        (MachineCodeSymbol.transition ::
          List.append rowCells afterRow)))
  have hseek := comparator_computes_finish_seek_prefix queryRead
    queryReadLeft processed
    (MachineCodeSymbol.transition :: List.append rowCells afterRow)
    hprocessedTransition hprocessedHeader
  have htransition := comparator_step_finish_transition queryRead
    processedLeft (List.append rowCells afterRow)
  have hrow := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_finish_row_blanks
      queryRead marked transitionLeft afterRow)
  have hrowDone := comparator_step_lift
    (runtimeKeyComparatorMachine_step_finish_row_done
      queryRead rowLeft
      (runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hcompare := comparator_step_lift
    (runtimeKeyComparatorMachine_step_compare_read
      queryRead rowRead MachineCodeSymbol.done
      (List.append comparisonPrefix [MachineCodeSymbol.header])
      actionSuffix)
  have hrestore := comparator_computes_rewind_restore_separated
    (runtimeKeyComparatorReadOutcome queryRead rowRead)
    queryCells hqueryCells queryRead processed
    hprocessedTransition hprocessedHeader rowCells hrowCells
    rowRead actionSuffix
  exact TuringMachine.computes_trans
    (by
      simpa [separatedComparatorComparedBody,
        separatedComparatorBody, queryCells, rowCells,
        afterRow, afterQuery, liftComparatorConfig,
        embedComparatorState, List.append_assoc] using hquery)
    (TuringMachine.Computes.step
      (by
        simpa [queryCells, queryLeft, rowCells, afterRow,
          liftComparatorConfig, embedComparatorState,
          List.append_assoc] using hqueryDone)
      (TuringMachine.Computes.step
        (by
          simpa [queryCells, queryLeft, queryDoneLeft,
            queryReadLeft, rowCells, afterRow,
            liftComparatorConfig, embedComparatorState,
            List.append_assoc] using hqueryRead)
        (TuringMachine.computes_trans
          (by
            simpa [comparatorFinishSeekConfig, queryReadLeft,
              queryDoneLeft, queryLeft, queryCells, rowCells,
              afterRow, List.append_assoc]
              using hseek)
          (TuringMachine.Computes.step
            (by
              simpa [comparatorFinishSeekConfig, processedLeft,

                queryReadLeft, queryDoneLeft, queryLeft,
                queryCells, rowCells, afterRow,
                List.append_assoc] using htransition)
            (TuringMachine.computes_trans
              (by
                simpa [transitionLeft, processedLeft,
                  queryReadLeft, queryDoneLeft, queryLeft,
                  queryCells, rowCells, afterRow, liftComparatorConfig,
                  embedComparatorState, List.append_assoc]
                  using hrow)
              (TuringMachine.Computes.step
                (by
                  simpa [rowLeft, transitionLeft, processedLeft,
                    queryReadLeft, queryDoneLeft, queryLeft,
                    comparisonPrefix,
                    separatedComparatorComparisonPrefix,
                    queryCells, rowCells, liftComparatorConfig,
                    embedComparatorState, List.append_assoc]
                    using hrowDone)
                (TuringMachine.Computes.step
                  (by
                    simpa [comparisonPrefix, liftComparatorConfig,
                      separatedComparatorComparisonPrefix,
                      rowLeft, transitionLeft, processedLeft,
                      queryReadLeft, queryDoneLeft, queryLeft,
                      queryCells, rowCells, embedComparatorState,
                      List.append_assoc] using hcompare)
                  (by
                    simpa [comparisonPrefix,
                      separatedComparatorComparisonPrefix,
                      queryCells, rowCells, List.reverse_replicate,
                      List.append_assoc]
                      using hrestore))))))))
  done

end RuntimeKeySingleKeyRepair
end FiniteRecognizer.Interpreter.UniformInterpreterOneStep
end Computability
end FoC
