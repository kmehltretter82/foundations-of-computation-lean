import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup.SingleKeyCore

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.UniformInterpreterOneStep
namespace RuntimeKeySingleKeyRepair

open FiniteRecognizer ExactFuel StrictProbe

theorem comparator_computes_equal_state_separated
    (state : Nat)
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
          (separatedComparatorBody
            (List.replicate state MachineCodeSymbol.tick)
            queryRead processed
            (List.replicate state MachineCodeSymbol.tick)
            rowRead actionSuffix) }
      { state := embedComparatorState
          (runtimeKeyComparatorOutcomeState
            (runtimeKeyComparatorReadOutcome queryRead rowRead))
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft
            (List.replicate state MachineCodeSymbol.tick)
            queryRead processed
            (List.replicate state MachineCodeSymbol.tick)
            rowRead [MachineCodeSymbol.header])
          actionSuffix } := by
  have hprefix := comparator_computes_equal_unary_prefixes_separated
    0 state queryRead processed hprocessedTransition hprocessedHeader
    rowRead actionSuffix
  have hfinish := comparator_computes_equal_state_finish_separated
    state queryRead processed hprocessedTransition hprocessedHeader
    rowRead actionSuffix
  exact TuringMachine.computes_trans
    (by
      simpa [separatedComparatorPairedBody] using hprefix)
    (by
      simpa [separatedComparatorPairedBody,
        separatedComparatorComparedBody,
        separatedComparatorRestoredLeft] using hfinish)
  done

theorem comparator_computes_query_shorter_finish_separated
    (marked rowExtra : Nat)
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
          (separatedComparatorComparedBody marked 0 (rowExtra + 1)
            queryRead processed rowRead actionSuffix) }
      { state := .missed
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft
            (List.replicate marked MachineCodeSymbol.blank)
            queryRead processed
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              (List.replicate (rowExtra + 1)
                MachineCodeSymbol.tick))
            rowRead [MachineCodeSymbol.header])
          actionSuffix } := by
  let queryCells : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let rowMarked : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let rowTail : Word MachineCodeSymbol :=
    List.replicate rowExtra MachineCodeSymbol.tick
  let rowCells : Word MachineCodeSymbol :=
    List.append rowMarked (MachineCodeSymbol.tick :: rowTail)
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
  let comparisonPrefix : Word MachineCodeSymbol :=
    separatedComparatorComparisonPrefix queryCells queryRead
      processed rowMarked
  have hqueryCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick := by
    intro symbol hmem
    left
    exact (List.mem_replicate.mp hmem).2
  have hrowMarked :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowMarked ->
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
    simp only [rowCells] at hmem
    rcases List.mem_append.mp hmem with hmarked | htail
    · exact hrowMarked symbol hmarked
    · rcases List.mem_cons.mp htail with htick | htail
      · right
        exact htick
      · right
        exact (List.mem_replicate.mp htail).2
  have hprefix := separatedComparatorComparisonPrefix_no_header
    queryCells hqueryCells queryRead processed hprocessedHeader
    rowMarked hrowMarked
  have hprefixNonempty : comparisonPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [comparisonPrefix, separatedComparatorComparisonPrefix] at hlen
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
      queryRead marked transitionLeft
      (MachineCodeSymbol.tick :: List.append rowTail afterRow))
  have hmissRewind := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_finish_row_tick_miss_and_rewind
      queryRead comparisonPrefix hprefix hprefixNonempty
      (List.append rowTail afterRow))
  have hrestore := comparator_computes_restore_outcome_separated
    RuntimeKeyComparatorOutcome.isMiss
    queryCells hqueryCells queryRead processed
    hprocessedTransition hprocessedHeader rowCells hrowCells
    rowRead [MachineCodeSymbol.header] actionSuffix
  exact TuringMachine.computes_trans
    (by
      simpa [separatedComparatorComparedBody,
        separatedComparatorBody, queryCells, rowMarked,
        rowTail, rowCells, afterRow, afterQuery,
        liftComparatorConfig, embedComparatorState,
        List.replicate_succ, List.append_assoc] using hquery)
    (TuringMachine.Computes.step
      (by
        simpa [queryCells, rowMarked, rowTail, rowCells,
          afterRow, queryLeft, liftComparatorConfig,
          embedComparatorState, List.append_assoc] using hqueryDone)
      (TuringMachine.Computes.step
        (by
          simpa [queryCells, rowMarked, rowTail, rowCells,
            afterRow, queryLeft, queryDoneLeft, queryReadLeft,
            liftComparatorConfig, embedComparatorState,
            List.append_assoc] using hqueryRead)
        (TuringMachine.computes_trans
          (by
            simpa [comparatorFinishSeekConfig, queryReadLeft,
              queryDoneLeft, queryLeft, queryCells, rowMarked,
              rowTail, rowCells, afterRow, List.append_assoc]
              using hseek)
          (TuringMachine.Computes.step
            (by
              simpa [comparatorFinishSeekConfig, processedLeft,
                queryReadLeft, queryDoneLeft, queryLeft,
                queryCells, rowMarked, rowTail, rowCells,
                afterRow, List.append_assoc] using htransition)
            (TuringMachine.computes_trans
              (by
                simpa [transitionLeft, processedLeft, queryReadLeft,
                  queryDoneLeft, queryLeft, queryCells, rowMarked,
                  rowTail, rowCells, afterRow, liftComparatorConfig,
                  embedComparatorState, List.append_assoc] using hrow)
              (TuringMachine.computes_trans
                (by
                  simpa [comparisonPrefix,
                    separatedComparatorComparisonPrefix,
                    queryCells, rowMarked, rowTail,
                    queryLeft, queryDoneLeft, queryReadLeft,
                    processedLeft, transitionLeft,
                    liftComparatorConfig, embedComparatorState,
                    List.reverse_replicate, List.append_assoc]
                    using hmissRewind)
                (by
                  simpa [queryCells, rowMarked, rowTail, rowCells,
                    afterRow, separatedComparatorBody,
                    separatedComparatorComparisonPrefix,
                    runtimeKeyComparatorOutcomeState,
                    embedComparatorState,
                    List.reverse_append, List.reverse_cons,
                    List.reverse_reverse, List.replicate_succ,
                    List.append_assoc] using hrestore)))))))
  done

theorem comparator_computes_query_shorter_separated
    (queryState rowExtra : Nat)
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
          (separatedComparatorBody
            (List.replicate queryState MachineCodeSymbol.tick)
            queryRead processed
            (List.replicate (queryState + (rowExtra + 1))
              MachineCodeSymbol.tick)
            rowRead actionSuffix) }
      { state := .missed
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft
            (List.replicate queryState MachineCodeSymbol.tick)
            queryRead processed
            (List.replicate (queryState + (rowExtra + 1))
              MachineCodeSymbol.tick)
            rowRead [MachineCodeSymbol.header])
          actionSuffix } := by
  have hprefix := comparator_computes_common_unary_prefix_separated
    0 queryState 0 (rowExtra + 1)
    queryRead processed hprocessedTransition hprocessedHeader
    rowRead actionSuffix
  have hfinish := comparator_computes_query_shorter_finish_separated
    queryState rowExtra queryRead processed
    hprocessedTransition hprocessedHeader rowRead actionSuffix
  have htarget :
      separatedComparatorRestoredLeft
          (List.replicate queryState MachineCodeSymbol.blank)
          queryRead processed
          (List.append
            (List.replicate queryState MachineCodeSymbol.blank)
            (List.replicate (rowExtra + 1) MachineCodeSymbol.tick))
          rowRead [MachineCodeSymbol.header] =
        separatedComparatorRestoredLeft
          (List.replicate queryState MachineCodeSymbol.tick)
          queryRead processed
          (List.replicate (queryState + (rowExtra + 1))
            MachineCodeSymbol.tick)
          rowRead [MachineCodeSymbol.header] := by
    rw [replicate_add_eq_append]
    simp [separatedComparatorRestoredLeft]
    rw [Nat.add_comm rowExtra queryState]
    rw [show queryState + (rowExtra + 1) =
      (queryState + rowExtra) + 1 by simp [Nat.add_assoc]]
    rw [List.replicate_succ]
    rfl
  exact TuringMachine.computes_trans
    (by
      simpa [separatedComparatorComparedBody,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprefix)
    (by
      rw [← htarget]
      simpa [separatedComparatorComparedBody] using hfinish)
  done

theorem comparator_computes_row_shorter_finish_separated
    (marked queryExtra : Nat)
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
          (separatedComparatorComparedBody marked (queryExtra + 1) 0
            queryRead processed rowRead actionSuffix) }
      { state := .missed
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              (List.replicate (queryExtra + 1)
                MachineCodeSymbol.tick))
            queryRead processed
            (List.replicate marked MachineCodeSymbol.blank)
            rowRead [MachineCodeSymbol.header])
          actionSuffix } := by
  let queryMarked : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let queryTail : Word MachineCodeSymbol :=
    List.replicate queryExtra MachineCodeSymbol.tick
  let queryCells : Word MachineCodeSymbol :=
    List.append queryMarked (MachineCodeSymbol.blank :: queryTail)
  let rowCells : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let afterRow : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      runtimeKeyCellSymbol rowRead :: actionSuffix
  let rowSource : Word MachineCodeSymbol :=
    List.append rowCells afterRow
  let afterQuery : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      runtimeKeyCellSymbol queryRead ::
      List.append processed
        (MachineCodeSymbol.transition :: rowSource)
  let queryMarkedLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.blank ::
      List.append queryMarked.reverse [MachineCodeSymbol.header]
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
  let comparisonPrefix : Word MachineCodeSymbol :=
    separatedComparatorComparisonPrefix queryCells queryRead
      processed rowCells
  have hqueryMarked :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryMarked ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick := by
    intro symbol hmem
    left
    exact (List.mem_replicate.mp hmem).2
  have hqueryCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol queryCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick := by
    intro symbol hmem
    simp only [queryCells] at hmem
    rcases List.mem_append.mp hmem with hmarked | htail
    · exact hqueryMarked symbol hmarked
    · rcases List.mem_cons.mp htail with hblank | htail
      · left
        exact hblank
      · right
        exact (List.mem_replicate.mp htail).2
  have hrowCells :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowCells ->
          symbol = MachineCodeSymbol.blank ∨
            symbol = MachineCodeSymbol.tick := by
    intro symbol hmem
    left
    exact (List.mem_replicate.mp hmem).2
  have hprefix := separatedComparatorComparisonPrefix_no_header
    queryCells hqueryCells queryRead processed hprocessedHeader
    rowCells hrowCells
  have hprefixNonempty : comparisonPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [comparisonPrefix, separatedComparatorComparisonPrefix] at hlen
  have hqueryMarks := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_scan_query_blanks
      marked [MachineCodeSymbol.header]
      (MachineCodeSymbol.tick :: List.append queryTail afterQuery))
  have hqueryMark := comparator_step_lift
    (runtimeKeyComparatorMachine_step_mark_query_tick
      (List.append queryMarked.reverse [MachineCodeSymbol.header])
      (List.append queryTail afterQuery))
  have hqueryTail := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_seek_query_ticks
      queryExtra queryMarkedLeft afterQuery)
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
  have hseek := comparator_computes_seek_prefix queryReadLeft processed
    (MachineCodeSymbol.transition :: rowSource)
    hprocessedTransition hprocessedHeader
  have htransition := comparator_step_select_transition
    processedLeft rowSource
  have hrow := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_scan_row_blanks
      marked transitionLeft afterRow)
  have hmissRewind := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_scan_row_done_miss_and_rewind
      comparisonPrefix hprefix hprefixNonempty
      (runtimeKeyCellSymbol rowRead :: actionSuffix))
  have hrestore := comparator_computes_restore_outcome_separated
    RuntimeKeyComparatorOutcome.isMiss
    queryCells hqueryCells queryRead processed
    hprocessedTransition hprocessedHeader rowCells hrowCells
    rowRead [MachineCodeSymbol.header] actionSuffix
  exact TuringMachine.computes_trans
    (by
      simpa [separatedComparatorComparedBody,
        separatedComparatorBody, queryMarked, queryTail,
        queryCells, rowCells, afterRow, rowSource, afterQuery,
        liftComparatorConfig, embedComparatorState,
        List.replicate_succ, List.append_assoc] using hqueryMarks)
    (TuringMachine.Computes.step
      (by
        simpa [queryMarked, queryTail, rowCells, afterRow,
          rowSource, afterQuery, queryMarkedLeft,
          liftComparatorConfig, embedComparatorState,
          List.append_assoc] using hqueryMark)
      (TuringMachine.computes_trans
        (by
          simpa [queryMarked, queryTail, rowCells, afterRow,
            rowSource, afterQuery, queryMarkedLeft, queryTailLeft,
            liftComparatorConfig, embedComparatorState,
            List.append_assoc] using hqueryTail)
        (TuringMachine.Computes.step
          (by
            simpa [queryMarked, queryTail, queryMarkedLeft,
              queryTailLeft, queryDoneLeft, rowCells, afterRow,
              rowSource, liftComparatorConfig, embedComparatorState,
              List.append_assoc] using hqueryDone)
          (TuringMachine.Computes.step
            (by
              simpa [queryMarked, queryTail, queryMarkedLeft,
                queryTailLeft, queryDoneLeft, queryReadLeft,
                rowCells, afterRow, rowSource, liftComparatorConfig,
                embedComparatorState, List.append_assoc]
                using hqueryRead)
            (TuringMachine.computes_trans
              (by
                simpa [comparatorSeekConfig, queryReadLeft,
                  queryDoneLeft, queryTailLeft, queryMarkedLeft,
                  queryMarked, queryTail, rowCells, afterRow,
                  rowSource, List.append_assoc] using hseek)
              (TuringMachine.Computes.step
                (by
                  simpa [comparatorSeekConfig, processedLeft,
                    queryReadLeft, queryDoneLeft, queryTailLeft,
                    queryMarkedLeft, queryMarked, queryTail,
                    rowCells, afterRow, rowSource,
                    List.append_assoc] using htransition)
                (TuringMachine.computes_trans
                  (by
                    simpa [transitionLeft, processedLeft,
                      queryReadLeft, queryDoneLeft, queryTailLeft,
                      queryMarkedLeft, queryMarked, queryTail,
                      rowCells, afterRow, rowSource,
                      liftComparatorConfig, embedComparatorState,
                      List.append_assoc] using hrow)
                  (TuringMachine.computes_trans
                    (by
                      simpa [comparisonPrefix,
                        separatedComparatorComparisonPrefix,
                        queryMarked, queryTail, queryCells, rowCells,
                        queryMarkedLeft, queryTailLeft,
                        queryDoneLeft, queryReadLeft, processedLeft,
                        transitionLeft, liftComparatorConfig,
                        embedComparatorState,
                        List.reverse_append, List.reverse_cons,
                        List.reverse_reverse, List.reverse_replicate,
                        List.append_assoc] using hmissRewind)
                    (by
                      simpa [queryMarked, queryTail, queryCells,
                        rowCells, separatedComparatorBody,
                        separatedComparatorRestoredLeft,
                        runtimeKeyComparatorOutcomeState,
                        embedComparatorState, List.replicate_succ,
                        List.append_assoc] using hrestore)))))))))
  done

theorem comparator_computes_row_shorter_separated
    (rowState queryExtra : Nat)
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
          (separatedComparatorBody
            (List.replicate (rowState + (queryExtra + 1))
              MachineCodeSymbol.tick)
            queryRead processed
            (List.replicate rowState MachineCodeSymbol.tick)
            rowRead actionSuffix) }
      { state := .missed
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft
            (List.replicate (rowState + (queryExtra + 1))
              MachineCodeSymbol.tick)
            queryRead processed
            (List.replicate rowState MachineCodeSymbol.tick)
            rowRead [MachineCodeSymbol.header])
          actionSuffix } := by
  have hprefix := comparator_computes_common_unary_prefix_separated
    0 rowState (queryExtra + 1) 0
    queryRead processed hprocessedTransition hprocessedHeader
    rowRead actionSuffix
  have hfinish := comparator_computes_row_shorter_finish_separated
    rowState queryExtra queryRead processed
    hprocessedTransition hprocessedHeader rowRead actionSuffix
  have htarget :
      separatedComparatorRestoredLeft
          (List.append
            (List.replicate rowState MachineCodeSymbol.blank)
            (List.replicate (queryExtra + 1) MachineCodeSymbol.tick))
          queryRead processed
          (List.replicate rowState MachineCodeSymbol.blank)
          rowRead [MachineCodeSymbol.header] =
        separatedComparatorRestoredLeft
          (List.replicate (rowState + (queryExtra + 1))
            MachineCodeSymbol.tick)
          queryRead processed
          (List.replicate rowState MachineCodeSymbol.tick)
          rowRead [MachineCodeSymbol.header] := by
    rw [replicate_add_eq_append]
    simp [separatedComparatorRestoredLeft]
    rw [Nat.add_comm queryExtra rowState]
    rw [show rowState + (queryExtra + 1) =
      (rowState + queryExtra) + 1 by simp [Nat.add_assoc]]
    rw [List.replicate_succ]
    rfl
  exact TuringMachine.computes_trans
    (by
      simpa [separatedComparatorComparedBody,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprefix)
    (by
      rw [← htarget]
      simpa [separatedComparatorComparedBody] using hfinish)
  done

/-- Exact one-row comparison with an arbitrary marked rejected-row block. -/
theorem comparator_computes_one_row_separated
    (queryState : Nat) (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed)
    (hprocessedHeader : transitionListParserNoHeader processed)
    (rowState : Nat) (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (separatedComparatorBody
            (List.replicate queryState MachineCodeSymbol.tick)
            queryRead processed
            (List.replicate rowState MachineCodeSymbol.tick)
            rowRead actionSuffix) }
      { state := embedComparatorState
          (runtimeKeyComparatorOutcomeState
            (runtimeKeyComparatorRowOutcome
              queryState queryRead rowState rowRead))
        tape := runtimeKeyComparatorTape
          (separatedComparatorRestoredLeft
            (List.replicate queryState MachineCodeSymbol.tick)
            queryRead processed
            (List.replicate rowState MachineCodeSymbol.tick)
            rowRead [MachineCodeSymbol.header])
          actionSuffix } := by
  rcases Nat.lt_trichotomy queryState rowState with
    hshort | hequal | hlong
  · rcases Nat.exists_eq_add_of_lt hshort with
      ⟨rowExtra, hrowState⟩
    subst rowState
    simpa [runtimeKeyComparatorRowOutcome,
      runtimeKeyComparatorOutcomeState, embedComparatorState,
      Nat.add_assoc] using
        comparator_computes_query_shorter_separated
          queryState rowExtra queryRead processed
          hprocessedTransition hprocessedHeader rowRead actionSuffix
  · subst rowState
    simpa [runtimeKeyComparatorRowOutcome] using
      comparator_computes_equal_state_separated
        queryState queryRead processed
        hprocessedTransition hprocessedHeader rowRead actionSuffix
  · rcases Nat.exists_eq_add_of_lt hlong with
      ⟨queryExtra, hqueryState⟩
    subst queryState
    simpa [runtimeKeyComparatorRowOutcome,
      runtimeKeyComparatorOutcomeState, embedComparatorState,
      Nat.add_assoc] using
        comparator_computes_row_shorter_separated
          rowState queryExtra queryRead processed
          hprocessedTransition hprocessedHeader rowRead actionSuffix
  done

def canonicalSeparatedRowSource
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := .inner RuntimeKeyComparatorState.scanQuery
    tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
      (List.append
        (runtimeKeyBuilderKeyCode current.state (Tape.read current.tape))
        (List.append (processedRows skipped)
          (MachineDescription.encodeTransitionAppend row
            (MachineDescription.encodeTransitionsAppend rest
              (MachineCodeSymbol.header :: protectedSuffix))))) }

def canonicalSeparatedRowTarget
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := embedComparatorState
      (runtimeKeyComparatorOutcomeState
        (runtimeKeyComparatorRowOutcome current.state
          (Tape.read current.tape) row.source row.read))
    tape := runtimeKeyComparatorTape
      (separatedComparatorRestoredLeft
        (List.replicate current.state MachineCodeSymbol.tick)
        (Tape.read current.tape) (processedRows skipped)
        (List.replicate row.source MachineCodeSymbol.tick)
        row.read [MachineCodeSymbol.header])
      (runtimeKeyCanonicalActionSuffix row rest
        (MachineCodeSymbol.header :: protectedSuffix)) }

/-- Exact canonical-row specialization of the arbitrary processed comparator. -/
theorem comparator_computes_canonical_separated_row
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      (canonicalSeparatedRowSource current skipped row rest protectedSuffix)
      (canonicalSeparatedRowTarget current skipped row rest
        protectedSuffix) := by
  have hrun := comparator_computes_one_row_separated
    current.state (Tape.read current.tape) (processedRows skipped)
    (processedRows_no_transition skipped)
    (processedRows_no_header skipped)
    row.source row.read
    (runtimeKeyCanonicalActionSuffix row rest
      (MachineCodeSymbol.header :: protectedSuffix))
  rcases row with ⟨source, read, write, move, target⟩
  cases move <;>
    simpa [canonicalSeparatedRowSource,
      canonicalSeparatedRowTarget, runtimeKeyBuilderKeyCode,
      separatedComparatorBody,
      runtimeKeyCanonicalActionSuffix,
      MachineDescription.encodeTransitionAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeDirectionAppend,
      MachineDescription.encodeDirection,
      runtimeKey_encodeNat_eq_replicate_tick_done,
      runtimeKey_encodeCell_eq_singleton,
      List.append_assoc] using hrun
  done

theorem comparator_step_missed_left_symbol
    (leftHead : MachineCodeSymbol)
    (leftTail : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.transition)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      { state := .missed
        tape := runtimeKeyComparatorTape (leftHead :: leftTail)
          (current :: suffix) }
      { state := .missed
        tape := runtimeKeyComparatorTape leftTail
          (leftHead :: current :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead current current]
  apply TuringMachine.Step.mk
  cases current <;>
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read]
      at hcurrent ⊢
  done

/-- Scan left from a rejected row's action field to its transition marker. -/
theorem comparator_computes_missed_to_transition
    (leftTail scanned : Word MachineCodeSymbol)
    (hscanned : RuntimeKeySelectedExtractor.NoTransition scanned)
    (current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.transition)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .missed
        tape := runtimeKeyComparatorTape
          (List.append scanned
            (MachineCodeSymbol.transition :: leftTail))
          (current :: suffix) }
      { state := .missed
        tape := runtimeKeyComparatorTape leftTail
          (MachineCodeSymbol.transition ::
            List.append scanned.reverse (current :: suffix)) } := by
  induction scanned generalizing current suffix with
  | nil =>
      exact TuringMachine.Computes.step
        (by
          simpa using comparator_step_missed_left_symbol
            MachineCodeSymbol.transition leftTail current hcurrent suffix)
        (TuringMachine.Computes.refl _)
  | cons head tail ih =>
      have hhead : head ≠ MachineCodeSymbol.transition :=
        hscanned head (List.Mem.head tail)
      have htail : RuntimeKeySelectedExtractor.NoTransition tail := by
        intro symbol hmem
        exact hscanned symbol (List.Mem.tail head hmem)
      exact TuringMachine.Computes.step
        (by
          simpa [List.append_assoc] using
            comparator_step_missed_left_symbol head
              (List.append tail
                (MachineCodeSymbol.transition :: leftTail))
              current hcurrent suffix)
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            ih htail head hhead (current :: suffix))
  done

theorem comparator_step_mark_rejected_transition
    (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      { state := .missed
        tape := runtimeKeyComparatorTape (leftHead :: leftTail)
          (MachineCodeSymbol.transition :: suffix) }
      { state := .rewindRejected
        tape := runtimeKeyComparatorTape leftTail
          (leftHead :: MachineCodeSymbol.done :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead MachineCodeSymbol.transition MachineCodeSymbol.done]
  exact TuringMachine.Step.mk (by
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read])
  done

theorem comparator_step_rewind_rejected_symbol
    (leftHead current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      { state := .rewindRejected
        tape := runtimeKeyComparatorTape (leftHead :: leftTail)
          (current :: suffix) }
      { state := .rewindRejected
        tape := runtimeKeyComparatorTape leftTail
          (leftHead :: current :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead current current]
  apply TuringMachine.Step.mk
  cases current <;>
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read]
      at hcurrent ⊢
  done

theorem comparator_computes_rewind_rejected_to_header
    (leftSymbols : Word MachineCodeSymbol)
    (hleftSymbols : transitionListParserNoHeader leftSymbols)
    (current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .rewindRejected
        tape := runtimeKeyComparatorTape
          (List.append leftSymbols [MachineCodeSymbol.header])
          (current :: suffix) }
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (List.append leftSymbols.reverse (current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      have hsymbol := comparator_step_rewind_rejected_symbol
        MachineCodeSymbol.header current hcurrent [] suffix
      have hheader :
          TuringMachine.Step comparatorMachine
            { state := .rewindRejected
              tape := runtimeKeyComparatorTape []
                (MachineCodeSymbol.header :: current :: suffix) }
            { state := .inner RuntimeKeyComparatorState.scanQuery
              tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
                (current :: suffix) } := by
        rw [← runtimeKeyComparatorTape_move_right []
          MachineCodeSymbol.header MachineCodeSymbol.header
          (current :: suffix)]
        exact TuringMachine.Step.mk (by
          simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read])
      exact TuringMachine.Computes.step
        (by simpa using hsymbol)
        (TuringMachine.Computes.step hheader
          (TuringMachine.Computes.refl _))
  | cons leftHead leftTail ih =>
      have hleftHead : leftHead ≠ MachineCodeSymbol.header :=
        hleftSymbols leftHead (List.Mem.head leftTail)
      have hleftTail : transitionListParserNoHeader leftTail := by
        intro symbol hmem
        exact hleftSymbols symbol (List.Mem.tail leftHead hmem)
      have hstep := comparator_step_rewind_rejected_symbol
        leftHead current hcurrent
        (List.append leftTail [MachineCodeSymbol.header]) suffix
      have hrest := ih hleftTail leftHead hleftHead (current :: suffix)
      exact TuringMachine.Computes.step
        (by simpa using hstep)
        (by
          simpa [List.reverse_cons, List.append_assoc] using hrest)
  done

theorem comparator_computes_mark_transition_and_rewind
    (leftOfTransition : Word MachineCodeSymbol)
    (hleftHeader : transitionListParserNoHeader leftOfTransition)
    (hleftNonempty : leftOfTransition ≠ [])
    (rowTail : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .missed
        tape := runtimeKeyComparatorTape
          (List.append leftOfTransition [MachineCodeSymbol.header])
          (MachineCodeSymbol.transition :: rowTail) }
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (List.append leftOfTransition.reverse
            (MachineCodeSymbol.done :: rowTail)) } := by
  cases leftOfTransition with
  | nil => exact False.elim (hleftNonempty rfl)
  | cons leftHead leftTail =>
      have hleftHead : leftHead ≠ MachineCodeSymbol.header :=
        hleftHeader leftHead (List.Mem.head leftTail)
      have hleftTail : transitionListParserNoHeader leftTail := by
        intro symbol hmem
        exact hleftHeader symbol (List.Mem.tail leftHead hmem)
      have hmark := comparator_step_mark_rejected_transition
        leftHead (List.append leftTail [MachineCodeSymbol.header]) rowTail
      have hrewind := comparator_computes_rewind_rejected_to_header
        leftTail hleftTail leftHead hleftHead
        (MachineCodeSymbol.done :: rowTail)
      exact TuringMachine.Computes.step
        (by simpa [List.append_assoc] using hmark)
        (by
          simpa [List.reverse_cons, List.append_assoc] using hrewind)
  done

theorem comparator_computes_rejected_block_restart
    (leftOfTransition : Word MachineCodeSymbol)
    (hleftHeader : transitionListParserNoHeader leftOfTransition)
    (hleftNonempty : leftOfTransition ≠ [])
    (scanned : Word MachineCodeSymbol)
    (hscanned : RuntimeKeySelectedExtractor.NoTransition scanned)
    (current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.transition)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .missed
        tape := runtimeKeyComparatorTape
          (List.append scanned
            (MachineCodeSymbol.transition ::
              List.append leftOfTransition [MachineCodeSymbol.header]))
          (current :: suffix) }
      { state := .inner RuntimeKeyComparatorState.scanQuery
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (List.append leftOfTransition.reverse
            (MachineCodeSymbol.done ::
              List.append scanned.reverse (current :: suffix))) } := by
  have hscan := comparator_computes_missed_to_transition
    (List.append leftOfTransition [MachineCodeSymbol.header])
    scanned hscanned current hcurrent suffix
  have hmark := comparator_computes_mark_transition_and_rewind
    leftOfTransition hleftHeader hleftNonempty
    (List.append scanned.reverse (current :: suffix))
  exact TuringMachine.computes_trans hscan hmark
  done

theorem embedComparatorState_rowOutcome
    (queryState : Nat) (queryRead : Option Bool)
    (row : TransitionDescription) :
    embedComparatorState
        (runtimeKeyComparatorOutcomeState
          (runtimeKeyComparatorRowOutcome queryState queryRead
            row.source row.read)) =
      if MachineDescription.Matches queryState queryRead row then
        ComparatorState.selected
      else
        ComparatorState.missed := by
  by_cases hstate : queryState = row.source
  · subst queryState
    by_cases hread : queryRead = row.read
    · subst queryRead
      simp [MachineDescription.Matches,
        runtimeKeyComparatorRowOutcome,
        runtimeKeyComparatorReadOutcome,
        runtimeKeyComparatorOutcomeState, embedComparatorState]
    · have hread' : row.read ≠ queryRead := by
        intro heq
        exact hread heq.symm
      simp [MachineDescription.Matches,
        runtimeKeyComparatorRowOutcome,
        runtimeKeyComparatorReadOutcome,
        runtimeKeyComparatorOutcomeState, embedComparatorState,
        hread, hread']
  · have hstate' : row.source ≠ queryState := by
      intro heq
      exact hstate heq.symm
    simp [MachineDescription.Matches,
      runtimeKeyComparatorRowOutcome,
      runtimeKeyComparatorOutcomeState, embedComparatorState,
      hstate, hstate']
  done

def canonicalRejectedRestartConfig
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := .inner RuntimeKeyComparatorState.scanQuery
    tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
      (List.append
        (runtimeKeyBuilderKeyCode current.state (Tape.read current.tape))
        (List.append (processedRows skipped)
          (List.append (processedRow row)
            (MachineDescription.encodeTransitionsAppend rest
              (MachineCodeSymbol.header :: protectedSuffix))))) }

theorem comparator_restarts_after_canonical_miss
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (hmiss :
      MachineDescription.Matches current.state (Tape.read current.tape)
        row = false) :
    TuringMachine.Computes comparatorMachine
      (canonicalSeparatedRowTarget current skipped row rest protectedSuffix)
      (canonicalRejectedRestartConfig current skipped row rest
        protectedSuffix) := by
  let queryCells : Word MachineCodeSymbol :=
    List.replicate current.state MachineCodeSymbol.tick
  let rowCells : Word MachineCodeSymbol :=
    List.replicate row.source MachineCodeSymbol.tick
  let scanned : Word MachineCodeSymbol :=
    runtimeKeyCellSymbol row.read ::
      MachineCodeSymbol.done :: rowCells.reverse
  let leftOfTransition : Word MachineCodeSymbol :=
    List.append (processedRows skipped).reverse
      (runtimeKeyCellSymbol (Tape.read current.tape) ::
        MachineCodeSymbol.done :: queryCells.reverse)
  let actionTail : Word MachineCodeSymbol :=
    MachineDescription.encodeDirectionAppend row.move
      (MachineDescription.encodeNatAppend row.target
        (MachineDescription.encodeTransitionsAppend rest
          (MachineCodeSymbol.header :: protectedSuffix)))
  have hleftHeader : transitionListParserNoHeader leftOfTransition := by
    intro symbol hmem
    simp only [leftOfTransition] at hmem
    rcases List.mem_append.mp hmem with hprocessed | hquery
    · have hprocessed' :
          List.Mem symbol (processedRows skipped) := by
        change symbol ∈
          (show List MachineCodeSymbol from (processedRows skipped).reverse)
          at hprocessed
        have hprocessed' := List.mem_reverse.mp hprocessed
        change List.Mem symbol (processedRows skipped) at hprocessed'
        exact hprocessed'
      exact processedRows_no_header skipped symbol hprocessed'
    · rcases List.mem_cons.mp hquery with hread | hquery
      · subst symbol
        cases Tape.read current.tape with
        | none => simp [runtimeKeyCellSymbol]
        | some bit => cases bit <;> simp [runtimeKeyCellSymbol]
      · rcases List.mem_cons.mp hquery with hdone | hquery
        · subst symbol
          simp
        · have hquery' : List.Mem symbol queryCells := by
            change symbol ∈
              (show List MachineCodeSymbol from queryCells.reverse) at hquery
            have hquery' := List.mem_reverse.mp hquery
            change List.Mem symbol queryCells at hquery'
            exact hquery'
          have heq := (List.mem_replicate.mp hquery').2
          subst symbol
          simp
  have hleftNonempty : leftOfTransition ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [leftOfTransition] at hlen
  have hscanned : RuntimeKeySelectedExtractor.NoTransition scanned := by
    intro symbol hmem
    simp only [scanned] at hmem
    rcases List.mem_cons.mp hmem with hread | hmem
    · subst symbol
      cases row.read with
      | none => simp [runtimeKeyCellSymbol]
      | some bit => cases bit <;> simp [runtimeKeyCellSymbol]
    · rcases List.mem_cons.mp hmem with hdone | hrow
      · subst symbol
        simp
      · have hrow' : List.Mem symbol rowCells := by
          change symbol ∈
            (show List MachineCodeSymbol from rowCells.reverse) at hrow
          have hrow' := List.mem_reverse.mp hrow
          change List.Mem symbol rowCells at hrow'
          exact hrow'
        have heq := (List.mem_replicate.mp hrow').2
        subst symbol
        simp
  have hwrite :
      runtimeKeyCellSymbol row.write ≠ MachineCodeSymbol.transition := by
    cases row.write with
    | none => simp [runtimeKeyCellSymbol]
    | some bit => cases bit <;> simp [runtimeKeyCellSymbol]
  have houtcome :
      embedComparatorState
          (runtimeKeyComparatorOutcomeState
            (runtimeKeyComparatorRowOutcome current.state
              (Tape.read current.tape) row.source row.read)) =
        ComparatorState.missed := by
    rw [embedComparatorState_rowOutcome, hmiss]
    rfl
  have hrun := comparator_computes_rejected_block_restart
    leftOfTransition hleftHeader hleftNonempty
    scanned hscanned (runtimeKeyCellSymbol row.write) hwrite actionTail
  rcases row with ⟨source, read, write, move, target⟩
  cases move <;> cases write <;>
    simp [canonicalSeparatedRowTarget,
      canonicalRejectedRestartConfig,
      houtcome,
      separatedComparatorRestoredLeft,
      runtimeKeyCanonicalActionSuffix,
      runtimeKeyBuilderKeyCode, processedRow,
      RuntimeKeySelectedExtractor.rowTail,
      runtimeKeyRawTransitionTail,
      queryCells, rowCells, scanned, leftOfTransition, actionTail,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeDirectionAppend,
      MachineDescription.encodeDirection,
      MachineDescription.encodeTransitionsAppend,
      runtimeKey_encodeNat_eq_replicate_tick_done,
      runtimeKey_encodeCell_eq_singleton,
      List.reverse_append, List.reverse_cons,
      List.reverse_reverse, List.reverse_replicate,
      List.append_assoc] at hrun ⊢
  all_goals
    simpa [runtimeKeyCellSymbol, List.append_assoc] using hrun
  done

theorem processedRows_append
    (left right : List TransitionDescription) :
    processedRows (List.append left right) =
      List.append (processedRows left) (processedRows right) := by
  induction left with
  | nil => rfl
  | cons row rest ih =>
      calc
        processedRows (List.append (row :: rest) right) =
            List.append (processedRow row)
              (processedRows (List.append rest right)) := rfl
        _ = List.append (processedRow row)
              (List.append (processedRows rest) (processedRows right)) :=
            congrArg (fun tail : Word MachineCodeSymbol =>
              List.append (processedRow row) tail) ih
        _ = List.append
              (List.append (processedRow row) (processedRows rest))
              (processedRows right) :=
            (List.append_assoc _ _ _).symm
        _ = List.append (processedRows (row :: rest))
              (processedRows right) := rfl
  done

theorem processedRows_append_singleton
    (rows : List TransitionDescription)
    (row : TransitionDescription) :
    processedRows (List.append rows [row]) =
      List.append (processedRows rows) (processedRow row) := by
  simpa [processedRows] using processedRows_append rows [row]
  done

def canonicalScanRowsConfig
    (current : MachineDescription.Configuration)
    (skipped rows : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := .inner RuntimeKeyComparatorState.scanQuery
    tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
      (List.append
        (runtimeKeyBuilderKeyCode current.state (Tape.read current.tape))
        (List.append (processedRows skipped)
          (MachineDescription.encodeTransitionsAppend rows
            (MachineCodeSymbol.header :: protectedSuffix)))) }

theorem canonicalScanRowsConfig_cons
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    canonicalScanRowsConfig current skipped (row :: rest)
        protectedSuffix =
      canonicalSeparatedRowSource current skipped row rest
        protectedSuffix := by
  simp [canonicalScanRowsConfig, canonicalSeparatedRowSource,
    MachineDescription.encodeTransitionsAppend]
  done

theorem canonicalRejectedRestartConfig_eq_scanRows
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    canonicalRejectedRestartConfig current skipped row rest
        protectedSuffix =
      canonicalScanRowsConfig current (List.append skipped [row]) rest
        protectedSuffix := by
  unfold canonicalRejectedRestartConfig canonicalScanRowsConfig
  rw [processedRows_append_singleton]
  simp [List.append_assoc]
  done

theorem comparator_computes_scan_head
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      (canonicalScanRowsConfig current skipped (row :: rest)
        protectedSuffix)
      (canonicalSeparatedRowTarget current skipped row rest
        protectedSuffix) := by
  rw [canonicalScanRowsConfig_cons]
  exact comparator_computes_canonical_separated_row
    current skipped row rest protectedSuffix
  done

theorem comparator_computes_miss_advance
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (hmiss :
      MachineDescription.Matches current.state (Tape.read current.tape)
        row = false) :
    TuringMachine.Computes comparatorMachine
      (canonicalScanRowsConfig current skipped (row :: rest)
        protectedSuffix)
      (canonicalScanRowsConfig current (List.append skipped [row]) rest
        protectedSuffix) := by
  exact TuringMachine.computes_trans
    (comparator_computes_scan_head current skipped row rest protectedSuffix)
    (by
      rw [← canonicalRejectedRestartConfig_eq_scanRows]
      exact comparator_restarts_after_canonical_miss
        current skipped row rest protectedSuffix hmiss)
  done

def canonicalSelectedRowTarget
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := .selected
    tape := (canonicalSeparatedRowTarget current skipped row rest
      protectedSuffix).tape }

theorem comparator_computes_selected_head
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (hmatch :
      MachineDescription.Matches current.state (Tape.read current.tape)
        row = true) :
    TuringMachine.Computes comparatorMachine
      (canonicalScanRowsConfig current skipped (row :: rest)
        protectedSuffix)
      (canonicalSelectedRowTarget current skipped row rest
        protectedSuffix) := by
  have hrun := comparator_computes_scan_head
    current skipped row rest protectedSuffix
  have houtcome := embedComparatorState_rowOutcome
    current.state (Tape.read current.tape) row
  rw [hmatch] at houtcome
  simp at houtcome
  simpa [canonicalSelectedRowTarget,
    canonicalSeparatedRowTarget, houtcome] using hrun
  done

/-!
The ordered first-match theorem: every row in `before` is rejected and marked,
then the first matching row is selected.  The final skipped block is exactly
the original block followed by `before`; no determinism hypothesis is needed.
-/
theorem comparator_computes_first_match_after_prefix
    (current : MachineDescription.Configuration)
    (skipped before : List TransitionDescription)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (hmiss :
      forall row : TransitionDescription,
        List.Mem row before ->
          MachineDescription.Matches current.state
            (Tape.read current.tape) row = false)
    (hmatch :
      MachineDescription.Matches current.state (Tape.read current.tape)
        selected = true) :
    TuringMachine.Computes comparatorMachine
      (canonicalScanRowsConfig current skipped
        (List.append before (selected :: rest)) protectedSuffix)
      (canonicalSelectedRowTarget current (List.append skipped before)
        selected rest protectedSuffix) := by
  induction before generalizing skipped with
  | nil =>
      simpa using comparator_computes_selected_head
        current skipped selected rest protectedSuffix hmatch
  | cons row tail ih =>
      have hrow :
          MachineDescription.Matches current.state
            (Tape.read current.tape) row = false :=
        hmiss row (List.Mem.head tail)
      have htail :
          forall candidate : TransitionDescription,
            List.Mem candidate tail ->
              MachineDescription.Matches current.state
                (Tape.read current.tape) candidate = false := by
        intro candidate hmem
        exact hmiss candidate (List.Mem.tail row hmem)
      have hadvance := comparator_computes_miss_advance
        current skipped row (List.append tail (selected :: rest))
        protectedSuffix hrow
      have hrest := ih (List.append skipped [row]) htail
      exact TuringMachine.computes_trans
        (by simpa [List.append_assoc] using hadvance)
        (by
          simpa [List.append_assoc] using hrest)
  done


end RuntimeKeySingleKeyRepair
end FiniteRecognizer.Interpreter.UniformInterpreterOneStep
end Computability
end FoC
