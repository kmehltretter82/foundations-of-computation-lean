import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup.Comparison

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.UniformInterpreterOneStep

theorem runtimeKeyComparatorMachine_computes_equal_state
    (state : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorBody
              (List.replicate state MachineCodeSymbol.tick)
              queryRead
              (List.replicate state MachineCodeSymbol.tick)
              rowRead actionSuffix) }
      { state :=
          runtimeKeyComparatorOutcomeState
            (runtimeKeyComparatorReadOutcome queryRead rowRead)
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.replicate state MachineCodeSymbol.tick)
              queryRead
              (List.replicate state MachineCodeSymbol.tick)
              rowRead [MachineCodeSymbol.header])
            actionSuffix } := by
  have hprefix :=
    runtimeKeyComparatorMachine_computes_equal_unary_prefixes
      0 state queryRead rowRead actionSuffix
  have hfinish :=
    runtimeKeyComparatorMachine_computes_equal_state_finish
      state queryRead rowRead actionSuffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorPairedBody]
          using hprefix)
      (by
        simpa [runtimeKeyComparatorPairedBody,
          runtimeKeyComparatorComparedBody,
          runtimeKeyComparatorRestoredLeft]
          using hfinish)
  done

theorem runtimeKeyComparatorMachine_computes_finish_row_tick_miss_and_rewind
    (read : Option Bool)
    (leftSymbols : Word MachineCodeSymbol)
    (hleftSymbols :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol leftSymbols ->
          symbol ≠ MachineCodeSymbol.header)
    (hleftSymbolsNonempty : leftSymbols ≠ [])
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.finishScanRow read
        tape :=
          runtimeKeyComparatorTape
            (List.append leftSymbols [MachineCodeSymbol.header])
            (MachineCodeSymbol.tick :: suffix) }
      { state :=
          RuntimeKeyComparatorState.restoreQuery
            RuntimeKeyComparatorOutcome.isMiss
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (List.append leftSymbols.reverse
              (MachineCodeSymbol.tick :: suffix)) } := by
  cases leftSymbols with
  | nil =>
      exact False.elim (hleftSymbolsNonempty rfl)
  | cons leftHead leftTail =>
      have hleftHead : leftHead ≠ MachineCodeSymbol.header :=
        hleftSymbols leftHead (List.Mem.head leftTail)
      have hleftTail :
          forall symbol : MachineCodeSymbol,
            List.Mem symbol leftTail ->
              symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hleftSymbols symbol (List.Mem.tail leftHead hmem)
      have hstep :=
        runtimeKeyComparatorMachine_step_finish_row_tick_miss
          read leftHead
          (List.append leftTail [MachineCodeSymbol.header]) suffix
      have hrewind :=
        runtimeKeyComparatorMachine_computes_rewind_outcome_to_header
          RuntimeKeyComparatorOutcome.isMiss
          leftTail hleftTail leftHead hleftHead
          (MachineCodeSymbol.tick :: suffix)
      exact
        TuringMachine.Computes.step
          (by simpa using hstep)
          (by
            simpa [List.reverse_cons, List.append_assoc]
              using hrewind)
  done

theorem runtimeKeyComparatorMachine_computes_query_shorter_finish
    (marked rowExtra : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorComparedBody marked 0 (rowExtra + 1)
              queryRead rowRead actionSuffix) }
      { state := RuntimeKeyComparatorState.missed
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.replicate marked MachineCodeSymbol.blank)
              queryRead
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
      MachineCodeSymbol.transition ::
      List.append rowCells afterRow
  let queryLeft : Word MachineCodeSymbol :=
    List.append queryCells.reverse [MachineCodeSymbol.header]
  let queryDoneLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.done :: queryLeft
  let queryReadLeft : Word MachineCodeSymbol :=
    runtimeKeyCellSymbol queryRead :: queryDoneLeft
  let transitionLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.transition :: queryReadLeft
  let comparisonPrefix : Word MachineCodeSymbol :=
    runtimeKeyComparatorComparisonPrefix
      queryCells queryRead rowMarked
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
  have hprefix :=
    runtimeKeyComparatorComparisonPrefix_no_header
      queryCells hqueryCells queryRead rowMarked hrowMarked
  have hprefixNonempty : comparisonPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [comparisonPrefix,
      runtimeKeyComparatorComparisonPrefix] at hlen
  have hquery :=
    runtimeKeyComparatorMachine_computes_scan_query_blanks
      marked [MachineCodeSymbol.header] afterQuery
  have hqueryDone :=
    runtimeKeyComparatorMachine_step_scan_query_done
      queryLeft
      (runtimeKeyCellSymbol queryRead ::
        MachineCodeSymbol.transition ::
        List.append rowCells afterRow)
  have hqueryRead :=
    runtimeKeyComparatorMachine_step_remember_query_read
      queryRead queryDoneLeft
      (MachineCodeSymbol.transition ::
        List.append rowCells afterRow)
  have htransition :=
    runtimeKeyComparatorMachine_step_finish_transition
      queryRead queryReadLeft (List.append rowCells afterRow)
  have hrow :=
    runtimeKeyComparatorMachine_computes_finish_row_blanks
      queryRead marked transitionLeft
      (MachineCodeSymbol.tick :: List.append rowTail afterRow)
  have hmissRewind :=
    runtimeKeyComparatorMachine_computes_finish_row_tick_miss_and_rewind
      queryRead comparisonPrefix hprefix hprefixNonempty
      (List.append rowTail afterRow)
  have hrestore :=
    runtimeKeyComparatorMachine_computes_restore_outcome_exact
      RuntimeKeyComparatorOutcome.isMiss
      queryCells hqueryCells queryRead
      rowCells hrowCells rowRead
      [MachineCodeSymbol.header] actionSuffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorComparedBody,
          runtimeKeyComparatorBody, queryCells,
          rowMarked, rowTail, rowCells,
          afterRow, afterQuery,
          List.replicate_succ,
          List.append_assoc]
          using hquery)
      (TuringMachine.Computes.step
        (by
          simpa [queryCells, rowMarked, rowTail,
            rowCells, afterRow, queryLeft,
            List.append_assoc]
            using hqueryDone)
        (TuringMachine.Computes.step
          (by
            simpa [queryCells, rowMarked, rowTail,
              rowCells, afterRow, queryLeft,
              queryDoneLeft, queryReadLeft,
              List.append_assoc]
              using hqueryRead)
          (TuringMachine.Computes.step
            (by
              simpa [queryCells, rowMarked, rowTail,
                rowCells, afterRow, queryLeft,
                queryDoneLeft, queryReadLeft,
                transitionLeft, List.append_assoc]
                using htransition)
            (TuringMachine.computes_trans
              (by
                simpa [queryCells, rowMarked, rowTail,
                  rowCells, afterRow, queryLeft,
                  queryDoneLeft, queryReadLeft,
                  transitionLeft, List.append_assoc]
                  using hrow)
              (TuringMachine.computes_trans
                (by
                  simpa [comparisonPrefix,
                    runtimeKeyComparatorComparisonPrefix,
                    queryCells, rowMarked, rowTail,
                    queryLeft, queryDoneLeft,
                    queryReadLeft, transitionLeft,
                    List.reverse_replicate,
                    List.append_assoc]
                    using hmissRewind)
                (by
                  simpa [queryCells, rowMarked, rowTail,
                    rowCells, afterRow,
                    runtimeKeyComparatorBody,
                    runtimeKeyComparatorOutcomeState,
                    runtimeKeyComparatorComparisonPrefix,
                    List.reverse_append, List.reverse_cons,
                    List.reverse_reverse,
                    List.replicate_succ,
                    List.append_assoc]
                    using hrestore))))))
  done

theorem runtimeKeyComparatorMachine_computes_query_shorter
    (queryState rowExtra : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorBody
              (List.replicate queryState MachineCodeSymbol.tick)
              queryRead
              (List.replicate (queryState + (rowExtra + 1))
                MachineCodeSymbol.tick)
              rowRead actionSuffix) }
      { state := RuntimeKeyComparatorState.missed
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.replicate queryState MachineCodeSymbol.tick)
              queryRead
              (List.replicate (queryState + (rowExtra + 1))
                MachineCodeSymbol.tick)
              rowRead [MachineCodeSymbol.header])
            actionSuffix } := by
  have hprefix :=
    runtimeKeyComparatorMachine_computes_common_unary_prefix
      0 queryState 0 (rowExtra + 1)
      queryRead rowRead actionSuffix
  have hfinish :=
    runtimeKeyComparatorMachine_computes_query_shorter_finish
      queryState rowExtra queryRead rowRead actionSuffix
  have htarget :
      runtimeKeyComparatorRestoredLeft
          (List.replicate queryState MachineCodeSymbol.blank)
          queryRead
          (List.append
            (List.replicate queryState MachineCodeSymbol.blank)
            (List.replicate (rowExtra + 1) MachineCodeSymbol.tick))
          rowRead [MachineCodeSymbol.header] =
        runtimeKeyComparatorRestoredLeft
          (List.replicate queryState MachineCodeSymbol.tick)
          queryRead
          (List.replicate (queryState + (rowExtra + 1))
            MachineCodeSymbol.tick)
          rowRead [MachineCodeSymbol.header] := by
    rw [replicate_add_eq_append]
    simp [runtimeKeyComparatorRestoredLeft]
    rw [Nat.add_comm rowExtra queryState]
    rw [show queryState + (rowExtra + 1) =
      (queryState + rowExtra) + 1 by simp [Nat.add_assoc]]
    rw [List.replicate_succ]
    rfl
    done
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorComparedBody,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hprefix)
      (by
        rw [← htarget]
        simpa [runtimeKeyComparatorComparedBody]
          using hfinish)
  done

theorem runtimeKeyComparatorMachine_computes_scan_row_done_miss_and_rewind
    (leftSymbols : Word MachineCodeSymbol)
    (hleftSymbols :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol leftSymbols ->
          symbol ≠ MachineCodeSymbol.header)
    (hleftSymbolsNonempty : leftSymbols ≠ [])
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanRow
        tape :=
          runtimeKeyComparatorTape
            (List.append leftSymbols [MachineCodeSymbol.header])
            (MachineCodeSymbol.done :: suffix) }
      { state :=
          RuntimeKeyComparatorState.restoreQuery
            RuntimeKeyComparatorOutcome.isMiss
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (List.append leftSymbols.reverse
              (MachineCodeSymbol.done :: suffix)) } := by
  cases leftSymbols with
  | nil =>
      exact False.elim (hleftSymbolsNonempty rfl)
  | cons leftHead leftTail =>
      have hleftHead : leftHead ≠ MachineCodeSymbol.header :=
        hleftSymbols leftHead (List.Mem.head leftTail)
      have hleftTail :
          forall symbol : MachineCodeSymbol,
            List.Mem symbol leftTail ->
              symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hleftSymbols symbol (List.Mem.tail leftHead hmem)
      have hstep :=
        runtimeKeyComparatorMachine_step_scan_row_done_miss
          leftHead (List.append leftTail [MachineCodeSymbol.header])
          suffix
      have hrewind :=
        runtimeKeyComparatorMachine_computes_rewind_outcome_to_header
          RuntimeKeyComparatorOutcome.isMiss
          leftTail hleftTail leftHead hleftHead
          (MachineCodeSymbol.done :: suffix)
      exact
        TuringMachine.Computes.step
          (by simpa using hstep)
          (by
            simpa [List.reverse_cons, List.append_assoc]
              using hrewind)
  done

theorem runtimeKeyComparatorMachine_computes_row_shorter_finish
    (marked queryExtra : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorComparedBody marked (queryExtra + 1) 0
              queryRead rowRead actionSuffix) }
      { state := RuntimeKeyComparatorState.missed
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.append
                (List.replicate marked MachineCodeSymbol.blank)
                (List.replicate (queryExtra + 1)
                  MachineCodeSymbol.tick))
              queryRead
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
      MachineCodeSymbol.transition :: rowSource
  let queryMarkedLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.blank ::
      List.append queryMarked.reverse [MachineCodeSymbol.header]
  let queryTailLeft : Word MachineCodeSymbol :=
    List.append queryTail.reverse queryMarkedLeft
  let queryDoneLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.done :: queryTailLeft
  let queryReadLeft : Word MachineCodeSymbol :=
    runtimeKeyCellSymbol queryRead :: queryDoneLeft
  let transitionLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.transition :: queryReadLeft
  let comparisonPrefix : Word MachineCodeSymbol :=
    runtimeKeyComparatorComparisonPrefix
      queryCells queryRead rowCells
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
  have hprefix :=
    runtimeKeyComparatorComparisonPrefix_no_header
      queryCells hqueryCells queryRead rowCells hrowCells
  have hprefixNonempty : comparisonPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [comparisonPrefix,
      runtimeKeyComparatorComparisonPrefix] at hlen
  have hqueryMarks :=
    runtimeKeyComparatorMachine_computes_scan_query_blanks
      marked [MachineCodeSymbol.header]
      (MachineCodeSymbol.tick :: List.append queryTail afterQuery)
  have hqueryMark :=
    runtimeKeyComparatorMachine_step_mark_query_tick
      (List.append queryMarked.reverse [MachineCodeSymbol.header])
      (List.append queryTail afterQuery)
  have hqueryTail :=
    runtimeKeyComparatorMachine_computes_seek_query_ticks
      queryExtra queryMarkedLeft afterQuery
  have hqueryDone :=
    runtimeKeyComparatorMachine_step_seek_query_done
      queryTailLeft
      (runtimeKeyCellSymbol queryRead ::
        MachineCodeSymbol.transition :: rowSource)
  have hqueryRead :=
    runtimeKeyComparatorMachine_step_skip_query_read
      queryRead queryDoneLeft
      (MachineCodeSymbol.transition :: rowSource)
  have htransition :=
    runtimeKeyComparatorMachine_step_need_transition
      queryReadLeft rowSource
  have hrow :=
    runtimeKeyComparatorMachine_computes_scan_row_blanks
      marked transitionLeft afterRow
  have hmissRewind :=
    runtimeKeyComparatorMachine_computes_scan_row_done_miss_and_rewind
      comparisonPrefix hprefix hprefixNonempty
      (runtimeKeyCellSymbol rowRead :: actionSuffix)
  have hrestore :=
    runtimeKeyComparatorMachine_computes_restore_outcome_exact
      RuntimeKeyComparatorOutcome.isMiss
      queryCells hqueryCells queryRead
      rowCells hrowCells rowRead
      [MachineCodeSymbol.header] actionSuffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorComparedBody,
          runtimeKeyComparatorBody, queryMarked,
          queryTail, queryCells, rowCells,
          afterRow, rowSource, afterQuery,
          List.replicate_succ,
          List.append_assoc]
          using hqueryMarks)
      (TuringMachine.Computes.step
        (by
          simpa [queryMarked, queryTail, rowCells,
            afterRow, rowSource, afterQuery,
            queryMarkedLeft, List.append_assoc]
            using hqueryMark)
        (TuringMachine.computes_trans
          (by
            simpa [queryMarked, queryTail, rowCells,
              afterRow, rowSource, afterQuery,
              queryMarkedLeft, queryTailLeft,
              List.append_assoc]
              using hqueryTail)
          (TuringMachine.Computes.step
            (by
              simpa [queryMarked, queryTail,
                queryMarkedLeft, queryTailLeft,
                queryDoneLeft, rowCells, afterRow,
                rowSource, List.append_assoc]
                using hqueryDone)
            (TuringMachine.Computes.step
              (by
                simpa [queryMarked, queryTail,
                  queryMarkedLeft, queryTailLeft,
                  queryDoneLeft, queryReadLeft,
                  rowCells, afterRow, rowSource,
                  List.append_assoc]
                  using hqueryRead)
              (TuringMachine.Computes.step
                (by
                  simpa [queryMarked, queryTail,
                    queryMarkedLeft, queryTailLeft,
                    queryDoneLeft, queryReadLeft,
                    transitionLeft, rowCells,
                    afterRow, rowSource,
                    List.append_assoc]
                    using htransition)
                (TuringMachine.computes_trans
                  (by
                    simpa [queryMarked, queryTail,
                      queryMarkedLeft, queryTailLeft,
                      queryDoneLeft, queryReadLeft,
                      transitionLeft, rowCells,
                      afterRow, rowSource,
                      List.append_assoc]
                      using hrow)
                  (TuringMachine.computes_trans
                    (by
                      simpa [comparisonPrefix,
                        runtimeKeyComparatorComparisonPrefix,
                        queryMarked, queryTail,
                        queryCells, rowCells,
                        queryMarkedLeft, queryTailLeft,
                        queryDoneLeft, queryReadLeft,
                        transitionLeft,
                        List.reverse_append,
                        List.reverse_cons,
                        List.reverse_reverse,
                        List.reverse_replicate,
                        List.append_assoc]
                        using hmissRewind)
                    (by
                      simpa [queryMarked, queryTail,
                        queryCells, rowCells,
                        runtimeKeyComparatorBody,
                        runtimeKeyComparatorOutcomeState,
                        runtimeKeyComparatorRestoredLeft,
                        List.replicate_succ,
                        List.append_assoc]
                        using hrestore))))))))
  done

theorem runtimeKeyComparatorMachine_computes_row_shorter
    (rowState queryExtra : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorBody
              (List.replicate (rowState + (queryExtra + 1))
                MachineCodeSymbol.tick)
              queryRead
              (List.replicate rowState MachineCodeSymbol.tick)
              rowRead actionSuffix) }
      { state := RuntimeKeyComparatorState.missed
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.replicate (rowState + (queryExtra + 1))
                MachineCodeSymbol.tick)
              queryRead
              (List.replicate rowState MachineCodeSymbol.tick)
              rowRead [MachineCodeSymbol.header])
            actionSuffix } := by
  have hprefix :=
    runtimeKeyComparatorMachine_computes_common_unary_prefix
      0 rowState (queryExtra + 1) 0
      queryRead rowRead actionSuffix
  have hfinish :=
    runtimeKeyComparatorMachine_computes_row_shorter_finish
      rowState queryExtra queryRead rowRead actionSuffix
  have htarget :
      runtimeKeyComparatorRestoredLeft
          (List.append
            (List.replicate rowState MachineCodeSymbol.blank)
            (List.replicate (queryExtra + 1) MachineCodeSymbol.tick))
          queryRead
          (List.replicate rowState MachineCodeSymbol.blank)
          rowRead [MachineCodeSymbol.header] =
        runtimeKeyComparatorRestoredLeft
          (List.replicate (rowState + (queryExtra + 1))
            MachineCodeSymbol.tick)
          queryRead
          (List.replicate rowState MachineCodeSymbol.tick)
          rowRead [MachineCodeSymbol.header] := by
    rw [replicate_add_eq_append]
    simp [runtimeKeyComparatorRestoredLeft]
    rw [Nat.add_comm queryExtra rowState]
    rw [show rowState + (queryExtra + 1) =
      (rowState + queryExtra) + 1 by simp [Nat.add_assoc]]
    rw [List.replicate_succ]
    rfl
    done
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorComparedBody,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hprefix)
      (by
        rw [← htarget]
        simpa [runtimeKeyComparatorComparedBody]
          using hfinish)
  done

theorem runtimeKeyComparatorMachine_computes_one_row_exact
    (queryState : Nat) (queryRead : Option Bool)
    (rowState : Nat) (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorBody
              (List.replicate queryState MachineCodeSymbol.tick)
              queryRead
              (List.replicate rowState MachineCodeSymbol.tick)
              rowRead actionSuffix) }
      { state :=
          runtimeKeyComparatorOutcomeState
            (runtimeKeyComparatorRowOutcome
              queryState queryRead rowState rowRead)
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.replicate queryState MachineCodeSymbol.tick)
              queryRead
              (List.replicate rowState MachineCodeSymbol.tick)
              rowRead [MachineCodeSymbol.header])
            actionSuffix } := by
  rcases Nat.lt_trichotomy queryState rowState with
    hshort | hequal | hlong
  · rcases Nat.exists_eq_add_of_lt hshort with
      ⟨rowExtra, hrowState⟩
    subst rowState
    simpa [runtimeKeyComparatorRowOutcome,
      runtimeKeyComparatorOutcomeState,
      Nat.add_assoc] using
        runtimeKeyComparatorMachine_computes_query_shorter
          queryState rowExtra queryRead rowRead actionSuffix
  · subst rowState
    simpa [runtimeKeyComparatorRowOutcome] using
      runtimeKeyComparatorMachine_computes_equal_state
        queryState queryRead rowRead actionSuffix
  · rcases Nat.exists_eq_add_of_lt hlong with
      ⟨queryExtra, hqueryState⟩
    subst queryState
    simpa [runtimeKeyComparatorRowOutcome,
      runtimeKeyComparatorOutcomeState,
      Nat.add_assoc] using
        runtimeKeyComparatorMachine_computes_row_shorter
          rowState queryExtra queryRead rowRead actionSuffix
  done

theorem runtimeKeyComparatorMachine_computes_one_row_from_header
    (queryState : Nat) (queryRead : Option Bool)
    (rowState : Nat) (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.needHeader
        tape :=
          runtimeKeyComparatorTape []
            (MachineCodeSymbol.header ::
              runtimeKeyComparatorBody
                (List.replicate queryState MachineCodeSymbol.tick)
                queryRead
                (List.replicate rowState MachineCodeSymbol.tick)
                rowRead actionSuffix) }
      { state :=
          runtimeKeyComparatorOutcomeState
            (runtimeKeyComparatorRowOutcome
              queryState queryRead rowState rowRead)
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.replicate queryState MachineCodeSymbol.tick)
              queryRead
              (List.replicate rowState MachineCodeSymbol.tick)
              rowRead [MachineCodeSymbol.header])
            actionSuffix } := by
  exact
    TuringMachine.Computes.step
      (runtimeKeyComparatorMachine_step_header
        (runtimeKeyComparatorBody
          (List.replicate queryState MachineCodeSymbol.tick)
          queryRead
          (List.replicate rowState MachineCodeSymbol.tick)
          rowRead actionSuffix))
      (runtimeKeyComparatorMachine_computes_one_row_exact
        queryState queryRead rowState rowRead actionSuffix)
  done

end FiniteRecognizer.Interpreter.UniformInterpreterOneStep
end Computability
end FoC
