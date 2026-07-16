import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup.Core

namespace FoC
namespace Computability

open Languages

namespace Section53UniformInterpreterOneStep

theorem runtimeKeyComparatorMachine_step_rewind_symbol
    (leftHead current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.rewind
        tape :=
          runtimeKeyComparatorTape (leftHead :: leftTail)
            (current :: suffix) }
      { state := RuntimeKeyComparatorState.rewind
        tape :=
          runtimeKeyComparatorTape leftTail
            (leftHead :: current :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead current current]
  exact TuringMachine.Step.mk (by
    cases current <;>
      simp [runtimeKeyComparatorMachine,
        runtimeKeyComparatorTape, Tape.read] at hcurrent ⊢)

theorem runtimeKeyComparatorMachine_computes_rewind_to_header
    (leftSymbols : Word MachineCodeSymbol)
    (hleftSymbols :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol leftSymbols ->
          symbol ≠ MachineCodeSymbol.header)
    (current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.rewind
        tape :=
          runtimeKeyComparatorTape
            (List.append leftSymbols [MachineCodeSymbol.header])
            (current :: suffix) }
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (List.append leftSymbols.reverse (current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      have hsymbol :=
        runtimeKeyComparatorMachine_step_rewind_symbol
          MachineCodeSymbol.header current hcurrent [] suffix
      have hheader :
          TuringMachine.Step runtimeKeyComparatorMachine
            { state := RuntimeKeyComparatorState.rewind
              tape :=
                runtimeKeyComparatorTape []
                  (MachineCodeSymbol.header :: current :: suffix) }
            { state := RuntimeKeyComparatorState.scanQuery
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
        runtimeKeyComparatorMachine_step_rewind_symbol
          leftHead current hcurrent
          (List.append leftTail [MachineCodeSymbol.header]) suffix
      have hrest :=
        ih hleftTail leftHead hleftHead (current :: suffix)
      exact
        TuringMachine.Computes.step
          (by simpa using hstep)
          (by
            simpa [List.reverse_cons, List.append_assoc]
              using hrest)

theorem runtimeKeyComparatorMachine_computes_scan_query_blanks
    (marked : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape leftRev
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              suffix) }
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape
            (List.append
              (List.replicate marked MachineCodeSymbol.blank).reverse
              leftRev)
            suffix } := by
  induction marked generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ marked ih =>
      have hstep :
          TuringMachine.Step runtimeKeyComparatorMachine
            { state := RuntimeKeyComparatorState.scanQuery
              tape :=
                runtimeKeyComparatorTape leftRev
                  (MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate marked MachineCodeSymbol.blank)
                      suffix) }
            { state := RuntimeKeyComparatorState.scanQuery
              tape :=
                runtimeKeyComparatorTape
                  (MachineCodeSymbol.blank :: leftRev)
                  (List.append
                    (List.replicate marked MachineCodeSymbol.blank)
                    suffix) } := by
        rw [← runtimeKeyComparatorTape_move_right leftRev
          MachineCodeSymbol.blank MachineCodeSymbol.blank
          (List.append
            (List.replicate marked MachineCodeSymbol.blank)
            suffix)]
        exact TuringMachine.Step.mk (by
          simp [runtimeKeyComparatorMachine,
            runtimeKeyComparatorTape, Tape.read])
      have hrest := ih (MachineCodeSymbol.blank :: leftRev)
      exact
        TuringMachine.Computes.step
          (by simpa [List.replicate_succ] using hstep)
          (by
            simpa [List.replicate_succ, List.reverse_cons,
              List.append_assoc]
              using hrest)

theorem runtimeKeyComparatorMachine_step_mark_query_tick
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := RuntimeKeyComparatorState.seekQueryEnd
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.blank :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.tick MachineCodeSymbol.blank suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_computes_seek_query_ticks
    (remaining : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.seekQueryEnd
        tape :=
          runtimeKeyComparatorTape leftRev
            (List.append
              (List.replicate remaining MachineCodeSymbol.tick)
              suffix) }
      { state := RuntimeKeyComparatorState.seekQueryEnd
        tape :=
          runtimeKeyComparatorTape
            (List.append
              (List.replicate remaining MachineCodeSymbol.tick).reverse
              leftRev)
            suffix } := by
  induction remaining generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ remaining ih =>
      have hstep :
          TuringMachine.Step runtimeKeyComparatorMachine
            { state := RuntimeKeyComparatorState.seekQueryEnd
              tape :=
                runtimeKeyComparatorTape leftRev
                  (MachineCodeSymbol.tick ::
                    List.append
                      (List.replicate remaining MachineCodeSymbol.tick)
                      suffix) }
            { state := RuntimeKeyComparatorState.seekQueryEnd
              tape :=
                runtimeKeyComparatorTape
                  (MachineCodeSymbol.tick :: leftRev)
                  (List.append
                    (List.replicate remaining MachineCodeSymbol.tick)
                    suffix) } := by
        rw [← runtimeKeyComparatorTape_move_right leftRev
          MachineCodeSymbol.tick MachineCodeSymbol.tick
          (List.append
            (List.replicate remaining MachineCodeSymbol.tick)
            suffix)]
        exact TuringMachine.Step.mk (by
          simp [runtimeKeyComparatorMachine,
            runtimeKeyComparatorTape, Tape.read])
      have hrest := ih (MachineCodeSymbol.tick :: leftRev)
      exact
        TuringMachine.Computes.step
          (by simpa [List.replicate_succ] using hstep)
          (by
            simpa [List.replicate_succ, List.reverse_cons,
              List.append_assoc]
              using hrest)

theorem runtimeKeyComparatorMachine_step_seek_query_done
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.seekQueryEnd
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := RuntimeKeyComparatorState.skipQueryRead
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.done MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_step_skip_query_read
    (read : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.skipQueryRead
        tape :=
          runtimeKeyComparatorTape leftRev
            (runtimeKeyCellSymbol read :: suffix) }
      { state := RuntimeKeyComparatorState.needTransition
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyCellSymbol read :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    (runtimeKeyCellSymbol read) (runtimeKeyCellSymbol read) suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_step_need_transition
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.needTransition
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.transition :: suffix) }
      { state := RuntimeKeyComparatorState.scanRow
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.transition :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.transition MachineCodeSymbol.transition suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_computes_scan_row_blanks
    (marked : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanRow
        tape :=
          runtimeKeyComparatorTape leftRev
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              suffix) }
      { state := RuntimeKeyComparatorState.scanRow
        tape :=
          runtimeKeyComparatorTape
            (List.append
              (List.replicate marked MachineCodeSymbol.blank).reverse
              leftRev)
            suffix } := by
  induction marked generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ marked ih =>
      have hstep :
          TuringMachine.Step runtimeKeyComparatorMachine
            { state := RuntimeKeyComparatorState.scanRow
              tape :=
                runtimeKeyComparatorTape leftRev
                  (MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate marked MachineCodeSymbol.blank)
                      suffix) }
            { state := RuntimeKeyComparatorState.scanRow
              tape :=
                runtimeKeyComparatorTape
                  (MachineCodeSymbol.blank :: leftRev)
                  (List.append
                    (List.replicate marked MachineCodeSymbol.blank)
                    suffix) } := by
        rw [← runtimeKeyComparatorTape_move_right leftRev
          MachineCodeSymbol.blank MachineCodeSymbol.blank
          (List.append
            (List.replicate marked MachineCodeSymbol.blank)
            suffix)]
        exact TuringMachine.Step.mk (by
          simp [runtimeKeyComparatorMachine,
            runtimeKeyComparatorTape, Tape.read])
      have hrest := ih (MachineCodeSymbol.blank :: leftRev)
      exact
        TuringMachine.Computes.step
          (by simpa [List.replicate_succ] using hstep)
          (by
            simpa [List.replicate_succ, List.reverse_cons,
              List.append_assoc]
              using hrest)

theorem runtimeKeyComparatorMachine_step_mark_row_tick
    (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanRow
        tape :=
          runtimeKeyComparatorTape (leftHead :: leftTail)
            (MachineCodeSymbol.tick :: suffix) }
      { state := RuntimeKeyComparatorState.rewind
        tape :=
          runtimeKeyComparatorTape leftTail
            (leftHead :: MachineCodeSymbol.blank :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead MachineCodeSymbol.tick MachineCodeSymbol.blank]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])

theorem runtimeKeyComparatorMachine_computes_mark_row_tick_and_rewind
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
            (MachineCodeSymbol.tick :: suffix) }
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (List.append leftSymbols.reverse
              (MachineCodeSymbol.blank :: suffix)) } := by
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
      have hmark :=
        runtimeKeyComparatorMachine_step_mark_row_tick
          leftHead (List.append leftTail [MachineCodeSymbol.header])
          suffix
      have hrewind :=
        runtimeKeyComparatorMachine_computes_rewind_to_header
          leftTail hleftTail leftHead hleftHead
          (MachineCodeSymbol.blank :: suffix)
      exact
        TuringMachine.Computes.step
          (by simpa using hmark)
          (by
            simpa [List.reverse_cons, List.append_assoc]
              using hrewind)

theorem runtimeKeyComparatorMachine_computes_paired_tick_cycle
    (marked queryRemaining : Nat)
    (queryRead : Option Bool)
    (rowRemaining : Nat)
    (rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorCycleSource marked queryRemaining
              queryRead rowRemaining rowRead actionSuffix) }
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorCycleTarget marked queryRemaining
              queryRead rowRemaining rowRead actionSuffix) } := by
  let queryMarks : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let queryTail : Word MachineCodeSymbol :=
    List.replicate queryRemaining MachineCodeSymbol.tick
  let rowMarks : Word MachineCodeSymbol :=
    List.replicate marked MachineCodeSymbol.blank
  let rowTail : Word MachineCodeSymbol :=
    List.replicate rowRemaining MachineCodeSymbol.tick
  let afterRow : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      runtimeKeyCellSymbol rowRead :: actionSuffix
  let rowSource : Word MachineCodeSymbol :=
    List.append rowMarks
      (MachineCodeSymbol.tick :: List.append rowTail afterRow)
  let afterQuery : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      runtimeKeyCellSymbol queryRead ::
      MachineCodeSymbol.transition :: rowSource
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
  let transitionLeft : Word MachineCodeSymbol :=
    MachineCodeSymbol.transition :: queryReadLeft
  let rowPrefix : Word MachineCodeSymbol :=
    List.append rowMarks.reverse
      (MachineCodeSymbol.transition ::
        runtimeKeyCellSymbol queryRead ::
        MachineCodeSymbol.done ::
        List.append queryTail.reverse queryMarkedBody)
  have hrowPrefixNoHeader :
      forall symbol : MachineCodeSymbol,
        List.Mem symbol rowPrefix ->
          symbol ≠ MachineCodeSymbol.header := by
    intro symbol hmem hsymbol
    subst symbol
    simp only [rowPrefix, rowMarks, queryTail,
      queryMarkedBody, queryMarks, List.reverse_replicate] at hmem
    rcases List.mem_append.mp hmem with hrowMark | hrest
    · have heq := (List.mem_replicate.mp hrowMark).2
      cases heq
    · rcases List.mem_cons.mp hrest with heq | hrest
      · cases heq
      · rcases List.mem_cons.mp hrest with heq | hrest
        · cases queryRead with
          | none => cases heq
          | some bit => cases bit <;> cases heq
        · rcases List.mem_cons.mp hrest with heq | hrest
          · cases heq
          · rcases List.mem_append.mp hrest with hqueryTick | hrest
            · have heq := (List.mem_replicate.mp hqueryTick).2
              cases heq
            · rcases List.mem_cons.mp hrest with heq | hqueryMark
              · cases heq
              · have heq := (List.mem_replicate.mp hqueryMark).2
                cases heq
  have hrowPrefixNonempty : rowPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [rowPrefix] at hlen
  have hqueryMarks :=
    runtimeKeyComparatorMachine_computes_scan_query_blanks
      marked [MachineCodeSymbol.header]
      (MachineCodeSymbol.tick :: List.append queryTail afterQuery)
  have hqueryMark :=
    runtimeKeyComparatorMachine_step_mark_query_tick
      (List.append queryMarks.reverse [MachineCodeSymbol.header])
      (List.append queryTail afterQuery)
  have hqueryTail :=
    runtimeKeyComparatorMachine_computes_seek_query_ticks
      queryRemaining queryMarkedLeft afterQuery
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
  have hrowMarks :=
    runtimeKeyComparatorMachine_computes_scan_row_blanks
      marked transitionLeft
      (MachineCodeSymbol.tick :: List.append rowTail afterRow)
  have hrowMarkRewind :=
    runtimeKeyComparatorMachine_computes_mark_row_tick_and_rewind
      rowPrefix hrowPrefixNoHeader hrowPrefixNonempty
      (List.append rowTail afterRow)
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorCycleSource, queryMarks,
          queryTail, rowMarks, rowTail, afterRow, rowSource,
          afterQuery]
          using hqueryMarks)
      (TuringMachine.Computes.step
        (by
          simpa [queryMarks, queryTail, rowMarks, rowTail,
            afterRow, rowSource, afterQuery,
            queryMarkedBody, queryMarkedLeft,
            List.append_assoc]
            using hqueryMark)
        (TuringMachine.computes_trans
          (by
            simpa [queryMarks, queryTail, rowMarks, rowTail,
              afterRow, rowSource, afterQuery, queryMarkedBody,
              queryMarkedLeft, queryTailLeft,
              List.append_assoc]
              using hqueryTail)
          (TuringMachine.Computes.step
            (by
              simpa [queryMarks, queryTail, rowMarks, rowTail,
                afterRow, rowSource, afterQuery,
                queryMarkedBody, queryMarkedLeft,
                queryTailLeft, queryDoneLeft,
                List.append_assoc]
                using hqueryDone)
            (TuringMachine.Computes.step
              (by
                simpa [queryMarks, queryTail, rowMarks, rowTail,
                  afterRow, rowSource, queryMarkedBody,
                  queryMarkedLeft, queryTailLeft,
                  queryDoneLeft, queryReadLeft,
                  List.append_assoc]
                  using hqueryRead)
              (TuringMachine.Computes.step
                (by
                  simpa [queryMarks, queryTail, rowMarks, rowTail,
                    afterRow, rowSource, queryMarkedBody,
                    queryMarkedLeft, queryTailLeft,
                    queryDoneLeft, queryReadLeft,
                    transitionLeft, List.append_assoc]
                    using htransition)
                (TuringMachine.computes_trans
                  (by
                    simpa [queryMarks, queryTail, rowMarks,
                      rowTail, afterRow, rowSource,
                      queryMarkedBody, queryMarkedLeft,
                      queryTailLeft, queryDoneLeft,
                      queryReadLeft, transitionLeft,
                      List.append_assoc]
                      using hrowMarks)
                  (by
                    simpa [runtimeKeyComparatorCycleTarget,
                      rowPrefix, transitionLeft, queryReadLeft,
                      queryDoneLeft, queryTailLeft, queryTail,
                      queryMarkedLeft, queryMarkedBody,
                      queryMarks, rowMarks,
                      rowTail, afterRow, rowSource, afterQuery,
                      List.reverse_append, List.reverse_cons,
                      List.reverse_reverse, List.reverse_replicate,
                      List.append_assoc]
                      using hrowMarkRewind)))))))

theorem runtimeKeyComparatorMachine_computes_paired_body_cycle
    (marked remaining : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorPairedBody marked (remaining + 1)
              queryRead rowRead actionSuffix) }
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorPairedBody (marked + 1) remaining
              queryRead rowRead actionSuffix) } := by
  have hsource :
      runtimeKeyComparatorCycleSource marked remaining queryRead
          remaining rowRead actionSuffix =
        runtimeKeyComparatorPairedBody marked (remaining + 1)
          queryRead rowRead actionSuffix := by
    simp only [runtimeKeyComparatorCycleSource,
      runtimeKeyComparatorPairedBody, runtimeKeyComparatorBody,
      replicate_succ_eq_append_singleton,
      cons_replicate_append_eq_replicate_append_cons]
    simp [List.append_assoc]
    done
  have htarget :
      runtimeKeyComparatorCycleTarget marked remaining queryRead
          remaining rowRead actionSuffix =
        runtimeKeyComparatorPairedBody (marked + 1) remaining
          queryRead rowRead actionSuffix := by
    simp only [runtimeKeyComparatorCycleTarget,
      runtimeKeyComparatorPairedBody, runtimeKeyComparatorBody,
      replicate_succ_eq_append_singleton]
    simp [List.append_assoc]
    done
  rw [← hsource, ← htarget]
  exact
    runtimeKeyComparatorMachine_computes_paired_tick_cycle
      marked remaining queryRead remaining rowRead actionSuffix
  done

theorem runtimeKeyComparatorMachine_computes_equal_unary_prefixes
    (marked remaining : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorPairedBody marked remaining
              queryRead rowRead actionSuffix) }
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorPairedBody (marked + remaining) 0
              queryRead rowRead actionSuffix) } := by
  induction remaining generalizing marked with
  | zero =>
      simpa using TuringMachine.Computes.refl
        ({ state := RuntimeKeyComparatorState.scanQuery
           tape :=
             runtimeKeyComparatorTape [MachineCodeSymbol.header]
               (runtimeKeyComparatorPairedBody marked 0
                 queryRead rowRead actionSuffix) } :
          TuringMachine.Configuration MachineCodeSymbol
            RuntimeKeyComparatorState)
  | succ remaining ih =>
      have hcycle :=
        runtimeKeyComparatorMachine_computes_paired_body_cycle
          marked remaining queryRead rowRead actionSuffix
      have hrest := ih (marked + 1)
      exact
        TuringMachine.computes_trans hcycle
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using hrest)
      done

theorem runtimeKeyComparatorCycleSource_eq_comparedBody
    (marked queryRemaining rowRemaining : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    runtimeKeyComparatorCycleSource marked queryRemaining queryRead
        rowRemaining rowRead actionSuffix =
      runtimeKeyComparatorComparedBody marked
        (queryRemaining + 1) (rowRemaining + 1)
        queryRead rowRead actionSuffix := by
  simp only [runtimeKeyComparatorCycleSource,
    runtimeKeyComparatorComparedBody, runtimeKeyComparatorBody,
    replicate_succ_eq_append_singleton,
    cons_replicate_append_eq_replicate_append_cons]
  simp [List.append_assoc]
  done

theorem runtimeKeyComparatorCycleTarget_eq_comparedBody
    (marked queryRemaining rowRemaining : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    runtimeKeyComparatorCycleTarget marked queryRemaining queryRead
        rowRemaining rowRead actionSuffix =
      runtimeKeyComparatorComparedBody (marked + 1)
        queryRemaining rowRemaining queryRead rowRead actionSuffix := by
  simp only [runtimeKeyComparatorCycleTarget,
    runtimeKeyComparatorComparedBody, runtimeKeyComparatorBody,
    replicate_succ_eq_append_singleton]
  simp [List.append_assoc]
  done

theorem runtimeKeyComparatorMachine_computes_compared_body_cycle
    (marked queryRemaining rowRemaining : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorComparedBody marked
              (queryRemaining + 1) (rowRemaining + 1)
              queryRead rowRead actionSuffix) }
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorComparedBody (marked + 1)
              queryRemaining rowRemaining
              queryRead rowRead actionSuffix) } := by
  rw [← runtimeKeyComparatorCycleSource_eq_comparedBody,
    ← runtimeKeyComparatorCycleTarget_eq_comparedBody]
  exact
    runtimeKeyComparatorMachine_computes_paired_tick_cycle
      marked queryRemaining queryRead rowRemaining rowRead actionSuffix
  done

theorem runtimeKeyComparatorMachine_computes_common_unary_prefix
    (marked common queryExtra rowExtra : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorComparedBody marked
              (queryExtra + common) (rowExtra + common)
              queryRead rowRead actionSuffix) }

      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorComparedBody (marked + common)
              queryExtra rowExtra queryRead rowRead actionSuffix) } := by
  induction common generalizing marked with
  | zero =>
      simpa using TuringMachine.Computes.refl
        ({ state := RuntimeKeyComparatorState.scanQuery
           tape :=
             runtimeKeyComparatorTape [MachineCodeSymbol.header]
               (runtimeKeyComparatorComparedBody marked
                 queryExtra rowExtra queryRead rowRead actionSuffix) } :
          TuringMachine.Configuration MachineCodeSymbol
            RuntimeKeyComparatorState)
  | succ common ih =>
      have hcycle :=
        runtimeKeyComparatorMachine_computes_compared_body_cycle
          marked (queryExtra + common) (rowExtra + common)
          queryRead rowRead actionSuffix
      have hrest := ih (marked + 1)
      exact
        TuringMachine.computes_trans
          (by
            simpa [Nat.add_assoc] using hcycle)
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using hrest)
      done

theorem runtimeKeyComparatorMachine_step_scan_query_done
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := RuntimeKeyComparatorState.rememberQueryRead
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.done MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])
  done

theorem runtimeKeyComparatorMachine_step_remember_query_read
    (read : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.rememberQueryRead
        tape :=
          runtimeKeyComparatorTape leftRev
            (runtimeKeyCellSymbol read :: suffix) }
      { state := RuntimeKeyComparatorState.finishNeedTransition read
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyCellSymbol read :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    (runtimeKeyCellSymbol read) (runtimeKeyCellSymbol read) suffix]
  cases read with
  | none =>
      exact TuringMachine.Step.mk (by
        simp [runtimeKeyComparatorMachine, runtimeKeyCellSymbol,
          runtimeKeyComparatorTape, Tape.read])
  | some bit =>
      cases bit <;>
        exact TuringMachine.Step.mk (by
          simp [runtimeKeyComparatorMachine, runtimeKeyCellSymbol,
          runtimeKeyComparatorTape, Tape.read])
  done

theorem runtimeKeyComparatorMachine_step_finish_transition
    (read : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.finishNeedTransition read
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.transition :: suffix) }
      { state := RuntimeKeyComparatorState.finishScanRow read
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.transition :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.transition MachineCodeSymbol.transition suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])
  done

theorem runtimeKeyComparatorMachine_computes_finish_row_blanks
    (read : Option Bool)
    (marked : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.finishScanRow read
        tape :=
          runtimeKeyComparatorTape leftRev
            (List.append
              (List.replicate marked MachineCodeSymbol.blank)
              suffix) }
      { state := RuntimeKeyComparatorState.finishScanRow read
        tape :=
          runtimeKeyComparatorTape
            (List.append
              (List.replicate marked MachineCodeSymbol.blank).reverse
              leftRev)
            suffix } := by
  induction marked generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ marked ih =>
      have hstep :
          TuringMachine.Step runtimeKeyComparatorMachine
            { state := RuntimeKeyComparatorState.finishScanRow read
              tape :=
                runtimeKeyComparatorTape leftRev
                  (MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate marked MachineCodeSymbol.blank)
                      suffix) }
            { state := RuntimeKeyComparatorState.finishScanRow read
              tape :=
                runtimeKeyComparatorTape
                  (MachineCodeSymbol.blank :: leftRev)
                  (List.append
                    (List.replicate marked MachineCodeSymbol.blank)
                    suffix) } := by
        rw [← runtimeKeyComparatorTape_move_right leftRev
          MachineCodeSymbol.blank MachineCodeSymbol.blank
          (List.append
            (List.replicate marked MachineCodeSymbol.blank)
            suffix)]
        exact TuringMachine.Step.mk (by
          simp [runtimeKeyComparatorMachine,
            runtimeKeyComparatorTape, Tape.read])
      have hrest := ih (MachineCodeSymbol.blank :: leftRev)
      exact
        TuringMachine.Computes.step
          (by simpa [List.replicate_succ] using hstep)
          (by
            simpa [List.replicate_succ, List.reverse_cons,
              List.append_assoc]
              using hrest)
  done

theorem runtimeKeyComparatorMachine_step_finish_row_tick_miss
    (read : Option Bool)
    (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.finishScanRow read
        tape :=
          runtimeKeyComparatorTape (leftHead :: leftTail)
            (MachineCodeSymbol.tick :: suffix) }
      { state :=
          RuntimeKeyComparatorState.rewindOutcome
            RuntimeKeyComparatorOutcome.isMiss
        tape :=
          runtimeKeyComparatorTape leftTail
            (leftHead :: MachineCodeSymbol.tick :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead MachineCodeSymbol.tick MachineCodeSymbol.tick]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])
  done

theorem runtimeKeyComparatorMachine_step_finish_row_done
    (read : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.finishScanRow read
        tape :=
          runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := RuntimeKeyComparatorState.compareRead read
        tape :=
          runtimeKeyComparatorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.done MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])
  done

theorem runtimeKeyComparatorMachine_step_scan_row_done_miss
    (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanRow
        tape :=
          runtimeKeyComparatorTape (leftHead :: leftTail)
            (MachineCodeSymbol.done :: suffix) }
      { state :=
          RuntimeKeyComparatorState.rewindOutcome
            RuntimeKeyComparatorOutcome.isMiss
        tape :=
          runtimeKeyComparatorTape leftTail
            (leftHead :: MachineCodeSymbol.done :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead MachineCodeSymbol.done MachineCodeSymbol.done]
  exact TuringMachine.Step.mk (by
    simp [runtimeKeyComparatorMachine,
      runtimeKeyComparatorTape, Tape.read])
  done

theorem runtimeKeyComparatorMachine_step_compare_read
    (queryRead rowRead : Option Bool)
    (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.compareRead queryRead
        tape :=
          runtimeKeyComparatorTape (leftHead :: leftTail)
            (runtimeKeyCellSymbol rowRead :: suffix) }
      { state :=
          RuntimeKeyComparatorState.rewindOutcome
            (runtimeKeyComparatorReadOutcome queryRead rowRead)
        tape :=
          runtimeKeyComparatorTape leftTail
            (leftHead :: runtimeKeyCellSymbol rowRead :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix leftHead
    (runtimeKeyCellSymbol rowRead) (runtimeKeyCellSymbol rowRead)]
  apply TuringMachine.Step.mk
  cases queryRead with
  | none =>
      cases rowRead with
      | none =>
          simp [runtimeKeyComparatorMachine,
            runtimeKeyComparatorReadOutcome, runtimeKeyCellSymbol,
            runtimeKeyComparatorTape, Tape.read]
      | some rowBit =>
          cases rowBit <;>
            simp [runtimeKeyComparatorMachine,
              runtimeKeyComparatorReadOutcome, runtimeKeyCellSymbol,
              runtimeKeyComparatorTape, Tape.read]
  | some queryBit =>
      cases queryBit with
      | false =>
          cases rowRead with
          | none =>
              simp [runtimeKeyComparatorMachine,
                runtimeKeyComparatorReadOutcome, runtimeKeyCellSymbol,
                runtimeKeyComparatorTape, Tape.read]
          | some rowBit =>
              cases rowBit <;>
                simp [runtimeKeyComparatorMachine,
                  runtimeKeyComparatorReadOutcome, runtimeKeyCellSymbol,
                  runtimeKeyComparatorTape, Tape.read]
      | true =>
          cases rowRead with
          | none =>
              simp [runtimeKeyComparatorMachine,
                runtimeKeyComparatorReadOutcome, runtimeKeyCellSymbol,
                runtimeKeyComparatorTape, Tape.read]
          | some rowBit =>
              cases rowBit <;>
                simp [runtimeKeyComparatorMachine,
                  runtimeKeyComparatorReadOutcome, runtimeKeyCellSymbol,
                  runtimeKeyComparatorTape, Tape.read]
  done

theorem runtimeKeyComparatorComparisonPrefix_no_header
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
            symbol = MachineCodeSymbol.tick) :
    forall symbol : MachineCodeSymbol,
      List.Mem symbol
          (runtimeKeyComparatorComparisonPrefix
            queryCells queryRead rowCells) ->
        symbol ≠ MachineCodeSymbol.header := by
  intro symbol hmem hsymbol
  subst symbol
  simp only [runtimeKeyComparatorComparisonPrefix] at hmem
  rcases List.mem_append.mp hmem with hrow | hrest
  · have hrow' := List.mem_reverse.mp hrow
    rcases hrowCells MachineCodeSymbol.header hrow' with
      hblank | htick
    · cases hblank
    · cases htick
  · rcases List.mem_cons.mp hrest with htransition | hrest
    · cases htransition
    · rcases List.mem_cons.mp hrest with hread | hrest
      · cases queryRead with
        | none => cases hread
        | some bit => cases bit <;> cases hread
      · rcases List.mem_cons.mp hrest with hdone | hquery
        · cases hdone
        · have hquery' := List.mem_reverse.mp hquery
          rcases hqueryCells MachineCodeSymbol.header hquery' with
            hblank | htick
          · cases hblank
          · cases htick
  done

theorem runtimeKeyComparatorMachine_computes_rewind_restore_exact
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
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.rewindOutcome outcome
        tape :=
          runtimeKeyComparatorTape
            (List.append
              (runtimeKeyComparatorComparisonPrefix
                queryCells queryRead rowCells)
              [MachineCodeSymbol.header])
            (MachineCodeSymbol.done ::
              runtimeKeyCellSymbol rowRead :: actionSuffix) }
      { state := runtimeKeyComparatorOutcomeState outcome
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft queryCells queryRead
              rowCells rowRead [MachineCodeSymbol.header])
            actionSuffix } := by
  have hprefix :=
    runtimeKeyComparatorComparisonPrefix_no_header
      queryCells hqueryCells queryRead rowCells hrowCells
  have hrewind :=
    runtimeKeyComparatorMachine_computes_rewind_outcome_to_header
      outcome
      (runtimeKeyComparatorComparisonPrefix
        queryCells queryRead rowCells)
      hprefix MachineCodeSymbol.done (by simp)
      (runtimeKeyCellSymbol rowRead :: actionSuffix)
  have hrestore :=
    runtimeKeyComparatorMachine_computes_restore_outcome_exact
      outcome queryCells hqueryCells queryRead
      rowCells hrowCells rowRead
      [MachineCodeSymbol.header] actionSuffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorComparisonPrefix,
          runtimeKeyComparatorBody,
          List.reverse_append, List.reverse_cons,
          List.reverse_reverse, List.append_assoc]
          using hrewind)
      hrestore
  done

theorem runtimeKeyComparatorMachine_computes_equal_state_finish
    (marked : Nat)
    (queryRead rowRead : Option Bool)
    (actionSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      { state := RuntimeKeyComparatorState.scanQuery
        tape :=
          runtimeKeyComparatorTape [MachineCodeSymbol.header]
            (runtimeKeyComparatorComparedBody marked 0 0
              queryRead rowRead actionSuffix) }
      { state :=
          runtimeKeyComparatorOutcomeState
            (runtimeKeyComparatorReadOutcome queryRead rowRead)
        tape :=
          runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.replicate marked MachineCodeSymbol.blank)
              queryRead
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
  let rowLeft : Word MachineCodeSymbol :=
    List.append rowCells.reverse transitionLeft
  let comparisonPrefix : Word MachineCodeSymbol :=
    runtimeKeyComparatorComparisonPrefix
      queryCells queryRead rowCells
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
      queryRead marked transitionLeft afterRow
  have hrowDone :=
    runtimeKeyComparatorMachine_step_finish_row_done
      queryRead rowLeft
      (runtimeKeyCellSymbol rowRead :: actionSuffix)
  have hcompare :=
    runtimeKeyComparatorMachine_step_compare_read
      queryRead rowRead MachineCodeSymbol.done
      (List.append comparisonPrefix [MachineCodeSymbol.header])
      actionSuffix
  have hrestore :=
    runtimeKeyComparatorMachine_computes_rewind_restore_exact
      (runtimeKeyComparatorReadOutcome queryRead rowRead)
      queryCells hqueryCells queryRead
      rowCells hrowCells rowRead actionSuffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [runtimeKeyComparatorComparedBody,
          runtimeKeyComparatorBody, queryCells, rowCells,
          afterRow, afterQuery]
          using hquery)
      (TuringMachine.Computes.step
        (by
          simpa [queryCells, queryLeft]
            using hqueryDone)
        (TuringMachine.Computes.step
          (by
            simpa [queryCells, queryLeft,
              queryDoneLeft, queryReadLeft]
              using hqueryRead)
          (TuringMachine.Computes.step
            (by
              simpa [queryCells, queryLeft,
                queryDoneLeft, queryReadLeft, transitionLeft]
                using htransition)
            (TuringMachine.computes_trans
              (by
                simpa [queryCells, rowCells, queryLeft,
                  queryDoneLeft, queryReadLeft,
                  transitionLeft, rowLeft, afterRow]
                  using hrow)
              (TuringMachine.Computes.step
                (by
                  simpa [rowLeft, comparisonPrefix,
                    runtimeKeyComparatorComparisonPrefix,
                    transitionLeft, queryReadLeft,
                    queryDoneLeft, queryLeft, queryCells,
                    rowCells, List.append_assoc]
                    using hrowDone)
                (TuringMachine.Computes.step
                  (by
                    simpa [comparisonPrefix,
                      runtimeKeyComparatorComparisonPrefix,
                      queryCells, rowCells,
                      List.reverse_replicate,
                      List.append_assoc]
                      using hcompare)
                  (by
                    simpa [queryCells, rowCells,
                      runtimeKeyComparatorComparisonPrefix,
                      List.reverse_replicate,
                      List.append_assoc]
                      using hrestore)))))))
  done

end Section53UniformInterpreterOneStep
end Computability
end FoC
