import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup

namespace FoC
namespace Computability

open Languages

namespace Section53UniformInterpreterOneStep
namespace RuntimeKeySingleKeyRepair

open FiniteRecognizer ExactFuel StrictProbe

theorem comparator_step_exhausted_rewind_symbol
    (leftHead current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      { state := .exhaustedRewind
        tape := runtimeKeyComparatorTape (leftHead :: leftTail)
          (current :: suffix) }
      { state := .exhaustedRewind
        tape := runtimeKeyComparatorTape leftTail
          (leftHead :: current :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead current current]
  apply TuringMachine.Step.mk
  cases current <;>
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read]
      at hcurrent ⊢
  done

theorem comparator_computes_exhausted_rewind_to_header
    (leftSymbols : Word MachineCodeSymbol)
    (hleftSymbols : transitionListParserNoHeader leftSymbols)
    (current : MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .exhaustedRewind
        tape := runtimeKeyComparatorTape
          (List.append leftSymbols [MachineCodeSymbol.header])
          (current :: suffix) }
      { state := .inner
          (RuntimeKeyComparatorState.restoreQuery
            RuntimeKeyComparatorOutcome.isMiss)
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (List.append leftSymbols.reverse (current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      have hsymbol := comparator_step_exhausted_rewind_symbol
        MachineCodeSymbol.header current hcurrent [] suffix
      have hheader : TuringMachine.Step comparatorMachine
          { state := .exhaustedRewind
            tape := runtimeKeyComparatorTape []
              (MachineCodeSymbol.header :: current :: suffix) }
          { state := .inner
              (RuntimeKeyComparatorState.restoreQuery
                RuntimeKeyComparatorOutcome.isMiss)
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
      have hstep := comparator_step_exhausted_rewind_symbol
        leftHead current hcurrent
        (List.append leftTail [MachineCodeSymbol.header]) suffix
      have hrest := ih hleftTail leftHead hleftHead (current :: suffix)
      exact TuringMachine.Computes.step
        (by simpa using hstep)
        (by
          simpa [List.reverse_cons, List.append_assoc] using hrest)
  done

theorem comparator_step_need_transition_end_guard
    (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      { state := .inner RuntimeKeyComparatorState.needTransition
        tape := runtimeKeyComparatorTape (leftHead :: leftTail)
          (MachineCodeSymbol.header :: suffix) }
      { state := .exhaustedRewind
        tape := runtimeKeyComparatorTape leftTail
          (leftHead :: MachineCodeSymbol.header :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead MachineCodeSymbol.header MachineCodeSymbol.header]
  exact TuringMachine.Step.mk (by
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read])
  done

theorem comparator_step_finish_end_guard
    (read : Option Bool)
    (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      { state := .inner
          (RuntimeKeyComparatorState.finishNeedTransition read)
        tape := runtimeKeyComparatorTape (leftHead :: leftTail)
          (MachineCodeSymbol.header :: suffix) }
      { state := .exhaustedRewind
        tape := runtimeKeyComparatorTape leftTail
          (leftHead :: MachineCodeSymbol.header :: suffix) } := by
  rw [← runtimeKeyComparatorTape_move_left leftTail suffix
    leftHead MachineCodeSymbol.header MachineCodeSymbol.header]
  exact TuringMachine.Step.mk (by
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read])
  done

theorem comparator_computes_need_transition_end_guard_rewind
    (leftRev : Word MachineCodeSymbol)
    (hleftHeader : transitionListParserNoHeader leftRev)
    (hleftNonempty : leftRev ≠ [])
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner RuntimeKeyComparatorState.needTransition
        tape := runtimeKeyComparatorTape
          (List.append leftRev [MachineCodeSymbol.header])
          (MachineCodeSymbol.header :: protectedSuffix) }
      { state := .inner
          (RuntimeKeyComparatorState.restoreQuery
            RuntimeKeyComparatorOutcome.isMiss)
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (List.append leftRev.reverse
            (MachineCodeSymbol.header :: protectedSuffix)) } := by
  cases leftRev with
  | nil => exact False.elim (hleftNonempty rfl)
  | cons leftHead leftTail =>
      have hleftHead : leftHead ≠ MachineCodeSymbol.header :=
        hleftHeader leftHead (List.Mem.head leftTail)
      have hleftTail : transitionListParserNoHeader leftTail := by
        intro symbol hmem
        exact hleftHeader symbol (List.Mem.tail leftHead hmem)
      exact TuringMachine.Computes.step
        (by
          simpa [List.append_assoc] using
            comparator_step_need_transition_end_guard leftHead
              (List.append leftTail [MachineCodeSymbol.header])
              protectedSuffix)
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            comparator_computes_exhausted_rewind_to_header
              leftTail hleftTail leftHead hleftHead
              (MachineCodeSymbol.header :: protectedSuffix))
  done

theorem comparator_computes_finish_end_guard_rewind
    (read : Option Bool)
    (leftRev : Word MachineCodeSymbol)
    (hleftHeader : transitionListParserNoHeader leftRev)
    (hleftNonempty : leftRev ≠ [])
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner
          (RuntimeKeyComparatorState.finishNeedTransition read)
        tape := runtimeKeyComparatorTape
          (List.append leftRev [MachineCodeSymbol.header])
          (MachineCodeSymbol.header :: protectedSuffix) }
      { state := .inner
          (RuntimeKeyComparatorState.restoreQuery
            RuntimeKeyComparatorOutcome.isMiss)
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (List.append leftRev.reverse
            (MachineCodeSymbol.header :: protectedSuffix)) } := by
  cases leftRev with
  | nil => exact False.elim (hleftNonempty rfl)
  | cons leftHead leftTail =>
      have hleftHead : leftHead ≠ MachineCodeSymbol.header :=
        hleftHeader leftHead (List.Mem.head leftTail)
      have hleftTail : transitionListParserNoHeader leftTail := by
        intro symbol hmem
        exact hleftHeader symbol (List.Mem.tail leftHead hmem)
      exact TuringMachine.Computes.step
        (by
          simpa [List.append_assoc] using
            comparator_step_finish_end_guard read leftHead
              (List.append leftTail [MachineCodeSymbol.header])
              protectedSuffix)
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            comparator_computes_exhausted_rewind_to_header
              leftTail hleftTail leftHead hleftHead
              (MachineCodeSymbol.header :: protectedSuffix))
  done

theorem comparator_step_restore_end_guard
    (outcome : RuntimeKeyComparatorOutcome)
    (leftRev protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Step comparatorMachine
      { state := .inner
          (RuntimeKeyComparatorState.restoreNeedTransition outcome)
        tape := runtimeKeyComparatorTape leftRev
          (MachineCodeSymbol.header :: protectedSuffix) }
      { state := .exhausted
        tape := runtimeKeyComparatorTape
          (MachineCodeSymbol.header :: leftRev) protectedSuffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.header MachineCodeSymbol.header protectedSuffix]
  exact TuringMachine.Step.mk (by
    simp [comparatorMachine, runtimeKeyComparatorTape, Tape.read])
  done

def exhaustedRestoredLeft
    (queryCells : Word MachineCodeSymbol)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    List.append processed.reverse
      (runtimeKeyCellSymbol queryRead ::
        MachineCodeSymbol.done ::
        List.append
          (queryCells.map (fun _ => MachineCodeSymbol.tick)).reverse
          [MachineCodeSymbol.header])

theorem comparator_computes_restore_query_then_exhausted
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
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      { state := .inner
          (RuntimeKeyComparatorState.restoreQuery
            RuntimeKeyComparatorOutcome.isMiss)
        tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
          (List.append queryCells
            (MachineCodeSymbol.done ::
              runtimeKeyCellSymbol queryRead ::
              List.append processed
                (MachineCodeSymbol.header :: protectedSuffix))) }
      { state := .exhausted
        tape := runtimeKeyComparatorTape
          (exhaustedRestoredLeft queryCells queryRead processed)
          protectedSuffix } := by
  let queryLeft : Word MachineCodeSymbol :=
    List.append
      (queryCells.map (fun _ => MachineCodeSymbol.tick)).reverse
      [MachineCodeSymbol.header]
  let afterQueryReadLeft : Word MachineCodeSymbol :=
    runtimeKeyCellSymbol queryRead ::
      MachineCodeSymbol.done :: queryLeft
  have hquery := comparator_computes_lift
    (runtimeKeyComparatorMachine_computes_restore_query_unary
      RuntimeKeyComparatorOutcome.isMiss queryCells hqueryCells
      [MachineCodeSymbol.header]
      (MachineCodeSymbol.done ::
        runtimeKeyCellSymbol queryRead ::
        List.append processed
          (MachineCodeSymbol.header :: protectedSuffix)))
  have hdone := comparator_step_lift
    (runtimeKeyComparatorMachine_step_restore_query_done
      RuntimeKeyComparatorOutcome.isMiss queryLeft
      (runtimeKeyCellSymbol queryRead ::
        List.append processed
          (MachineCodeSymbol.header :: protectedSuffix)))
  have hread := comparator_step_lift
    (runtimeKeyComparatorMachine_step_restore_query_read
      RuntimeKeyComparatorOutcome.isMiss queryRead
      (MachineCodeSymbol.done :: queryLeft)
      (List.append processed
        (MachineCodeSymbol.header :: protectedSuffix)))
  have hseek := comparator_computes_restore_seek_prefix
    RuntimeKeyComparatorOutcome.isMiss afterQueryReadLeft
    processed (MachineCodeSymbol.header :: protectedSuffix)
    hprocessedTransition hprocessedHeader
  have hexhaust := comparator_step_restore_end_guard
    RuntimeKeyComparatorOutcome.isMiss
    (List.append processed.reverse afterQueryReadLeft)
    protectedSuffix
  exact TuringMachine.computes_trans
    (by
      simpa [queryLeft, liftComparatorConfig,
        embedComparatorState] using hquery)
    (TuringMachine.Computes.step
      (by
        simpa [queryLeft, liftComparatorConfig,
          embedComparatorState] using hdone)
      (TuringMachine.Computes.step
        (by
          simpa [queryLeft, afterQueryReadLeft,
            liftComparatorConfig, embedComparatorState] using hread)
        (TuringMachine.computes_trans
          (by
            simpa [comparatorRestoreSeekConfig,
              afterQueryReadLeft, queryLeft,
              embedComparatorState, List.append_assoc] using hseek)
          (TuringMachine.Computes.step
            (by
              simpa [afterQueryReadLeft, queryLeft,
                exhaustedRestoredLeft, List.append_assoc]
                using hexhaust)
            (TuringMachine.Computes.refl _)))))
  done

def canonicalExhaustedRowsTarget
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol ComparatorState :=
  { state := .exhausted
    tape := runtimeKeyComparatorTape
      (MachineCodeSymbol.header ::
        List.append (processedRows skipped).reverse
          (runtimeKeyCellSymbol (Tape.read current.tape) ::
            MachineCodeSymbol.done ::
            List.append
              (List.replicate current.state MachineCodeSymbol.tick).reverse
              [MachineCodeSymbol.header]))
      protectedSuffix }

theorem replicate_tick_succ_append_header
    (remaining : Nat) :
    List.append
        (List.replicate remaining MachineCodeSymbol.tick)
        [MachineCodeSymbol.tick, MachineCodeSymbol.header] =
      List.append
        (List.replicate (Nat.succ remaining) MachineCodeSymbol.tick)
        [MachineCodeSymbol.header] := by
  induction remaining with
  | zero => rfl
  | succ remaining ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons MachineCodeSymbol.tick) ih
  done

theorem replicate_tick_add_one_append_header
    (remaining : Nat) :
    List.append
        (List.replicate remaining MachineCodeSymbol.tick)
        [MachineCodeSymbol.tick, MachineCodeSymbol.header] =
      List.append
        (List.replicate (remaining + 1) MachineCodeSymbol.tick)
        [MachineCodeSymbol.header] := by
  simpa [Nat.succ_eq_add_one] using
    replicate_tick_succ_append_header remaining
  done

theorem replicate_tick_append_tick_append_header
    (remaining : Nat) :
    List.append
        (List.append
          (List.replicate remaining MachineCodeSymbol.tick)
          [MachineCodeSymbol.tick])
        [MachineCodeSymbol.header] =
      List.append
        (List.replicate (remaining + 1) MachineCodeSymbol.tick)
        [MachineCodeSymbol.header] := by
  calc
    List.append
          (List.append
            (List.replicate remaining MachineCodeSymbol.tick)
            [MachineCodeSymbol.tick])
          [MachineCodeSymbol.header] =
        List.append
          (List.replicate remaining MachineCodeSymbol.tick)
          (List.append [MachineCodeSymbol.tick]
            [MachineCodeSymbol.header]) :=
      List.append_assoc _ _ _
    _ = List.append
          (List.replicate remaining MachineCodeSymbol.tick)
          [MachineCodeSymbol.tick, MachineCodeSymbol.header] := rfl
    _ = List.append
          (List.replicate (remaining + 1) MachineCodeSymbol.tick)
          [MachineCodeSymbol.header] :=
      replicate_tick_add_one_append_header remaining
  done

theorem comparator_computes_empty_rows_exhausted
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes comparatorMachine
      (canonicalScanRowsConfig current skipped [] protectedSuffix)
      (canonicalExhaustedRowsTarget current skipped protectedSuffix) := by
  let queryRead : Option Bool := Tape.read current.tape
  let processed : Word MachineCodeSymbol := processedRows skipped
  have hprocessedTransition :
      RuntimeKeySelectedExtractor.NoTransition processed := by
    simpa [processed] using processedRows_no_transition skipped
  have hprocessedHeader : transitionListParserNoHeader processed := by
    simpa [processed] using processedRows_no_header skipped
  cases hstate : current.state with
  | zero =>
      let leftRev : Word MachineCodeSymbol :=
        List.append processed.reverse
          [runtimeKeyCellSymbol queryRead, MachineCodeSymbol.done]
      have hleftHeader : transitionListParserNoHeader leftRev := by
        apply transitionListParserNoHeader_append
        · intro symbol hmem
          apply hprocessedHeader symbol
          exact List.mem_reverse.mp hmem
        · intro symbol hmem
          rcases List.mem_cons.mp hmem with hread | hmem
          · subst symbol
            cases queryRead with
            | none => simp [runtimeKeyCellSymbol]
            | some bit => cases bit <;> simp [runtimeKeyCellSymbol]
          · have hdone := List.mem_singleton.mp hmem
            subst symbol
            simp
      have hleftNonempty : leftRev ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp [leftRev] at hlen
      have hdone := comparator_step_lift
        (runtimeKeyComparatorMachine_step_scan_query_done
          [MachineCodeSymbol.header]
          (runtimeKeyCellSymbol queryRead ::
            List.append processed
              (MachineCodeSymbol.header :: protectedSuffix)))
      have hread := comparator_step_lift
        (runtimeKeyComparatorMachine_step_remember_query_read
          queryRead
          (MachineCodeSymbol.done :: [MachineCodeSymbol.header])
          (List.append processed
            (MachineCodeSymbol.header :: protectedSuffix)))
      have hseek := comparator_computes_finish_seek_prefix queryRead
        (runtimeKeyCellSymbol queryRead ::
          MachineCodeSymbol.done :: [MachineCodeSymbol.header])
        processed (MachineCodeSymbol.header :: protectedSuffix)
        hprocessedTransition hprocessedHeader
      have hguard := comparator_computes_finish_end_guard_rewind
        queryRead leftRev hleftHeader hleftNonempty protectedSuffix
      have hrestore := comparator_computes_restore_query_then_exhausted
        [] (by
          intro symbol hmem
          nomatch hmem)
        queryRead processed hprocessedTransition hprocessedHeader
        protectedSuffix
      exact TuringMachine.Computes.step
        (by
          simpa [canonicalScanRowsConfig, runtimeKeyBuilderKeyCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeTransitionsAppend,
            runtimeKey_encodeNat_eq_replicate_tick_done,
            runtimeKey_encodeCell_eq_singleton,
            queryRead, processed,
            hstate, liftComparatorConfig, embedComparatorState,
            List.append_assoc] using hdone)
        (TuringMachine.Computes.step
          (by
            simpa [queryRead, processed,
              liftComparatorConfig, embedComparatorState,
              List.append_assoc] using hread)
          (TuringMachine.computes_trans
            (by
              simpa [comparatorFinishSeekConfig, queryRead,
                processed, List.append_assoc] using hseek)
            (TuringMachine.computes_trans
              (by
                simpa [leftRev, queryRead, processed,
                  List.reverse_append, List.append_assoc] using hguard)
              (by
                simpa [canonicalExhaustedRowsTarget,
                  exhaustedRestoredLeft, queryRead, processed,
                  hstate, List.append_assoc] using hrestore))))
  | succ remaining =>
      let queryCells : Word MachineCodeSymbol :=
        MachineCodeSymbol.blank ::
          List.replicate remaining MachineCodeSymbol.tick
      let queryMarkedLeft : Word MachineCodeSymbol :=
        MachineCodeSymbol.blank :: [MachineCodeSymbol.header]
      let queryTicksLeft : Word MachineCodeSymbol :=
        List.append
          (List.replicate remaining MachineCodeSymbol.tick).reverse
          queryMarkedLeft
      let queryDoneLeft : Word MachineCodeSymbol :=
        MachineCodeSymbol.done :: queryTicksLeft
      let queryReadLeft : Word MachineCodeSymbol :=
        runtimeKeyCellSymbol queryRead :: queryDoneLeft
      let leftRev : Word MachineCodeSymbol :=
        List.append processed.reverse
          (runtimeKeyCellSymbol queryRead ::
            MachineCodeSymbol.done ::
            List.append
              (List.replicate remaining MachineCodeSymbol.tick).reverse
              [MachineCodeSymbol.blank])
      have hqueryCells :
          forall symbol : MachineCodeSymbol,
            List.Mem symbol queryCells ->
              symbol = MachineCodeSymbol.blank ∨
                symbol = MachineCodeSymbol.tick := by
        intro symbol hmem
        rcases List.mem_cons.mp hmem with hblank | htick
        · exact Or.inl hblank
        · exact Or.inr (List.mem_replicate.mp htick).2
      have hleftHeader : transitionListParserNoHeader leftRev := by
        apply transitionListParserNoHeader_append
        · intro symbol hmem
          apply hprocessedHeader symbol
          exact List.mem_reverse.mp hmem
        · intro symbol hmem
          rcases List.mem_cons.mp hmem with hread | hmem
          · subst symbol
            cases queryRead with
            | none => simp [runtimeKeyCellSymbol]
            | some bit => cases bit <;> simp [runtimeKeyCellSymbol]
          · rcases List.mem_cons.mp hmem with hdone | htail
            · subst symbol
              simp
            · rcases List.mem_append.mp htail with htick | hblank
              · have heq := (List.mem_replicate.mp
                  (List.mem_reverse.mp htick)).2
                subst symbol
                simp
              · have heq := List.mem_singleton.mp hblank
                subst symbol
                simp
      have hleftNonempty : leftRev ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp [leftRev] at hlen
      have hmark := comparator_step_lift
        (runtimeKeyComparatorMachine_step_mark_query_tick
          [MachineCodeSymbol.header]
          (List.append
            (List.replicate remaining MachineCodeSymbol.tick)
            (MachineCodeSymbol.done ::
              runtimeKeyCellSymbol queryRead ::
              List.append processed
                (MachineCodeSymbol.header :: protectedSuffix))))
      have hticks := comparator_computes_lift
        (runtimeKeyComparatorMachine_computes_seek_query_ticks
          remaining queryMarkedLeft
          (MachineCodeSymbol.done ::
            runtimeKeyCellSymbol queryRead ::
            List.append processed
              (MachineCodeSymbol.header :: protectedSuffix)))
      have hdone := comparator_step_lift
        (runtimeKeyComparatorMachine_step_seek_query_done queryTicksLeft
          (runtimeKeyCellSymbol queryRead ::
            List.append processed
              (MachineCodeSymbol.header :: protectedSuffix)))
      have hread := comparator_step_lift
        (runtimeKeyComparatorMachine_step_skip_query_read queryRead
          queryDoneLeft
          (List.append processed
            (MachineCodeSymbol.header :: protectedSuffix)))
      have hseek := comparator_computes_seek_prefix queryReadLeft processed
        (MachineCodeSymbol.header :: protectedSuffix)
        hprocessedTransition hprocessedHeader
      have hguard := comparator_computes_need_transition_end_guard_rewind
        leftRev hleftHeader hleftNonempty protectedSuffix
      have hrestore := comparator_computes_restore_query_then_exhausted
        queryCells hqueryCells queryRead processed
        hprocessedTransition hprocessedHeader protectedSuffix
      have htarget :
          ({ state := ComparatorState.exhausted
             tape := runtimeKeyComparatorTape
               (exhaustedRestoredLeft queryCells queryRead processed)
               protectedSuffix } :
            TuringMachine.Configuration MachineCodeSymbol ComparatorState) =
            canonicalExhaustedRowsTarget current skipped
              protectedSuffix := by
        unfold canonicalExhaustedRowsTarget exhaustedRestoredLeft
        rw [hstate]
        simp only [queryCells, queryRead, processed,
          List.map_cons, List.map_replicate,
          List.reverse_cons, List.reverse_replicate]
        exact congrArg
          (fun tail : Word MachineCodeSymbol =>
            ({ state := ComparatorState.exhausted
               tape := runtimeKeyComparatorTape
                 (MachineCodeSymbol.header ::
                   List.append (processedRows skipped).reverse
                     (runtimeKeyCellSymbol (Tape.read current.tape) ::
                       MachineCodeSymbol.done :: tail))
                 protectedSuffix } :
              TuringMachine.Configuration MachineCodeSymbol
                ComparatorState))
          (replicate_tick_append_tick_append_header remaining)
      have hrestore' :
          TuringMachine.Computes comparatorMachine
            { state := .inner
                (RuntimeKeyComparatorState.restoreQuery
                  RuntimeKeyComparatorOutcome.isMiss)
              tape := runtimeKeyComparatorTape [MachineCodeSymbol.header]
                (List.append queryCells
                  (MachineCodeSymbol.done ::
                    runtimeKeyCellSymbol queryRead ::
                    List.append processed
                      (MachineCodeSymbol.header :: protectedSuffix))) }
            (canonicalExhaustedRowsTarget current skipped
              protectedSuffix) := by
        rw [← htarget]
        exact hrestore
      exact TuringMachine.Computes.step
        (by
          simpa [canonicalScanRowsConfig, runtimeKeyBuilderKeyCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeTransitionsAppend,
            runtimeKey_encodeNat_eq_replicate_tick_done,
            runtimeKey_encodeCell_eq_singleton,
            queryRead, processed,
            hstate, liftComparatorConfig, embedComparatorState,
            List.replicate_succ, List.append_assoc] using hmark)
        (TuringMachine.computes_trans
          (by
            simpa [queryMarkedLeft, liftComparatorConfig,
              embedComparatorState, List.append_assoc] using hticks)
          (TuringMachine.Computes.step
            (by
              simpa [queryTicksLeft, queryMarkedLeft,
                liftComparatorConfig, embedComparatorState,
                List.append_assoc] using hdone)
            (TuringMachine.Computes.step
              (by
                simpa [queryDoneLeft, queryTicksLeft,
                  queryMarkedLeft, queryRead,
                  liftComparatorConfig, embedComparatorState,
                  List.append_assoc] using hread)
              (TuringMachine.computes_trans
                (by
                  simpa [comparatorSeekConfig, queryReadLeft,
                    queryDoneLeft, queryTicksLeft, queryMarkedLeft,
                    List.append_assoc] using hseek)
                (TuringMachine.computes_trans
                  (by
                    simpa [leftRev, queryReadLeft, queryDoneLeft,
                      queryTicksLeft, queryMarkedLeft, queryRead,
                      processed, List.reverse_append,
                      List.append_assoc] using hguard)
                  (by
                    simpa [queryCells, queryRead, processed,
                      List.append_assoc] using hrestore'))))))
  done

theorem comparator_computes_all_miss_exhausted
    (current : MachineDescription.Configuration)
    (skipped rows : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (hmiss :
      forall row : TransitionDescription,
        List.Mem row rows ->
          MachineDescription.Matches current.state
            (Tape.read current.tape) row = false) :
    TuringMachine.Computes comparatorMachine
      (canonicalScanRowsConfig current skipped rows protectedSuffix)
      (canonicalExhaustedRowsTarget current
        (List.append skipped rows) protectedSuffix) := by
  induction rows generalizing skipped with
  | nil =>
      simpa using comparator_computes_empty_rows_exhausted
        current skipped protectedSuffix
  | cons row rest ih =>
      have hrow :
          MachineDescription.Matches current.state
            (Tape.read current.tape) row = false :=
        hmiss row (List.Mem.head rest)
      have hrest :
          forall candidate : TransitionDescription,
            List.Mem candidate rest ->
              MachineDescription.Matches current.state
                (Tape.read current.tape) candidate = false := by
        intro candidate hmem
        exact hmiss candidate (List.Mem.tail row hmem)
      have hadvance := comparator_computes_miss_advance
        current skipped row rest protectedSuffix hrow
      have hexhaust := ih (List.append skipped [row]) hrest
      exact TuringMachine.computes_trans hadvance
        (by simpa [List.append_assoc] using hexhaust)
  done


end RuntimeKeySingleKeyRepair
end Section53UniformInterpreterOneStep
end Computability
end FoC
