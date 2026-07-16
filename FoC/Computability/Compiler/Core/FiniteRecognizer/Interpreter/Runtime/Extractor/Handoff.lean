import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Extractor.DeletePhases

namespace FoC
namespace Computability

open Languages

namespace RuntimeKeySelectedExtractorArbitrary

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

def singleKeySelectedLeft
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription) : Word MachineCodeSymbol :=
  runtimeKeyCellSymbol selected.read ::
    MachineCodeSymbol.done ::
    List.append
      (List.replicate selected.source MachineCodeSymbol.tick).reverse
      (MachineCodeSymbol.transition :: baseLeftRev)

def singleKeySourceTape
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  runtimeKeyComparatorTape
    (singleKeySelectedLeft baseLeftRev selected)
    (runtimeKeyCanonicalActionSuffix selected rest
      (MachineCodeSymbol.header :: protectedSuffix))

def singleKeySourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .skipWrite
  tape := singleKeySourceTape baseLeftRev selected rest protectedSuffix

def singleKeyTargetTape
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  runtimeKeyComparatorTape baseLeftRev
    (MachineDescription.encodeTransitionAppend selected
      (MachineCodeSymbol.header :: protectedSuffix))

def singleKeyTargetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := singleKeyTargetTape baseLeftRev selected protectedSuffix

def singleKeyDisposalLeft
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription) : Word MachineCodeSymbol :=
  List.append
    (List.replicate selected.target MachineCodeSymbol.tick).reverse
    (runtimeKeyDirectionSymbol selected.move ::
      runtimeKeyCellSymbol selected.write ::
      singleKeySelectedLeft baseLeftRev selected)

theorem singleKeySourceTape_shape
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    singleKeySourceTape baseLeftRev selected rest protectedSuffix =
      runtimeKeyComparatorTape
        (singleKeySelectedLeft baseLeftRev selected)
        (runtimeKeyCellSymbol selected.write ::
          runtimeKeyDirectionSymbol selected.move ::
          MachineDescription.encodeNatAppend selected.target
            (MachineDescription.encodeTransitionsAppend rest
              (MachineCodeSymbol.header :: protectedSuffix))) := by
  simp [singleKeySourceTape, runtimeKeyCanonicalActionSuffix,
    runtimeKey_encodeCell_eq_singleton,
    runtimeKey_encodeDirection_eq_singleton,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeDirectionAppend]
  done

theorem singleKey_computes_to_disposal
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (singleKeySourceConfig baseLeftRev selected rest protectedSuffix)
      (parseConfig .boundary
        (singleKeyDisposalLeft baseLeftRev selected)
        (MachineDescription.encodeTransitionsAppend rest
          (MachineCodeSymbol.header :: protectedSuffix))) := by
  let prefixLeft := singleKeySelectedLeft baseLeftRev selected
  let frame := MachineDescription.encodeTransitionsAppend rest
    (MachineCodeSymbol.header :: protectedSuffix)
  have hwrite : TuringMachine.Step machine
      (singleKeySourceConfig baseLeftRev selected rest protectedSuffix)
      (cursorConfig .skipMove
        (runtimeKeyCellSymbol selected.write :: prefixLeft)
        (runtimeKeyDirectionSymbol selected.move ::
          MachineDescription.encodeNatAppend selected.target frame)) := by
    rw [singleKeySourceConfig, singleKeySourceTape_shape]
    exact step_write selected.write prefixLeft
      (runtimeKeyDirectionSymbol selected.move ::
        MachineDescription.encodeNatAppend selected.target frame)
  have hmove : TuringMachine.Step machine
      (cursorConfig .skipMove
        (runtimeKeyCellSymbol selected.write :: prefixLeft)
        (runtimeKeyDirectionSymbol selected.move ::
          MachineDescription.encodeNatAppend selected.target frame))
      (cursorConfig .scanTarget
        (runtimeKeyDirectionSymbol selected.move ::
          runtimeKeyCellSymbol selected.write :: prefixLeft)
        (MachineDescription.encodeNatAppend selected.target frame)) :=
    step_move selected.move
      (runtimeKeyCellSymbol selected.write :: prefixLeft)
      (MachineDescription.encodeNatAppend selected.target frame)
  have hticks : TuringMachine.Computes machine
      (cursorConfig .scanTarget
        (runtimeKeyDirectionSymbol selected.move ::
          runtimeKeyCellSymbol selected.write :: prefixLeft)
        (MachineDescription.encodeNatAppend selected.target frame))
      (cursorConfig .scanTarget
        (singleKeyDisposalLeft baseLeftRev selected)
        (MachineCodeSymbol.done :: frame)) := by
    simpa [cursorConfig, MachineDescription.encodeNatAppend,
      runtimeKey_encodeNat_eq_replicate_tick_done,
      singleKeyDisposalLeft, prefixLeft, List.append_assoc] using
        computes_target_ticks selected.target
          (runtimeKeyDirectionSymbol selected.move ::
            runtimeKeyCellSymbol selected.write :: prefixLeft)
          (MachineCodeSymbol.done :: frame)
  have hframe : frame ≠ [] := by
    cases rest <;>
      simp [frame, MachineDescription.encodeTransitionsAppend,
        MachineDescription.encodeTransitionAppend]
  have hdone : TuringMachine.Step machine
      (cursorConfig .scanTarget
        (singleKeyDisposalLeft baseLeftRev selected)
        (MachineCodeSymbol.done :: frame))
      (parseConfig .boundary
        (singleKeyDisposalLeft baseLeftRev selected) frame) :=
    step_target_done_erase
      (singleKeyDisposalLeft baseLeftRev selected) frame hframe
  simpa [frame] using
    TuringMachine.Computes.step hwrite
      (TuringMachine.Computes.step hmove
        (TuringMachine.computes_trans hticks
          (TuringMachine.Computes.step hdone
            (TuringMachine.Computes.refl _))))
  done

theorem singleKey_computes_to_guard
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (singleKeySourceConfig baseLeftRev selected rest protectedSuffix)
        { state := .parse .boundary, tape := targetTape } ∧
      Tape.Equiv
        (sentinelTape (singleKeyDisposalLeft baseLeftRev selected)
          (MachineCodeSymbol.header :: protectedSuffix)) targetTape := by
  rcases disposeRows (singleKeyDisposalLeft baseLeftRev selected) rest
      protectedSuffix
      (sentinelTape (singleKeyDisposalLeft baseLeftRev selected)
        (MachineDescription.encodeTransitionsAppend rest
          (MachineCodeSymbol.header :: protectedSuffix)))
      (Tape.Equiv.refl _) with
    ⟨targetTape, hdispose, htarget⟩
  exact ⟨targetTape,
    TuringMachine.computes_trans
      (singleKey_computes_to_disposal baseLeftRev selected rest
        protectedSuffix)
      hdispose,
    htarget⟩
  done

def singleKeyRewindWord
    (selected : TransitionDescription) : Word MachineCodeSymbol :=
  (RuntimeKeySelectedExtractor.rowTail selected).reverse.tail

def singleKeyRewindConfig
    (baseLeftRev remaining crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewindSelected
  tape := RuntimeKeySelectedExtractor.rewindTape
    baseLeftRev remaining crossed

theorem singleKeyDisposalLeft_eq
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription) :
    singleKeyDisposalLeft baseLeftRev selected =
      List.append (singleKeyRewindWord selected)
        (MachineCodeSymbol.transition :: baseLeftRev) := by
  rcases selected with ⟨source, read, write, move, target⟩
  cases move <;>
    simp [singleKeyDisposalLeft, singleKeySelectedLeft,
      singleKeyRewindWord, RuntimeKeySelectedExtractor.rowTail,
      runtimeKeyRawTransitionTail,
      runtimeKey_encodeNat_eq_replicate_tick_done,
      runtimeKey_encodeCell_eq_singleton,
      runtimeKey_encodeDirection_eq_singleton,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeDirectionAppend,
      MachineDescription.encodeTransitionsAppend,
      List.reverse_append, List.append_assoc]
  done

theorem singleKeyRewindWord_ne_nil
    (selected : TransitionDescription) :
    singleKeyRewindWord selected ≠ [] := by
  rcases selected with ⟨source, read, write, move, target⟩
  intro hnil
  have hlength := congrArg List.length hnil
  cases move <;>
    simp [singleKeyRewindWord, RuntimeKeySelectedExtractor.rowTail,
      runtimeKeyRawTransitionTail,
      runtimeKey_encodeNat_eq_replicate_tick_done,
      runtimeKey_encodeCell_eq_singleton,
      runtimeKey_encodeDirection_eq_singleton,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeDirectionAppend,
      MachineDescription.encodeTransitionsAppend,
      List.reverse_append, List.append_assoc] at hlength
  done

theorem singleKey_restore_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (parseConfig .boundary
          (singleKeyDisposalLeft baseLeftRev selected)
          (MachineCodeSymbol.header :: protectedSuffix)) =
      some (singleKeyRewindConfig baseLeftRev
        (singleKeyRewindWord selected)
        (MachineCodeSymbol.done ::
          MachineCodeSymbol.header :: protectedSuffix)) := by
  cases hword : singleKeyRewindWord selected with
  | nil => exact (singleKeyRewindWord_ne_nil selected hword).elim
  | cons current more =>
      rw [singleKeyDisposalLeft_eq, hword]
      cases more <;> cases baseLeftRev <;> cases protectedSuffix <;> rfl
  done

theorem singleKey_step_rewind_nontransition
    (baseLeftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (more crossed : Word MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.transition) :
    TuringMachine.Step machine
      (singleKeyRewindConfig baseLeftRev (current :: more) crossed)
      (singleKeyRewindConfig baseLeftRev more
        (current :: crossed)) := by
  cases more with
  | nil =>
      change TuringMachine.Step machine
        { state := .rewindSelected
          tape := runtimeKeyComparatorTape
            (MachineCodeSymbol.transition :: baseLeftRev)
            (current :: crossed) }
        { state := .rewindSelected
          tape := runtimeKeyComparatorTape baseLeftRev
            (MachineCodeSymbol.transition :: current :: crossed) }
      rw [← runtimeKeyComparatorTape_move_left baseLeftRev crossed
        MachineCodeSymbol.transition current current]
      apply TuringMachine.Step.mk
      cases current <;>
        simp [machine, transition, runtimeKeyComparatorTape,
          Tape.read] at hcurrent ⊢
  | cons next tail =>
      change TuringMachine.Step machine
        { state := .rewindSelected
          tape := runtimeKeyComparatorTape
            (next :: List.append tail
              (MachineCodeSymbol.transition :: baseLeftRev))
            (current :: crossed) }
        { state := .rewindSelected
          tape := runtimeKeyComparatorTape
            (List.append tail
              (MachineCodeSymbol.transition :: baseLeftRev))
            (next :: current :: crossed) }
      rw [← runtimeKeyComparatorTape_move_left
        (List.append tail
          (MachineCodeSymbol.transition :: baseLeftRev))
        crossed next current current]
      apply TuringMachine.Step.mk
      cases current <;>
        simp [machine, transition, runtimeKeyComparatorTape,
          Tape.read] at hcurrent ⊢
  done

theorem singleKey_computes_rewind
    (baseLeftRev remaining crossed : Word MachineCodeSymbol)
    (hremaining : RuntimeKeySelectedExtractor.NoTransition remaining) :
    TuringMachine.Computes machine
      (singleKeyRewindConfig baseLeftRev remaining crossed)
      (singleKeyRewindConfig baseLeftRev []
        (List.append remaining.reverse crossed)) := by
  induction remaining generalizing crossed with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons current more ih =>
      have hcurrent : current ≠ MachineCodeSymbol.transition :=
        hremaining current (by simp)
      have hmore : RuntimeKeySelectedExtractor.NoTransition more := by
        intro symbol hmem
        exact hremaining symbol (by simp [hmem])
      exact TuringMachine.Computes.step
        (singleKey_step_rewind_nontransition baseLeftRev current more
          crossed hcurrent)
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            ih (current :: crossed) hmore)
  done

theorem singleKeyRewindWord_no_transition
    (selected : TransitionDescription) :
    RuntimeKeySelectedExtractor.NoTransition
      (singleKeyRewindWord selected) := by
  intro symbol hmem
  exact RuntimeKeySelectedExtractor.noTransition_reverse
    (RuntimeKeySelectedExtractor.rowTail_no_transition selected)
    symbol (List.mem_of_mem_tail hmem)
  done

theorem singleKey_rewind_endpoint_eq_ready
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    singleKeyRewindConfig baseLeftRev []
        (List.append (singleKeyRewindWord selected).reverse
          (MachineCodeSymbol.done ::
            MachineCodeSymbol.header :: protectedSuffix)) =
      { state := .rewindSelected
        tape := singleKeyTargetTape baseLeftRev selected
          protectedSuffix } := by
  rcases selected with ⟨source, read, write, move, target⟩
  cases move <;>
    simp [singleKeyRewindConfig,
      RuntimeKeySelectedExtractor.rewindTape,
      singleKeyRewindWord, singleKeyTargetTape,
      RuntimeKeySelectedExtractor.rowTail,
      runtimeKeyRawTransitionTail,
      runtimeKey_encodeNat_eq_replicate_tick_done,
      runtimeKey_encodeCell_eq_singleton,
      runtimeKey_encodeDirection_eq_singleton,
      MachineDescription.encodeTransitionAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeDirectionAppend,
      MachineDescription.encodeTransitionsAppend,
      List.reverse_append, List.append_assoc]
  done

theorem singleKeyTargetTape_eq_rowTail
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    singleKeyTargetTape baseLeftRev selected protectedSuffix =
      runtimeKeyComparatorTape baseLeftRev
        (MachineCodeSymbol.transition ::
          List.append (RuntimeKeySelectedExtractor.rowTail selected)
            (MachineCodeSymbol.header :: protectedSuffix)) := by
  simp [singleKeyTargetTape, RuntimeKeySelectedExtractor.rowTail,
    runtimeKeyRawTransitionTail,
    MachineDescription.encodeTransitionAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeDirectionAppend,
    MachineDescription.encodeTransitionsAppend,
    List.append_assoc]
  done

theorem singleKey_step_transition_right
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      { state := .rewindSelected
        tape := runtimeKeyComparatorTape baseLeftRev
          (MachineCodeSymbol.transition :: first :: rest) }
      { state := .bounceSelected
        tape := runtimeKeyComparatorTape
          (MachineCodeSymbol.transition :: baseLeftRev)
          (first :: rest) } := by
  rw [← runtimeKeyComparatorTape_move_right baseLeftRev
    MachineCodeSymbol.transition MachineCodeSymbol.transition
    (first :: rest)]
  exact TuringMachine.Step.mk (by
    simp [machine, transition, runtimeKeyComparatorTape, Tape.read])
  done

theorem singleKey_step_bounce_left
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      { state := .bounceSelected
        tape := runtimeKeyComparatorTape
          (MachineCodeSymbol.transition :: baseLeftRev)
          (first :: rest) }
      { state := .halt
        tape := runtimeKeyComparatorTape baseLeftRev
          (MachineCodeSymbol.transition :: first :: rest) } := by
  rw [← runtimeKeyComparatorTape_move_left baseLeftRev rest
    MachineCodeSymbol.transition first first]
  exact TuringMachine.Step.mk (by
    simp [machine, transition, runtimeKeyComparatorTape, Tape.read])
  done

theorem singleKey_computes_from_guard
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (parseConfig .boundary
        (singleKeyDisposalLeft baseLeftRev selected)
        (MachineCodeSymbol.header :: protectedSuffix))
      (singleKeyTargetConfig baseLeftRev selected protectedSuffix) := by
  have hrestore : TuringMachine.Computes machine
      (parseConfig .boundary
        (singleKeyDisposalLeft baseLeftRev selected)
        (MachineCodeSymbol.header :: protectedSuffix))
      (singleKeyRewindConfig baseLeftRev
        (singleKeyRewindWord selected)
        (MachineCodeSymbol.done ::
          MachineCodeSymbol.header :: protectedSuffix)) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (singleKey_restore_exact baseLeftRev selected protectedSuffix))
  have hrewind := singleKey_computes_rewind baseLeftRev
    (singleKeyRewindWord selected)
    (MachineCodeSymbol.done ::
      MachineCodeSymbol.header :: protectedSuffix)
    (singleKeyRewindWord_no_transition selected)
  have hready : TuringMachine.Computes machine
      (parseConfig .boundary
        (singleKeyDisposalLeft baseLeftRev selected)
        (MachineCodeSymbol.header :: protectedSuffix))
      { state := .rewindSelected
        tape := singleKeyTargetTape baseLeftRev selected
          protectedSuffix } :=
    TuringMachine.computes_trans hrestore (by
      simpa only [singleKey_rewind_endpoint_eq_ready] using hrewind)
  cases htail : RuntimeKeySelectedExtractor.rowTail selected with
  | nil =>
      exact (RuntimeKeySelectedExtractor.rowTail_ne_nil selected htail).elim
  | cons first rowRest =>
      have htape : singleKeyTargetTape baseLeftRev selected
            protectedSuffix =
          runtimeKeyComparatorTape baseLeftRev
            (MachineCodeSymbol.transition :: first ::
              List.append rowRest
                (MachineCodeSymbol.header :: protectedSuffix)) := by
        rw [singleKeyTargetTape_eq_rowTail, htail]
        rfl
      have htransition : TuringMachine.Step machine
          { state := .rewindSelected
            tape := singleKeyTargetTape baseLeftRev selected
              protectedSuffix }
          { state := .bounceSelected
            tape := runtimeKeyComparatorTape
              (MachineCodeSymbol.transition :: baseLeftRev)
              (first :: List.append rowRest
                (MachineCodeSymbol.header :: protectedSuffix)) } := by
        rw [htape]
        exact singleKey_step_transition_right baseLeftRev first
          (List.append rowRest
            (MachineCodeSymbol.header :: protectedSuffix))
      have hbounce : TuringMachine.Step machine
          { state := .bounceSelected
            tape := runtimeKeyComparatorTape
              (MachineCodeSymbol.transition :: baseLeftRev)
              (first :: List.append rowRest
                (MachineCodeSymbol.header :: protectedSuffix)) }
          (singleKeyTargetConfig baseLeftRev selected
            protectedSuffix) := by
        simpa only [singleKeyTargetConfig, htape] using
          singleKey_step_bounce_left baseLeftRev first
            (List.append rowRest
              (MachineCodeSymbol.header :: protectedSuffix))
      exact TuringMachine.computes_trans hready
        (TuringMachine.Computes.step htransition
          (TuringMachine.Computes.step hbounce
            (TuringMachine.Computes.refl _)))
  done

theorem singleKey_computes_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (singleKeySourceConfig baseLeftRev selected rest protectedSuffix)
        { state := .halt, tape := targetTape } ∧
      Tape.Equiv
        (singleKeyTargetTape baseLeftRev selected protectedSuffix)
        targetTape := by
  rcases singleKey_computes_to_guard baseLeftRev selected rest
      protectedSuffix with
    ⟨guardTape, htoGuard, hguardTape⟩
  rcases TuringMachine.computes_to_computesIn
      (singleKey_computes_from_guard baseLeftRev selected
        protectedSuffix) with
    ⟨steps, hcanonical⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonical hguardTape with
    ⟨targetConfig', hfromGuard, htargetState, htargetTape⟩
  rcases targetConfig' with ⟨targetState, targetTape⟩
  simp only [singleKeyTargetConfig] at htargetState
  subst targetState
  refine ⟨targetTape, ?_, ?_⟩
  · exact TuringMachine.computes_trans htoGuard (by
      simpa [parseConfig] using
        TuringMachine.computesIn_to_computes hfromGuard)
  · simpa [singleKeyTargetConfig] using htargetTape
  done

def singleKeyActionBase
    (leftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool) :
    Word MachineCodeSymbol :=
  runtimeKeyCellSymbol queryRead ::
    MachineCodeSymbol.done ::
    List.append
      (List.replicate queryState MachineCodeSymbol.tick).reverse
      leftRev

theorem comparatorRestoredLeft_eq_singleKeySelectedLeft
    (leftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription) :
    runtimeKeyComparatorRestoredLeft
        (List.replicate queryState MachineCodeSymbol.tick)
        queryRead
        (List.replicate selected.source MachineCodeSymbol.tick)
        selected.read leftRev =
      singleKeySelectedLeft
        (singleKeyActionBase leftRev queryState queryRead) selected := by
  simp [runtimeKeyComparatorRestoredLeft, singleKeySelectedLeft,
    singleKeyActionBase]
  done

theorem computes_comparator_selected_handoff
    (leftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .skipWrite
          tape := runtimeKeyComparatorTape
            (runtimeKeyComparatorRestoredLeft
              (List.replicate queryState MachineCodeSymbol.tick)
              queryRead
              (List.replicate selected.source MachineCodeSymbol.tick)
              selected.read leftRev)
            (runtimeKeyCanonicalActionSuffix selected rest
              (MachineCodeSymbol.header :: protectedSuffix)) }
        { state := .halt, tape := targetTape } ∧
      Tape.Equiv
        (runtimeKeyComparatorTape
          (singleKeyActionBase leftRev queryState queryRead)
          (MachineDescription.encodeTransitionAppend selected
            (MachineCodeSymbol.header :: protectedSuffix)))
        targetTape := by
  rw [comparatorRestoredLeft_eq_singleKeySelectedLeft]
  simpa [singleKeySourceConfig, singleKeySourceTape,
    singleKeyTargetTape] using
      singleKey_computes_exact
        (singleKeyActionBase leftRev queryState queryRead)
        selected rest protectedSuffix
  done

def singleKeySeparatedActionBase
    (leftRev processed : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool) :
    Word MachineCodeSymbol :=
  List.append processed.reverse
    (runtimeKeyCellSymbol queryRead ::
      MachineCodeSymbol.done ::
      List.append
        (List.replicate queryState MachineCodeSymbol.tick).reverse
        leftRev)

def singleKeySeparatedRestoredLeft
    (queryCells : Word MachineCodeSymbol)
    (queryRead : Option Bool)
    (processed : Word MachineCodeSymbol)
    (rowCells : Word MachineCodeSymbol)
    (rowRead : Option Bool)
    (leftRev : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
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

theorem separatedComparatorRestoredLeft_eq_singleKeySelectedLeft
    (leftRev processed : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription) :
    singleKeySeparatedRestoredLeft
        (List.replicate queryState MachineCodeSymbol.tick)
        queryRead processed
        (List.replicate selected.source MachineCodeSymbol.tick)
        selected.read leftRev =
      singleKeySelectedLeft
        (singleKeySeparatedActionBase leftRev processed
          queryState queryRead) selected := by
  simp [singleKeySeparatedRestoredLeft,
    singleKeySelectedLeft, singleKeySeparatedActionBase]
  done

theorem computes_separated_comparator_selected_handoff
    (leftRev processed : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .skipWrite
          tape := runtimeKeyComparatorTape
            (singleKeySeparatedRestoredLeft
              (List.replicate queryState MachineCodeSymbol.tick)
              queryRead processed
              (List.replicate selected.source MachineCodeSymbol.tick)
              selected.read leftRev)
            (runtimeKeyCanonicalActionSuffix selected rest
              (MachineCodeSymbol.header :: protectedSuffix)) }
        { state := .halt, tape := targetTape } ∧
      Tape.Equiv
        (runtimeKeyComparatorTape
          (singleKeySeparatedActionBase leftRev processed
            queryState queryRead)
          (MachineDescription.encodeTransitionAppend selected
            (MachineCodeSymbol.header :: protectedSuffix)))
        targetTape := by
  rw [separatedComparatorRestoredLeft_eq_singleKeySelectedLeft]
  simpa [singleKeySourceConfig, singleKeySourceTape,
    singleKeyTargetTape] using
      singleKey_computes_exact
        (singleKeySeparatedActionBase leftRev processed
          queryState queryRead)
        selected rest protectedSuffix
  done

end RuntimeKeySelectedExtractorArbitrary

end Computability
end FoC
