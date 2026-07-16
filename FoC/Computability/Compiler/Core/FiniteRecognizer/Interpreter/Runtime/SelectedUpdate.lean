import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Extractor.Handoff
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.ActionState
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.FixedUpdate

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.SelectedUpdateIntegration

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair

/-!
**Selected-update integration.** The comparator and arbitrary-rest extractor
share one exact single-key representation. This module proves their handoff,
transports the finite action parser across the extractor's tape-equivalent
endpoint, materializes the fixed-placeholder source, and invokes the verified
selected-update kernel.
-/

def actionBase
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription) :
    Word MachineCodeSymbol :=
  RuntimeKeySelectedExtractorArbitrary.singleKeySeparatedActionBase
    [MachineCodeSymbol.header] (processedRows skipped)
    current.state (Tape.read current.tape)

def extractorSourceConfig
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeySelectedExtractorArbitrary.Control :=
  RuntimeKeySelectedExtractorArbitrary.singleKeySourceConfig
    (actionBase current skipped) selected rest protectedSuffix

def compactedSelectedTape
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  runtimeKeyComparatorTape (actionBase current skipped)
    (MachineDescription.encodeTransitionAppend selected
      (MachineCodeSymbol.header :: protectedSuffix))

theorem comparator_selected_tape_eq_extractor_source
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    (canonicalSelectedRowTarget current skipped selected rest
        protectedSuffix).tape =
      (extractorSourceConfig current skipped selected rest
        protectedSuffix).tape := by
  simp [canonicalSelectedRowTarget, canonicalSeparatedRowTarget,
    extractorSourceConfig,
    RuntimeKeySelectedExtractorArbitrary.singleKeySourceConfig,
    RuntimeKeySelectedExtractorArbitrary.singleKeySourceTape,
    RuntimeKeySelectedExtractorArbitrary.singleKeySelectedLeft,
    actionBase, separatedComparatorRestoredLeft,
    RuntimeKeySelectedExtractorArbitrary.singleKeySeparatedActionBase]
  done

theorem extractor_computes_from_comparator_selected
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes RuntimeKeySelectedExtractorArbitrary.machine
        (extractorSourceConfig current skipped selected rest
          protectedSuffix)
        { state := RuntimeKeySelectedExtractorArbitrary.Control.halt
          tape := targetTape } ∧
      Tape.Equiv
        (compactedSelectedTape current skipped selected protectedSuffix)
        targetTape := by
  simpa [extractorSourceConfig, compactedSelectedTape,
    RuntimeKeySelectedExtractorArbitrary.singleKeyTargetTape] using
    RuntimeKeySelectedExtractorArbitrary.singleKey_computes_exact
      (actionBase current skipped) selected rest protectedSuffix
  done

theorem comparator_first_match_then_extracts
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
          selected rest protectedSuffix) ∧
      exists targetTape : Tape MachineCodeSymbol,
        TuringMachine.Computes RuntimeKeySelectedExtractorArbitrary.machine
          (extractorSourceConfig current (List.append skipped before)
            selected rest protectedSuffix)
          { state := RuntimeKeySelectedExtractorArbitrary.Control.halt
            tape := targetTape } ∧
        Tape.Equiv
          (compactedSelectedTape current (List.append skipped before)
            selected protectedSuffix)
          targetTape := by
  exact
    ⟨comparator_computes_first_match_after_prefix
      current skipped before selected rest protectedSuffix hmiss hmatch,
      extractor_computes_from_comparator_selected
        current (List.append skipped before) selected rest protectedSuffix⟩
  done

theorem comparatorTape_eq_actionPrefixTape
    (leftRev rest : Word MachineCodeSymbol) :
    runtimeKeyComparatorTape leftRev rest =
      FiniteRecognizer.Interpreter.RuntimeActionPrefix.tapeAtWords leftRev rest := by
  cases rest <;> rfl
  done

theorem compactedSelectedTape_eq_actionPrefixSource
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    compactedSelectedTape current skipped selected protectedSuffix =
      (FiniteRecognizer.Interpreter.RuntimeActionPrefix.sourceConfig
        (actionBase current skipped) selected
        (MachineCodeSymbol.header :: protectedSuffix)).tape := by
  unfold compactedSelectedTape FiniteRecognizer.Interpreter.RuntimeActionPrefix.sourceConfig
  rw [comparatorTape_eq_actionPrefixTape]
  done

theorem actionPrefix_computes_of_tape_equiv
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource :
      Tape.Equiv
        (FiniteRecognizer.Interpreter.RuntimeActionPrefix.sourceConfig
          baseLeftRev selected suffix).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine
        { state := FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.needTransition
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.ready
            selected.write selected.move
          tape := targetTape } ∧
      Tape.Equiv
        (FiniteRecognizer.Interpreter.RuntimeActionPrefix.targetConfig
          baseLeftRev selected suffix).tape targetTape := by
  have hrun := FiniteRecognizer.Interpreter.RuntimeActionPrefix.run_exact
    baseLeftRev selected suffix
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨target, htargetRun, htargetState, htargetTape⟩
  rcases target with ⟨state, tape⟩
  simp only [FiniteRecognizer.Interpreter.RuntimeActionPrefix.targetConfig] at htargetState
  subst state
  exact ⟨tape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun),
    htargetTape⟩
  done

theorem extracted_tape_enters_action_prefix
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource :
      Tape.Equiv
        (compactedSelectedTape current skipped selected protectedSuffix)
        sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine
        { state := FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.needTransition
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.ready
            selected.write selected.move
          tape := targetTape } ∧
      Tape.Equiv
        (FiniteRecognizer.Interpreter.RuntimeActionPrefix.targetConfig
          (actionBase current skipped) selected
          (MachineCodeSymbol.header :: protectedSuffix)).tape
        targetTape := by
  apply actionPrefix_computes_of_tape_equiv
    (actionBase current skipped) selected
      (MachineCodeSymbol.header :: protectedSuffix) sourceTape
  rw [← compactedSelectedTape_eq_actionPrefixSource]
  exact hsource
  done

theorem leftCleanup_computes_of_action_target_equiv
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource :
      Tape.Equiv
        (FiniteRecognizer.Interpreter.RuntimeActionPrefix.targetConfig
          baseLeftRev selected suffix).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine
        { state := FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.enter
            (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.ready
            (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
          tape := targetTape } ∧
      Tape.Equiv targetTape
        (Tape.input
          (MachineDescription.encodeNatAppend selected.target suffix)) := by
  rcases FiniteRecognizer.Interpreter.RuntimeLeftCleanup.computes_from_action_target
      baseLeftRev selected suffix with
    ⟨canonicalTargetTape, hrun, hcanonical⟩
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hrunIn hsource with
    ⟨target, htargetRun, htargetState, htargetTape⟩
  rcases target with ⟨state, tape⟩
  simp only at htargetState
  subst state
  exact ⟨tape, TuringMachine.computesIn_to_computes htargetRun,
    Tape.Equiv.trans (Tape.Equiv.symm htargetTape) hcanonical⟩
  done

theorem extracted_action_then_cleanup
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (extractedTape : Tape MachineCodeSymbol)
    (hextracted :
      Tape.Equiv
        (compactedSelectedTape current skipped selected protectedSuffix)
        extractedTape) :
    exists actionTape cleanedTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine
        { state := FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.needTransition
          tape := extractedTape }
        { state := FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.ready
            selected.write selected.move
          tape := actionTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine
        { state := FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.enter
            (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
          tape := actionTape }
        { state := FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.ready
            (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
          tape := cleanedTape } ∧
      Tape.Equiv cleanedTape
        (Tape.input
          (MachineDescription.encodeNatAppend selected.target
            (MachineCodeSymbol.header :: protectedSuffix))) := by
  rcases extracted_tape_enters_action_prefix
      current skipped selected protectedSuffix extractedTape hextracted with
    ⟨actionTape, haction, hactionTape⟩
  rcases leftCleanup_computes_of_action_target_equiv
      (actionBase current skipped) selected
      (MachineCodeSymbol.header :: protectedSuffix)
      actionTape hactionTape with
    ⟨cleanedTape, hcleanup, hcleaned⟩
  exact ⟨actionTape, cleanedTape, haction, hcleanup, hcleaned⟩
  done

/-!
The verified fixed-placeholder update accepts a strict-probe selected-prefix
tape, whereas the successful runtime comparator branch currently exposes the
selected transition plus protected `(left,right)` context fields.  The
following contract isolates the required finite materializer without hiding
that representation change behind tape equivalence.
-/

def SelectedEntryMaterializerContract
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (entry : materializerState)
    (ready : Option Bool -> Direction -> materializerState) : Prop :=
  forall
    (fuel haltState : Nat)
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (selected : TransitionDescription)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol),
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes materializer
        { state := entry
          tape := compactedSelectedTape current skipped selected
            (protectedTapeContextsAppend current.tape
              (MachineDescription.encodeNatAppend fuel
                (MachineDescription.encodeNatAppend haltState
                  (MachineDescription.encodeTransitionsAppend transitions
                    suffix)))) }
        { state := ready selected.write selected.move
          tape := targetTape } ∧
      Tape.Equiv
        (Update.LeftKernel.selectedPrefixTape
          (FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.callerData selected.target
            haltState transitions suffix)
          fuel (FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.frame (fuel + 1)
            current.tape)
          (FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.encodeCell selected.write)
          selected.move FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.placeholder)
        targetTape

theorem fixedUpdate_computes_of_tape_equiv
    (fuel haltState : Nat)
    (tape : Tape Bool)
    (selected : TransitionDescription)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource :
      Tape.Equiv
        (Update.LeftKernel.selectedPrefixTape
          (FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.callerData selected.target
            haltState transitions suffix)
          fuel (FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.frame (fuel + 1) tape)
          (FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.encodeCell selected.write)
          selected.move FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.placeholder)
        sourceTape) :
    let action := Update.LeftKernel.selectedPayload
      (FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.encodeCell selected.write)
      selected.move FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.placeholder
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (Update.Kernel.machine action)
        { state := (Update.Kernel.machine action).start
          tape := sourceTape }
        { state := Update.Kernel.Control.done
          tape := targetTape } ∧
      Tape.Equiv
        (CyclicDriverIntegration.roundTripTape targetTape)
        (Tape.input
          (FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.workWord fuel selected.target
            haltState
            (Tape.move selected.move
              (Tape.write selected.write tape))
            transitions suffix)) := by
  dsimp only
  rcases FiniteRecognizer.Interpreter.FixedPlaceholderUpdate.selected_transition_update_run
      fuel tape selected haltState transitions suffix with
    ⟨steps, canonicalTargetTape, hrun, hcanonical⟩
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨target, htargetRun, htargetState, htargetTape⟩
  rcases target with ⟨state, tape'⟩
  simp only at htargetState
  subst state
  refine ⟨tape', ?_, ?_⟩
  · exact TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun)
  · have hround : Tape.Equiv
        (CyclicDriverIntegration.roundTripTape canonicalTargetTape)
        (CyclicDriverIntegration.roundTripTape tape') :=
      Tape.Equiv.move (Tape.Equiv.move htargetTape Direction.right)
        Direction.left
    exact Tape.Equiv.trans (Tape.Equiv.symm hround) hcanonical
  done


end FiniteRecognizer.Interpreter.SelectedUpdateIntegration

end Computability
end FoC
