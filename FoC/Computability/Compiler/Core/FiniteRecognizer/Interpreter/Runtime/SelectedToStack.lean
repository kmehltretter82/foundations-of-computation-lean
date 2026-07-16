import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.SelectedUpdate
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Stack.Iteration

namespace FoC
namespace Computability

open Languages

namespace Section53SelectedToStack

open Section53UniformInterpreterOneStep
open Section53UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open Section53LoopRestagingAudit
open Section53SelectedUpdateIntegration

/-- Exact successful-row phase chain up to the stack updater.  The selected
finite write/move action remains in the cleanup control while the unbounded
target state is serialized at the front of `postSelectedWord`. -/
theorem first_match_to_postSelected
    (current : MachineDescription.Configuration)
    (before : List TransitionDescription)
    (selected : TransitionDescription)
    (after : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (hmiss :
      forall row : TransitionDescription,
        List.Mem row before ->
          MachineDescription.Matches current.state
            (Tape.read current.tape) row = false)
    (hmatch :
      MachineDescription.Matches current.state
        (Tape.read current.tape) selected = true) :
    let transitions := List.append before (selected :: after)
    let protectedSuffix :=
      activeProtectedSuffix transitions copies current.tape haltState
        callerSuffix
    exists extractedTape actionTape cleanedTape : Tape MachineCodeSymbol,
      TuringMachine.Computes comparatorMachine
        (canonicalScanRowsConfig current [] transitions protectedSuffix)
        (canonicalSelectedRowTarget current before selected after
          protectedSuffix) /\
      TuringMachine.Computes
        RuntimeKeySelectedExtractorArbitrary.machine
        (extractorSourceConfig current before selected after protectedSuffix)
        { state := RuntimeKeySelectedExtractorArbitrary.Control.halt
          tape := extractedTape } /\
      TuringMachine.Computes Section53RuntimeActionPrefix.machine
        { state := Section53RuntimeActionPrefix.Control.needTransition
          tape := extractedTape }
        { state := Section53RuntimeActionPrefix.Control.ready
            selected.write selected.move
          tape := actionTape } /\
      TuringMachine.Computes Section53RuntimeLeftCleanup.machine
        { state := Section53RuntimeLeftCleanup.Control.enter
            (Section53RuntimeLeftCleanup.selectedAction selected)
          tape := actionTape }
        { state := Section53RuntimeLeftCleanup.Control.ready
            (Section53RuntimeLeftCleanup.selectedAction selected)
          tape := cleanedTape } /\
      Tape.Equiv cleanedTape
        (Tape.input
          (postSelectedWord selected.target transitions copies current.tape
            haltState callerSuffix)) := by
  dsimp only
  let transitions := List.append before (selected :: after)
  let protectedSuffix :=
    activeProtectedSuffix transitions copies current.tape haltState
      callerSuffix
  have hfirst := comparator_first_match_then_extracts
    current [] before selected after protectedSuffix hmiss hmatch
  rcases hfirst with
    ⟨hcomparator, extractedTape, hextractor, hextractedTape⟩
  rcases extracted_action_then_cleanup
      current before selected protectedSuffix extractedTape
      (by simpa using hextractedTape) with
    ⟨actionTape, cleanedTape, haction, hcleanup, hcleanedTape⟩
  refine ⟨extractedTape, actionTape, cleanedTape, ?_, ?_, haction,
    hcleanup, ?_⟩
  · simpa [transitions, protectedSuffix] using hcomparator
  · simpa [transitions, protectedSuffix] using hextractor
  · simpa [postSelectedWord, protectedSuffix, transitions] using
      hcleanedTape
  done


end Section53SelectedToStack

end Computability
end FoC
