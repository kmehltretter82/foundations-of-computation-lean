import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.LeftCleanup
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.StateCompactor

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.RuntimeActionStateAssembly

theorem compactor_computes_of_tape_equiv
    (action : FiniteRecognizer.Interpreter.RuntimeStateCompactor.Action)
    (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource :
      Tape.Equiv
        (FiniteRecognizer.Interpreter.RuntimeStateCompactor.sourceConfig action target oldState
          protectedSuffix).tape
        sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeStateCompactor.machine
          { state := FiniteRecognizer.Interpreter.RuntimeStateCompactor.Control.seekMarker action
            tape := sourceTape }
          { state := FiniteRecognizer.Interpreter.RuntimeStateCompactor.Control.ready action
            tape := targetTape } ∧
        Tape.Equiv
          (FiniteRecognizer.Interpreter.RuntimeStateCompactor.targetConfig
            action target protectedSuffix).tape
          targetTape := by
  rcases FiniteRecognizer.Interpreter.RuntimeStateCompactor.run_exact
      action target oldState protectedSuffix with
    ⟨canonicalTarget, hrun, hcanonicalTarget⟩
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hrun hsource with
    ⟨target, htargetRun, htargetState, htargetTape⟩
  rcases target with ⟨state, tape⟩
  simp only at htargetState
  subst state
  refine ⟨tape, ?_, ?_⟩
  · exact TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun)
  · exact Tape.Equiv.trans hcanonicalTarget htargetTape
  done

theorem selected_action_to_compacted_state
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists cleanedTape finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine
          (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.fromActionConfig
            baseLeftRev selected
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend oldState
                protectedSuffix))
          { state := FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.ready
              (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
            tape := cleanedTape } ∧
        TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeStateCompactor.machine
          { state := FiniteRecognizer.Interpreter.RuntimeStateCompactor.Control.seekMarker
              (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
            tape := cleanedTape }
          { state := FiniteRecognizer.Interpreter.RuntimeStateCompactor.Control.ready
              (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
            tape := finalTape } ∧
        Tape.Equiv
          (FiniteRecognizer.Interpreter.RuntimeStateCompactor.targetConfig
            (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
            selected.target protectedSuffix).tape
          finalTape := by
  rcases FiniteRecognizer.Interpreter.RuntimeLeftCleanup.computes_from_action_target
      baseLeftRev selected
      (MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend oldState protectedSuffix) with
    ⟨cleanedTape, hcleanup, hcleaned⟩
  have hsource :
      Tape.Equiv
        (FiniteRecognizer.Interpreter.RuntimeStateCompactor.sourceConfig
          (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
          selected.target oldState protectedSuffix).tape
        cleanedTape := by
    exact Tape.Equiv.symm (by
      simpa [FiniteRecognizer.Interpreter.RuntimeStateCompactor.sourceConfig,
        FiniteRecognizer.Interpreter.RuntimeStateCompactor.sourceWord] using hcleaned)
  rcases compactor_computes_of_tape_equiv
      (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
      selected.target oldState
      protectedSuffix cleanedTape hsource with
    ⟨finalTape, hcompactor, hfinal⟩
  exact ⟨cleanedTape, finalTape, hcleanup, hcompactor, hfinal⟩
  done


end FiniteRecognizer.Interpreter.RuntimeActionStateAssembly

end Computability
end FoC
