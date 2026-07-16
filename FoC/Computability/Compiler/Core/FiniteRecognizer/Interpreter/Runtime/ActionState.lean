import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.LeftCleanup
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.StateCompactor

namespace FoC
namespace Computability

open Languages

namespace Section53RuntimeActionStateAssembly

theorem compactor_computes_of_tape_equiv
    (action : Section53RuntimeStateCompactor.Action)
    (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource :
      Tape.Equiv
        (Section53RuntimeStateCompactor.sourceConfig action target oldState
          protectedSuffix).tape
        sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Section53RuntimeStateCompactor.machine
          { state := Section53RuntimeStateCompactor.Control.seekMarker action
            tape := sourceTape }
          { state := Section53RuntimeStateCompactor.Control.ready action
            tape := targetTape } ∧
        Tape.Equiv
          (Section53RuntimeStateCompactor.targetConfig
            action target protectedSuffix).tape
          targetTape := by
  rcases Section53RuntimeStateCompactor.run_exact
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
      TuringMachine.Computes Section53RuntimeLeftCleanup.machine
          (Section53RuntimeLeftCleanup.fromActionConfig
            baseLeftRev selected
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend oldState
                protectedSuffix))
          { state := Section53RuntimeLeftCleanup.Control.ready
              (Section53RuntimeLeftCleanup.selectedAction selected)
            tape := cleanedTape } ∧
        TuringMachine.Computes Section53RuntimeStateCompactor.machine
          { state := Section53RuntimeStateCompactor.Control.seekMarker
              (Section53RuntimeLeftCleanup.selectedAction selected)
            tape := cleanedTape }
          { state := Section53RuntimeStateCompactor.Control.ready
              (Section53RuntimeLeftCleanup.selectedAction selected)
            tape := finalTape } ∧
        Tape.Equiv
          (Section53RuntimeStateCompactor.targetConfig
            (Section53RuntimeLeftCleanup.selectedAction selected)
            selected.target protectedSuffix).tape
          finalTape := by
  rcases Section53RuntimeLeftCleanup.computes_from_action_target
      baseLeftRev selected
      (MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend oldState protectedSuffix) with
    ⟨cleanedTape, hcleanup, hcleaned⟩
  have hsource :
      Tape.Equiv
        (Section53RuntimeStateCompactor.sourceConfig
          (Section53RuntimeLeftCleanup.selectedAction selected)
          selected.target oldState protectedSuffix).tape
        cleanedTape := by
    exact Tape.Equiv.symm (by
      simpa [Section53RuntimeStateCompactor.sourceConfig,
        Section53RuntimeStateCompactor.sourceWord] using hcleaned)
  rcases compactor_computes_of_tape_equiv
      (Section53RuntimeLeftCleanup.selectedAction selected)
      selected.target oldState
      protectedSuffix cleanedTape hsource with
    ⟨finalTape, hcompactor, hfinal⟩
  exact ⟨cleanedTape, finalTape, hcleanup, hcompactor, hfinal⟩
  done


end Section53RuntimeActionStateAssembly

end Computability
end FoC
