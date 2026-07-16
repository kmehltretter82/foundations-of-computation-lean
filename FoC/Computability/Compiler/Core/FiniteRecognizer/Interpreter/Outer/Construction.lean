import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.PhaseSum
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Positive.Machine
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.Canonical
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.PrefixEvidence

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.Construction

open FiniteRecognizer.Interpreter.InitializerFrontier

abbrev InitializerControl :=
  FiniteRecognizer.Interpreter.PositiveInitializerMachine.Machine.Control

abbrev initializer : TuringMachine MachineCodeSymbol InitializerControl :=
  FiniteRecognizer.Interpreter.PositiveInitializerMachine.Machine.machine

abbrev initializerEntry : Option MachineCodeSymbol -> InitializerControl :=
  FiniteRecognizer.Interpreter.PositiveInitializerMachine.Machine.entry

abbrev initializerReady : InitializerControl :=
  FiniteRecognizer.Interpreter.PositiveInitializerMachine.Machine.ready

theorem entry_ne_ready (saved : Option MachineCodeSymbol) :
    initializerEntry saved ≠ initializerReady := by
  simp only [initializerEntry, initializerReady,
    FiniteRecognizer.Interpreter.PositiveInitializerMachine.Machine.entry,
    FiniteRecognizer.Interpreter.PositiveInitializerMachine.Machine.ready,
    FiniteRecognizer.Interpreter.PositiveInitializerMachine.Machine.liftMaterializerControl]
  split <;> simp

theorem ready_transition_none (read : Option MachineCodeSymbol) :
    initializer.transition initializerReady read = none := by
  rfl

/-- Contract for the initializer half of the positive canonical phase, after
the parser branch reaches the marked tape. -/
def PositiveInitializerContract : Prop :=
  forall (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (_htransitions : D.transitions = first :: rest)
    (parserTape : Tape MachineCodeSymbol),
    Tape.Equiv
        (markedParserMaterializerSourceTape
          (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
            (remainingFuel + 1))
          first rest input)
        parserTape ->
      exists initializerTape : Tape MachineCodeSymbol,
        TuringMachine.Computes initializer
          { state := initializerEntry (transitionListParserSavedHead input)
            tape := parserTape }
          { state := initializerReady
            tape := initializerTape } ∧
        Tape.Equiv
          (FiniteRecognizer.Interpreter.BoundedLoopInduction.loopSourceConfig
            (initialConfiguration D input)
            (first :: rest) remainingFuel D.halt []).tape
          initializerTape

/-- Assemble the canonical phase contract from the positive initializer
contract. -/
def canonicalPhaseContract
    (positive : PositiveInitializerContract) :
    FiniteRecognizer.Interpreter.OuterPhaseSumGeneric.CanonicalPhaseContract
      initializer initializerEntry initializerReady where
  entry_ne_ready := entry_ne_ready
  ready_transition_none := ready_transition_none
  direct :=
    FiniteRecognizer.Interpreter.ParserCanonicalBranches.directBranch_computes_to_directDecision
  positive := by
    intro D first rest remainingFuel input htransitions
    rcases
        FiniteRecognizer.Interpreter.ParserCanonicalBranches.positiveNonemptyTable_computes_to_ready
          D first rest remainingFuel input htransitions with
      ⟨parserTape, hparser, hmarked⟩
    rcases positive D first rest remainingFuel input htransitions
        parserTape hmarked with
      ⟨initializerTape, hinitializer, htape⟩
    exact ⟨parserTape, initializerTape, hparser, hinitializer, htape⟩

def construction_of_positive
    (positive : PositiveInitializerContract) :
    FiniteRecognizer.DecodedDescriptionInterpreterConstruction :=
  FiniteRecognizer.Interpreter.OuterPhaseSumGeneric.construction
    initializer initializerEntry initializerReady
    (canonicalPhaseContract positive)
    FiniteRecognizer.Interpreter.SuccessfulPrefixEvidence.contract

def finStateConstruction_of_positive
    (positive : PositiveInitializerContract) :
    FiniteRecognizer.DecodedDescriptionInterpreterFinStateConstruction :=
  FiniteRecognizer.Interpreter.OuterPhaseSumGeneric.finStateConstruction
    initializer initializerEntry initializerReady
    (canonicalPhaseContract positive)
    FiniteRecognizer.Interpreter.SuccessfulPrefixEvidence.contract

theorem positiveInitializerContract : PositiveInitializerContract := by
  intro D first rest remainingFuel input htransitions parserTape hparser
  exact
    FiniteRecognizer.Interpreter.PositiveInitializerMachine.positive_nonempty_computes_from_parser_tape
      D remainingFuel input first rest htransitions parserTape hparser

def construction :
    FiniteRecognizer.DecodedDescriptionInterpreterConstruction :=
  construction_of_positive positiveInitializerContract

def finStateConstruction :
    FiniteRecognizer.DecodedDescriptionInterpreterFinStateConstruction :=
  finStateConstruction_of_positive positiveInitializerContract


end FiniteRecognizer.Interpreter.Construction
end Computability
end FoC
