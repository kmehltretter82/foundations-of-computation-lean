import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.Projection
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Semantics.Acceptance
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.BoundaryContinuation

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.ParserCanonicalBranches

open FiniteRecognizer.Interpreter.ParserAssembly
open FiniteRecognizer.Interpreter.ParserPrefixPhaseSum
open FiniteRecognizer.Interpreter.ParserBranchPhaseSum
open FiniteRecognizer.Interpreter.InitializerFrontier

/-- Canonical branch-machine entry for a bounded description run. -/
def canonicalSourceConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.Control :=
  FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parserConfig
    (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSourceConfig D fuel input)

theorem canonicalSourceConfig_eq_sourceConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    canonicalSourceConfig D fuel input =
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.sourceConfig
        (MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeDescriptionAppend D input)) := by
  rfl

theorem canonicalSourceConfig_eq_initial
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    canonicalSourceConfig D fuel input =
      TuringMachine.initial FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
        (MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeDescriptionAppend D input)) := by
  rw [canonicalSourceConfig_eq_sourceConfig]
  exact FiniteRecognizer.Interpreter.ParserBranchPhaseSum.sourceConfig_eq_initial _

private theorem empty_terminal_to_directDecision
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (terminalTape : Tape MachineCodeSymbol)
    (hprefix : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine
        (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSourceConfig D fuel input)
        { state :=
            FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control.table
              (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.fuelZeroFlag fuel)
              (FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.parser
                TransitionListParserState.halt)
          tape := terminalTape })
    (htape : Tape.Equiv
      (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.zeroSavedTableTargetConfig
        (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel) input).tape
      terminalTape) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
        (canonicalSourceConfig D fuel input)
        (FiniteRecognizer.Interpreter.ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  have hbranchPrefix := FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parser_computes hprefix
  have htoProbe : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
      (canonicalSourceConfig D fuel input)
      { state := FiniteRecognizer.Interpreter.ParserBranchPhaseSum.Control.zeroProbe
        tape := terminalTape } := by
    simpa [canonicalSourceConfig,
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parserConfig,
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parserTarget,
      TuringMachine.PhaseEmbedding.liftConfig] using hbranchPrefix
  have hprobeTape : Tape.Equiv
      (FiniteRecognizer.Interpreter.ParserBranchPhaseSum.zeroProbeConfig
        (none ::
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
            fuel D.stateCount D.start D.halt).map some)
        input).tape terminalTape := by
    simpa [FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.zeroSavedTableTargetConfig,
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.zeroProbeConfig,
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev_eq_headerAfterHaltLeftRev]
      using htape
  rcases FiniteRecognizer.Interpreter.ParserBranchPhaseSum.zero_probe_then_decide_of_tape_equiv
      fuel D.stateCount D.start D.halt input terminalTape hprobeTape with
    ⟨finalTape, hfinish⟩
  exact ⟨finalTape, TuringMachine.computes_trans htoProbe hfinish⟩

private theorem zero_nonempty_terminal_to_directDecision
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol)
    (terminalTape : Tape MachineCodeSymbol)
    (hprefix : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine
        (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSourceConfig D 0 input)
        { state :=
            FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control.table true
              (FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready
                (transitionListParserSavedHead input))
          tape := terminalTape })
    (htape : Tape.Equiv
      (markedParserMaterializerSourceTape
        (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D 0)
        first rest input)
      terminalTape) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
        (canonicalSourceConfig D 0 input)
        (FiniteRecognizer.Interpreter.ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  have hbranchPrefix := FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parser_computes hprefix
  have htoExtract : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
      (canonicalSourceConfig D 0 input)
      { state := FiniteRecognizer.Interpreter.ParserBranchPhaseSum.Control.extract
          FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.preserveContextBlank
        tape := terminalTape } := by
    simpa [canonicalSourceConfig,
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parserConfig,
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parserTarget,
      TuringMachine.PhaseEmbedding.liftConfig] using hbranchPrefix
  let symbols := MachineDescription.encodeTransitions (first :: rest)
  cases hpayload : FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.parserPayloadWord
      symbols input with
  | nil =>
      exact False.elim
        (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.parserPayloadWord_ne_nil
          symbols input hpayload)
  | cons payloadFirst payloadRest =>
      have hcanonicalTape :
          markedParserMaterializerSourceTape
              (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D 0)
              first rest input =
            (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
              (parsedTableLeftRev (first :: rest).length ++
                (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
                  0 D.stateCount D.start D.halt).map some)
              payloadFirst payloadRest).tape := by
        calc
          markedParserMaterializerSourceTape
              (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D 0)
              first rest input =
            FiniteRecognizer.Interpreter.ParserAssembly.TransitionParserContextTransport.appendLeftContext
                (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D 0)
                (parsedTransitionHaltConfig (first :: rest).length
                  (MachineDescription.encodeTransitions (first :: rest))
                  input).tape := by
                    rfl
          _ =
            (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
              (parsedTableLeftRev (first :: rest).length ++
                (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D 0).map
                  some)
              payloadFirst payloadRest).tape := by
                simpa [symbols] using
                  (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextual_parser_endpoint_tape
                      (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D 0)
                      symbols input (first :: rest).length payloadFirst
                      payloadRest hpayload)
          _ =
            (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
              (parsedTableLeftRev (first :: rest).length ++
                (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
                  0 D.stateCount D.start D.halt).map some)
              payloadFirst payloadRest).tape := by
                rfl
      have hsource : Tape.Equiv
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
            (parsedTableLeftRev (first :: rest).length ++
              (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
                0 D.stateCount D.start D.halt).map some)
            payloadFirst payloadRest).tape terminalTape := by
        rw [← hcanonicalTape]
        exact htape
      have hextract :=
        FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextual_extractor_computes
          0 D.stateCount D.start D.halt (first :: rest).length
          payloadFirst payloadRest
      rcases FiniteRecognizer.Interpreter.ParserBranchPhaseSum.extract_then_decide_of_tape_equiv
          FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.preserveContextBlank
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
            (parsedTableLeftRev (first :: rest).length ++
              (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
                0 D.stateCount D.start D.halt).map some)
            payloadFirst payloadRest).tape
          terminalTape
          ((FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.olderMetadataLeftRev
            0 D.stateCount).length + 2)
          D.start D.halt
          ((MachineCodeSymbol.done ::
            List.replicate (first :: rest).length
              MachineCodeSymbol.blank).length +
            (payloadRest.length + 1)).succ
          hextract hsource with
        ⟨finalTape, hfinish⟩
      exact ⟨finalTape, TuringMachine.computes_trans htoExtract hfinish⟩

private theorem positive_terminal_to_ready
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (terminalTape : Tape MachineCodeSymbol)
    (hprefix : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine
        (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSourceConfig D
          (remainingFuel + 1) input)
        { state :=
            FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control.table false
              (FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready
                (transitionListParserSavedHead input))
          tape := terminalTape })
    (htape : Tape.Equiv
      (markedParserMaterializerSourceTape
        (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
          (remainingFuel + 1))
        first rest input)
      terminalTape) :
    TuringMachine.Computes FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
        (canonicalSourceConfig D (remainingFuel + 1) input)
        { state := FiniteRecognizer.Interpreter.ParserBranchPhaseSum.Control.positiveReady
            (transitionListParserSavedHead input)
          tape := terminalTape } ∧
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
            (remainingFuel + 1))
          first rest input)
        terminalTape := by
  refine ⟨?_, htape⟩
  have hbranchPrefix := FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parser_computes hprefix
  simpa [canonicalSourceConfig,
    FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parserConfig,
    FiniteRecognizer.Interpreter.ParserBranchPhaseSum.parserTarget,
    TuringMachine.PhaseEmbedding.liftConfig] using hbranchPrefix

private theorem nonempty_terminal_data_of_marked_projection
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (hmarked : forall canonicalTarget :
        TuringMachine.Configuration MachineCodeSymbol
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control,
      TuringMachine.Computes FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
          (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSavedTableSourceConfig
            D fuel input)
          canonicalTarget ->
      canonicalTarget.state =
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input) ->
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel)
          first rest input)
        canonicalTarget.tape) :
    exists terminalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine
        (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSourceConfig D fuel input)
        { state :=
            FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control.table
              (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.fuelZeroFlag fuel)
              (FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready
                (transitionListParserSavedHead input))
          tape := terminalTape } ∧
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel)
          first rest input)
        terminalTape := by
  rcases
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonical_nonemptyTable_computes_to_terminal_with_tape_equiv
        D first rest htransitions fuel input with
    ⟨⟨terminalState, terminalTape⟩, canonicalTarget,
      hprefix, hcanonical, hterminalState, hcanonicalState, htape⟩
  simp only at hterminalState
  subst terminalState
  exact ⟨terminalTape, hprefix,
    Tape.Equiv.trans
      (hmarked canonicalTarget hcanonical hcanonicalState) htape⟩

/-- A canonical nonempty table at zero fuel takes the direct final-decision
branch after the exact marked parser endpoint is projected through the prefix
machine. -/
theorem zeroNonemptyTable_computes_to_directDecision
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = first :: rest) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
        (canonicalSourceConfig D 0 input)
        (FiniteRecognizer.Interpreter.ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  have hmarked : forall canonicalTarget :
      TuringMachine.Configuration MachineCodeSymbol
        FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control,
      TuringMachine.Computes FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
          (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSavedTableSourceConfig
            D 0 input)
          canonicalTarget ->
      canonicalTarget.state =
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input) ->
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D 0)
          first rest input)
        canonicalTarget.tape := by
    intro canonicalTarget hrun hstate
    apply
      FiniteRecognizer.Interpreter.ExactBoundaryContinuation.contextualNonemptyReadyTapeEquivMarked
        (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D 0)
        first rest input canonicalTarget
    · simpa [FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSavedTableSourceConfig,
        htransitions] using hrun
    · exact hstate
  rcases nonempty_terminal_data_of_marked_projection
      D first rest htransitions 0 input hmarked with
    ⟨terminalTape, hprefix, htape⟩
  exact zero_nonempty_terminal_to_directDecision
    D first rest input terminalTape hprefix htape

/-- A canonical positive-fuel nonempty table reaches the exact positive-ready
branch state, and its physical tape remains in the marked materializer
currency expected by the initializer. -/
theorem positiveNonemptyTable_computes_to_ready
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = first :: rest) :
    exists parserTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
          (canonicalSourceConfig D (remainingFuel + 1) input)
          { state := FiniteRecognizer.Interpreter.ParserBranchPhaseSum.Control.positiveReady
              (transitionListParserSavedHead input)
            tape := parserTape } ∧
        Tape.Equiv
          (markedParserMaterializerSourceTape
            (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
              (remainingFuel + 1))
            first rest input)
          parserTape := by
  have hmarked : forall canonicalTarget :
      TuringMachine.Configuration MachineCodeSymbol
        FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control,
      TuringMachine.Computes FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
          (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSavedTableSourceConfig
            D (remainingFuel + 1) input)
          canonicalTarget ->
      canonicalTarget.state =
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input) ->
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
            (remainingFuel + 1))
          first rest input)
        canonicalTarget.tape := by
    intro canonicalTarget hrun hstate
    apply
      FiniteRecognizer.Interpreter.ExactBoundaryContinuation.contextualNonemptyReadyTapeEquivMarked
        (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
          (remainingFuel + 1))
        first rest input canonicalTarget
    · simpa [FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonicalSavedTableSourceConfig,
        htransitions] using hrun
    · exact hstate
  rcases nonempty_terminal_data_of_marked_projection
      D first rest htransitions (remainingFuel + 1) input hmarked with
    ⟨parserTape, hprefix, htape⟩
  refine ⟨parserTape, ?_⟩
  exact positive_terminal_to_ready
    D first rest remainingFuel input parserTape
    (by
      simpa [FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.fuelZeroFlag] using hprefix)
    htape

/-- A canonical empty transition table takes the direct final-decision branch
at every fuel. -/
theorem emptyTable_computes_to_directDecision
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = []) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
        (canonicalSourceConfig D fuel input)
        (FiniteRecognizer.Interpreter.ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  rcases
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.canonical_zeroTable_computes_to_terminal_with_tape_equiv
          D htransitions fuel input with
    ⟨⟨terminalState, terminalTape⟩, hprefix, hstate, htape⟩
  simp only at hstate
  subst terminalState
  exact empty_terminal_to_directDecision D fuel input terminalTape
    hprefix htape

/-- The complete direct side of the outer canonical contract: either zero fuel
or an empty transition table reaches the direct decision state. -/
theorem directBranch_computes_to_directDecision
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (hbranch : fuel = 0 ∨ D.transitions = []) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
        (canonicalSourceConfig D fuel input)
        (FiniteRecognizer.Interpreter.ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  rcases hbranch with hfuel | hempty
  · subst fuel
    cases htransitions : D.transitions with
    | nil =>
        exact emptyTable_computes_to_directDecision
          D 0 input htransitions
    | cons first rest =>
        exact zeroNonemptyTable_computes_to_directDecision
          D first rest input htransitions
  · exact emptyTable_computes_to_directDecision
      D fuel input hempty

/-- Operational acceptance of the canonical empty-table parser branch is the
public bounded semantic predicate. -/
theorem emptyTable_haltsFrom_iff_haltsIn
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = []) :
    TuringMachine.HaltsFrom FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
        (canonicalSourceConfig D fuel input) ↔
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input) := by
  rcases emptyTable_computes_to_directDecision
      D fuel input htransitions with
    ⟨finalTape, hrun⟩
  exact FiniteRecognizer.Interpreter.SemanticAcceptance.parser_direct_haltsFrom_iff_haltsIn
    D fuel input (Or.inr htransitions)
    (canonicalSourceConfig D fuel input) finalTape hrun


end FiniteRecognizer.Interpreter.ParserCanonicalBranches

end Computability
end FoC
