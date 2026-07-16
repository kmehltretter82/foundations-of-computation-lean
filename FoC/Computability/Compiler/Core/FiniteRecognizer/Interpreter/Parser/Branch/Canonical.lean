import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.Projection
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Semantics.Acceptance
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.BoundaryContinuation

namespace FoC
namespace Computability

open Languages

namespace Section53ParserCanonicalBranches

open Section53ParserAssembly
open Section53ParserPrefixPhaseSum
open Section53ParserBranchPhaseSum
open Section53InitializerFrontier

/-- Canonical branch-machine entry for a bounded description run. -/
def canonicalSourceConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Section53ParserBranchPhaseSum.Control :=
  Section53ParserBranchPhaseSum.parserConfig
    (Section53ParserPrefixPhaseSum.canonicalSourceConfig D fuel input)

theorem canonicalSourceConfig_eq_sourceConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    canonicalSourceConfig D fuel input =
      Section53ParserBranchPhaseSum.sourceConfig
        (MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeDescriptionAppend D input)) := by
  rfl

theorem canonicalSourceConfig_eq_initial
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    canonicalSourceConfig D fuel input =
      TuringMachine.initial Section53ParserBranchPhaseSum.machine
        (MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeDescriptionAppend D input)) := by
  rw [canonicalSourceConfig_eq_sourceConfig]
  exact Section53ParserBranchPhaseSum.sourceConfig_eq_initial _

private theorem empty_terminal_to_directDecision
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (terminalTape : Tape MachineCodeSymbol)
    (hprefix : TuringMachine.Computes
      Section53ParserPrefixPhaseSum.machine
        (Section53ParserPrefixPhaseSum.canonicalSourceConfig D fuel input)
        { state :=
            Section53ParserPrefixPhaseSum.Control.table
              (Section53ParserPrefixPhaseSum.fuelZeroFlag fuel)
              (Section53SavedCellTransitionParser.Control.parser
                TransitionListParserState.halt)
          tape := terminalTape })
    (htape : Tape.Equiv
      (Section53ParserPrefixPhaseSum.zeroSavedTableTargetConfig
        (Section53ParserAssembly.headerAfterHaltLeftRev D fuel) input).tape
      terminalTape) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Section53ParserBranchPhaseSum.machine
        (canonicalSourceConfig D fuel input)
        (Section53ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  have hbranchPrefix := Section53ParserBranchPhaseSum.parser_computes hprefix
  have htoProbe : TuringMachine.Computes
      Section53ParserBranchPhaseSum.machine
      (canonicalSourceConfig D fuel input)
      { state := Section53ParserBranchPhaseSum.Control.zeroProbe
        tape := terminalTape } := by
    simpa [canonicalSourceConfig,
      Section53ParserBranchPhaseSum.parserConfig,
      Section53ParserBranchPhaseSum.parserTarget,
      TuringMachine.PhaseEmbedding.liftConfig] using hbranchPrefix
  have hprobeTape : Tape.Equiv
      (Section53ParserBranchPhaseSum.zeroProbeConfig
        (none ::
          (Section53ZeroEmptyMetadataFinal.metadataLeftRev
            fuel D.stateCount D.start D.halt).map some)
        input).tape terminalTape := by
    simpa [Section53ParserPrefixPhaseSum.zeroSavedTableTargetConfig,
      Section53ParserBranchPhaseSum.zeroProbeConfig,
      Section53ZeroEmptyMetadataFinal.metadataLeftRev_eq_headerAfterHaltLeftRev]
      using htape
  rcases Section53ParserBranchPhaseSum.zero_probe_then_decide_of_tape_equiv
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
      Section53ParserPrefixPhaseSum.machine
        (Section53ParserPrefixPhaseSum.canonicalSourceConfig D 0 input)
        { state :=
            Section53ParserPrefixPhaseSum.Control.table true
              (Section53SavedCellTransitionParser.Control.ready
                (transitionListParserSavedHead input))
          tape := terminalTape })
    (htape : Tape.Equiv
      (markedParserMaterializerSourceTape
        (Section53ParserAssembly.headerAfterHaltLeftRev D 0)
        first rest input)
      terminalTape) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Section53ParserBranchPhaseSum.machine
        (canonicalSourceConfig D 0 input)
        (Section53ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  have hbranchPrefix := Section53ParserBranchPhaseSum.parser_computes hprefix
  have htoExtract : TuringMachine.Computes
      Section53ParserBranchPhaseSum.machine
      (canonicalSourceConfig D 0 input)
      { state := Section53ParserBranchPhaseSum.Control.extract
          Section53ZeroEmptyMetadataFinal.Control.preserveContextBlank
        tape := terminalTape } := by
    simpa [canonicalSourceConfig,
      Section53ParserBranchPhaseSum.parserConfig,
      Section53ParserBranchPhaseSum.parserTarget,
      TuringMachine.PhaseEmbedding.liftConfig] using hbranchPrefix
  let symbols := MachineDescription.encodeTransitions (first :: rest)
  cases hpayload : Section53ZeroEmptyMetadataFinal.parserPayloadWord
      symbols input with
  | nil =>
      exact False.elim
        (Section53ZeroEmptyMetadataFinal.parserPayloadWord_ne_nil
          symbols input hpayload)
  | cons payloadFirst payloadRest =>
      have hcanonicalTape :
          markedParserMaterializerSourceTape
              (Section53ParserAssembly.headerAfterHaltLeftRev D 0)
              first rest input =
            (Section53ZeroEmptyMetadataFinal.contextSourceConfig
              (parsedTableLeftRev (first :: rest).length ++
                (Section53ZeroEmptyMetadataFinal.metadataLeftRev
                  0 D.stateCount D.start D.halt).map some)
              payloadFirst payloadRest).tape := by
        calc
          markedParserMaterializerSourceTape
              (Section53ParserAssembly.headerAfterHaltLeftRev D 0)
              first rest input =
            Section53ParserAssembly.TransitionParserContextTransport.appendLeftContext
                (Section53ParserAssembly.headerAfterHaltLeftRev D 0)
                (parsedTransitionHaltConfig (first :: rest).length
                  (MachineDescription.encodeTransitions (first :: rest))
                  input).tape := by
                    rfl
          _ =
            (Section53ZeroEmptyMetadataFinal.contextSourceConfig
              (parsedTableLeftRev (first :: rest).length ++
                (Section53ParserAssembly.headerAfterHaltLeftRev D 0).map
                  some)
              payloadFirst payloadRest).tape := by
                simpa [symbols] using
                  (Section53ZeroEmptyMetadataFinal.contextual_parser_endpoint_tape
                      (Section53ParserAssembly.headerAfterHaltLeftRev D 0)
                      symbols input (first :: rest).length payloadFirst
                      payloadRest hpayload)
          _ =
            (Section53ZeroEmptyMetadataFinal.contextSourceConfig
              (parsedTableLeftRev (first :: rest).length ++
                (Section53ZeroEmptyMetadataFinal.metadataLeftRev
                  0 D.stateCount D.start D.halt).map some)
              payloadFirst payloadRest).tape := by
                rfl
      have hsource : Tape.Equiv
          (Section53ZeroEmptyMetadataFinal.contextSourceConfig
            (parsedTableLeftRev (first :: rest).length ++
              (Section53ZeroEmptyMetadataFinal.metadataLeftRev
                0 D.stateCount D.start D.halt).map some)
            payloadFirst payloadRest).tape terminalTape := by
        rw [← hcanonicalTape]
        exact htape
      have hextract :=
        Section53ZeroEmptyMetadataFinal.contextual_extractor_computes
          0 D.stateCount D.start D.halt (first :: rest).length
          payloadFirst payloadRest
      rcases Section53ParserBranchPhaseSum.extract_then_decide_of_tape_equiv
          Section53ZeroEmptyMetadataFinal.Control.preserveContextBlank
          (Section53ZeroEmptyMetadataFinal.contextSourceConfig
            (parsedTableLeftRev (first :: rest).length ++
              (Section53ZeroEmptyMetadataFinal.metadataLeftRev
                0 D.stateCount D.start D.halt).map some)
            payloadFirst payloadRest).tape
          terminalTape
          ((Section53ZeroEmptyMetadataFinal.olderMetadataLeftRev
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
      Section53ParserPrefixPhaseSum.machine
        (Section53ParserPrefixPhaseSum.canonicalSourceConfig D
          (remainingFuel + 1) input)
        { state :=
            Section53ParserPrefixPhaseSum.Control.table false
              (Section53SavedCellTransitionParser.Control.ready
                (transitionListParserSavedHead input))
          tape := terminalTape })
    (htape : Tape.Equiv
      (markedParserMaterializerSourceTape
        (Section53ParserAssembly.headerAfterHaltLeftRev D
          (remainingFuel + 1))
        first rest input)
      terminalTape) :
    TuringMachine.Computes Section53ParserBranchPhaseSum.machine
        (canonicalSourceConfig D (remainingFuel + 1) input)
        { state := Section53ParserBranchPhaseSum.Control.positiveReady
            (transitionListParserSavedHead input)
          tape := terminalTape } ∧
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (Section53ParserAssembly.headerAfterHaltLeftRev D
            (remainingFuel + 1))
          first rest input)
        terminalTape := by
  refine ⟨?_, htape⟩
  have hbranchPrefix := Section53ParserBranchPhaseSum.parser_computes hprefix
  simpa [canonicalSourceConfig,
    Section53ParserBranchPhaseSum.parserConfig,
    Section53ParserBranchPhaseSum.parserTarget,
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
          Section53SavedCellTransitionParser.Control,
      TuringMachine.Computes Section53SavedCellTransitionParser.machine
          (Section53ParserPrefixPhaseSum.canonicalSavedTableSourceConfig
            D fuel input)
          canonicalTarget ->
      canonicalTarget.state =
          Section53SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input) ->
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (Section53ParserAssembly.headerAfterHaltLeftRev D fuel)
          first rest input)
        canonicalTarget.tape) :
    exists terminalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Section53ParserPrefixPhaseSum.machine
        (Section53ParserPrefixPhaseSum.canonicalSourceConfig D fuel input)
        { state :=
            Section53ParserPrefixPhaseSum.Control.table
              (Section53ParserPrefixPhaseSum.fuelZeroFlag fuel)
              (Section53SavedCellTransitionParser.Control.ready
                (transitionListParserSavedHead input))
          tape := terminalTape } ∧
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (Section53ParserAssembly.headerAfterHaltLeftRev D fuel)
          first rest input)
        terminalTape := by
  rcases
      Section53ParserPrefixPhaseSum.canonical_nonemptyTable_computes_to_terminal_with_tape_equiv
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
      TuringMachine.Computes Section53ParserBranchPhaseSum.machine
        (canonicalSourceConfig D 0 input)
        (Section53ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  have hmarked : forall canonicalTarget :
      TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control,
      TuringMachine.Computes Section53SavedCellTransitionParser.machine
          (Section53ParserPrefixPhaseSum.canonicalSavedTableSourceConfig
            D 0 input)
          canonicalTarget ->
      canonicalTarget.state =
          Section53SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input) ->
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (Section53ParserAssembly.headerAfterHaltLeftRev D 0)
          first rest input)
        canonicalTarget.tape := by
    intro canonicalTarget hrun hstate
    apply
      Section53ExactBoundaryContinuation.contextualNonemptyReadyTapeEquivMarked
        (Section53ParserAssembly.headerAfterHaltLeftRev D 0)
        first rest input canonicalTarget
    · simpa [Section53ParserPrefixPhaseSum.canonicalSavedTableSourceConfig,
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
      TuringMachine.Computes Section53ParserBranchPhaseSum.machine
          (canonicalSourceConfig D (remainingFuel + 1) input)
          { state := Section53ParserBranchPhaseSum.Control.positiveReady
              (transitionListParserSavedHead input)
            tape := parserTape } ∧
        Tape.Equiv
          (markedParserMaterializerSourceTape
            (Section53ParserAssembly.headerAfterHaltLeftRev D
              (remainingFuel + 1))
            first rest input)
          parserTape := by
  have hmarked : forall canonicalTarget :
      TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control,
      TuringMachine.Computes Section53SavedCellTransitionParser.machine
          (Section53ParserPrefixPhaseSum.canonicalSavedTableSourceConfig
            D (remainingFuel + 1) input)
          canonicalTarget ->
      canonicalTarget.state =
          Section53SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input) ->
      Tape.Equiv
        (markedParserMaterializerSourceTape
          (Section53ParserAssembly.headerAfterHaltLeftRev D
            (remainingFuel + 1))
          first rest input)
        canonicalTarget.tape := by
    intro canonicalTarget hrun hstate
    apply
      Section53ExactBoundaryContinuation.contextualNonemptyReadyTapeEquivMarked
        (Section53ParserAssembly.headerAfterHaltLeftRev D
          (remainingFuel + 1))
        first rest input canonicalTarget
    · simpa [Section53ParserPrefixPhaseSum.canonicalSavedTableSourceConfig,
        htransitions] using hrun
    · exact hstate
  rcases nonempty_terminal_data_of_marked_projection
      D first rest htransitions (remainingFuel + 1) input hmarked with
    ⟨parserTape, hprefix, htape⟩
  refine ⟨parserTape, ?_⟩
  exact positive_terminal_to_ready
    D first rest remainingFuel input parserTape
    (by
      simpa [Section53ParserPrefixPhaseSum.fuelZeroFlag] using hprefix)
    htape

/-- A canonical empty transition table takes the direct final-decision branch
at every fuel. -/
theorem emptyTable_computes_to_directDecision
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = []) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Section53ParserBranchPhaseSum.machine
        (canonicalSourceConfig D fuel input)
        (Section53ParserBranchPhaseSum.directDecisionConfig
          D.start D.halt finalTape) := by
  rcases
      Section53ParserPrefixPhaseSum.canonical_zeroTable_computes_to_terminal_with_tape_equiv
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
      TuringMachine.Computes Section53ParserBranchPhaseSum.machine
        (canonicalSourceConfig D fuel input)
        (Section53ParserBranchPhaseSum.directDecisionConfig
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
    TuringMachine.HaltsFrom Section53ParserBranchPhaseSum.machine
        (canonicalSourceConfig D fuel input) ↔
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input) := by
  rcases emptyTable_computes_to_directDecision
      D fuel input htransitions with
    ⟨finalTape, hrun⟩
  exact Section53SemanticAcceptance.parser_direct_haltsFrom_iff_haltsIn
    D fuel input (Or.inr htransitions)
    (canonicalSourceConfig D fuel input) finalTape hrun


end Section53ParserCanonicalBranches

end Computability
end FoC
