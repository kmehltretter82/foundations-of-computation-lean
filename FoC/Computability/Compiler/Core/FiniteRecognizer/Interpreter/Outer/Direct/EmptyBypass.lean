import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Assembly
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.FinalCompare

namespace FoC
namespace Computability

open Languages

namespace Section53EmptyTableFinalBypass

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Section53ParserAssembly
open Section53UniformInterpreterOneStep
open Section53UniformInterpreterOneStep.RuntimeKeySingleKeyRepair

/-!
# Empty-table and zero-fuel final-gate bypass

An empty transition table cannot change the simulated configuration at any
fuel, and fuel zero performs no semantic step. Both branches bypass
table-stack construction and enter the verified final-state comparator. The
parser path starts in the contextual count/table currency. Its endpoint may
contain harmless parser-window padding, so the materializer contract consumes
that endpoint together with its canonical tape equivalence and preserved blank
boundary. The contract is independent of a particular saved-cell
implementation.
-/

def inputBits (input : Word MachineCodeSymbol) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput input

def initialTape (input : Word MachineCodeSymbol) : Tape Bool :=
  Tape.input (inputBits input)

def initialConfiguration
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) : MachineDescription.Configuration :=
  D.initial (inputBits input)

def finalSuffix (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  protectedTapeContextsAppend (initialTape input) []

def finalComparatorSource
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeyComparatorState :=
  finalComparatorSourceConfig D.halt D.start (finalSuffix input)

def finalComparatorTarget
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeyComparatorState :=
  finalComparatorTargetConfig D.halt D.start (finalSuffix input)

theorem finalComparator_computes
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      (finalComparatorSource D input)
      (finalComparatorTarget D input) := by
  exact finalComparator_computes_exact D.halt D.start (finalSuffix input)

theorem finalComparator_haltsFrom_iff
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (finalComparatorSource D input) <->
      D.start = D.halt := by
  simpa [finalComparatorSource, eq_comm] using
    (Section53UniformInterpreterOneStep.finalComparator_haltsFrom_iff
      D.halt D.start (finalSuffix input))

theorem runConfig_zero
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    D.runConfig 0 (initialConfiguration D input) =
      initialConfiguration D input := by
  rfl

theorem runConfig_of_transitions_eq_nil
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = []) :
    D.runConfig fuel (initialConfiguration D input) =
      initialConfiguration D input := by
  cases fuel with
  | zero => rfl
  | succ remaining =>
      apply runConfig_fullScanNoMatch
      intro transition hmem
      rw [htransitions] at hmem
      simp at hmem

theorem zeroFuel_semanticFinal_iff
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (D.runConfig 0 (initialConfiguration D input)).state = D.halt <->
      D.start = D.halt := by
  rw [runConfig_zero]
  rfl

theorem emptyTable_semanticFinal_iff
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = []) :
    (D.runConfig fuel (initialConfiguration D input)).state = D.halt <->
      D.start = D.halt := by
  rw [runConfig_of_transitions_eq_nil D fuel input htransitions]
  rfl

theorem zeroFuel_finalComparator_halts_iff_semanticFinal
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (finalComparatorSource D input) <->
      (D.runConfig 0 (initialConfiguration D input)).state = D.halt := by
  rw [finalComparator_haltsFrom_iff,
    zeroFuel_semanticFinal_iff]

theorem emptyTable_finalComparator_halts_iff_semanticFinal
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = []) :
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (finalComparatorSource D input) <->
      (D.runConfig fuel (initialConfiguration D input)).state = D.halt := by
  rw [finalComparator_haltsFrom_iff,
    emptyTable_semanticFinal_iff D fuel input htransitions]

theorem directFinalBranch_halts_iff_semanticFinal
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (hbranch : fuel = 0 ∨ D.transitions = []) :
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (finalComparatorSource D input) <->
      (D.runConfig fuel (initialConfiguration D input)).state = D.halt := by
  rcases hbranch with hzero | hempty
  · subst fuel
    exact zeroFuel_finalComparator_halts_iff_semanticFinal D input
  · exact
      emptyTable_finalComparator_halts_iff_semanticFinal
        D fuel input hempty

/-! ## Repaired contextual parser endpoint -/

def contextualParserSource
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  TransitionParserContextTransport.contextualCanonicalSource
    (headerAfterHaltLeftRev D fuel) [] input

def contextualParserEndpoint
    (D : MachineDescription)
    (fuel : Nat)
    (cleanEndpoint :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  TransitionParserContextTransport.appendLeftContextConfig
    (headerAfterHaltLeftRev D fuel) cleanEndpoint

theorem contextualEmptyTable_parser_forward
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    exists cleanEndpoint :
        TuringMachine.Configuration MachineCodeSymbol
          TransitionListParserState,
      TuringMachine.Computes transitionListParserMachine
          (contextualParserSource D fuel input)
          (contextualParserEndpoint D fuel cleanEndpoint) ∧
        cleanEndpoint.state = TransitionListParserState.halt ∧
        Tape.Equiv (zeroTransitionHaltConfig input).tape
          cleanEndpoint.tape ∧
        TransitionParserContextTransport.configHasBlankBarrier
          cleanEndpoint := by
  obtain ⟨cleanEndpoint, hrun, hstate, htape, hbarrier⟩ :=
    TransitionParserContextTransport.contextualCanonicalSource_parser_forward
      (headerAfterHaltLeftRev D fuel) [] input
  refine ⟨cleanEndpoint, ?_, ?_, htape, hbarrier⟩
  · simpa [contextualParserSource, contextualParserEndpoint] using hrun
  · simpa [canonicalTransitionParserHaltConfig,
      zeroTransitionHaltConfig] using hstate

/-! ## Direct-branch materializer contract -/

/-- The direct-branch materializer consumes the padded zero-row parser endpoint
with retained header/fuel context, constructs the initial Boolean tape
contexts, and emits the exact source of the verified final comparator. -/
def EmptyTableFinalGateMaterializerContract
    {materializerState : Type}
    (materializer :
      TuringMachine MachineCodeSymbol materializerState)
    (entry halt : materializerState) : Prop :=
  forall (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (cleanEndpoint :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState),
    cleanEndpoint.state = TransitionListParserState.halt ->
    Tape.Equiv (zeroTransitionHaltConfig input).tape
      cleanEndpoint.tape ->
    TransitionParserContextTransport.configHasBlankBarrier
      cleanEndpoint ->
    TuringMachine.Computes materializer
      { state := entry
        tape := (contextualParserEndpoint D fuel cleanEndpoint).tape }
      { state := halt
        tape := (finalComparatorSource D input).tape }

theorem contextualParser_to_finalComparator_of_contract
    {materializerState : Type}
    (materializer :
      TuringMachine MachineCodeSymbol materializerState)
    (entry halt : materializerState)
    (hcontract :
      EmptyTableFinalGateMaterializerContract materializer entry halt)
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    exists cleanEndpoint :
        TuringMachine.Configuration MachineCodeSymbol
          TransitionListParserState,
      TuringMachine.Computes transitionListParserMachine
          (contextualParserSource D fuel input)
          (contextualParserEndpoint D fuel cleanEndpoint) ∧
        cleanEndpoint.state = TransitionListParserState.halt ∧
        Tape.Equiv (zeroTransitionHaltConfig input).tape
          cleanEndpoint.tape ∧
        TransitionParserContextTransport.configHasBlankBarrier
          cleanEndpoint ∧
        TuringMachine.Computes materializer
          { state := entry
            tape := (contextualParserEndpoint D fuel cleanEndpoint).tape }
          { state := halt
            tape := (finalComparatorSource D input).tape } := by
  rcases contextualEmptyTable_parser_forward D fuel input with
    ⟨cleanEndpoint, hparser, hstate, htape, hbarrier⟩
  refine ⟨cleanEndpoint, hparser, hstate, htape, hbarrier, ?_⟩
  exact hcontract D fuel input cleanEndpoint hstate htape hbarrier


end Section53EmptyTableFinalBypass
end Computability
end FoC
