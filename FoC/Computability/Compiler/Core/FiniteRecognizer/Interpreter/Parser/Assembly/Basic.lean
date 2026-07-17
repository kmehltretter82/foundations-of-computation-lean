import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Input
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CleanupGap
import FoC.Computability.Compiler.UniversalAndRanges.HeaderParser
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.MarkerRestore.Runs
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Soundness

namespace FoC
namespace Computability

open Languages
open FiniteRecognizer ExactFuel StrictProbe

namespace FiniteRecognizer.Interpreter.ParserAssembly

/-!
# Parser assembly

The forward route keeps outer fuel on the physical left stack, parses the
description header through the halt field, and leaves the transition count
under the head. ContextualPrefixRightShiftOne supplies the physical handoff
into the transition-table parser.
-/

def outerFuelSourceConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      ProductInput.PairFuelParser.Control :=
  ProductInput.PairFuelParser.config .outer []
    (MachineDescription.encodeNatAppend fuel
      (MachineDescription.encodeDescriptionAppend D input))

def outerFuelEndpointConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      ProductInput.PairFuelParser.Control :=
  ProductInput.PairFuelParser.config .inner
    (MachineDescription.encodeNat fuel).reverse
    (MachineDescription.encodeDescriptionAppend D input)

theorem outerFuelParser_run_exact
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    ProductInput.PairFuelParser.machine.runConfigExact? (fuel + 1)
        (outerFuelSourceConfig D fuel input) =
      some (outerFuelEndpointConfig D fuel input) := by
  simpa [outerFuelSourceConfig, outerFuelEndpointConfig] using
    ProductInput.PairFuelParser.outer_run fuel
      ([] : Word MachineCodeSymbol)
      (MachineDescription.encodeDescriptionAppend D input)

def headerParserSourceConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      HeaderFieldsParserState :=
  { state := HeaderFieldsParserState.needHeader
    tape :=
      headerFieldsParserTape
        (MachineDescription.encodeNat fuel).reverse
        (MachineDescription.encodeDescriptionAppend D input) }

theorem outerFuelEndpoint_headerSource_tape
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    (outerFuelEndpointConfig D fuel input).tape =
      (headerParserSourceConfig D fuel input).tape := by
  rfl

def headerAfterHeaderLeftRev
    (fuel : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    (MachineDescription.encodeNat fuel).reverse

def headerAfterStateLeftRev
    (D : MachineDescription)
    (fuel : Nat) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat D.stateCount).reverse
    (headerAfterHeaderLeftRev fuel)

def headerAfterStartLeftRev
    (D : MachineDescription)
    (fuel : Nat) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat D.start).reverse
    (headerAfterStateLeftRev D fuel)

def headerAfterHaltLeftRev
    (D : MachineDescription)
    (fuel : Nat) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat D.halt).reverse
    (headerAfterStartLeftRev D fuel)

def headerParserTransitionCountConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      HeaderFieldsParserState :=
  { state := HeaderFieldsParserState.transitionCount
    tape :=
      headerFieldsParserTape
        (headerAfterHaltLeftRev D fuel)
        (MachineDescription.encodeNatAppend D.transitions.length
          (MachineDescription.encodeTransitionsAppend D.transitions
            input)) }

theorem headerParser_computes_to_transitionCount_exact
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Computes headerFieldsParserMachine
      (headerParserSourceConfig D fuel input)
      (headerParserTransitionCountConfig D fuel input) := by
  let suffixState : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend D.start
      (MachineDescription.encodeNatAppend D.halt
        (MachineDescription.encodeNatAppend D.transitions.length
          (MachineDescription.encodeTransitionsAppend D.transitions
            input)))
  let suffixStart : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend D.halt
      (MachineDescription.encodeNatAppend D.transitions.length
        (MachineDescription.encodeTransitionsAppend D.transitions input))
  let suffixHalt : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend D.transitions.length
      (MachineDescription.encodeTransitionsAppend D.transitions input)
  have hheader :
      TuringMachine.Step headerFieldsParserMachine
        (headerParserSourceConfig D fuel input)
        { state := HeaderFieldsParserState.stateCount
          tape :=
            headerFieldsParserTape
              (headerAfterHeaderLeftRev fuel)
              (MachineDescription.encodeNatAppend D.stateCount
                suffixState) } := by
    simpa [headerParserSourceConfig, headerAfterHeaderLeftRev,
      MachineDescription.encodeDescriptionAppend, suffixState] using
      headerFieldsParserMachine_step_header
        (MachineDescription.encodeNat fuel).reverse
        (MachineDescription.encodeNatAppend D.stateCount suffixState)
  have hstateIn :
      TuringMachine.ComputesIn headerFieldsParserMachine
        (D.stateCount + 1)
        { state := HeaderFieldsParserState.stateCount
          tape :=
            headerFieldsParserTape
              (headerAfterHeaderLeftRev fuel)
              (MachineDescription.encodeNatAppend D.stateCount
                suffixState) }
        { state := HeaderFieldsParserState.startField
          tape :=
            headerFieldsParserTape
              (headerAfterStateLeftRev D fuel) suffixState } := by
    simpa [headerAfterStateLeftRev] using
      headerFieldsParserMachine_computesIn_nat
        headerFieldsParserMachine_step_tick_stateCount
        headerFieldsParserMachine_step_done_stateCount
        (headerAfterHeaderLeftRev fuel) D.stateCount suffixState
  have hstartIn :
      TuringMachine.ComputesIn headerFieldsParserMachine
        (D.start + 1)
        { state := HeaderFieldsParserState.startField
          tape :=
            headerFieldsParserTape
              (headerAfterStateLeftRev D fuel)
              (MachineDescription.encodeNatAppend D.start suffixStart) }
        { state := HeaderFieldsParserState.haltField
          tape :=
            headerFieldsParserTape
              (headerAfterStartLeftRev D fuel) suffixStart } := by
    simpa [headerAfterStartLeftRev] using
      headerFieldsParserMachine_computesIn_nat
        headerFieldsParserMachine_step_tick_startField
        headerFieldsParserMachine_step_done_startField
        (headerAfterStateLeftRev D fuel) D.start suffixStart
  have hhaltIn :
      TuringMachine.ComputesIn headerFieldsParserMachine
        (D.halt + 1)
        { state := HeaderFieldsParserState.haltField
          tape :=
            headerFieldsParserTape
              (headerAfterStartLeftRev D fuel)
              (MachineDescription.encodeNatAppend D.halt suffixHalt) }
        (headerParserTransitionCountConfig D fuel input) := by
    simpa [headerParserTransitionCountConfig,
      headerAfterHaltLeftRev] using
      headerFieldsParserMachine_computesIn_nat
        headerFieldsParserMachine_step_tick_haltField
        headerFieldsParserMachine_step_done_haltField
        (headerAfterStartLeftRev D fuel) D.halt suffixHalt
  have hstate := TuringMachine.computesIn_to_computes hstateIn
  have hstart := TuringMachine.computesIn_to_computes hstartIn
  have hhalt := TuringMachine.computesIn_to_computes hhaltIn
  exact
    TuringMachine.Computes.step hheader
      (TuringMachine.computes_trans hstate
        (TuringMachine.computes_trans
          (by simpa [suffixState] using hstart)
          (by simpa [suffixStart, suffixHalt] using hhalt)))

theorem headerFieldsParserTape_eq_transitionListParserOptionTape
    (leftRev rest : Word MachineCodeSymbol) :
    headerFieldsParserTape leftRev rest =
      transitionListParserOptionTape
        (leftRev.map some) (rest.map some) := by
  cases rest <;> rfl

def cleanTransitionParserSourceConfig
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  TuringMachine.initial transitionListParserMachine
    (MachineDescription.encodeNatAppend D.transitions.length
      (MachineDescription.encodeTransitionsAppend D.transitions input))

def contextualTransitionParserSourceConfig
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state :=
      TransitionListParserState.findCount
        TransitionListParserMarker.initial
    tape := (headerParserTransitionCountConfig D fuel input).tape }

theorem headerEndpoint_contextualTransitionSource_tape
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    (headerParserTransitionCountConfig D fuel input).tape =
      (contextualTransitionParserSourceConfig D fuel input).tape := by
  rfl

theorem dropTrailingNone_map_some
    (symbols : Word MachineCodeSymbol) :
    Tape.dropTrailingNone (symbols.map some) = symbols.map some := by
  induction symbols with
  | nil => rfl
  | cons symbol rest ih =>
      simp [Tape.dropTrailingNone, ih]

theorem headerAfterHaltLeftRev_ne_nil
    (D : MachineDescription)
    (fuel : Nat) :
    headerAfterHaltLeftRev D fuel ≠ [] := by
  intro hempty
  have hlength := congrArg List.length hempty
  simp [headerAfterHaltLeftRev, headerAfterStartLeftRev,
    headerAfterStateLeftRev, headerAfterHeaderLeftRev] at hlength

theorem transitionListParserOptionTape_equiv_left
    {leftRev₁ leftRev₂ rest : List (Option MachineCodeSymbol)}
    (hequiv :
      Tape.Equiv
        (transitionListParserOptionTape leftRev₁ rest)
        (transitionListParserOptionTape leftRev₂ rest)) :
    Tape.dropTrailingNone leftRev₁ =
      Tape.dropTrailingNone leftRev₂ := by
  cases rest <;> exact hequiv.1

/-- The header endpoint is not even tape-equivalent to the clean source used
by the transition-list parser's existing forward and inversion theorems. -/
theorem cleanTransitionSource_not_equiv_contextualHeaderEndpoint
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    ¬ Tape.Equiv
      (cleanTransitionParserSourceConfig D input).tape
      (contextualTransitionParserSourceConfig D fuel input).tape := by
  let tokens : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend D.transitions.length
      (MachineDescription.encodeTransitionsAppend D.transitions input)
  have hclean :
      (cleanTransitionParserSourceConfig D input).tape =
        transitionListParserOptionTape [] (tokens.map some) := by
    change Tape.input tokens = _
    exact (transitionListParserOptionTape_nil_eq_input tokens).symm
  have hcontext :
      (contextualTransitionParserSourceConfig D fuel input).tape =
        transitionListParserOptionTape
          ((headerAfterHaltLeftRev D fuel).map some)
          (tokens.map some) := by
    change
      headerFieldsParserTape (headerAfterHaltLeftRev D fuel) tokens = _
    exact
      headerFieldsParserTape_eq_transitionListParserOptionTape
        (headerAfterHaltLeftRev D fuel) tokens
  intro hequiv
  rw [hclean, hcontext] at hequiv
  have hleft := transitionListParserOptionTape_equiv_left hequiv
  rw [dropTrailingNone_map_some] at hleft
  cases hshape : headerAfterHaltLeftRev D fuel with
  | nil =>
      exact headerAfterHaltLeftRev_ne_nil D fuel hshape
  | cons symbol rest =>
      rw [hshape] at hleft
      cases hleft

def contextualZeroTransitionHaltConfig
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state := TransitionListParserState.halt
    tape :=
      transitionListParserOptionTape
        (some MachineCodeSymbol.done :: baseLeftRev.map some)
        (input.map some) }

/-- Count zero is already contextual: `findCount` immediately consumes the
`done` delimiter and never enters the retained description prefix. -/
theorem transitionListParserMachine_computes_zero_context_exact
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state :=
          TransitionListParserState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (baseLeftRev.map some)
            ((MachineDescription.encodeNatAppend 0 input).map some) }
      (contextualZeroTransitionHaltConfig baseLeftRev input) := by
  simpa [contextualZeroTransitionHaltConfig,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat]
    using
      transitionListParserMachine_computes_findCount_blanks_done_exact
        TransitionListParserMarker.initial 0
        (baseLeftRev.map some) (input.map some)

/-- A description-header cell is not a left barrier for the transition-list
parser.  Its `returnLeft` phase deliberately crosses every nonblank cell. -/
theorem transitionListParserMachine_returnLeft_crosses_header
    (saved : Option MachineCodeSymbol) :
    transitionListParserMachine.transition
        (TransitionListParserState.returnLeft saved)
        (some MachineCodeSymbol.header) =
      some
        (some MachineCodeSymbol.header, Direction.left,
          TransitionListParserState.returnLeft saved) := by
  rfl

namespace ContextualPrefixRightShiftOne

abbrev Control := ProductCleanupGap.PrefixRightShiftOne.Control

def machine : TuringMachine MachineCodeSymbol Control :=
  ProductCleanupGap.PrefixRightShiftOne.machine

def config (state : Control) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := state, tape := tape }

def sourceTape
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  { left := baseLeftRev.map some
    head := some first
    right := List.append (rest.map some)
      (none :: none :: callerCells) }

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .takeFirst
    (sourceTape baseLeftRev first rest callerCells)

def carryTape
    (baseLeftRev processedRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := List.append (processedRev.map some)
          (none :: baseLeftRev.map some)
        head := none
        right := none :: callerCells }
  | current :: rest =>
      { left := List.append (processedRev.map some)
          (none :: baseLeftRev.map some)
        head := some current
        right := List.append (rest.map some)
          (none :: none :: callerCells) }

def carryConfig
    (baseLeftRev processedRev remaining : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config (.carry carried)
    (carryTape baseLeftRev processedRev remaining callerCells)

def turnConfig
    (baseLeftRev wordRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .turnGap
    { left := List.append (wordRev.map some)
        (none :: baseLeftRev.map some)
      head := none
      right := callerCells }

def rewindTape
    (baseLeftRev remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := baseLeftRev.map some
        head := none
        right := List.append (crossed.map some)
          (none :: callerCells) }
  | current :: rest =>
      { left := List.append (rest.map some)
          (none :: baseLeftRev.map some)
        head := some current
        right := List.append (crossed.map some)
          (none :: callerCells) }

def rewindConfig
    (baseLeftRev remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .rewind
    (rewindTape baseLeftRev remainingRev crossed callerCells)

def targetTapeWord
    (baseLeftRev word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := none :: baseLeftRev.map some
        head := none
        right := callerCells }
  | first :: rest =>
      { left := none :: baseLeftRev.map some
        head := some first
        right := List.append (rest.map some)
          (none :: callerCells) }

def targetConfigWord
    (baseLeftRev word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .halt
    (targetTapeWord baseLeftRev word callerCells)

def targetTape
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  targetTapeWord baseLeftRev (first :: rest) callerCells

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  targetConfigWord baseLeftRev (first :: rest) callerCells

theorem take_step
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (sourceConfig baseLeftRev first rest callerCells) =
      some
        (carryConfig baseLeftRev [] rest first callerCells) := by
  cases rest <;> rfl

theorem carry_step
    (baseLeftRev : Word MachineCodeSymbol)
    (current carried : MachineCodeSymbol)
    (processedRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (carryConfig baseLeftRev processedRev
          (current :: remaining) carried callerCells) =
      some
        (carryConfig baseLeftRev (carried :: processedRev)
          remaining current callerCells) := by
  cases remaining <;> rfl

theorem carry_finish
    (baseLeftRev processedRev : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (carryConfig baseLeftRev processedRev [] carried callerCells) =
      some
        (turnConfig baseLeftRev (carried :: processedRev)
          callerCells) := by
  rfl

theorem turn_step
    (baseLeftRev : Word MachineCodeSymbol)
    (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (turnConfig baseLeftRev (last :: remainingRev) callerCells) =
      some
        (rewindConfig baseLeftRev (last :: remainingRev) []
          callerCells) := by
  cases remainingRev <;> rfl

theorem rewind_step
    (baseLeftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (rewindConfig baseLeftRev (current :: remainingRev)
          crossed callerCells) =
      some
        (rewindConfig baseLeftRev remainingRev (current :: crossed)
          callerCells) := by
  cases remainingRev <;> rfl

theorem rewind_finish
    (baseLeftRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (rewindConfig baseLeftRev [] crossed callerCells) =
      some (targetConfigWord baseLeftRev crossed callerCells) := by
  cases crossed <;> rfl

theorem carry_run_exact
    (baseLeftRev processedRev remaining : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (remaining.length + 1)
        (carryConfig baseLeftRev processedRev remaining carried
          callerCells) =
      some
        (turnConfig baseLeftRev
          (List.append remaining.reverse (carried :: processedRev))
          callerCells) := by
  induction remaining generalizing processedRev carried with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact carry_finish baseLeftRev processedRev carried callerCells
  | cons current remaining ih =>
      change machine.runConfigExact? ((remaining.length + 1) + 1)
          (carryConfig baseLeftRev processedRev (current :: remaining)
            carried callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [carry_step]
      simp only
      rw [ih (carried :: processedRev) current]
      simp [List.reverse_cons, List.append_assoc]

theorem turn_word_step
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (turnConfig baseLeftRev (first :: rest).reverse callerCells) =
      some
        (rewindConfig baseLeftRev (first :: rest).reverse []
          callerCells) := by
  have hnonempty : (first :: rest).reverse ≠ [] := by simp
  cases hrev : (first :: rest).reverse with
  | nil => contradiction
  | cons last remainingRev =>
      simpa [hrev] using
        turn_step baseLeftRev last remainingRev callerCells

theorem rewind_run_exact
    (baseLeftRev remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (remainingRev.length + 1)
        (rewindConfig baseLeftRev remainingRev crossed callerCells) =
      some
        (targetConfigWord baseLeftRev
          (List.append remainingRev.reverse crossed) callerCells) := by
  induction remainingRev generalizing crossed with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact rewind_finish baseLeftRev crossed callerCells
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1)
          (rewindConfig baseLeftRev (current :: remainingRev)
            crossed callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [rewind_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

/-- Existing `PrefixRightShiftOne` specialized to an arbitrary retained
far-left context.  Its newly blanked source head is the rewind barrier. -/
theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact?
        (ProductCleanupGap.PrefixRightShiftOne.runSteps (first :: rest))
        (sourceConfig baseLeftRev first rest callerCells) =
      some (targetConfig baseLeftRev first rest callerCells) := by
  let word := first :: rest
  have htake :
      machine.runConfigExact? 1
          (sourceConfig baseLeftRev first rest callerCells) =
        some
          (carryConfig baseLeftRev [] rest first callerCells) := by
    rw [TuringMachine.runConfigExact?]
    exact take_step baseLeftRev first rest callerCells
  have hcarry :
      machine.runConfigExact? word.length
          (carryConfig baseLeftRev [] rest first callerCells) =
        some (turnConfig baseLeftRev word.reverse callerCells) := by
    simpa [word, List.reverse_cons, List.append_assoc] using
      carry_run_exact baseLeftRev [] rest first callerCells
  have hturn :
      machine.runConfigExact? 1
          (turnConfig baseLeftRev word.reverse callerCells) =
        some
          (rewindConfig baseLeftRev word.reverse [] callerCells) := by
    rw [TuringMachine.runConfigExact?]
    exact turn_word_step baseLeftRev first rest callerCells
  have hrewind :
      machine.runConfigExact? (word.length + 1)
          (rewindConfig baseLeftRev word.reverse [] callerCells) =
        some (targetConfig baseLeftRev first rest callerCells) := by
    simpa [word, targetConfig, List.append_assoc] using
      rewind_run_exact baseLeftRev word.reverse [] callerCells
  unfold ProductCleanupGap.PrefixRightShiftOne.runSteps
  rw [show 2 * (first :: rest).length + 3 =
      1 + (word.length + (1 + (word.length + 1))) by
    simp [word]
    lia]
  rw [TuringMachine.runConfigExact?_add]
  rw [htake]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [hcarry]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [hturn]
  simp only
  exact hrewind

def cursorSourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .takeFirst
    (headerFieldsParserTape baseLeftRev (first :: rest))

theorem sourceTape_equiv_cursorTape
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    Tape.Equiv
      (sourceTape baseLeftRev first rest [])
      (headerFieldsParserTape baseLeftRev (first :: rest)) := by
  refine ⟨?_, rfl, ?_⟩
  · change
      Tape.dropTrailingNone (baseLeftRev.map some) =
        Tape.dropTrailingNone (baseLeftRev.map some)
    rfl
  · change
      Tape.dropTrailingNone (rest.map some ++ [none, none]) =
        Tape.dropTrailingNone (rest.map some)
    rw [show rest.map some ++ [none, none] =
        (rest.map some ++ [none]) ++ [none] by simp]
    rw [dropTrailingNone_append_none,
      dropTrailingNone_append_none]

/-- The contextual shift starts on the actual unpadded header-parser cursor;
the extra far-right blanks used by the exact run are transported by tape
equivalence. -/
theorem run_from_cursor
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    exists endpoint :
        TuringMachine.Configuration MachineCodeSymbol Control,
      machine.runConfigExact?
          (ProductCleanupGap.PrefixRightShiftOne.runSteps (first :: rest))
          (cursorSourceConfig baseLeftRev first rest) =
        some endpoint ∧
      endpoint.state = .halt ∧
      Tape.Equiv (targetTape baseLeftRev first rest []) endpoint.tape := by
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (run_exact baseLeftRev first rest [])
        (sourceTape_equiv_cursorTape baseLeftRev first rest) with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨endpoint, hrun, hstate, htape⟩

end ContextualPrefixRightShiftOne

def transitionParserWord
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend D.transitions.length
    (MachineDescription.encodeTransitionsAppend D.transitions input)

theorem transitionParserWord_ne_nil
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    transitionParserWord D input ≠ [] := by
  cases hcount : D.transitions.length with
  | zero =>
      simp [transitionParserWord, MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, hcount]
  | succ count =>
      simp [transitionParserWord, MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, hcount]

/-- Exact first physical handoff: shift the complete count/table/input word one
cell right, leaving a real blank separator before it and retaining every parsed
header field plus the outer fuel beyond that separator. -/
theorem headerEndpoint_prefixRightShiftOne_forward
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    exists first : MachineCodeSymbol,
    exists rest : Word MachineCodeSymbol,
    exists endpoint :
        TuringMachine.Configuration MachineCodeSymbol
          ContextualPrefixRightShiftOne.Control,
      transitionParserWord D input = first :: rest ∧
      ContextualPrefixRightShiftOne.machine.runConfigExact?
          (ProductCleanupGap.PrefixRightShiftOne.runSteps (first :: rest))
          { state :=
              ProductCleanupGap.PrefixRightShiftOne.Control.takeFirst
            tape := (headerParserTransitionCountConfig D fuel input).tape } =
        some endpoint ∧
      endpoint.state =
        ProductCleanupGap.PrefixRightShiftOne.Control.halt ∧
      Tape.Equiv
        (ContextualPrefixRightShiftOne.targetTape
          (headerAfterHaltLeftRev D fuel) first rest [])
        endpoint.tape := by
  have hnonempty := transitionParserWord_ne_nil D input
  cases hword : transitionParserWord D input with
  | nil =>
      exact False.elim (hnonempty hword)
  | cons first rest =>
      rcases
          ContextualPrefixRightShiftOne.run_from_cursor
            (headerAfterHaltLeftRev D fuel) first rest with
        ⟨endpoint, hrun, hstate, htape⟩
      refine ⟨first, rest, endpoint, rfl, ?_, hstate, htape⟩
      change
        ContextualPrefixRightShiftOne.machine.runConfigExact?
            (ProductCleanupGap.PrefixRightShiftOne.runSteps (first :: rest))
            { state :=
                ProductCleanupGap.PrefixRightShiftOne.Control.takeFirst
              tape :=
                headerFieldsParserTape (headerAfterHaltLeftRev D fuel)
                  (transitionParserWord D input) } =
          some endpoint
      rw [hword]
      simpa [ContextualPrefixRightShiftOne.cursorSourceConfig,
        ContextualPrefixRightShiftOne.config] using hrun

end FiniteRecognizer.Interpreter.ParserAssembly
end Computability
end FoC
