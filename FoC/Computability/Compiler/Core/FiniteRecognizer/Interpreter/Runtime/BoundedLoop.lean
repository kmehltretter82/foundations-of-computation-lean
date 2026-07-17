import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.SelectedToStack
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.NoMatch.Trace
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Semantics.Iteration

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BoundedLoopInduction

open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.StackIteration
open FiniteRecognizer.Interpreter.SelectedUpdateIntegration
open FiniteRecognizer.Interpreter.SelectedToStack
open FiniteRecognizer.Interpreter.FinalGateMaterializer
open FiniteRecognizer.Interpreter.NoMatchFinalGate
open FiniteRecognizer.Interpreter.NoMatchFinalGate.LastMiss
open FiniteRecognizer.Interpreter.SemanticIteration

/-- Canonical physical entry to one positive-fuel loop iteration.  `copies`
counts the table copies reserved for later semantic iterations; the active
table is the explicit `transitions` argument of `canonicalScanRowsConfig`. -/
def loopSourceConfig
    (current : MachineDescription.Configuration)
    (transitions : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :=
  canonicalScanRowsConfig current [] transitions
    (activeProtectedSuffix transitions copies current.tape haltState
      callerSuffix)

/-- The exact outer-loop state with an arbitrary padding-equivalent physical
tape. -/
def loopSourceWithTape
    (current : MachineDescription.Configuration)
    (transitions : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeySingleKeyRepair.ComparatorState :=
  { state := (loopSourceConfig current transitions copies haltState
      callerSuffix).state
    tape := tape }

/-- Shared terminal comparator boundary used by both the zero-fuel lane and
the positive-fuel loop. -/
def loopTerminalConfig
    (final : MachineDescription.Configuration)
    (haltState : Nat)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeyComparatorState :=
  { state := if final.state = haltState then
        RuntimeKeyComparatorState.matched
      else RuntimeKeyComparatorState.missed
    tape := tape }

theorem loopSourceConfig_eq_canonical
    (current : MachineDescription.Configuration)
    (transitions : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    loopSourceConfig current transitions copies haltState callerSuffix =
      canonicalScanRowsConfig current [] transitions
        (activeProtectedSuffix transitions copies current.tape haltState
          callerSuffix) := by
  rfl

/-- Semantic successor produced by one selected runtime row. -/
def selectedNextConfig
    (current : MachineDescription.Configuration)
    (selected : TransitionDescription) :
    MachineDescription.Configuration :=
  { state := selected.target
    tape := Tape.move selected.move
      (Tape.write selected.write current.tape) }

def outerLoopConfig
    {outerState : Type}
    (embed : RuntimeKeySingleKeyRepair.ComparatorState -> outerState)
    (current : MachineDescription.Configuration)
    (transitions : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol outerState :=
  { state := embed
      (loopSourceConfig current transitions copies haltState
        callerSuffix).state
    tape := tape }

def outerTerminalConfig
    {outerState : Type}
    (embed : RuntimeKeyComparatorState -> outerState)
    (final : MachineDescription.Configuration)
    (haltState : Nat)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol outerState :=
  { state := embed
      (if final.state = haltState then RuntimeKeyComparatorState.matched
       else RuntimeKeyComparatorState.missed)
    tape := tape }

/-- Macro contracts that the concrete runtime phase sum must discharge.
They expose exact outer control states while permitting padding-equivalent
physical tapes at loopback boundaries. -/
structure RuntimeLoopPhaseContract
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState) where
  loopEmbed : RuntimeKeySingleKeyRepair.ComparatorState -> outerState
  finalEmbed : RuntimeKeyComparatorState -> outerState
  miss :
    forall (D : MachineDescription),
    forall (first : TransitionDescription),
    forall (rest : List TransitionDescription),
    forall (copies : Nat),
    forall (current : MachineDescription.Configuration),
    forall (haltState : Nat),
    forall (callerSuffix : Word MachineCodeSymbol),
    forall (sourceTape : Tape MachineCodeSymbol),
      D.transitions = first :: rest ->
      D.lookupTransition current.state (Tape.read current.tape) = none ->
      Tape.Equiv
        (loopSourceConfig current (first :: rest) copies haltState
          callerSuffix).tape sourceTape ->
      exists terminalTape : Tape MachineCodeSymbol,
        TuringMachine.Computes outer
          (outerLoopConfig loopEmbed current (first :: rest) copies
            haltState callerSuffix sourceTape)
          (outerTerminalConfig finalEmbed current haltState terminalTape)
  lastSuccess :
    forall (D : MachineDescription),
    forall (first : TransitionDescription),
    forall (rest : List TransitionDescription),
    forall (current : MachineDescription.Configuration),
    forall (selected : TransitionDescription),
    forall (haltState : Nat),
    forall (callerSuffix : Word MachineCodeSymbol),
    forall (sourceTape : Tape MachineCodeSymbol),
      D.transitions = first :: rest ->
      D.lookupTransition current.state (Tape.read current.tape) =
        some selected ->
      Tape.Equiv
        (loopSourceConfig current (first :: rest) 0 haltState
          callerSuffix).tape sourceTape ->
      exists terminalTape : Tape MachineCodeSymbol,
        TuringMachine.Computes outer
          (outerLoopConfig loopEmbed current (first :: rest) 0
            haltState callerSuffix sourceTape)
          (outerTerminalConfig finalEmbed
            (selectedNextConfig current selected) haltState terminalTape)
  nextSuccess :
    forall (D : MachineDescription),
    forall (first : TransitionDescription),
    forall (rest : List TransitionDescription),
    forall (copies : Nat),
    forall (current : MachineDescription.Configuration),
    forall (selected : TransitionDescription),
    forall (haltState : Nat),
    forall (callerSuffix : Word MachineCodeSymbol),
    forall (sourceTape : Tape MachineCodeSymbol),
      D.transitions = first :: rest ->
      D.lookupTransition current.state (Tape.read current.tape) =
        some selected ->
      Tape.Equiv
        (loopSourceConfig current (first :: rest) (copies + 1)
          haltState callerSuffix).tape sourceTape ->
      exists nextTape : Tape MachineCodeSymbol,
        TuringMachine.Computes outer
          (outerLoopConfig loopEmbed current (first :: rest) (copies + 1)
            haltState callerSuffix sourceTape)
          (outerLoopConfig loopEmbed (selectedNextConfig current selected)
            (first :: rest) copies haltState callerSuffix nextTape) /\
        Tape.Equiv
          (loopSourceConfig (selectedNextConfig current selected)
            (first :: rest) copies haltState callerSuffix).tape nextTape

theorem runConfig_succ_eq_selectedNext
    (D : MachineDescription)
    (remaining : Nat)
    (current : MachineDescription.Configuration)
    (selected : TransitionDescription)
    (hlookup :
      D.lookupTransition current.state (Tape.read current.tape) =
        some selected) :
    D.runConfig (remaining + 1) current =
      D.runConfig remaining (selectedNextConfig current selected) := by
  exact runConfig_succ_of_lookup_some D remaining current selected hlookup

/-- Positive-fuel induction over the concrete loop boundary.  The theorem is
parametric in the finite phase sum; its three macro obligations are exactly
the miss terminal, last-success terminal, and successful loopback routes. -/
theorem bounded_loop_computes
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (phase : RuntimeLoopPhaseContract outer)
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest)
    (copies : Nat)
    (current : MachineDescription.Configuration)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (loopSourceConfig current (first :: rest) copies haltState
        callerSuffix).tape sourceTape) :
    exists terminalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes outer
        (outerLoopConfig phase.loopEmbed current (first :: rest) copies
          haltState callerSuffix sourceTape)
        (outerTerminalConfig phase.finalEmbed
          (D.runConfig (copies + 1) current) haltState terminalTape) := by
  induction copies generalizing current sourceTape with
  | zero =>
      cases hlookup :
          D.lookupTransition current.state (Tape.read current.tape) with
      | none =>
          rcases phase.miss D first rest 0 current haltState callerSuffix
              sourceTape htransitions hlookup hsource with
            ⟨terminalTape, hrun⟩
          have hsemantic : D.runConfig (0 + 1) current = current :=
            runConfig_succ_of_lookup_none D 0 current hlookup
          exact ⟨terminalTape, by simpa [hsemantic] using hrun⟩
      | some selected =>
          rcases phase.lastSuccess D first rest current selected haltState
              callerSuffix sourceTape htransitions hlookup hsource with
            ⟨terminalTape, hrun⟩
          have hsemantic :
              D.runConfig (0 + 1) current =
                selectedNextConfig current selected := by
            simpa [MachineDescription.runConfig] using
              runConfig_succ_eq_selectedNext D 0 current selected hlookup
          exact ⟨terminalTape, by simpa [hsemantic] using hrun⟩
  | succ copies ih =>
      cases hlookup :
          D.lookupTransition current.state (Tape.read current.tape) with
      | none =>
          rcases phase.miss D first rest (copies + 1) current haltState
              callerSuffix sourceTape htransitions hlookup hsource with
            ⟨terminalTape, hrun⟩
          have hsemantic :
              D.runConfig ((copies + 1) + 1) current = current :=
            runConfig_succ_of_lookup_none D (copies + 1) current hlookup
          exact ⟨terminalTape, by simpa [hsemantic] using hrun⟩
      | some selected =>
          rcases phase.nextSuccess D first rest copies current selected
              haltState callerSuffix sourceTape htransitions hlookup hsource
              with
            ⟨nextTape, hstep, hnext⟩
          rcases ih (selectedNextConfig current selected) nextTape hnext with
            ⟨terminalTape, hrest⟩
          have hsemantic :
              D.runConfig ((copies + 1) + 1) current =
                D.runConfig (copies + 1)
                  (selectedNextConfig current selected) := by
            exact runConfig_succ_eq_selectedNext D (copies + 1) current
              selected hlookup
          exact ⟨terminalTape, by
            rw [hsemantic]
            exact TuringMachine.computes_trans hstep hrest⟩

/-- The semantic comparator statement exported with the bounded execution.
It is deliberately phrased at the same source gate used by the zero-fuel
lane. -/
theorem finalComparator_haltsFrom_iff_boundedFinal
    (D : MachineDescription)
    (copies : Nat)
    (current : MachineDescription.Configuration) :
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (finalComparatorSourceConfig
          (D.runConfig (copies + 1) current).state D.halt []) <->
      (D.runConfig (copies + 1) current).state = D.halt := by
  exact finalComparator_haltsFrom_iff
    (D.runConfig (copies + 1) current).state D.halt []

/-! ## Concrete local phase bundles -/

/-- Physical first-match scan, extraction, action parsing, and selected-prefix
cleanup from an arbitrary tape equivalent to the canonical active scan. -/
def FirstMatchPhysicalTrace
    (current : MachineDescription.Configuration)
    (before : List TransitionDescription)
    (selected : TransitionDescription)
    (after : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape cleanedTape : Tape MachineCodeSymbol) : Prop :=
  let transitions := List.append before (selected :: after)
  let _protectedSuffix :=
    activeProtectedSuffix transitions copies current.tape haltState
      callerSuffix
  exists selectedTape extractedTape actionTape : Tape MachineCodeSymbol,
    TuringMachine.Computes comparatorMachine
      (loopSourceWithTape current transitions copies haltState callerSuffix
        sourceTape)
      { state := RuntimeKeySingleKeyRepair.ComparatorState.selected
        tape := selectedTape } /\
    TuringMachine.Computes RuntimeKeySelectedExtractorArbitrary.machine
      { state := RuntimeKeySelectedExtractorArbitrary.Control.skipWrite
        tape := selectedTape }
      { state := RuntimeKeySelectedExtractorArbitrary.Control.halt
        tape := extractedTape } /\
    TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine
      { state := FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.needTransition
        tape := extractedTape }
      { state := FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.ready
          selected.write selected.move
        tape := actionTape } /\
    TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine
      { state := FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.enter
          (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
        tape := actionTape }
      { state := FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.ready
          (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected)
        tape := cleanedTape } /\
    Tape.Equiv cleanedTape
      (Tape.input
        (postSelectedWord selected.target transitions copies current.tape
          haltState callerSuffix))

theorem firstMatchPhysicalTrace_of_tape_equiv
    (current : MachineDescription.Configuration)
    (before : List TransitionDescription)
    (selected : TransitionDescription)
    (after : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hmiss :
      forall row : TransitionDescription,
        List.Mem row before ->
          MachineDescription.Matches current.state
            (Tape.read current.tape) row = false)
    (hmatch :
      MachineDescription.Matches current.state
        (Tape.read current.tape) selected = true)
    (hsource : Tape.Equiv
      (loopSourceConfig current (List.append before (selected :: after))
        copies haltState callerSuffix).tape sourceTape) :
    exists cleanedTape : Tape MachineCodeSymbol,
      FirstMatchPhysicalTrace current before selected after copies haltState
        callerSuffix sourceTape cleanedTape := by
  let transitions := List.append before (selected :: after)
  let protectedSuffix :=
    activeProtectedSuffix transitions copies current.tape haltState
      callerSuffix
  have hscanCanonical :=
    comparator_computes_first_match_after_prefix current [] before selected
      after protectedSuffix hmiss hmatch
  have hscanSource : Tape.Equiv
      (canonicalScanRowsConfig current [] transitions protectedSuffix).tape
      sourceTape := by
    simpa [transitions, protectedSuffix, loopSourceConfig] using hsource
  rcases computes_transport_of_tape_equiv hscanCanonical hscanSource with
    ⟨selectedConfig, hscan, hselectedState, hselectedTape⟩
  rcases selectedConfig with ⟨selectedState, selectedTape⟩
  change selectedState =
    RuntimeKeySingleKeyRepair.ComparatorState.selected at hselectedState
  subst selectedState
  have hextractorCanonical :=
    extractor_computes_from_comparator_selected current before selected after
      protectedSuffix
  rcases hextractorCanonical with
    ⟨canonicalExtractedTape, hextractorCanonical,
      hcanonicalExtracted⟩
  have hextractorSource : Tape.Equiv
      (extractorSourceConfig current before selected after
        protectedSuffix).tape selectedTape := by
    rw [← comparator_selected_tape_eq_extractor_source]
    exact hselectedTape
  rcases computes_transport_of_tape_equiv hextractorCanonical
      hextractorSource with
    ⟨extractedConfig, hextractor, hextractedState, hextractedTape⟩
  rcases extractedConfig with ⟨extractedState, extractedTape⟩
  change extractedState =
    RuntimeKeySelectedExtractorArbitrary.Control.halt at hextractedState
  subst extractedState
  have hcompacted : Tape.Equiv
      (compactedSelectedTape current before selected protectedSuffix)
      extractedTape :=
    Tape.Equiv.trans hcanonicalExtracted hextractedTape
  rcases extracted_action_then_cleanup current before selected
      protectedSuffix extractedTape hcompacted with
    ⟨actionTape, cleanedTape, haction, hcleanup, hcleaned⟩
  refine ⟨cleanedTape, ?_⟩
  dsimp [FirstMatchPhysicalTrace]
  refine ⟨selectedTape, extractedTape, actionTape, ?_, hextractor,
    haction, hcleanup, ?_⟩
  · simpa [loopSourceWithTape, transitions, protectedSuffix,
      loopSourceConfig] using hscan
  · simpa [postSelectedWord, transitions, protectedSuffix] using hcleaned



end FiniteRecognizer.Interpreter.BoundedLoopInduction

end Computability
end FoC
