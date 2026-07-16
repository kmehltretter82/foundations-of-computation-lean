import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.NoMatch.Shapes

namespace FoC
namespace Computability

open Languages

namespace Section53NoMatchFinalGate

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Section53UniformInterpreterOneStep
open Section53UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open Section53LoopRestagingAudit
open Section53StackIteration
open Section53FinalGateMaterializer

namespace LastMiss

theorem lastMiss_trace
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    exists stackTape leftBoundaryTape rightBoundaryTape markerTape rewindTape :
        Tape MachineCodeSymbol,
    exists builderTape finalTape comparatorTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Section53StackSkip.machine
        { state := Section53StackSkip.Control.afterHeader
          tape :=
            (canonicalExhaustedRowsTarget current skipped
              (activeProtectedSuffix (first :: rest) copies current.tape
                haltState suffix)).tape }
        { state := Section53StackSkip.Control.ready
          tape := stackTape } ∧
      TuringMachine.Computes Section53DirectContextUpdate.Boundary.machine
        { state := Section53DirectContextUpdate.Boundary.Control.locate .count
          tape := stackTape }
        { state := Section53DirectContextUpdate.Boundary.Control.ready
          tape := leftBoundaryTape } ∧
      TuringMachine.Computes Section53DirectContextUpdate.Boundary.machine
        { state := Section53DirectContextUpdate.Boundary.Control.locate .count
          tape := leftBoundaryTape }
        { state := Section53DirectContextUpdate.Boundary.Control.ready
          tape := rightBoundaryTape } ∧
      TuringMachine.Computes DoubleTransitionMarker.machine
        { state := DoubleTransitionMarker.Control.enter
          tape := rightBoundaryTape }
        { state := DoubleTransitionMarker.Control.ready
          tape := markerTape } ∧
      TuringMachine.Computes RewindWord.machine
        { state := RewindWord.Control.scan, tape := markerTape }
        { state := RewindWord.Control.gate, tape := rewindTape } ∧
      TuringMachine.Computes CurrentBuilder.machine
        { state := CurrentBuilder.Control.start, tape := rewindTape }
        { state := CurrentBuilder.Control.ready (firstToken haltState)
          tape := builderTape } ∧
      TuringMachine.Computes HaltCopier.machine
        { state := HaltCopier.Control.seekSource (firstToken haltState)
          tape := builderTape }
        { state := HaltCopier.Control.ready, tape := finalTape } ∧
      TuringMachine.Computes runtimeKeyComparatorMachine
        { state := RuntimeKeyComparatorState.needHeader, tape := finalTape }
        { state := if current.state = haltState then
              RuntimeKeyComparatorState.matched
            else RuntimeKeyComparatorState.missed
          tape := comparatorTape } := by
  rcases contextPrefix_split_last_two
      current.tape.left current.tape.right with
    ⟨firstBefore, secondBefore, contextFront,
      hcontext, hcontextNoTransition⟩
  rcases middleWordCopies_decompose skipped (first :: rest) copies
      contextFront hcontextNoTransition with
    ⟨firstJunk, secondJunk, gap, hmiddle, hnoDouble⟩
  let stackTape : Tape MachineCodeSymbol :=
    (Section53StackSkip.targetConfig
      (exhaustedBaseLeftRev current skipped)
      first rest copies (contextTail current.tape haltState suffix)).tape
  have hskipRaw := Section53StackSkip.run_context_exact
    (exhaustedBaseLeftRev current skipped) first rest copies
    current.tape haltState suffix
  have hskipCanonical : TuringMachine.Computes Section53StackSkip.machine
      (Section53StackSkip.sourceConfig
        (exhaustedBaseLeftRev current skipped)
        first rest copies (contextTail current.tape haltState suffix))
      (Section53StackSkip.targetConfig
        (exhaustedBaseLeftRev current skipped)
        first rest copies (contextTail current.tape haltState suffix)) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hskipRaw)
  have hskip : TuringMachine.Computes Section53StackSkip.machine
      { state := Section53StackSkip.Control.afterHeader
        tape :=
          (canonicalExhaustedRowsTarget current skipped
            (activeProtectedSuffix (first :: rest) copies current.tape
              haltState suffix)).tape }
      { state := Section53StackSkip.Control.ready, tape := stackTape } := by
    simpa [stackTape,
      canonicalExhausted_tape_eq_stackSkip_source,
      Section53StackSkip.sourceConfig, Section53StackSkip.targetConfig,
      Section53StackSkip.cursorConfig] using hskipCanonical
  let leftBoundaryTape : Tape MachineCodeSymbol :=
    (Section53DirectContextUpdate.Boundary.targetConfig
      (remainingStackBaseLeftRev current skipped (first :: rest) copies)
      current.tape.left current.tape.right.length
      (MachineDescription.encodeCellsAppend current.tape.right
        (persistent haltState suffix))).tape
  have hleftRaw := Section53DirectContextUpdate.Boundary.run_exact
    (remainingStackBaseLeftRev current skipped (first :: rest) copies)
    current.tape.left current.tape.right.length
    (MachineDescription.encodeCellsAppend current.tape.right
      (persistent haltState suffix))
  have hleftCanonical := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hleftRaw)
  have hleft : TuringMachine.Computes
      Section53DirectContextUpdate.Boundary.machine
      { state := Section53DirectContextUpdate.Boundary.Control.locate .count
        tape := stackTape }
      { state := Section53DirectContextUpdate.Boundary.Control.ready
        tape := leftBoundaryTape } := by
    simpa [stackTape, leftBoundaryTape,
      remainingStack_target_tape_eq_leftBoundary_source,
      Section53DirectContextUpdate.Boundary.sourceConfig,
      Section53DirectContextUpdate.Boundary.targetConfig,
      Section53DirectContextUpdate.Boundary.locateConfig,
      Section53RuntimeEncodedList.PayloadLocator.sourceConfig] using
      hleftCanonical
  let rightBoundaryTape : Tape MachineCodeSymbol :=
    (Section53DirectContextUpdate.Boundary.targetConfig
      (remainingLeftBoundaryBaseLeftRev current skipped (first :: rest)
        copies current.tape.left)
      current.tape.right haltState suffix).tape
  have hrightRaw := Section53DirectContextUpdate.Boundary.run_exact
    (remainingLeftBoundaryBaseLeftRev current skipped (first :: rest)
      copies current.tape.left)
    current.tape.right haltState suffix
  have hrightCanonical := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrightRaw)
  have hright : TuringMachine.Computes
      Section53DirectContextUpdate.Boundary.machine
      { state := Section53DirectContextUpdate.Boundary.Control.locate .count
        tape := leftBoundaryTape }
      { state := Section53DirectContextUpdate.Boundary.Control.ready
        tape := rightBoundaryTape } := by
    simpa [leftBoundaryTape, rightBoundaryTape,
      remainingLeftBoundary_target_tape_eq_rightBoundary_source,
      Section53DirectContextUpdate.Boundary.sourceConfig,
      Section53DirectContextUpdate.Boundary.targetConfig,
      Section53DirectContextUpdate.Boundary.locateConfig,
      Section53RuntimeEncodedList.PayloadLocator.sourceConfig] using
      hrightCanonical
  let markerTape : Tape MachineCodeSymbol :=
    (DoubleTransitionMarker.targetConfig
      (remainingMarkerBaseLeftRev current skipped (first :: rest) copies
        contextFront)
      haltState suffix).tape
  have hmarkerRaw := DoubleTransitionMarker.run_exact
    (remainingMarkerBaseLeftRev current skipped (first :: rest) copies
      contextFront)
    firstBefore secondBefore haltState suffix
  have hmarkerCanonical := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hmarkerRaw)
  have hmarker : TuringMachine.Computes DoubleTransitionMarker.machine
      { state := DoubleTransitionMarker.Control.enter
        tape := rightBoundaryTape }
      { state := DoubleTransitionMarker.Control.ready
        tape := markerTape } := by
    simpa [rightBoundaryTape, markerTape,
      remainingRightBoundary_target_tape_eq_marker_source current skipped
        (first :: rest) copies haltState suffix firstBefore secondBefore
        contextFront hcontext,
      DoubleTransitionMarker.sourceConfig,
      DoubleTransitionMarker.targetConfig] using
      hmarkerCanonical
  let rewindTape : Tape MachineCodeSymbol :=
    (Dispatch.NeighborProbe.PrefixRewind.gateConfig
      (remainingMarkedFullWord current skipped (first :: rest) copies
        contextFront haltState suffix)).tape
  have hrewindRaw := Dispatch.NeighborProbe.PrefixRewind.scan_run_exact
    (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
      remainingMarkerBaseLeftRev current skipped (first :: rest) copies
        contextFront)
    (MachineDescription.encodeNatAppend haltState suffix)
  have hrewindCanonical := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrewindRaw)
  have hrewindWord :
      List.append
          (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
            remainingMarkerBaseLeftRev current skipped (first :: rest)
              copies contextFront).reverse
          (MachineDescription.encodeNatAppend haltState suffix) =
        remainingMarkedFullWord current skipped (first :: rest) copies
          contextFront haltState suffix := by
    simp [remainingMarkedFullWord, List.reverse_cons, List.append_assoc]
  have hrewind : TuringMachine.Computes RewindWord.machine
      { state := RewindWord.Control.scan, tape := markerTape }
      { state := RewindWord.Control.gate, tape := rewindTape } := by
    rw [hrewindWord] at hrewindCanonical
    simpa [markerTape, rewindTape,
      remainingMarker_target_tape_eq_rewind_scan,
      Dispatch.NeighborProbe.PrefixRewind.scanConfig,
      Dispatch.NeighborProbe.PrefixRewind.gateConfig] using
      hrewindCanonical
  have hmarkedWord := remainingMarkedFullWord_eq_sourceWord current skipped
    (first :: rest) copies contextFront haltState suffix firstJunk
    secondJunk gap hmiddle
  have hbuilderSource : Tape.Equiv
      (Tape.input
        (CurrentBuilder.sourceWord current.state
          (runtimeKeyCellSymbol (Tape.read current.tape))
          firstJunk secondJunk gap haltState suffix)) rewindTape := by
    have hgate := Tape.Equiv.symm
      (Dispatch.NeighborProbe.PrefixRewind.gateTape_equiv_input
        (remainingMarkedFullWord current skipped (first :: rest) copies
          contextFront haltState suffix))
    simpa [rewindTape, hmarkedWord,
      Dispatch.NeighborProbe.PrefixRewind.gateConfig] using hgate
  rcases currentBuilder_materializes_finalComparator_of_tape_equiv
      current.state (runtimeKeyCellSymbol (Tape.read current.tape))
      firstJunk secondJunk gap haltState suffix rewindTape hnoDouble
      hbuilderSource with
    ⟨builderTape, finalTape, hbuilder, hcopy, hfinal⟩
  have hcomparatorCanonical :=
    finalComparator_computes_exact current.state haltState []
  rcases computes_transport_of_tape_equiv hcomparatorCanonical
      (Tape.Equiv.symm hfinal) with
    ⟨comparatorConfig, hcomparator, hcomparatorState,
      hcomparatorTape⟩
  rcases comparatorConfig with ⟨comparatorState, comparatorTape⟩
  change comparatorState =
    (if current.state = haltState then RuntimeKeyComparatorState.matched
      else RuntimeKeyComparatorState.missed) at hcomparatorState
  subst comparatorState
  exact ⟨stackTape, leftBoundaryTape, rightBoundaryTape, markerTape,
    rewindTape, builderTape, finalTape, comparatorTape,
    hskip, hleft, hright, hmarker, hrewind, hbuilder, hcopy, hcomparator⟩
  done


end LastMiss

end Section53NoMatchFinalGate

end Computability
end FoC
