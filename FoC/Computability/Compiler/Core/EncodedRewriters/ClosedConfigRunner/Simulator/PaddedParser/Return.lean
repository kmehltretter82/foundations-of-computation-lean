import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedParser.Scanners

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner

open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.DovetailStagePrefix
open CommonGround.SeqComposition

/--
Return from a scanned right edge to the standard right-shifted input head.

This phase assumes the validating scanner has already halted at the last
nonblank bit and is sequenced with a left handoff.  It scans left to the blank
before the word, then moves right twice, landing one cell right of the first
bit.  The phase preserves every stored cell, including any explicit trailing
blank already introduced by the scanner.
-/
def FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ keepMove 0 (some false) Direction.left 0
    , keepMove 0 (some true) Direction.left 0
    , keepMove 0 none Direction.right 1
    , keepMove 1 (some false) Direction.right 2
    , keepMove 1 (some true) Direction.right 2
    ]

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_wellFormed_configRunner :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.transitions)
      (stateCount :=
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.transitions)
      (by decide)

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltTransitionFree_configRunner :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.transitions)
    (state :=
      FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.halt)
    (by decide)

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.SubroutineReady :=
  ⟨fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_wellFormed_configRunner,
    fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltTransitionFree_configRunner⟩

private abbrev FDBSReturnToRightShiftedInput_configRunner :=
  FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_run_configRunner
    (leftRev : Word Bool) (current : Bool) (right : List (Option Bool)) :
    FDBSReturnToRightShiftedInput_configRunner.runConfig
        (leftRev.length + 3)
        (DovetailInitialLayoutInitializer.config
          FDBSReturnToRightShiftedInput_configRunner.start
          (leftRev.map some)
          (some current :: right)) =
      { state := FDBSReturnToRightShiftedInput_configRunner.halt
        tape :=
          Tape.move Direction.right
            (DovetailInitialLayoutInitializer.tapeAtCells [none]
              (List.append (leftRev.reverse.map some)
                (some current :: right))) } := by
  induction leftRev generalizing current right with
  | nil =>
      cases current
      · cases right with
        | nil =>
            simp [FDBSReturnToRightShiftedInput_configRunner,
              FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
              DovetailInitialLayoutInitializer.config,
              DovetailInitialLayoutInitializer.tapeAtCells,
              runConfig, stepConfig, lookupTransition, Matches,
              keepMove, transition, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, Tape.moveRight]
        | cons cell rest =>
            cases cell <;>
              simp [FDBSReturnToRightShiftedInput_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.config,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                keepMove, transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight]
      · cases right with
        | nil =>
            simp [FDBSReturnToRightShiftedInput_configRunner,
              FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
              DovetailInitialLayoutInitializer.config,
              DovetailInitialLayoutInitializer.tapeAtCells,
              runConfig, stepConfig, lookupTransition, Matches,
              keepMove, transition, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, Tape.moveRight]
        | cons cell rest =>
            cases cell <;>
              simp [FDBSReturnToRightShiftedInput_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.config,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                keepMove, transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight]
  | cons leftBit rest ih =>
      simp only [List.length_cons]
      rw [show Nat.succ rest.length + 3 = (rest.length + 3) + 1 by omega]
      rw [runConfig]
      cases current
      · simpa [FDBSReturnToRightShiftedInput_configRunner,
          FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
          DovetailInitialLayoutInitializer.config,
          DovetailInitialLayoutInitializer.tapeAtCells,
          stepConfig, lookupTransition, Matches, keepMove, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.append_assoc] using ih leftBit (some false :: right)
      · simpa [FDBSReturnToRightShiftedInput_configRunner,
          FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
          DovetailInitialLayoutInitializer.config,
          DovetailInitialLayoutInitializer.tapeAtCells,
          stepConfig, lookupTransition, Matches, keepMove, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.append_assoc] using ih leftBit (some true :: right)

theorem fixedDescriptionBoundedSimulator_reverse_two_split_configRunner
    (w : Word Bool) (h : 2 <= w.length) :
    exists last penult : Bool,
    exists middleRev : Word Bool,
      w.reverse = last :: penult :: middleRev ∧
        w = List.append middleRev.reverse [penult, last] := by
  cases hr : w.reverse with
  | nil =>
      have hlen : w.length = 0 := by
        have := congrArg List.length hr
        simpa using this
      omega
  | cons last rest =>
      cases hrest : rest with
      | nil =>
          have hlen : w.length = 1 := by
            have := congrArg List.length hr
            simp [hrest] at this
            simpa using this
          omega
      | cons penult middleRev =>
          refine ⟨last, penult, middleRev, ?_, ?_⟩
          · rfl
          · have hrev : w.reverse = last :: penult :: middleRev := by
              simpa [hrest] using hr
            have := congrArg List.reverse hrev
            simpa using this

theorem fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_eq_terminal_left_configRunner
    (L : SimulatorLayout) :
    fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner L [] =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          ((SimulatorLayout.asBoolInput L).reverse.map some) []) := by
  rw [fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner]
  rw [boolFinalHandoffConfigWithBase]
  simp
  have hleft :=
    FixedDescriptionBoundedSimulator.LayoutScannerRestoredLeft.eq_asBoolInput_reverse_map_some_configRunner
      L
  simpa [List.map_reverse] using
    congrArg
      (fun left =>
        Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells left []))
      hleft

theorem fixedDescriptionBoundedSimulator_tapeAtCells_left_blank_append_none_equiv_input_configRunner
    (w : Word Bool) :
    Tape.Equiv
      (DovetailInitialLayoutInitializer.tapeAtCells [none]
        (List.append (w.map some) [none]))
      (Tape.input w) := by
  cases w with
  | nil =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.input, Tape.blank, Tape.Equiv, Tape.dropTrailingNone]
  | cons bit rest =>
      constructor
      · rfl
      constructor
      · rfl
      · simp [DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.input,
          fixedDescriptionBoundedSimulator_dropTrailingNone_append_none]

namespace FixedDescriptionBoundedSimulator

namespace ReturnToRightShiftedInputDescription

theorem haltsFromTapeEquiv_terminal_configRunner
    (middleRev : Word Bool) (penult last : Bool) :
    FDBSReturnToRightShiftedInput_configRunner.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            ((last :: penult :: middleRev).map some) [])))
      (Tape.move Direction.right
        (Tape.input (List.append middleRev.reverse [penult, last]))) := by
  let Tactual : Tape Bool :=
    Tape.move Direction.right
      (DovetailInitialLayoutInitializer.tapeAtCells [none]
        (List.append (middleRev.reverse.map some)
          [some penult, some last, none]))
  refine ⟨Tactual, ?_, ?_⟩
  · refine ⟨middleRev.length + 3, ?_⟩
    have hrun :=
      fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_run_configRunner
        middleRev penult [some last, none]
    constructor
    · simpa [Tactual, HaltsFromTapeIn,
        DovetailInitialLayoutInitializer.config,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft] using
        congrArg Configuration.state hrun
    · simpa [Tactual, HaltsFromTapeIn,
        DovetailInitialLayoutInitializer.config,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft] using
        congrArg Configuration.tape hrun
  · have heq :=
      Tape.Equiv.move
        (fixedDescriptionBoundedSimulator_tapeAtCells_left_blank_append_none_equiv_input_configRunner
          (List.append middleRev.reverse [penult, last]))
        Direction.right
    simpa [Tactual, List.map_append, List.append_assoc] using heq

theorem haltsFromTapeEquiv_scannerHandoff_configRunner
    (L : SimulatorLayout) :
    FDBSReturnToRightShiftedInput_configRunner.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
          L []))
      (CommonGround.SimulatorLayouts.handoffTape L) := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  rcases
      fixedDescriptionBoundedSimulator_reverse_two_split_configRunner
        (SimulatorLayout.asBoolInput L) hlen with
    ⟨last, penult, middleRev, hrev, hw⟩
  have hreturn :=
    haltsFromTapeEquiv_terminal_configRunner
      middleRev penult last
  have hout :
      List.append middleRev.reverse [penult, last] =
        encodeCodeWordAsInput (SimulatorLayout.encode L) := by
    simpa [SimulatorLayout.asBoolInput] using hw.symm
  have hscanner :=
    fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_eq_terminal_left_configRunner
      L
  rw [hout] at hreturn
  rw [hscanner]
  rw [hrev]
  simpa [
    CommonGround.SimulatorLayouts.handoffTape,
    CommonGround.SimulatorLayouts.encode,
    CommonGround.SimulatorLayouts.bits,
    SimulatorLayout.asBoolInput,
    CommonGround.LayoutTapes.HandoffTape,
    CommonGround.LayoutTapes.InputTape,
    CommonGround.LayoutTapes.Bits] using hreturn

end ReturnToRightShiftedInputDescription

end FixedDescriptionBoundedSimulator

def FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner :
    MachineDescription :=
  seqSubroutine
    FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
    Direction.left

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
    fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner

theorem fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithTape_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.HaltsWithTape
      (FixedDescriptionBoundedSimulatorInput L)
      (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
        L []) := by
  rcases
      run_fixedDescriptionBoundedSimulatorLayoutScanner_raw_to_handoff_withBase_configRunner
        L [] with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [HaltsWithTapeIn, initial,
      FixedDescriptionBoundedSimulatorInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.input] using congrArg Configuration.state hsteps
  · simpa [HaltsWithTapeIn, initial,
      FixedDescriptionBoundedSimulatorInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.input] using congrArg Configuration.tape hsteps

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_haltsWithTapeEquiv_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner.HaltsWithTapeEquiv
      (FixedDescriptionBoundedSimulatorInput L)
      (CommonGround.SimulatorLayouts.handoffTape L) := by
  have hscanner :=
    fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithTape_configRunner
      L
  rcases
      FixedDescriptionBoundedSimulator.ReturnToRightShiftedInputDescription.haltsFromTapeEquiv_scannerHandoff_configRunner
        L with
    ⟨Tactual, hreturn, hTequiv⟩
  have hseq :
      FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner.HaltsWithTape
        (FixedDescriptionBoundedSimulatorInput L) Tactual := by
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hscanner
        (runConfig_eq_halt_of_haltsFromTape hreturn)
  exact ⟨Tactual, hseq, hTequiv⟩

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_closed_configRunner
    (L : SimulatorLayout) (T : Tape Bool)
    (hhlt :
      FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner.HaltsWithTape
        (FixedDescriptionBoundedSimulatorInput L) T) :
    Tape.Equiv T (CommonGround.SimulatorLayouts.handoffTape L) := by
  have hscannerKnown :=
    fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithTape_configRunner
      L
  rcases
      seqSubroutine_haltsWithTape_inv
        fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hhlt with
    ⟨Tmid, hscannerRun, hreturnReach⟩
  have hTmid_eq :
      Tmid =
        fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
          L [] :=
    haltsWithTape_functional_of_haltTransitionFree
      fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner.right
      hscannerRun hscannerKnown
  subst Tmid
  rcases hreturnReach with ⟨n, hn⟩
  have hreturnRun :
      FDBSReturnToRightShiftedInput_configRunner.HaltsFromTape
        (Tape.move Direction.left
          (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
            L []))
        T := by
    refine ⟨n, ?_⟩
    constructor
    · simpa [HaltsFromTapeIn] using
        congrArg Configuration.state hn
    · simpa [HaltsFromTapeIn] using
        congrArg Configuration.tape hn
  rcases
      FixedDescriptionBoundedSimulator.ReturnToRightShiftedInputDescription.haltsFromTapeEquiv_scannerHandoff_configRunner
        L with
    ⟨Tactual, hreturnActual, hTequiv⟩
  have hT_eq : T = Tactual :=
    haltsFromTape_functional_of_haltTransitionFree
      fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner.right
      hreturnRun hreturnActual
  rw [hT_eq]
  exact hTequiv

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivSpec_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEquivSpec_configRunner
      FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner := by
  constructor
  · exact
      fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_subroutineReady_configRunner
  constructor
  · intro L
    exact
      fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_haltsWithTapeEquiv_configRunner
        L
  · intro L T hhalt
    exact
      fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_closed_configRunner
        L T hhalt

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_configRunner :=
  ⟨FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner,
    fixedDescriptionBoundedSimulatorPaddedParserEquivSpec_scaffold_configRunner⟩


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
