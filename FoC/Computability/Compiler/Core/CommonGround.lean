import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.Assembly
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.BoolWordQuoter
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.ReturnAppend

set_option doc.verso true

/-!
# Common compiler helper surface

This module collects stable names for the helper families that are shared by
the remaining finite-machine leaves: complete canonical field inversions,
exact/right-shifted code-word emitter contracts, closed scanner inversions, and
append/return-to-marker machines.

The declarations are re-exported rather than moved in this first pass.  That
keeps existing proof files untouched while giving later driver proofs a single
import path that does not depend on initializer-internal module names.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround

namespace FieldInversions

export EncodedRewriters.CanonicalLayouts.Fields
  ( decodeNatComplete
    decodeNatComplete_encode
    decodeNatComplete_eq_some_encode
    decodeBoolComplete
    decodeBoolComplete_encode
    decodeBoolComplete_eq_some_encode
    decodeBoolWordComplete
    decodeBoolWordComplete_encode
    decodeBoolWordComplete_eq_some_encode
    decodeCodeWordFieldComplete
    decodeCodeWordFieldComplete_encode
    decodeCodeWordFieldComplete_eq_some_encode
    decodeCellListComplete
    decodeCellListComplete_encode
    decodeCellListComplete_eq_some_encode
    decodeTapeComplete
    decodeTapeComplete_encode
    decodeTapeComplete_eq_some_encode
    decodeConfigurationComplete
    decodeConfigurationComplete_encode
    decodeConfigurationComplete_eq_some_encode )

end FieldInversions

namespace ScannerInversions

export EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner
  ( boolWordSuffixScannerDescription_runConfig_start_bit_inv
    boolWordSuffixScannerDescription_runConfig_start_nat_prefix_inv
    boolWordSuffixScannerDescription_runConfig_code_inv
    cellListSuffixScannerDescription_runConfig_code_inv
    cellListSuffixScannerDescription_runConfig_encodeCellListAppend_handoff_false
    cellListSuffixScannerDescription_runConfig_encodeCellListAppend_suffix_false
    natSuffixScannerDescription_runConfig_nonblank_suffix_inv
    configurationSuffixScannerDescription_runConfig_canonical_false_suffix_inv
    finalHitFlagsScannerDescription_runConfig_canonical_inv
    finalHitFlagsScannerDescription_runConfig_inv
    checkedDovetailLayoutScannerDescription_haltsWithTape_inputBoolWord_inv
    checkedDovetailLayoutScannerDescription_haltsWithTape_finalFlags_inv )

export EncodedRewriters.CanonicalLayouts.DovetailStagePrefix
  ( natBits_eq_encodeNatAppend
    markedPrefix_run_state200_stageNat_handoff
    natSuffix_run_state200_stageNat_to_state210 )

end ScannerInversions

namespace CodeWordEmitters

export EncodedRewriters.CanonicalLayouts
  ( ExactOutputTape
    exactOutputTape_normalizedOutput
    ExactEmitterSpec
    ExactEmitterConstruction
    OutputTape
    outputTape_normalizedOutput
    RightShiftedOutputTape
    rightShiftedOutputTape_normalizedOutput
    EmitterSpec
    EmitterConstruction
    RightShiftedEmitterSpec
    RightShiftedEmitterConstruction )

end CodeWordEmitters

namespace BoolWordQuoters

export DovetailInitialLayoutInitializer
  ( stageInputBits
    inputTapeBits
    AppendInputTapeReturnForwardSpec
    AppendInputTapeReturnSpec
    appendInputTapeReturnSpec_realizer
    checkedNonemptyBoolWordQuoteDirectSourceBits
    checkedNonemptyBoolWordQuoteDirectSourceBits_eq
    checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits
    checkedNonemptyBoolWordQuoteDirectSourceBits_encodeNatAppend
    CheckedRawBoolWordAppendCodeWordReturnDescription
    checkedRawBoolWordAppendCodeWordReturnDescription_subroutineReady
    checkedRawBoolWordAppendCodeWordReturnDescription_run
    checkedRawBoolWordAppendCodeWordReturnDescription_haltsFromTape
    CheckedRawBoolWordAppendHeaderReturnDescription
    checkedRawBoolWordAppendHeaderReturnDescription_subroutineReady
    checkedRawBoolWordAppendHeaderReturnDescription_run
    checkedRawBoolWordAppendHeaderReturnDescription_haltsFromTape )

end BoolWordQuoters

namespace Identity

theorem exactIdentityDescription_subroutineReady :
    MachineDescription.ExactIdentityDescription.SubroutineReady :=
  ⟨MachineDescription.exactIdentityDescription_wellFormed,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem exactIdentityDescription_haltsFromTape
    (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.HaltsFromTape T T := by
  refine ⟨0, ?_⟩
  constructor <;> rfl

end Identity

namespace LeftBoundaryReturn

def ReturnToLeftBoundaryDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove
        0 (some false) Direction.left 0
    , DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove
        0 (some true) Direction.left 0
    , DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove
        0 none Direction.right 1
    ]

theorem returnToLeftBoundaryDescription_wellFormed :
    ReturnToLeftBoundaryDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ReturnToLeftBoundaryDescription.transitions)
      (stateCount := ReturnToLeftBoundaryDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ReturnToLeftBoundaryDescription.transitions)
      (by native_decide)

theorem returnToLeftBoundaryDescription_haltTransitionFree :
    ReturnToLeftBoundaryDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ReturnToLeftBoundaryDescription.transitions)
    (state := ReturnToLeftBoundaryDescription.halt)
    (by native_decide)

theorem returnToLeftBoundaryDescription_subroutineReady :
    ReturnToLeftBoundaryDescription.SubroutineReady :=
  ⟨returnToLeftBoundaryDescription_wellFormed,
    returnToLeftBoundaryDescription_haltTransitionFree⟩

def returnToLeftBoundaryScanConfig
    (remainingRev : Word Bool) (scanned : List (Option Bool)) :
    MachineDescription.Configuration :=
  match remainingRev with
  | [] =>
      { state := 0
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells []
            (none :: scanned) }
  | bit :: rest =>
      { state := 0
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (rest.map some) (some bit :: scanned) }

theorem returnToLeftBoundaryDescription_run_scan
    (remainingRev : Word Bool) (scanned : List (Option Bool)) :
    ReturnToLeftBoundaryDescription.runConfig
        (remainingRev.length + 1)
        (returnToLeftBoundaryScanConfig remainingRev scanned) =
      { state := ReturnToLeftBoundaryDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (remainingRev.reverse.map some) scanned) } := by
  induction remainingRev generalizing scanned with
  | nil =>
      cases scanned <;>
      simp [returnToLeftBoundaryScanConfig,
        ReturnToLeftBoundaryDescription,
        DovetailInitialLayoutInitializer.tapeAtCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      have hstep :
          ReturnToLeftBoundaryDescription.runConfig 1
              (returnToLeftBoundaryScanConfig (bit :: rest) scanned) =
            returnToLeftBoundaryScanConfig rest (some bit :: scanned) := by
        cases bit <;> cases rest <;>
          simp [returnToLeftBoundaryScanConfig,
            ReturnToLeftBoundaryDescription,
            DovetailInitialLayoutInitializer.tapeAtCells,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
            MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches,
            MachineDescription.transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [MachineDescription.runConfig_add]
      rw [hstep]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some bit :: scanned)

theorem returnToLeftBoundaryDescription_run_from_cells
    (prefixRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    ReturnToLeftBoundaryDescription.runConfig
        (prefixRev.length + 2)
        { state := ReturnToLeftBoundaryDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (prefixRev.map some) (some current :: right) } =
      { state := ReturnToLeftBoundaryDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (prefixRev.reverse.map some)
              (some current :: right)) } := by
  rw [show prefixRev.length + 2 = 1 + (prefixRev.length + 1) by omega]
  rw [MachineDescription.runConfig_add]
  have hstep :
      ReturnToLeftBoundaryDescription.runConfig 1
          { state := ReturnToLeftBoundaryDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (prefixRev.map some) (some current :: right) } =
        returnToLeftBoundaryScanConfig prefixRev
          (some current :: right) := by
    cases current <;> cases prefixRev <;>
      simp [returnToLeftBoundaryScanConfig,
        ReturnToLeftBoundaryDescription,
        DovetailInitialLayoutInitializer.tapeAtCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hstep]
  simpa [List.append_assoc] using
    returnToLeftBoundaryDescription_run_scan prefixRev
      (some current :: right)

theorem returnToLeftBoundaryDescription_haltsFromTape_from_cells
    (prefixRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    ReturnToLeftBoundaryDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells
        (prefixRev.map some) (some current :: right))
      (DovetailInitialLayoutInitializer.tapeAtCells [none]
        (List.append (prefixRev.reverse.map some)
          (some current :: right))) := by
  rcases
      returnToLeftBoundaryDescription_run_from_cells
        prefixRev current right with
    hrun
  refine ⟨prefixRev.length + 2, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.state hrun
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.tape hrun

end LeftBoundaryReturn

namespace AppendReturn

export DovetailInitialLayoutInitializer
  ( AppendCodeWordLastDescription
    appendCodeWordLastDescription_subroutineReady
    appendCodeWordLastDescription_run_from_scan
    appendCodeWordLastDescription_run_from_scan_atCells
    appendCodeWordLastTape
    appendCodeWordLastTapeAtCells
    ReturnToCurrentMarkerDescription
    returnToCurrentMarkerDescription_subroutineReady
    returnToCurrentMarkerDescription_run
    returnToCurrentMarkerDescription_run_after_append_atCells
    AppendCodeWordReturnToCurrentMarkerDescription
    appendCodeWordReturnToCurrentMarkerDescription_subroutineReady
    appendCodeWordReturnToCurrentMarkerDescription_run_from_scan
    AppendCodeSymbolReturnToCurrentMarkerDescription
    appendCodeSymbolReturnToCurrentMarkerDescription_subroutineReady
    appendCodeSymbolReturnToCurrentMarkerDescription_run_from_scan
    TransitionPrefixedThenAppendCodeWordLastDescription
    transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
    transitionPrefixedThenAppendCodeWordLastDescription_run )

end AppendReturn

end CommonGround

end Computability
end FoC
