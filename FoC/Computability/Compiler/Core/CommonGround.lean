import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts
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
