import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadScan
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.PhaseAdapters
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Composition.Runs

set_option doc.verso true

/-!
# Boundary-marked encoded-field erasers

This module adapts the reusable boundary eraser to canonical encoded fields.
The first adapter validates one encoded configuration field with the existing
scanner and then erases the restored field back to a caller-placed blank
boundary marker.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

def configurationFieldBoundaryEraserDescription :
    MachineDescription :=
  SeqViaCanonical
    ConfigurationSuffixScannerDescription
    leftBoundaryEraserDescription

theorem configurationFieldBoundaryEraserDescription_subroutineReady :
    configurationFieldBoundaryEraserDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    configurationSuffixScannerDescription_subroutineReady
    leftBoundaryEraserDescription_subroutineReady

theorem configurationRestoredLeftWithBase_eq_fieldBits_reverse_append
    (cfg : Configuration) (baseLeft : List (Option Bool)) :
    configurationRestoredLeftWithBase cfg baseLeft =
      List.append ((configurationFieldBits cfg []).reverse.map some)
        baseLeft := by
  rw [← configurationRestoredBitsRev_map_some_withBase cfg baseLeft]
  rw [← configurationRestoredBitsRev_reverse cfg]
  simp

theorem configurationSuffixScannerDescription_haltsFrom_boundary
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    ConfigurationSuffixScannerDescription.HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        ((configurationFieldBits cfg
          (false :: suffixTail)).map some))
      (leftBoundaryEraserSourceTape baseLeft
        (configurationFieldBits cfg [])
        (some false) (suffixTail.map some)) := by
  rcases
      run_configurationSuffix_raw_to_handoff_withBase
        cfg (none :: baseLeft) suffixTail with
    ⟨steps, hsteps⟩
  have htarget :
      (cellListCanonicalHandoffConfigWithBase cfg.tape.right
          (List.append ((cellCodeBits cfg.tape.head).reverse.map
            some)
            (cellListCanonicalRestoredLeftWithBase cfg.tape.left
              (List.append ((stageNatBits cfg.state).reverse.map
                some)
                (none :: baseLeft))))
          (false :: suffixTail)).tape =
        leftBoundaryEraserSourceTape baseLeft
          (configurationFieldBits cfg [])
          (some false) (suffixTail.map some) := by
    rw [leftBoundaryEraserSourceTape]
    simp [cellListCanonicalHandoffConfigWithBase]
    have hleft :
        cellListCanonicalRestoredLeftWithBase cfg.tape.right
            ((List.map some (cellCodeBits cfg.tape.head)).reverse ++
              cellListCanonicalRestoredLeftWithBase cfg.tape.left
                ((List.map some (stageNatBits cfg.state)).reverse ++
                  none :: baseLeft)) =
          configurationRestoredLeftWithBase cfg (none :: baseLeft) := by
      simp [configurationRestoredLeftWithBase]
    rw [hleft]
    change
      Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            (configurationRestoredLeftWithBase cfg (none :: baseLeft))
            (some false :: List.map some suffixTail)) =
        Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            ((List.map some (configurationFieldBits cfg [])).reverse ++
              none :: baseLeft)
            (some false :: List.map some suffixTail))
    have hcfg :
        configurationRestoredLeftWithBase cfg (none :: baseLeft) =
          (List.map some (configurationFieldBits cfg [])).reverse ++
            none :: baseLeft := by
      rw [← configurationRestoredBitsRev_map_some_withBase
        cfg (none :: baseLeft)]
      rw [← configurationRestoredBitsRev_reverse cfg]
      simp [List.map_reverse]
    rw [hcfg]
  refine ⟨steps, ?_⟩
  constructor
  · simpa using congrArg Configuration.state hsteps
  · exact Eq.trans
      (by simpa using congrArg Configuration.tape hsteps)
      htarget

theorem configurationFieldBoundaryEraserDescription_haltsFrom
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    configurationFieldBoundaryEraserDescription.HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        ((configurationFieldBits cfg
          (false :: suffixTail)).map some))
      (leftBoundaryEraserTargetTape baseLeft
        (configurationFieldBits cfg [])
        (some false) (suffixTail.map some)) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      configurationSuffixScannerDescription_subroutineReady
      leftBoundaryEraserDescription_subroutineReady
      (configurationSuffixScannerDescription_haltsFrom_boundary
        cfg baseLeft suffixTail)
      (leftBoundaryEraserSourceTape_move_left_move_right
        baseLeft (configurationFieldBits cfg [])
        (some false) (suffixTail.map some))
      (leftBoundaryEraserDescription_haltsFromTape
        baseLeft (configurationFieldBits cfg [])
        (some false) (suffixTail.map some))

def configurationFieldBoundaryEraseAndPayloadScanDescription :
    MachineDescription :=
  SeqViaCanonical
    configurationFieldBoundaryEraserDescription
    rightBlankGapPayloadScanDescription

theorem configurationFieldBoundaryEraseAndPayloadScanDescription_subroutineReady :
    configurationFieldBoundaryEraseAndPayloadScanDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    configurationFieldBoundaryEraserDescription_subroutineReady
    rightBlankGapPayloadScanDescription_subroutineReady

theorem leftBoundaryEraserTargetTape_eq_gapPayloadScanSource
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    leftBoundaryEraserTargetTape baseLeft
        (configurationFieldBits cfg [])
        (some false) (suffixTail.map some) =
      rightBlankGapPayloadScanSourceTapeImplicit
        (none :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail := by
  simp [leftBoundaryEraserTargetTape,
    rightBlankGapPayloadScanSourceTapeImplicit]

theorem configurationFieldBits_length_pos
    (cfg : Configuration) :
    0 < (configurationFieldBits cfg []).length := by
  rcases configurationFieldBits_cons_false cfg [] with
    ⟨tail, htail⟩
  rw [htail]
  simp

theorem configurationFieldBoundaryEraseAndPayloadScanDescription_haltsFrom
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    configurationFieldBoundaryEraseAndPayloadScanDescription.HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        ((configurationFieldBits cfg
          (false :: suffixTail)).map some))
      (rightBlankGapPayloadScanTargetTapeImplicit
        (none :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      configurationFieldBoundaryEraserDescription_subroutineReady
      rightBlankGapPayloadScanDescription_subroutineReady
      (configurationFieldBoundaryEraserDescription_haltsFrom
        cfg baseLeft suffixTail)
      (by
        rw [leftBoundaryEraserTargetTape_eq_gapPayloadScanSource]
        exact
          rightBlankGapPayloadScanSourceTapeImplicit_move_left_move_right
            (none :: baseLeft)
            (configurationFieldBits cfg []).length false suffixTail
            (configurationFieldBits_length_pos cfg))
      (rightBlankGapPayloadScanDescription_haltsFromTapeImplicit
        (none :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail)

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
