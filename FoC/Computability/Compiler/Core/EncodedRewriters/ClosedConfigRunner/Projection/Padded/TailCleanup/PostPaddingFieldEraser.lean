import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadScan
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.PhaseAdapters
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Composition.Runs
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.TaggedBrancher

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

theorem configurationSuffixScannerDescription_haltsFrom_boundary_withRight
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    ConfigurationSuffixScannerDescription.HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        (List.append
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some)
          rightPadding))
      (leftBoundaryEraserSourceTape baseLeft
        (configurationFieldBits cfg [])
        (some false)
        (List.append (suffixTail.map some) rightPadding)) := by
  rcases
      run_configurationSuffix_raw_to_handoff_withBaseAndRight
        cfg (none :: baseLeft) suffixTail rightPadding with
    ⟨steps, hsteps⟩
  have htarget :
      (cellListCanonicalHandoffConfigWithBaseAndRight cfg.tape.right
          (List.append ((cellCodeBits cfg.tape.head).reverse.map
            some)
            (cellListCanonicalRestoredLeftWithBase cfg.tape.left
              (List.append ((stageNatBits cfg.state).reverse.map
                some)
                (none :: baseLeft))))
          (false :: suffixTail) rightPadding).tape =
        leftBoundaryEraserSourceTape baseLeft
          (configurationFieldBits cfg [])
          (some false)
          (List.append (suffixTail.map some) rightPadding) := by
    rw [leftBoundaryEraserSourceTape]
    simp [cellListCanonicalHandoffConfigWithBaseAndRight]
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
            (some false ::
              List.append (List.map some suffixTail) rightPadding)) =
        Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            ((List.map some (configurationFieldBits cfg [])).reverse ++
              none :: baseLeft)
            (some false ::
              List.append (List.map some suffixTail) rightPadding))
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

theorem configurationFieldBoundaryEraserDescription_haltsFrom_withRight
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    configurationFieldBoundaryEraserDescription.HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        (List.append
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some)
          rightPadding))
      (leftBoundaryEraserTargetTape baseLeft
        (configurationFieldBits cfg [])
        (some false)
        (List.append (suffixTail.map some) rightPadding)) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      configurationSuffixScannerDescription_subroutineReady
      leftBoundaryEraserDescription_subroutineReady
      (configurationSuffixScannerDescription_haltsFrom_boundary_withRight
        cfg baseLeft suffixTail rightPadding)
      (leftBoundaryEraserSourceTape_move_left_move_right
        baseLeft (configurationFieldBits cfg [])
        (some false)
        (List.append (suffixTail.map some) rightPadding))
      (leftBoundaryEraserDescription_haltsFromTape
        baseLeft (configurationFieldBits cfg [])
        (some false)
        (List.append (suffixTail.map some) rightPadding))

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

theorem leftBoundaryEraserTargetTape_eq_gapPayloadScanSource_withRight
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (padding : List (Option Bool)) :
    leftBoundaryEraserTargetTape baseLeft
        (configurationFieldBits cfg [])
        (some false)
        (List.append (suffixTail.map some)
          (none :: padding)) =
      rightBlankGapPayloadScanSourceTape
        (none :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail
        padding := by
  simp [leftBoundaryEraserTargetTape,
    rightBlankGapPayloadScanSourceTape]

theorem rightBlankGapPayloadScanSourceTape_move_left_move_right
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) (hgap : 0 < gap) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightBlankGapPayloadScanSourceTape
            baseLeft gap current payloadRest padding)) =
      rightBlankGapPayloadScanSourceTape
        baseLeft gap current payloadRest padding := by
  cases gap with
  | zero =>
      omega
  | succ gap =>
      cases gap with
      | zero =>
          simp [rightBlankGapPayloadScanSourceTape, tapeAtCells,
            Tape.move, Tape.moveLeft, Tape.moveRight, List.replicate_succ]
      | succ gap =>
          simp [rightBlankGapPayloadScanSourceTape, tapeAtCells,
            Tape.move, Tape.moveLeft, Tape.moveRight, List.replicate_succ]

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

theorem configurationFieldBoundaryEraseAndPayloadScanDescription_haltsFrom_withRight
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (padding : List (Option Bool)) :
    configurationFieldBoundaryEraseAndPayloadScanDescription.HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        (List.append
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some)
          (none :: padding)))
      (rightBlankGapPayloadScanTargetTape
        (none :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail
        padding) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      configurationFieldBoundaryEraserDescription_subroutineReady
      rightBlankGapPayloadScanDescription_subroutineReady
      (configurationFieldBoundaryEraserDescription_haltsFrom_withRight
        cfg baseLeft suffixTail (none :: padding))
      (by
        rw [leftBoundaryEraserTargetTape_eq_gapPayloadScanSource_withRight]
        exact
          rightBlankGapPayloadScanSourceTape_move_left_move_right
            (none :: baseLeft)
            (configurationFieldBits cfg []).length false suffixTail
            padding
            (configurationFieldBits_length_pos cfg))
      (rightBlankGapPayloadScanDescription_haltsFromTape
        (none :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail
        padding)

def restoreBoundaryBitDescription
    (bit : Bool) : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none (some bit) Direction.right 2
    , transition 2 none none Direction.left 3
    ]

theorem restoreBoundaryBitDescription_wellFormed
    (bit : Bool) :
    (restoreBoundaryBitDescription bit).WellFormed := by
  refine
    ⟨by cases bit <;> decide,
      by cases bit <;> decide,
      by cases bit <;> decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (restoreBoundaryBitDescription bit).transitions)
      (stateCount := (restoreBoundaryBitDescription bit).stateCount)
      (by cases bit <;> decide)
  · exact transition_deterministic_of_all
      (l := (restoreBoundaryBitDescription bit).transitions)
      (by cases bit <;> decide)

theorem restoreBoundaryBitDescription_haltTransitionFree
    (bit : Bool) :
    (restoreBoundaryBitDescription bit).HaltTransitionFree :=
  transition_notFrom_of_all
    (l := (restoreBoundaryBitDescription bit).transitions)
    (state := (restoreBoundaryBitDescription bit).halt)
    (by cases bit <;> decide)

theorem restoreBoundaryBitDescription_subroutineReady
    (bit : Bool) :
    (restoreBoundaryBitDescription bit).SubroutineReady :=
  ⟨restoreBoundaryBitDescription_wellFormed bit,
    restoreBoundaryBitDescription_haltTransitionFree bit⟩

theorem restoreBoundaryBitDescription_haltsFromTape
    (bit : Bool) (baseLeft right : List (Option Bool)) :
    (restoreBoundaryBitDescription bit).HaltsFromTape
      (tapeAtCells (none :: baseLeft) (none :: right))
      (tapeAtCells baseLeft (some bit :: none :: right)) := by
  refine ⟨3, ?_⟩
  constructor <;>
  cases right <;>
    simp [restoreBoundaryBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

def restoreBoundaryBitAndPayloadScanDescription
    (bit : Bool) : MachineDescription :=
  seqSubroutine (restoreBoundaryBitDescription bit)
    rightBlankGapPayloadScanDescription Direction.right

theorem restoreBoundaryBitAndPayloadScanDescription_subroutineReady
    (bit : Bool) :
    (restoreBoundaryBitAndPayloadScanDescription bit).SubroutineReady :=
  seqSubroutine_subroutineReady
    (restoreBoundaryBitDescription_subroutineReady bit)
    rightBlankGapPayloadScanDescription_subroutineReady

theorem restoreBoundaryBitAndPayloadScanDescription_haltsFromTape
    (bit : Bool) (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    (restoreBoundaryBitAndPayloadScanDescription bit).HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        (List.append
          (List.replicate (Nat.succ gap) (none : Option Bool))
          (some current :: List.append (payloadRest.map some)
            (none :: padding))))
      (rightBlankGapPayloadScanTargetTape
        (some bit :: baseLeft) (Nat.succ gap) current payloadRest
        padding) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (restoreBoundaryBitDescription_subroutineReady bit)
      rightBlankGapPayloadScanDescription_subroutineReady
      (restoreBoundaryBitDescription_haltsFromTape bit baseLeft
        (List.append
          (List.replicate gap (none : Option Bool))
          (some current :: List.append (payloadRest.map some)
            (none :: padding))))
      (by
        simp [rightBlankGapPayloadScanSourceTape, tapeAtCells,
          Tape.move, Tape.moveRight, List.replicate_succ,
          List.replicate_succ])
      (rightBlankGapPayloadScanDescription_haltsFromTape
        (some bit :: baseLeft) (Nat.succ gap) current payloadRest
        padding)

def restoreBoundaryBitFromBoundaryDescription
    (bit : Bool) : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none (some bit) Direction.right 1
    , transition 1 none none Direction.left 2
    ]

theorem restoreBoundaryBitFromBoundaryDescription_wellFormed
    (bit : Bool) :
    (restoreBoundaryBitFromBoundaryDescription bit).WellFormed := by
  refine
    ⟨by cases bit <;> decide,
      by cases bit <;> decide,
      by cases bit <;> decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (restoreBoundaryBitFromBoundaryDescription bit).transitions)
      (stateCount :=
        (restoreBoundaryBitFromBoundaryDescription bit).stateCount)
      (by cases bit <;> decide)
  · exact transition_deterministic_of_all
      (l := (restoreBoundaryBitFromBoundaryDescription bit).transitions)
      (by cases bit <;> decide)

theorem restoreBoundaryBitFromBoundaryDescription_haltTransitionFree
    (bit : Bool) :
    (restoreBoundaryBitFromBoundaryDescription bit).HaltTransitionFree :=
  transition_notFrom_of_all
    (l := (restoreBoundaryBitFromBoundaryDescription bit).transitions)
    (state := (restoreBoundaryBitFromBoundaryDescription bit).halt)
    (by cases bit <;> decide)

theorem restoreBoundaryBitFromBoundaryDescription_subroutineReady
    (bit : Bool) :
    (restoreBoundaryBitFromBoundaryDescription bit).SubroutineReady :=
  ⟨restoreBoundaryBitFromBoundaryDescription_wellFormed bit,
    restoreBoundaryBitFromBoundaryDescription_haltTransitionFree bit⟩

theorem restoreBoundaryBitFromBoundaryDescription_haltsFromTape
    (bit : Bool) (baseLeft right : List (Option Bool)) :
    (restoreBoundaryBitFromBoundaryDescription bit).HaltsFromTape
      (tapeAtCells baseLeft (none :: none :: right))
      (tapeAtCells baseLeft (some bit :: none :: right)) := by
  refine ⟨2, ?_⟩
  constructor <;>
  cases right <;>
    simp [restoreBoundaryBitFromBoundaryDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

def restoreBoundaryBitFromBoundaryAndPayloadScanDescription
    (bit : Bool) : MachineDescription :=
  seqSubroutine (restoreBoundaryBitFromBoundaryDescription bit)
    rightBlankGapPayloadScanDescription Direction.right

theorem restoreBoundaryBitFromBoundaryAndPayloadScanDescription_subroutineReady
    (bit : Bool) :
    (restoreBoundaryBitFromBoundaryAndPayloadScanDescription bit).SubroutineReady :=
  seqSubroutine_subroutineReady
    (restoreBoundaryBitFromBoundaryDescription_subroutineReady bit)
    rightBlankGapPayloadScanDescription_subroutineReady

theorem restoreBoundaryBitFromBoundaryAndPayloadScanDescription_haltsFromTape
    (bit : Bool) (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    (restoreBoundaryBitFromBoundaryAndPayloadScanDescription bit).HaltsFromTape
      (tapeAtCells baseLeft
        (none ::
          List.append
            (List.replicate (Nat.succ gap) (none : Option Bool))
            (some current :: List.append (payloadRest.map some)
              (none :: padding))))
      (rightBlankGapPayloadScanTargetTape
        (some bit :: baseLeft) (Nat.succ gap) current payloadRest
        padding) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (restoreBoundaryBitFromBoundaryDescription_subroutineReady bit)
      rightBlankGapPayloadScanDescription_subroutineReady
      (by
        simpa [List.replicate_succ, List.append_assoc] using
          restoreBoundaryBitFromBoundaryDescription_haltsFromTape
            bit baseLeft
            (List.append
              (List.replicate gap (none : Option Bool))
              (some current :: List.append (payloadRest.map some)
                (none :: padding))))
      (by
        simp [rightBlankGapPayloadScanSourceTape, tapeAtCells,
          Tape.move, Tape.moveRight, List.replicate_succ])
      (rightBlankGapPayloadScanDescription_haltsFromTape
        (some bit :: baseLeft) (Nat.succ gap) current payloadRest
        padding)

theorem restoreBoundaryBitFromBoundaryAndPayloadScanDescription_haltsFromTape_pos
    (bit : Bool) (baseLeft : List (Option Bool)) (gap : Nat)
    (hgap : 0 < gap) (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    (restoreBoundaryBitFromBoundaryAndPayloadScanDescription bit).HaltsFromTape
      (tapeAtCells baseLeft
        (none ::
          List.append
            (List.replicate gap (none : Option Bool))
            (some current :: List.append (payloadRest.map some)
              (none :: padding))))
      (rightBlankGapPayloadScanTargetTape
        (some bit :: baseLeft) gap current payloadRest padding) := by
  cases gap with
  | zero =>
      omega
  | succ gap =>
      exact
        restoreBoundaryBitFromBoundaryAndPayloadScanDescription_haltsFromTape
          bit baseLeft gap current payloadRest padding

def configurationFieldBoundaryEraseRestoreAndPayloadScanDescription
    (bit : Bool) : MachineDescription :=
  seqSubroutine configurationFieldBoundaryEraserDescription
    (restoreBoundaryBitFromBoundaryAndPayloadScanDescription bit)
    Direction.left

theorem configurationFieldBoundaryEraseRestoreAndPayloadScanDescription_subroutineReady
    (bit : Bool) :
    (configurationFieldBoundaryEraseRestoreAndPayloadScanDescription
      bit).SubroutineReady :=
  seqSubroutine_subroutineReady
    configurationFieldBoundaryEraserDescription_subroutineReady
    (restoreBoundaryBitFromBoundaryAndPayloadScanDescription_subroutineReady
      bit)

theorem configurationFieldBoundaryEraseRestoreAndPayloadScanDescription_haltsFrom_withRight
    (bit : Bool) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (padding : List (Option Bool)) :
    (configurationFieldBoundaryEraseRestoreAndPayloadScanDescription
      bit).HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        (List.append
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some)
          (none :: padding)))
      (rightBlankGapPayloadScanTargetTape
        (some bit :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail
        padding) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      configurationFieldBoundaryEraserDescription_subroutineReady
      (restoreBoundaryBitFromBoundaryAndPayloadScanDescription_subroutineReady
        bit)
      (configurationFieldBoundaryEraserDescription_haltsFrom_withRight
        cfg baseLeft suffixTail (none :: padding))
      (by
        cases hlen : (configurationFieldBits cfg []).length with
        | zero =>
            simp [leftBoundaryEraserTargetTape, tapeAtCells, Tape.move,
              Tape.moveLeft, hlen]
        | succ gap =>
            simp [leftBoundaryEraserTargetTape, tapeAtCells, Tape.move,
              Tape.moveLeft, hlen, List.replicate_succ])
      (restoreBoundaryBitFromBoundaryAndPayloadScanDescription_haltsFromTape_pos
        bit baseLeft (configurationFieldBits cfg []).length
        (configurationFieldBits_length_pos cfg) false suffixTail padding)

def blankLeftFalseMarkerBeforeFieldDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 1 (some false) none Direction.right 2
    ]

theorem blankLeftFalseMarkerBeforeFieldDescription_wellFormed :
    blankLeftFalseMarkerBeforeFieldDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := blankLeftFalseMarkerBeforeFieldDescription.transitions)
      (stateCount :=
        blankLeftFalseMarkerBeforeFieldDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := blankLeftFalseMarkerBeforeFieldDescription.transitions)
      (by decide)

theorem blankLeftFalseMarkerBeforeFieldDescription_haltTransitionFree :
    blankLeftFalseMarkerBeforeFieldDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := blankLeftFalseMarkerBeforeFieldDescription.transitions)
    (state := blankLeftFalseMarkerBeforeFieldDescription.halt)
    (by decide)

theorem blankLeftFalseMarkerBeforeFieldDescription_subroutineReady :
    blankLeftFalseMarkerBeforeFieldDescription.SubroutineReady :=
  ⟨blankLeftFalseMarkerBeforeFieldDescription_wellFormed,
    blankLeftFalseMarkerBeforeFieldDescription_haltTransitionFree⟩

theorem blankLeftFalseMarkerBeforeFieldDescription_haltsFromTape
    (baseLeft rest : List (Option Bool)) :
    blankLeftFalseMarkerBeforeFieldDescription.HaltsFromTape
      (tapeAtCells (some false :: baseLeft) (some false :: rest))
      (tapeAtCells (none :: baseLeft) (some false :: rest)) := by
  refine ⟨2, ?_⟩
  constructor <;>
  cases rest <;>
    simp [blankLeftFalseMarkerBeforeFieldDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

def blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
    (bit : Bool) : MachineDescription :=
  SeqViaCanonical blankLeftFalseMarkerBeforeFieldDescription
    (configurationFieldBoundaryEraseRestoreAndPayloadScanDescription bit)

theorem blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription_subroutineReady
    (bit : Bool) :
    (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
      bit).SubroutineReady :=
  SeqViaCanonical_subroutineReady
    blankLeftFalseMarkerBeforeFieldDescription_subroutineReady
    (configurationFieldBoundaryEraseRestoreAndPayloadScanDescription_subroutineReady
      bit)

theorem blankBoundaryFieldSourceTape_move_left_move_right
    (baseLeft rest : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells (none :: baseLeft) (some false :: none :: rest))) =
      tapeAtCells (none :: baseLeft) (some false :: none :: rest) := by
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem blankBoundaryFieldSourceTape_move_left_move_right_field
    (baseLeft fieldRest : List (Option Bool))
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells (none :: baseLeft)
            (some false :: fieldRest ++ none :: padding))) =
      tapeAtCells (none :: baseLeft)
        (some false :: fieldRest ++ none :: padding) := by
  cases fieldRest <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription_haltsFrom_withRight
    (bit : Bool) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (padding : List (Option Bool)) :
    (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
      bit).HaltsFromTape
      (tapeAtCells (some false :: baseLeft)
        (List.append
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some)
          (none :: padding)))
      (rightBlankGapPayloadScanTargetTape
        (some bit :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail
        padding) := by
  rcases configurationFieldBits_cons_false cfg (false :: suffixTail) with
    ⟨fieldRest, hfield⟩
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      blankLeftFalseMarkerBeforeFieldDescription_subroutineReady
      (configurationFieldBoundaryEraseRestoreAndPayloadScanDescription_subroutineReady
        bit)
      (by
        rw [hfield]
        simpa [List.map_append, List.append_assoc] using
          blankLeftFalseMarkerBeforeFieldDescription_haltsFromTape
            baseLeft
            (List.append (fieldRest.map some) (none :: padding)))
      (by
        rw [hfield]
        simpa [List.map_append, List.append_assoc] using
          blankBoundaryFieldSourceTape_move_left_move_right_field
            baseLeft (fieldRest.map some) padding)
      (configurationFieldBoundaryEraseRestoreAndPayloadScanDescription_haltsFrom_withRight
        bit cfg baseLeft suffixTail padding)

def boundaryBitConfigurationFieldEraseAndPayloadScanDescription :
    MachineDescription :=
  DovetailInitialLayoutInitializer.RestoreFirstBitTaggedBrancherDescription
    ExactIdentityDescription
    (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
      false)
    (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
      true)

theorem boundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady :
    boundaryBitConfigurationFieldEraseAndPayloadScanDescription.SubroutineReady :=
  DovetailInitialLayoutInitializer.restoreFirstBitTaggedBrancherDescription_subroutineReady
    CommonGround.Identity.exactIdentityDescription_subroutineReady
    (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription_subroutineReady
      false)
    (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription_subroutineReady
      true)

theorem boundaryBitConfigurationFieldEraseAndPayloadScanDescription_haltsFromTape
    (bit : Bool) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (padding : List (Option Bool)) :
    boundaryBitConfigurationFieldEraseAndPayloadScanDescription.HaltsFromTape
      (tapeAtCells baseLeft
        (some bit ::
          List.append
            ((configurationFieldBits cfg
              (false :: suffixTail)).map some)
            (none :: padding)))
      (rightBlankGapPayloadScanTargetTape
        (some bit :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail
        padding) := by
  rcases configurationFieldBits_cons_false cfg (false :: suffixTail) with
    ⟨fieldRest, hfield⟩
  let T : Tape Bool :=
    tapeAtCells baseLeft
      (some bit ::
        List.append
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some)
          (none :: padding))
  let Tout : Tape Bool :=
    rightBlankGapPayloadScanTargetTape
      (some bit :: baseLeft)
      (configurationFieldBits cfg []).length false suffixTail padding
  have hblankReady : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hfalseReady :
      (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
        false).SubroutineReady :=
    blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription_subroutineReady
      false
  have htrueReady :
      (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
        true).SubroutineReady :=
    blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription_subroutineReady
      true
  cases bit
  · have hread : Tape.read T = some false := by
      simp [T, tapeAtCells, Tape.read]
    rcases
        runConfig_eq_halt_of_haltsFromTape
          (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription_haltsFrom_withRight
            false cfg baseLeft suffixTail padding) with
      ⟨steps, hsteps⟩
    have hbranch :
        exists steps : Nat,
          (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
            false).runConfig steps
            { state :=
                (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
                  false).start,
              tape := Tape.move Direction.right (Tape.write (some false) T) } =
          { state :=
              (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
                false).halt,
            tape := Tout } := by
      refine ⟨steps, ?_⟩
      simpa [T, Tout, hfield, tapeAtCells, Tape.write, Tape.move,
        Tape.moveRight, List.map_append, List.append_assoc] using hsteps
    rcases
        DovetailInitialLayoutInitializer.restoreFirstBitTaggedBrancherDescription_run_false
          hblankReady hfalseReady htrueReady hread hbranch with
      ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    constructor
    · simpa [boundaryBitConfigurationFieldEraseAndPayloadScanDescription,
        T, Tout, MachineDescription.HaltsFromTapeIn] using
        congrArg MachineDescription.Configuration.state hsteps
    · simpa [boundaryBitConfigurationFieldEraseAndPayloadScanDescription,
        T, Tout, MachineDescription.HaltsFromTapeIn] using
        congrArg MachineDescription.Configuration.tape hsteps
  · have hread : Tape.read T = some true := by
      simp [T, tapeAtCells, Tape.read]
    rcases
        runConfig_eq_halt_of_haltsFromTape
          (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription_haltsFrom_withRight
            true cfg baseLeft suffixTail padding) with
      ⟨steps, hsteps⟩
    have hbranch :
        exists steps : Nat,
          (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
            true).runConfig steps
            { state :=
                (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
                  true).start,
              tape := Tape.move Direction.right (Tape.write (some false) T) } =
          { state :=
              (blankMarkerThenConfigurationFieldBoundaryEraseRestoreAndPayloadScanDescription
                true).halt,
            tape := Tout } := by
      refine ⟨steps, ?_⟩
      simpa [T, Tout, hfield, tapeAtCells, Tape.write, Tape.move,
        Tape.moveRight, List.map_append, List.append_assoc] using hsteps
    rcases
        DovetailInitialLayoutInitializer.restoreFirstBitTaggedBrancherDescription_run_true
          hblankReady hfalseReady htrueReady hread hbranch with
      ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    constructor
    · simpa [boundaryBitConfigurationFieldEraseAndPayloadScanDescription,
        T, Tout, MachineDescription.HaltsFromTapeIn] using
        congrArg MachineDescription.Configuration.state hsteps
    · simpa [boundaryBitConfigurationFieldEraseAndPayloadScanDescription,
        T, Tout, MachineDescription.HaltsFromTapeIn] using
        congrArg MachineDescription.Configuration.tape hsteps

def leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription :
    MachineDescription :=
  SeqViaCanonical leftMoveOnceDescription
    boundaryBitConfigurationFieldEraseAndPayloadScanDescription

theorem leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady :
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    leftMoveOnceDescription_subroutineReady
    boundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady

theorem boundaryBitSourceTape_move_left_move_right
    (bit : Bool) (baseLeft rest : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells baseLeft (some bit :: some false :: rest))) =
      tapeAtCells baseLeft (some bit :: some false :: rest) := by
  cases bit <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_haltsFromTape
    (bit : Bool) (cfg : Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool)
    (padding : List (Option Bool)) :
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription.HaltsFromTape
      (tapeAtCells (some bit :: baseLeft)
        (List.append
          ((configurationFieldBits cfg
            (false :: suffixTail)).map some)
          (none :: padding)))
      (rightBlankGapPayloadScanTargetTape
        (some bit :: baseLeft)
        (configurationFieldBits cfg []).length false suffixTail
        padding) := by
  rcases configurationFieldBits_cons_false cfg (false :: suffixTail) with
    ⟨fieldRest, hfield⟩
  let Tin2 : Tape Bool :=
    tapeAtCells baseLeft
      (some bit ::
        some false ::
          List.append (fieldRest.map some) (none :: padding))
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      (Tin2 := Tin2)
      leftMoveOnceDescription_subroutineReady
      boundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady
      (leftMoveOnceDescription_haltsFromTape
        (tapeAtCells (some bit :: baseLeft)
          (List.append
            ((configurationFieldBits cfg
              (false :: suffixTail)).map some)
            (none :: padding))))
      (by
        rw [hfield]
        simpa [Tin2, List.map_append, List.append_assoc] using
          boundaryBitSourceTape_move_left_move_right
            bit baseLeft
            (List.append (fieldRest.map some) (none :: padding)))
      (by
        simpa [Tin2, hfield, List.map_append, List.append_assoc] using
          boundaryBitConfigurationFieldEraseAndPayloadScanDescription_haltsFromTape
            bit cfg baseLeft suffixTail padding)

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
