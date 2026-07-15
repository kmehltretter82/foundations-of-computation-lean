import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.RejectGap
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingFieldEraser
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Tape2SubroutineLift

set_option doc.verso true

/-!
Rejecting-route tape-0 padding and accept-count restoration.
-/

set_option linter.unusedSimpArgs false

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectTape0Padding

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptFinish AcceptReconstructPrefix AcceptT0Allocator AcceptFinalTail
open RejectTape2Tail RejectBranchShapes

def processedSourceBits (L : DovetailLayout) : List Bool :=
  List.append boolWordRawBitsDecoderHeaderBits
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        (ParsedLayoutBits L).length)
      (AcceptConfigCopy.wrappedBits (prefixThroughStageBits L)))

def remainingSourceBits (L : DovetailLayout) : List Bool :=
  List.append (AcceptConfigCopy.wrappedBits (configHitBits L))
    (false ::
      countWindowPostFieldDecodedPrefixStructuredSuffixTail false L)
theorem sourceWord_eq_processed_remaining (L : DovetailLayout) :
    sourceWord false L =
      List.append (processedSourceBits L) (remainingSourceBits L) := by
  unfold sourceWord processedSourceBits remainingSourceBits
    boolWordRawBitsDecoderEncodedFieldBits
  rw [← wrappedBits_eq_cellsCodeBits_map_some]
  rw [parsedLayoutBits_eq_prefix_configHit, wrappedBits_append]
  simp [List.append_assoc]
  done

theorem afterDriverTape0_eq_processed_scan (L : DovetailLayout) :
    afterDriverTape0 false L =
      tapeAtCells
        (List.append ((processedSourceBits L).reverse.map some) [none])
        (List.append ((remainingSourceBits L).map some) [none]) := by
  simp [afterDriverTape0, processedSourceBits, remainingSourceBits,
    positionTape0Left, scanTape, List.reverse_append, List.map_append,
    List.append_assoc]
  done

def rightEdgeTape0 (L : DovetailLayout) : Tape Bool :=
  Tape0RewindPadded.sourceTape [] (sourceWord false L) []
theorem tape0RightEdge_target_eq_rightEdgeTape0 (L : DovetailLayout) :
    Tape0RightEdge.targetTape
        (List.append ((processedSourceBits L).reverse.map some) [none])
        (remainingSourceBits L) =
      rightEdgeTape0 L := by
  unfold rightEdgeTape0 Tape0RewindPadded.sourceTape
  rw [sourceWord_eq_processed_remaining]
  simp [Tape0RightEdge.targetTape, List.reverse_append, List.map_append,
    List.append_assoc]
  done

theorem rightEdgeDescription_realizes
    (L : DovetailLayout) (T2 : Tape Bool) :
    loweredRightEdgeDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 false L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 L) Tape.blank T2) := by
  rw [afterDriverTape0_eq_processed_scan]
  have h := loweredRightEdgeDescription_realizes
    (remainingSourceBits L)
    (List.append ((processedSourceBits L).reverse.map some) [none]) T2
  rw [tape0RightEdge_target_eq_rightEdgeTape0] at h
  exact h
  done

namespace LocateAccept

def origin : Nat := 0
def leading : Nat := 1
def stageSecond : Nat := 2
def stageThird : Nat := 3
def stageFourth : Nat := 4
def stageFirst : Nat := 5
def halt : Nat := 6
def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action2 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 keepS keepS action2 target

def rows : List Transition :=
  [ rowsForTape2Read origin none (writeR (some true)) leading
  , rowsForTape2Read leading none keepR leading
  , rowsForTape2Read leading (some false) keepR stageSecond
  , rowsForTape2Read stageFirst (some false) keepR stageSecond
  , rowsForTape2Read stageSecond (some false) keepR stageThird
  , rowsForTape2Read stageThird (some true) keepR stageFourth
  , rowsForTape2Read stageFourth (some false) keepR stageFirst
  , rowsForTape2Read stageFourth (some true) (writeR none) halt ].flatten

def description : Description :=
  ThreeTape.description 7 origin halt rows
theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

syntax "locate_accept_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| locate_accept_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape2Read,
          origin, leading, stageSecond, stageThird, stageFourth,
          stageFirst, halt, allReads2, allReadCells, List.find?,
          tapeAtCells, $lemmas,*])

theorem origin_step
    (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        (config origin T0 T1 (tapeAtCells left (none :: right))) =
      config leading T0 T1 (tapeAtCells (some true :: left) right) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit => cases bit <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit1 => cases bit1 <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
theorem leading_blank_step
    (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        (config leading T0 T1 (tapeAtCells left (none :: right))) =
      config leading T0 T1 (tapeAtCells (none :: left) right) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit => cases bit <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit1 => cases bit1 <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  done

theorem leading_blanks_run
    (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig n
        (config leading T0 T1
          (tapeAtCells left
            (List.append (List.replicate n (none : Option Bool)) right))) =
      config leading T0 T1
        (tapeAtCells
          (List.append (List.replicate n (none : Option Bool)) left)
          right) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      rw [show n + 1 = 1 + n by lia]
      rw [Description.runConfig_add]
      simp only [List.append_eq, List.cons_append]
      rw [leading_blank_step]
      apply Eq.trans (ih (none :: left))
      rw [AcceptFinish.replicate_none_append_cons]
      rfl
  done

theorem leading_tick_run
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 4
        (config leading T0 T1
          (tapeAtCells left
            (some false :: some false :: some true :: some false :: right))) =
      config stageFirst T0 T1
        (tapeAtCells
          (some false :: some true :: some false :: some false :: left)
          right) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit => cases bit <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit1 => cases bit1 <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  done
theorem stageFirst_tick_run
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 4
        (config stageFirst T0 T1
          (tapeAtCells left
            (some false :: some false :: some true :: some false :: right))) =
      config stageFirst T0 T1
        (tapeAtCells
          (some false :: some true :: some false :: some false :: left)
          right) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit => cases bit <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit1 => cases bit1 <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  done

theorem leading_done_run
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 4
        (config leading T0 T1
          (tapeAtCells left
            (some false :: some false :: some true :: some true :: right))) =
      config halt T0 T1
        (tapeAtCells
          (none :: some true :: some false :: some false :: left) right) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit => cases bit <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit1 => cases bit1 <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  done

theorem stageFirst_done_run
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 4
        (config stageFirst T0 T1
          (tapeAtCells left
            (some false :: some false :: some true :: some true :: right))) =
      config halt T0 T1
        (tapeAtCells
          (none :: some true :: some false :: some false :: left) right) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit => cases bit <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => locate_accept_step [h0, h1] <;> cases right <;> rfl
      | some bit1 => cases bit1 <;>
          locate_accept_step [h0, h1] <;> cases right <;> rfl
  done
def stageBeforeLastBits (n : Nat) : Word Bool :=
  List.append (OutputLengthAllocator.tickStream n) [false, false, true]

theorem stageNatBits_eq_beforeLast_true (n : Nat) :
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n =
      List.append (stageBeforeLastBits n) [true] := by
  rw [OutputLengthAllocator.stageNatBits_eq_tickStream_append_done]
  simp [stageBeforeLastBits, List.append_assoc]
  done

theorem stageNatBits_succ_cells
    (n : Nat) (right : List (Option Bool)) :
    List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (n + 1)).map some)
        right =
      some false :: some false :: some true :: some false ::
        List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            n).map some)
          right := by
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ]
  rfl
theorem stageFirst_run
    (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig (4 * (n + 1))
        (config stageFirst T0 T1
          (tapeAtCells left
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n).map some)
              right))) =
      config halt T0 T1
        (tapeAtCells
          (List.append
            (none :: (stageBeforeLastBits n).reverse.map some)
            left)
          right) := by
  induction n generalizing left with
  | zero => exact stageFirst_done_run T0 T1 left right
  | succ n ih =>
      rw [stageNatBits_succ_cells]
      rw [show 4 * (n + 1 + 1) = 4 + 4 * (n + 1) by lia]
      rw [Description.runConfig_add]
      rw [stageFirst_tick_run]
      rw [ih]
      simp [stageBeforeLastBits, OutputLengthAllocator.tickStream,
        List.reverse_append, List.map_append, List.append_assoc]

theorem leadingStage_run
    (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig (4 * (n + 1))
        (config leading T0 T1
          (tapeAtCells left
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n).map some)
              right))) =
      config halt T0 T1
        (tapeAtCells
          (List.append
            (none :: (stageBeforeLastBits n).reverse.map some)
            left)
          right) := by
  cases n with
  | zero => exact leading_done_run T0 T1 left right
  | succ n =>
      rw [stageNatBits_succ_cells]
      rw [show 4 * (n + 1 + 1) = 4 + 4 * (n + 1) by lia]
      rw [Description.runConfig_add]
      rw [leading_tick_run]
      rw [stageFirst_run]
      simp [stageBeforeLastBits, OutputLengthAllocator.tickStream,
        List.reverse_append, List.map_append, List.append_assoc]

theorem run
    (padding stage : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig (1 + padding + 4 * (stage + 1))
        (config origin T0 T1
          (tapeAtCells left
            (none ::
              List.append (List.replicate padding none)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage).map some)
                  right)))) =
      config halt T0 T1
        (tapeAtCells
          (List.append
            (none :: (stageBeforeLastBits stage).reverse.map some)
            (List.append (List.replicate padding none) (some true :: left)))
          right) := by
  rw [show 1 + padding + 4 * (stage + 1) =
      1 + (padding + 4 * (stage + 1)) by lia]
  rw [Description.runConfig_add]
  rw [origin_step]
  rw [Description.runConfig_add]
  rw [leading_blanks_run]
  exact leadingStage_run stage T0 T1
    (List.append (List.replicate padding none) (some true :: left)) right
def sourceTape
    (padding stage : Nat) (left right : List (Option Bool)) : Tape Bool :=
  tapeAtCells left
    (none ::
      List.append (List.replicate padding none)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          right))

def targetTape
    (padding stage : Nat) (left right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (none :: (stageBeforeLastBits stage).reverse.map some)
      (List.append (List.replicate padding none) (some true :: left)))
    right

def fuel (padding stage : Nat) : Nat :=
  1 + padding + 4 * (stage + 1)
def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_ready : loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady ready.left supports

theorem loweredDescription_realizes
    (padding stage : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1
        (sourceTape padding stage left right))
      (encodedGuardedStructured3Tapes T0 T1
        (targetTape padding stage left right)) := by
  simpa [loweredDescription, sourceTape, targetTape, fuel,
    encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      ready.left ready.right supports
      (c := config origin T0 T1 (sourceTape padding stage left right))
      (tapes := [T0, T1, targetTape padding stage left right])
      rfl rfl ⟨fuel padding stage, by
        rw [show description.halt = halt by rfl]
        change description.runConfig (fuel padding stage)
            (config origin T0 T1 (sourceTape padding stage left right)) =
          config halt T0 T1 (targetTape padding stage left right)
        simpa [fuel, sourceTape, targetTape] using
          run padding stage T0 T1 left right⟩

end LocateAccept
def locateLeadingPadding (L : DovetailLayout) : Nat :=
  (ParsedLayoutBits L).length + markerOffset L + 7

def rejectPostStageRight (L : DovetailLayout) : List (Option Bool) :=
  List.append ((AcceptBranch.acceptBits L).map some)
    (List.append ((AcceptBranch.rejectBits L).map some)
      (List.append (List.replicate 4 none)
        (List.append
          ((RejectBranchShapes.rejectHitBits L).map some)
          [none, none])))

theorem locateSourceTape_eq_rejectFinalOutputTape2 (L : DovetailLayout) :
    LocateAccept.sourceTape
        (locateLeadingPadding L) L.stage [none]
        (rejectPostStageRight L) =
      rejectFinalOutputTape2 L := by
  rw [rejectFinalOutputTape2_shape]
  simp [LocateAccept.sourceTape, locateLeadingPadding, rejectPostStageRight,
    RejectLive.rejectKeptPrefixBits,
    AcceptBranch.acceptBits, AcceptBranch.rejectBits,
    RejectBranchShapes.rejectHitBits,
    List.map_append, List.append_assoc]
  congr 1
  done
def afterLocateTape2 (L : DovetailLayout) : Tape Bool :=
  LocateAccept.targetTape
    (locateLeadingPadding L) L.stage [none]
    (rejectPostStageRight L)

theorem locateAcceptDescription_realizes (L : DovetailLayout) :
    LocateAccept.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 L) Tape.blank (rejectFinalOutputTape2 L))
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 L) Tape.blank (afterLocateTape2 L)) := by
  rw [← locateSourceTape_eq_rejectFinalOutputTape2]
  exact LocateAccept.loweredDescription_realizes
    (locateLeadingPadding L) L.stage (rightEdgeTape0 L) Tape.blank
    [none] (rejectPostStageRight L)

def rejectConfigTail (L : DovetailLayout) : Word Bool :=
  (configurationFieldBits L.rejectConfig []).tail
theorem rejectBits_eq_false_cons_tail (L : DovetailLayout) :
    AcceptBranch.rejectBits L =
      false :: rejectConfigTail L := by
  rcases configurationFieldBits_cons_false L.rejectConfig [] with
    ⟨tail, htail⟩
  simp [AcceptBranch.rejectBits, rejectConfigTail, htail]
  done

def rejectRightPadding (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 4 none)
    (List.append
      ((RejectBranchShapes.rejectHitBits L).map some)
      [none, none])

def acceptScanBaseLeft (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((LocateAccept.stageBeforeLastBits L.stage).reverse.map some)
    (List.append (List.replicate (locateLeadingPadding L) none)
      [some true, none])
def acceptScannerSourceTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells (none :: acceptScanBaseLeft L)
    (List.append
      ((configurationFieldBits L.acceptConfig
        (false :: rejectConfigTail L)).map some)
      (rejectRightPadding L))

theorem afterLocateTape2_eq_unparsedAcceptTape2
    (L : DovetailLayout) :
    afterLocateTape2 L =
      tapeAtCells (none :: acceptScanBaseLeft L)
        (rejectPostStageRight L) := by
  rfl

theorem acceptScannerRight_eq (L : DovetailLayout) :
    List.append
        ((configurationFieldBits L.acceptConfig []).map some)
        (List.append ((false :: rejectConfigTail L).map some)
          (rejectRightPadding L)) =
      List.append
        ((configurationFieldBits L.acceptConfig
          (false :: rejectConfigTail L)).map some)
        (rejectRightPadding L) := by
  let acceptCells : List (Option Bool) :=
    (configurationFieldBits L.acceptConfig []).map some
  let rejectCells : List (Option Bool) :=
    (false :: rejectConfigTail L).map some
  have hprefix : List.append acceptCells rejectCells =
      (configurationFieldBits L.acceptConfig
        (false :: rejectConfigTail L)).map some := by
    dsimp [acceptCells, rejectCells]
    exact Eq.trans
      (List.map_append
        (f := some)
        (l₁ := show List Bool from configurationFieldBits L.acceptConfig [])
        (l₂ := show List Bool from false :: rejectConfigTail L)).symm
      (congrArg (fun bits : Word Bool => bits.map some)
        (configurationFieldBits_append_nil L.acceptConfig
          (false :: rejectConfigTail L)))
  exact Eq.trans
    (List.append_assoc acceptCells rejectCells (rejectRightPadding L)).symm
    (congrArg (fun cells => List.append cells (rejectRightPadding L)) hprefix)
theorem afterLocateTape2_eq_acceptScannerSourceTape2
    (L : DovetailLayout) :
    afterLocateTape2 L = acceptScannerSourceTape2 L := by
  rw [afterLocateTape2_eq_unparsedAcceptTape2]
  unfold acceptScannerSourceTape2 rejectPostStageRight
  rw [rejectBits_eq_false_cons_tail]
  unfold AcceptBranch.acceptBits
  exact congrArg (tapeAtCells (none :: acceptScanBaseLeft L))
    (acceptScannerRight_eq L)

def afterAcceptScanTape2 (L : DovetailLayout) : Tape Bool :=
  leftBoundaryEraserSourceTape
    (acceptScanBaseLeft L)
    (configurationFieldBits L.acceptConfig [])
    (some false)
    (List.append ((rejectConfigTail L).map some)
      (rejectRightPadding L))

namespace AcceptScannerLift

def source : MachineDescription :=
  ConfigurationSuffixScannerDescription
def sourceReady : source.SubroutineReady :=
  configurationSuffixScannerDescription_subroutineReady

def table :=
  BoundedFuelPairSearch.Tape2SubroutineLift.table source sourceReady

def description : MachineDescription :=
  lowerStructured3Description table.description
theorem ready : description.SubroutineReady := by
  simpa [description, table] using
    lowerStructured3Description_subroutineReady
      table.description_wellFormed
      table.description_supportsReadWriteRows3

theorem realizes
    (L : DovetailLayout) (T0 T1 : Tape Bool) :
    description.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        T0 T1 (acceptScannerSourceTape2 L))
      (encodedGuardedStructured3Tapes
        T0 T1 (afterAcceptScanTape2 L)) := by
  apply BoundedFuelPairSearch.Tape2SubroutineLift.lowered_haltsFromTapeEquiv
    source sourceReady T0 T1
  simpa [source, acceptScannerSourceTape2, afterAcceptScanTape2] using
    configurationSuffixScannerDescription_haltsFrom_boundary_withRight
      L.acceptConfig (acceptScanBaseLeft L) (rejectConfigTail L)
      (rejectRightPadding L)

end AcceptScannerLift

theorem acceptScannerDescription_realizes (L : DovetailLayout) :
    AcceptScannerLift.description.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 L) Tape.blank (afterLocateTape2 L))
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 L) Tape.blank (afterAcceptScanTape2 L)) := by
  rw [afterLocateTape2_eq_acceptScannerSourceTape2]
  exact AcceptScannerLift.realizes L (rightEdgeTape0 L) Tape.blank

namespace AfterAcceptCount
def start : Nat := 0
def count : Nat := 1
def off2 : Nat := 2
def off3 : Nat := 3
def off4 : Nat := 4
def halt : Nat := 5

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action0 action2 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 action0 keepS action2 target

def rowsForAllReads
    (source : Nat) (action0 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads3 fun read0 read1 read2 =>
    row source read0 read1 read2 action0 keepS action2 target
def rows : List Transition :=
  [ rowsForTape2Read start (some false)
      (writeR (some true)) keepL count
  , rowsForTape2Read start (some true)
      (writeR (some true)) keepL count
  , rowsForTape2Read count (some false) (writeR none) keepL count
  , rowsForTape2Read count (some true) (writeR none) keepL count
  , rowsForTape2Read count none
      (writeR none) (writeR (some true)) off2
  , rowsForAllReads off2 (writeR none) keepS off3
  , rowsForAllReads off3 (writeR none) keepS off4
  , rowsForAllReads off4 (writeR none) keepS halt ].flatten

def description : Description :=
  ThreeTape.description 6 start halt rows

theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)
theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

syntax "after_accept_count_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| after_accept_count_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape2Read,
          rowsForAllReads, start, count, off2, off3, off4, halt,
          allReads3, allReads2, allReadCells, List.find?, tapeAtCells,
          $lemmas,*])

end AfterAcceptCount

end RejectTape0Padding
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC


namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace AfterAcceptCountRuns

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open RejectTape0Padding

open RejectTape0Padding.AfterAcceptCount

def initialTape0 (base0 : List (Option Bool)) : Tape Bool :=
  tapeAtCells base0 [none]

def countedTape0
    (base0 : List (Option Bool)) (blanks : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate blanks (none : Option Bool))
      (some true :: base0))
    [none]
def countingTape2
    (base2 suffix : List (Option Bool))
    (remainingRev processed : List Bool) : Tape Bool :=
  match remainingRev with
  | [] =>
      tapeAtCells base2
        (none :: List.append (processed.map some) suffix)
  | current :: rest =>
      tapeAtCells
        (List.append (rest.map some) (none :: base2))
        (some current :: List.append (processed.map some) suffix)

def restoredTape2
    (base2 : List (Option Bool)) (bits : List Bool)
    (suffix : List (Option Bool)) : Tape Bool :=
  tapeAtCells (some true :: base2)
    (List.append (bits.map some) suffix)

def sourceTape2
    (base2 : List (Option Bool)) (bits : List Bool)
    (suffix : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append (bits.reverse.map some) (none :: base2)) suffix)

syntax "after_accept_count_run_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| after_accept_count_run_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [AfterAcceptCount.description, AfterAcceptCount.rows,
          AfterAcceptCount.rowsForTape2Read,
          AfterAcceptCount.rowsForAllReads,
          AfterAcceptCount.start, AfterAcceptCount.count,
          AfterAcceptCount.off2, AfterAcceptCount.off3,
          AfterAcceptCount.off4, AfterAcceptCount.halt,
          allReads3, allReads2, allReadCells, List.find?, initialTape0,
          countedTape0, countingTape2, restoredTape2, sourceTape2,
          tapeAtCells, $lemmas,*])
theorem start_step
    (base0 base2 suffix : List (Option Bool))
    (current : Bool) (remainingRev : List Bool) (T1 : Tape Bool) :
    AfterAcceptCount.description.runConfig 1
        (config AfterAcceptCount.start (initialTape0 base0) T1
          (countingTape2 base2 suffix (current :: remainingRev) [])) =
      config AfterAcceptCount.count (countedTape0 base0 0) T1
        (countingTape2 base2 suffix remainingRev [current]) := by
  cases h1 : T1.head with
  | none =>
      cases current <;> cases remainingRev <;>
        after_accept_count_run_step [h1, List.replicate_succ,
          List.append_assoc]
  | some bit1 =>
      cases bit1 <;> cases current <;> cases remainingRev <;>
        after_accept_count_run_step [h1, List.replicate_succ,
          List.append_assoc]

theorem count_step
    (base0 base2 suffix : List (Option Bool))
    (blanks : Nat) (next : Bool)
    (rest processed : List Bool) (T1 : Tape Bool) :
    AfterAcceptCount.description.runConfig 1
        (config AfterAcceptCount.count (countedTape0 base0 blanks) T1
          (countingTape2 base2 suffix (next :: rest) processed)) =
      config AfterAcceptCount.count (countedTape0 base0 (blanks + 1)) T1
        (countingTape2 base2 suffix rest (next :: processed)) := by
  cases h1 : T1.head with
  | none =>
      cases next <;> cases rest <;>
        after_accept_count_run_step [h1, List.replicate_succ,
          List.append_assoc]
  | some bit1 =>
      cases bit1 <;> cases next <;> cases rest <;>
        after_accept_count_run_step [h1, List.replicate_succ,
          List.append_assoc]

theorem boundary_step
    (base0 base2 suffix : List (Option Bool))
    (blanks : Nat) (processed : List Bool) (T1 : Tape Bool) :
    AfterAcceptCount.description.runConfig 1
        (config AfterAcceptCount.count (countedTape0 base0 blanks) T1
          (countingTape2 base2 suffix [] processed)) =
      config AfterAcceptCount.off2 (countedTape0 base0 (blanks + 1)) T1
        (restoredTape2 base2 processed suffix) := by
  cases h1 : T1.head with
  | none =>
      cases processed with
      | nil =>
          cases suffix with
          | nil =>
              after_accept_count_run_step [h1, List.replicate_succ,
                List.append_assoc]
          | cons cell suffix => cases cell with
            | none =>
                after_accept_count_run_step [h1, List.replicate_succ,
                  List.append_assoc]
            | some bit => cases bit <;>
                after_accept_count_run_step [h1, List.replicate_succ,
                  List.append_assoc]
      | cons current processed => cases current <;>
          after_accept_count_run_step [h1, List.replicate_succ,
            List.append_assoc]
  | some bit1 => cases bit1 <;>
      cases processed with
      | nil =>
          cases suffix with
          | nil =>
              after_accept_count_run_step [h1, List.replicate_succ,
                List.append_assoc]
          | cons cell suffix => cases cell with
            | none =>
                after_accept_count_run_step [h1, List.replicate_succ,
                  List.append_assoc]
            | some bit => cases bit <;>
                after_accept_count_run_step [h1, List.replicate_succ,
                  List.append_assoc]
      | cons current processed => cases current <;>
          after_accept_count_run_step [h1, List.replicate_succ,
            List.append_assoc]
theorem offset2_step
    (base0 : List (Option Bool)) (blanks : Nat)
    (T1 T2 : Tape Bool) :
    AfterAcceptCount.description.runConfig 1
        (config AfterAcceptCount.off2 (countedTape0 base0 blanks) T1 T2) =
      config AfterAcceptCount.off3
        (countedTape0 base0 (blanks + 1)) T1 T2 := by
  cases h1 : T1.head with
  | none =>
      cases h2 : T2.head with
      | none =>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
      | some bit2 => cases bit2 <;>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
  | some bit1 => cases bit1 <;>
      cases h2 : T2.head with
      | none =>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
      | some bit2 => cases bit2 <;>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]

theorem offset3_step
    (base0 : List (Option Bool)) (blanks : Nat)
    (T1 T2 : Tape Bool) :
    AfterAcceptCount.description.runConfig 1
        (config AfterAcceptCount.off3 (countedTape0 base0 blanks) T1 T2) =
      config AfterAcceptCount.off4
        (countedTape0 base0 (blanks + 1)) T1 T2 := by
  cases h1 : T1.head with
  | none =>
      cases h2 : T2.head with
      | none =>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
      | some bit2 => cases bit2 <;>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
  | some bit1 => cases bit1 <;>
      cases h2 : T2.head with
      | none =>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
      | some bit2 => cases bit2 <;>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]

theorem offset4_step
    (base0 : List (Option Bool)) (blanks : Nat)
    (T1 T2 : Tape Bool) :
    AfterAcceptCount.description.runConfig 1
        (config AfterAcceptCount.off4 (countedTape0 base0 blanks) T1 T2) =
      config AfterAcceptCount.halt
        (countedTape0 base0 (blanks + 1)) T1 T2 := by
  cases h1 : T1.head with
  | none =>
      cases h2 : T2.head with
      | none =>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
      | some bit2 => cases bit2 <;>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
  | some bit1 => cases bit1 <;>
      cases h2 : T2.head with
      | none =>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
      | some bit2 => cases bit2 <;>
          after_accept_count_run_step [h1, h2, List.replicate_succ,
            List.append_assoc]
theorem count_run
    (base0 base2 suffix : List (Option Bool))
    (remainingRev processed : List Bool) (blanks : Nat)
    (T1 : Tape Bool) :
    AfterAcceptCount.description.runConfig remainingRev.length
        (config AfterAcceptCount.count (countedTape0 base0 blanks) T1
          (countingTape2 base2 suffix remainingRev processed)) =
      config AfterAcceptCount.count
        (countedTape0 base0 (blanks + remainingRev.length)) T1
        (countingTape2 base2 suffix []
          (List.append remainingRev.reverse processed)) := by
  induction remainingRev generalizing blanks processed with
  | nil => rfl
  | cons next rest ih =>
      rw [show (next :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [count_step]
      rw [ih]
      have hblanks : blanks + 1 + rest.length =
          blanks + (1 + rest.length) := by
        lia
      rw [hblanks]
      simp [List.reverse_cons, List.append_assoc]
      done

theorem fixed_tail_run
    (base0 base2 suffix : List (Option Bool))
    (processed : List Bool) (blanks : Nat) (T1 : Tape Bool) :
    AfterAcceptCount.description.runConfig 4
        (config AfterAcceptCount.count (countedTape0 base0 blanks) T1
          (countingTape2 base2 suffix [] processed)) =
      config AfterAcceptCount.halt
        (countedTape0 base0 (blanks + 4)) T1
        (restoredTape2 base2 processed suffix) := by
  rw [show 4 = 1 + 3 by decide]
  rw [Description.runConfig_add]
  rw [boundary_step]
  rw [show 3 = 1 + 2 by decide]
  rw [Description.runConfig_add]
  rw [offset2_step]
  rw [show 2 = 1 + 1 by decide]
  rw [Description.runConfig_add]
  rw [offset3_step]
  rw [offset4_step]

def fuel (bits : List Bool) : Nat := bits.length + 4
theorem sourceTape2_eq_countingTape2
    (base2 suffixTail : List (Option Bool))
    (suffixHead : Option Bool) (bits remainingRev : List Bool)
    (current : Bool)
    (hrev : bits.reverse = current :: remainingRev) :
    sourceTape2 base2 bits (suffixHead :: suffixTail) =
      countingTape2 base2 (suffixHead :: suffixTail)
        (current :: remainingRev) [] := by
  simp [sourceTape2, countingTape2, hrev, tapeAtCells,
    Tape.move, Tape.moveLeft, List.map_append, List.append_assoc]

theorem run
    (base0 base2 suffixTail : List (Option Bool))
    (suffixHead : Option Bool) (bits : List Bool)
    (T1 : Tape Bool) (hne : bits ≠ []) :
    AfterAcceptCount.description.runConfig (fuel bits)
        (config AfterAcceptCount.start (initialTape0 base0) T1
          (sourceTape2 base2 bits (suffixHead :: suffixTail))) =
      config AfterAcceptCount.halt
        (countedTape0 base0 (bits.length + 3)) T1
        (restoredTape2 base2 bits (suffixHead :: suffixTail)) := by
  cases hrev : bits.reverse with
  | nil =>
      exfalso
      apply hne
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hrev
      simpa using hlen
  | cons current remainingRev =>
      have hbits : bits = List.append remainingRev.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa [List.reverse_cons] using h
      have hlen : bits.length = remainingRev.length + 1 := by
        have h := congrArg List.length hrev
        simpa using h
      rw [sourceTape2_eq_countingTape2 base2 suffixTail suffixHead bits
        remainingRev current hrev]
      rw [show fuel bits = 1 + (remainingRev.length + 4) by
        unfold fuel
        lia]
      rw [Description.runConfig_add]
      rw [start_step]
      rw [Description.runConfig_add]
      rw [count_run]
      rw [fixed_tail_run]
      simp [hbits, hlen, List.append_assoc]
      done

def loweredDescription : MachineDescription :=
  lowerStructured3Description AfterAcceptCount.description
theorem loweredDescription_ready : loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      AfterAcceptCount.ready.left AfterAcceptCount.supports

theorem loweredDescription_realizes
    (base0 base2 suffixTail : List (Option Bool))
    (suffixHead : Option Bool) (bits : List Bool)
    (T1 : Tape Bool) (hne : bits ≠ []) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (initialTape0 base0) T1
        (sourceTape2 base2 bits (suffixHead :: suffixTail)))
      (encodedGuardedStructured3Tapes
        (countedTape0 base0 (bits.length + 3)) T1
        (restoredTape2 base2 bits (suffixHead :: suffixTail))) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      AfterAcceptCount.ready.left AfterAcceptCount.ready.right
      AfterAcceptCount.supports
      (c := config AfterAcceptCount.start (initialTape0 base0) T1
        (sourceTape2 base2 bits (suffixHead :: suffixTail)))
      (tapes := [countedTape0 base0 (bits.length + 3), T1,
        restoredTape2 base2 bits (suffixHead :: suffixTail)])
      rfl rfl ⟨fuel bits,
        run base0 base2 suffixTail suffixHead bits T1 hne⟩

def countedAcceptBits (L : DovetailLayout) : List Bool :=
  configurationFieldBits L.acceptConfig []
def rightEdgeBase0 (L : DovetailLayout) : List (Option Bool) :=
  List.append ((sourceWord false L).reverse.map some) [none]

def countedSuffixTail (L : DovetailLayout) : List (Option Bool) :=
  List.append ((rejectConfigTail L).map some) (rejectRightPadding L)

def afterAcceptCountTape0 (L : DovetailLayout) : Tape Bool :=
  countedTape0 (rightEdgeBase0 L) ((countedAcceptBits L).length + 3)
def afterAcceptCountTape2 (L : DovetailLayout) : Tape Bool :=
  restoredTape2 (acceptScanBaseLeft L) (countedAcceptBits L)
    (some false :: countedSuffixTail L)

theorem initialTape0_rightEdgeBase0_eq (L : DovetailLayout) :
    initialTape0 (rightEdgeBase0 L) = rightEdgeTape0 L := by
  simp [initialTape0, rightEdgeBase0, rightEdgeTape0,
    AcceptFinalTail.Tape0RewindPadded.sourceTape,
    List.append_assoc]

theorem sourceTape2_accept_eq_afterAcceptScanTape2
    (L : DovetailLayout) :
    sourceTape2 (acceptScanBaseLeft L) (countedAcceptBits L)
        (some false :: countedSuffixTail L) =
      afterAcceptScanTape2 L := by
  rfl
theorem countedAcceptBits_ne_nil (L : DovetailLayout) :
    countedAcceptBits L ≠ [] := by
  exact List.ne_nil_of_length_pos
    (configurationFieldBits_length_pos L.acceptConfig)

theorem afterAcceptCountDescription_realizes (L : DovetailLayout) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 L) Tape.blank (afterAcceptScanTape2 L))
      (encodedGuardedStructured3Tapes
        (afterAcceptCountTape0 L) Tape.blank
        (afterAcceptCountTape2 L)) := by
  rw [← initialTape0_rightEdgeBase0_eq]
  rw [← sourceTape2_accept_eq_afterAcceptScanTape2]
  simpa [afterAcceptCountTape0, afterAcceptCountTape2] using
    loweredDescription_realizes
      (rightEdgeBase0 L) (acceptScanBaseLeft L) (countedSuffixTail L)
      (some false) (countedAcceptBits L) Tape.blank
      (countedAcceptBits_ne_nil L)

end AfterAcceptCountRuns
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
