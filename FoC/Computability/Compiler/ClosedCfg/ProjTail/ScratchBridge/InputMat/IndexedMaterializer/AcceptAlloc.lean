import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.AcceptCore
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.Tape2Rewinder

set_option doc.verso true

/-!
Blank-span allocation, live-word marking, and prefix reconstruction.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace BlankSpanAllocator

open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

def enter : Nat := 0
def seek : Nat := 1
def scan : Nat := 2
def rewind : Nat := 3
def halt : Nat := 4

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action0 action2 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 action0 keepS action2 target
def rows : List Transition :=
  [ rowsForTape2Read enter (some true) keepS keepL seek
  , rowsForTape2Read seek none keepS keepL seek
  , rowsForTape2Read seek (some true) keepS keepR scan
  , rowsForTape2Read scan none keepR keepR scan
  , rowsForTape2Read scan (some true) keepS (writeL (some false)) rewind
  , rowsForTape2Read rewind none keepL keepL rewind
  , rowsForTape2Read rewind (some true) keepS (writeR none) halt ].flatten

def description : Description :=
  ThreeTape.description 5 enter halt rows

theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)
theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def dataSourceTape (baseLeft : List (Option Bool)) : Tape Bool :=
  tapeAtCells baseLeft [none]

def dataTargetTape
    (baseLeft : List (Option Bool)) (count : Nat) : Tape Bool :=
  tapeAtCells baseLeft
    (none :: List.replicate count (none : Option Bool))
def endMarkedTape
    (baseLeft : List (Option Bool)) (count : Nat)
    (rightTail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate count (none : Option Bool))
      (some true :: baseLeft))
    (some true :: rightTail)

def restoredTape
    (baseLeft : List (Option Bool)) (count : Nat)
    (rightTail : List (Option Bool)) : Tape Bool :=
  tapeAtCells (none :: baseLeft)
    (none ::
      List.append (List.replicate count (none : Option Bool))
        (some false :: rightTail))

syntax "span_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| span_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape2Read,
          enter, seek, scan, rewind, halt, allReads2, allReadCells,
          List.find?, dataSourceTape, dataTargetTape, endMarkedTape,
          restoredTape, tapeAtCells, $lemmas,*])

theorem enter_step
    (dataBase markerBase : List (Option Bool)) (n : Nat)
    (rightTail : List (Option Bool)) :
    description.runConfig 1
        (config enter (dataSourceTape dataBase) Tape.blank
          (endMarkedTape markerBase (n + 1) rightTail)) =
      config seek (dataSourceTape dataBase) Tape.blank
        (tapeAtCells
          (List.append (List.replicate n (none : Option Bool))
            (some true :: markerBase))
          (none :: some true :: rightTail)) := by
  cases n <;>
    span_step [List.replicate_succ, List.append_assoc]
theorem seek_step
    (T0 : Tape Bool) (markerBase : List (Option Bool))
    (remaining processed : Nat) (rightTail : List (Option Bool)) :
    description.runConfig 1
        (config seek T0 Tape.blank
          (tapeAtCells
            (List.append (List.replicate remaining (none : Option Bool))
              (some true :: markerBase))
            (none ::
              List.append (List.replicate processed none)
                (some true :: rightTail)))) =
      match remaining with
      | 0 =>
          config seek T0 Tape.blank
            (tapeAtCells markerBase
              (some true ::
                List.append (List.replicate (processed + 1) none)
                  (some true :: rightTail)))
      | remaining + 1 =>
          config seek T0 Tape.blank
            (tapeAtCells
              (List.append (List.replicate remaining none)
                (some true :: markerBase))
              (none ::
                List.append (List.replicate (processed + 1) none)
                  (some true :: rightTail))) := by
  cases h0 : T0.head with
  | none => cases remaining <;>
      span_step [h0, List.replicate_succ, List.append_assoc]
  | some bit => cases bit <;> cases remaining <;>
      span_step [h0, List.replicate_succ, List.append_assoc]

theorem seek_run
    (T0 : Tape Bool) (markerBase : List (Option Bool))
    (remaining processed : Nat) (rightTail : List (Option Bool)) :
    description.runConfig (remaining + 1)
        (config seek T0 Tape.blank
          (tapeAtCells
            (List.append (List.replicate remaining (none : Option Bool))
              (some true :: markerBase))
            (none ::
              List.append (List.replicate processed none)
                (some true :: rightTail)))) =
      config seek T0 Tape.blank
        (tapeAtCells markerBase
          (some true ::
            List.append
              (List.replicate (remaining + processed + 1) none)
              (some true :: rightTail))) := by
  induction remaining generalizing processed with
  | zero =>
      simpa only [Nat.zero_add] using
        seek_step T0 markerBase 0 processed rightTail
  | succ remaining ih =>
      rw [show (remaining + 1) + 1 = 1 + (remaining + 1) by lia]
      rw [Description.runConfig_add]
      rw [seek_step]
      rw [ih (processed + 1)]
      congr 3
      congr 2
      lia

theorem seek_finish
    (T0 : Tape Bool) (markerBase : List (Option Bool))
    (count : Nat) (rightTail : List (Option Bool)) :
    description.runConfig 1
        (config seek T0 Tape.blank
          (tapeAtCells markerBase
            (some true ::
              List.append (List.replicate count none)
                (some true :: rightTail)))) =
      config scan T0 Tape.blank
        (tapeAtCells (some true :: markerBase)
          (List.append (List.replicate count none)
            (some true :: rightTail))) := by
  cases h0 : T0.head with
  | none => cases count <;>
      span_step [h0, List.replicate_succ, List.append_assoc]
  | some bit => cases bit <;> cases count <;>
      span_step [h0, List.replicate_succ, List.append_assoc]
def scannedDataTape
    (baseLeft : List (Option Bool)) (processed : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate processed (none : Option Bool)) baseLeft)
    [none]

def scanningTape
    (markerBase : List (Option Bool))
    (processed remaining : Nat)
    (rightTail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate processed (none : Option Bool))
      (some true :: markerBase))
    (List.append (List.replicate remaining none)
      (some true :: rightTail))

theorem scan_step
    (dataBase markerBase : List (Option Bool))
    (processed remaining : Nat) (rightTail : List (Option Bool)) :
    description.runConfig 1
        (config scan (scannedDataTape dataBase processed) Tape.blank
          (scanningTape markerBase processed (remaining + 1) rightTail)) =
      config scan (scannedDataTape dataBase (processed + 1)) Tape.blank
        (scanningTape markerBase (processed + 1) remaining rightTail) := by
  cases processed <;> cases remaining <;>
    span_step [scannedDataTape, scanningTape, List.replicate_succ,
      List.append_assoc]
theorem scan_run
    (dataBase markerBase : List (Option Bool))
    (processed remaining : Nat) (rightTail : List (Option Bool)) :
    description.runConfig remaining
        (config scan (scannedDataTape dataBase processed) Tape.blank
          (scanningTape markerBase processed remaining rightTail)) =
      config scan
        (scannedDataTape dataBase (processed + remaining)) Tape.blank
        (scanningTape markerBase (processed + remaining) 0 rightTail) := by
  induction remaining generalizing processed with
  | zero => simp [Description.runConfig]
  | succ remaining ih =>
      rw [show remaining + 1 = 1 + remaining by lia]
      rw [Description.runConfig_add]
      rw [show 1 + remaining = remaining + 1 by lia]
      rw [scan_step]
      rw [ih]
      congr 2 <;> lia

theorem end_step
    (dataBase markerBase : List (Option Bool))
    (count : Nat) (rightTail : List (Option Bool)) :
    description.runConfig 1
        (config scan (scannedDataTape dataBase (count + 1)) Tape.blank
          (scanningTape markerBase (count + 1) 0 rightTail)) =
      config rewind (scannedDataTape dataBase (count + 1)) Tape.blank
        (tapeAtCells
          (List.append (List.replicate count none)
            (some true :: markerBase))
          (none :: some false :: rightTail)) := by
  cases count <;>
    span_step [scannedDataTape, scanningTape, List.replicate_succ,
      List.append_assoc]

def rewindingDataTape
    (baseLeft : List (Option Bool))
    (remaining processed : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (remaining + 1) (none : Option Bool)) baseLeft)
    (none :: List.replicate processed (none : Option Bool))
def rewindingMarkerTape
    (markerBase : List (Option Bool))
    (remaining processed : Nat)
    (rightTail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate remaining (none : Option Bool))
      (some true :: markerBase))
    (none ::
      List.append (List.replicate processed none)
        (some false :: rightTail))

theorem rewind_step
    (dataBase markerBase : List (Option Bool))
    (remaining processed : Nat) (rightTail : List (Option Bool)) :
    description.runConfig 1
        (config rewind
          (rewindingDataTape dataBase remaining processed) Tape.blank
          (rewindingMarkerTape markerBase remaining processed rightTail)) =
      match remaining with
      | 0 =>
          config rewind (dataTargetTape dataBase (processed + 1)) Tape.blank
            (tapeAtCells markerBase
              (some true ::
                List.append (List.replicate (processed + 1) none)
                  (some false :: rightTail)))
      | remaining + 1 =>
          config rewind
            (rewindingDataTape dataBase remaining (processed + 1)) Tape.blank
            (rewindingMarkerTape markerBase remaining (processed + 1)
              rightTail) := by
  cases remaining <;> cases processed <;>
    span_step [rewindingDataTape, rewindingMarkerTape, dataTargetTape,
      List.replicate_succ, List.append_assoc]

theorem rewind_run
    (dataBase markerBase : List (Option Bool))
    (remaining processed : Nat) (rightTail : List (Option Bool)) :
    description.runConfig (remaining + 1)
        (config rewind
          (rewindingDataTape dataBase remaining processed) Tape.blank
          (rewindingMarkerTape markerBase remaining processed rightTail)) =
      config rewind
        (dataTargetTape dataBase (remaining + processed + 1)) Tape.blank
        (tapeAtCells markerBase
          (some true ::
            List.append
              (List.replicate (remaining + processed + 1) none)
              (some false :: rightTail))) := by
  induction remaining generalizing processed with
  | zero =>
      simpa only [Nat.zero_add] using
        rewind_step dataBase markerBase 0 processed rightTail
  | succ remaining ih =>
      rw [show (remaining + 1) + 1 = 1 + (remaining + 1) by lia]
      rw [Description.runConfig_add]
      rw [rewind_step]
      rw [ih (processed + 1)]
      have hcount :
          remaining + (processed + 1) + 1 =
            remaining + 1 + processed + 1 := by
        lia
      rw [hcount]
theorem rewind_finish
    (dataBase markerBase : List (Option Bool))
    (count : Nat) (rightTail : List (Option Bool)) :
    description.runConfig 1
        (config rewind (dataTargetTape dataBase (count + 1)) Tape.blank
          (tapeAtCells markerBase
            (some true ::
              List.append (List.replicate (count + 1) none)
                (some false :: rightTail)))) =
      config halt (dataTargetTape dataBase (count + 1)) Tape.blank
        (restoredTape markerBase count rightTail) := by
  cases count <;>
    span_step [dataTargetTape, restoredTape, List.replicate_succ,
      List.append_assoc]

def fuel (count : Nat) : Nat :=
  3 * count + 7

theorem full_run
    (dataBase markerBase : List (Option Bool))
    (count : Nat) (rightTail : List (Option Bool)) :
    description.runConfig (fuel count)
        (config enter (dataSourceTape dataBase) Tape.blank
          (endMarkedTape markerBase (count + 1) rightTail)) =
      config halt (dataTargetTape dataBase (count + 1)) Tape.blank
        (restoredTape markerBase count rightTail) := by
  rw [fuel]
  rw [show 3 * count + 7 =
      1 + ((count + 1) +
        (1 + ((count + 1) + (1 + ((count + 1) + 1))))) by lia]
  rw [Description.runConfig_add]
  rw [enter_step]
  rw [Description.runConfig_add]
  have hs := seek_run (dataSourceTape dataBase) markerBase count 0 rightTail
  simp only [List.replicate_zero, List.append, Nat.add_zero] at hs
  rw [hs]
  rw [Description.runConfig_add]
  rw [seek_finish]
  rw [Description.runConfig_add]
  have hscan := scan_run dataBase markerBase 0 (count + 1) rightTail
  have hscanSource :
      scannedDataTape dataBase 0 = dataSourceTape dataBase := by
    rfl
  have hscanMarker :
      scanningTape markerBase 0 (count + 1) rightTail =
        tapeAtCells (some true :: markerBase)
          (List.append (List.replicate (count + 1) none)
            (some true :: rightTail)) := by
    rfl
  rw [hscanSource, hscanMarker] at hscan
  simp only [Nat.zero_add] at hscan
  rw [hscan]
  rw [Description.runConfig_add]
  rw [end_step]
  rw [Description.runConfig_add]
  have hr := rewind_run dataBase markerBase count 0 rightTail
  have hrewindData :
      scannedDataTape dataBase (count + 1) =
        rewindingDataTape dataBase count 0 := by
    rfl
  have hrewindMarker :
      tapeAtCells
          (List.append (List.replicate count none)
            (some true :: markerBase))
          (none :: some false :: rightTail) =
        rewindingMarkerTape markerBase count 0 rightTail := by
    rfl
  rw [← hrewindData, ← hrewindMarker] at hr
  simp only [Nat.add_zero] at hr
  rw [hr]
  rw [rewind_finish]
def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_ready : loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady ready.left supports

theorem loweredDescription_realizes
    (dataBase markerBase : List (Option Bool))
    (count : Nat) (rightTail : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (dataSourceTape dataBase) Tape.blank
        (endMarkedTape markerBase (count + 1) rightTail))
      (encodedGuardedStructured3Tapes
        (dataTargetTape dataBase (count + 1)) Tape.blank
        (restoredTape markerBase count rightTail)) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      ready.left ready.right supports
      (c := config enter (dataSourceTape dataBase) Tape.blank
        (endMarkedTape markerBase (count + 1) rightTail))
      (tapes :=
        [ dataTargetTape dataBase (count + 1)
        , Tape.blank
        , restoredTape markerBase count rightTail ])
      rfl rfl ⟨fuel count, full_run dataBase markerBase count rightTail⟩

end BlankSpanAllocator
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
namespace AcceptMarkedLive

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptFinish AcceptInternalMarker
def markedGapPrefix (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate ((remainingBits L).length + 3)
      (none : Option Bool))
    (some true :: none :: counterBaseTail L)

theorem markedGapTape2_eq_tapeAtCells (L : DovetailLayout) :
    markedGapTape2 L =
      tapeAtCells (markedGapPrefix L)
        (List.append ((gapOldTailBits L).map some) [none]) := by
  rw [markedGapTape2_shape]
  rw [remainingBits_add_four_eq_direct_length]
  rfl

theorem prefixGateDescription_realizes_with_tape
    (L : DovetailLayout) (T2 : Tape Bool) :
    prefixGateDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 true L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (afterFirstStageTape0 L) Tape.blank
        (Components.markCurrent (L.stage = 0) T2)) := by
  let cellsRest : List Bool :=
    List.append (Components.wrappedCellTokens L.input)
      (List.append (Components.wrappedNatTokens L.stage) (configRest L))
  have ha : MarkerAwareCommon.Lowered.armDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 true L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (remarkedParsedTape0 true L) Tape.blank T2) := by
    unfold rewoundParsedTape0 remarkedParsedTape0
    rw [MarkerAwareCommon.wrappedParsedBoundary_eq_false_cons_tail]
    rw [MarkerAwareCommon.wrappedParsedBoundary_eq_false_cons_tail]
    exact MarkerAwareCommon.Lowered.armDescription_realizes
      (primaryMarkerBaseLeft L)
      (List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
        (rawBoundaryRest true L)).tail T2
  have hp := MarkerAwareCommon.Lowered.prefixDescription_realizes
    L.input.length (none :: primaryMarkerBaseLeft L) cellsRest T2
  have hg : cellStageGateDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape (postPrefixLeft L)
          (List.append (Components.wrappedCellTokens L.input)
            (List.append (Components.wrappedNatTokens L.stage)
              (configRest L))))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (afterFirstStageTape0 L) Tape.blank
        (Components.markCurrent (L.stage = 0) T2)) := by
    cases hstage : L.stage with
    | zero =>
        simpa [afterFirstStageTape0, postPrefixLeft, hstage,
          Components.wrappedNatTokens] using
          cellStageGateDescription_realizes_zero L.input
            (postPrefixLeft L) (configRest L) T2
    | succ stage =>
        simpa [afterFirstStageTape0, hstage,
          Components.wrappedNatTokens, List.append_assoc] using
          cellStageGateDescription_realizes_succ L.input stage
            (postPrefixLeft L) (configRest L) T2
  have hcore := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    MarkerAwareCommon.Lowered.prefixDescription_ready
    cellStageGateDescription_ready hp hg
  have hcore' : prefixGateCoreDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (remarkedParsedTape0 true L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (afterFirstStageTape0 L) Tape.blank
        (Components.markCurrent (L.stage = 0) T2)) := by
    simpa [prefixGateCoreDescription, remarkedParsedTape0, cellsRest,
      configRest, postPrefixLeft, wrappedBits_parsedLayoutBits,
      List.append_assoc] using hcore
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    MarkerAwareCommon.Lowered.armDescription_ready
    prefixGateCoreDescription_ready ha hcore'
  simpa [prefixGateDescription] using h
def markedAfterStagePrefixTape2 (L : DovetailLayout) : Tape Bool :=
  writeWordRight (StagePrefixForward.bits (L.stage = 0))
    (markedGapTape2 L)

theorem stagePrefixDescription_realizes_marked (L : DovetailLayout) :
    stagePrefixDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 true L) Tape.blank (markedGapTape2 L))
      (encodedGuardedStructured3Tapes
        (afterFirstStageTape0 L) Tape.blank
        (markedAfterStagePrefixTape2 L)) := by
  have hg := prefixGateDescription_realizes_with_tape L (markedGapTape2 L)
  have hf := stagePrefixFillDescription_realizes
    (L.stage = 0) (afterFirstStageTape0 L) (markedGapTape2 L)
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    prefixGateDescription_ready stagePrefixFillDescription_ready hg hf
  simpa [stagePrefixDescription, markedAfterStagePrefixTape2] using h

def markedAfterLiveCopyTape2 (L : DovetailLayout) : Tape Bool :=
  writeWordRight (remainingLiveBits L) (markedAfterStagePrefixTape2 L)
theorem liveCopyAtMarkedStagePrefix_realizes (L : DovetailLayout) :
    liveCopyDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterFirstStageTape0 L) Tape.blank
        (markedAfterStagePrefixTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (markedAfterLiveCopyTape2 L)) := by
  rw [afterFirstStageTape0_eq_copySource]
  exact liveCopyDescription_realizes (remainingLiveBits L)
    (afterFirstStageLeft L) ((rawBoundaryRest true L).drop 2)
    (markedAfterStagePrefixTape2 L)

theorem markedAfterLiveCopyTape2_eq_write_live (L : DovetailLayout) :
    markedAfterLiveCopyTape2 L =
      writeWordRight (liveBits L) (markedGapTape2 L) := by
  rw [markedAfterLiveCopyTape2, markedAfterStagePrefixTape2]
  rw [writeWordRight_append]
  rw [stagePrefix_append_remaining_eq_liveBits]

def markedCopiedLiveTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (List.append ((liveBits L).reverse.map some) (markedGapPrefix L))
    [none]
theorem markedAfterLiveCopyTape2_eq_copied (L : DovetailLayout) :
    markedAfterLiveCopyTape2 L = markedCopiedLiveTape2 L := by
  rw [markedAfterLiveCopyTape2_eq_write_live,
    markedGapTape2_eq_tapeAtCells]
  exact writeWordRight_tapeAtCells_of_length_lt
    (liveBits L) (gapOldTailBits L) (markedGapPrefix L)
    (gapOldTailBits_length_lt_liveBits L)

def markedExactOutputEndTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate 5 (none : Option Bool))
      (List.append ((keptLiveBits L).reverse.map some)
        (markedGapPrefix L)))
    [none]

theorem cleanup_marked_copied_eq_exact (L : DovetailLayout) :
    keepR.apply
        (Components.eraseRight 4
          (moveLeftFour (markedCopiedLiveTape2 L))) =
      markedExactOutputEndTape2 L := by
  have hhit : rejectHitBits L =
      [false, true, L.rejectHit, !L.rejectHit] := by
    cases hrejectHit : L.rejectHit <;>
      simp [rejectHitBits, boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
        hrejectHit]
  rw [markedCopiedLiveTape2, liveBits_eq_kept_append_rejectHit]
  rw [hhit]
  simp [moveLeftFour, keepR, TapeAction.apply, HeadMove.apply,
    Components.eraseRight, Tape.move, Tape.moveLeft, Tape.moveRight,
    Tape.write, tapeAtCells, markedExactOutputEndTape2,
    List.reverse_append, List.map_append, List.append_assoc]
theorem cleanupAtMarkedLiveCopy_realizes (L : DovetailLayout) :
    cleanupDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (markedAfterLiveCopyTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (markedExactOutputEndTape2 L)) := by
  rw [markedAfterLiveCopyTape2_eq_copied]
  rw [← cleanup_marked_copied_eq_exact]
  exact cleanupDescription_realizes
    (afterLiveCopyTape0 L) (markedCopiedLiveTape2 L)

theorem rewindFull_realizes_with_tape
    (L : DovetailLayout) (T2 : Tape Bool) :
    MarkerAwareCommon.Lowered.rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (atBoundaryTape0 L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 true L) Tape.blank T2) := by
  rw [atBoundaryTape0_eq_rewindSource]
  exact MarkerAwareCommon.Lowered.rewindDescription_realizes
    (ParsedLayoutBits L) (primaryMarkerBaseLeft L)
    (rawBoundaryRest true L) T2

def markedLiveDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      MarkerAwareCommon.Lowered.rewindDescription
      stagePrefixDescription)
    (canonicalPrimitiveSeqDescription liveCopyDescription cleanupDescription)
theorem markedLiveDescription_ready : markedLiveDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      MarkerAwareCommon.Lowered.rewindDescription_ready
      stagePrefixDescription_ready)
    (canonicalPrimitiveSeqDescription_subroutineReady
      liveCopyDescription_ready cleanupDescription_ready)

theorem markedLiveDescription_realizes (L : DovetailLayout) :
    markedLiveDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (atBoundaryTape0 L) Tape.blank (markedGapTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (markedExactOutputEndTape2 L)) := by
  have hr := rewindFull_realizes_with_tape L (markedGapTape2 L)
  have hs := stagePrefixDescription_realizes_marked L
  have hrs := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    MarkerAwareCommon.Lowered.rewindDescription_ready
    stagePrefixDescription_ready hr hs
  have hl := liveCopyAtMarkedStagePrefix_realizes L
  have hc := cleanupAtMarkedLiveCopy_realizes L
  have hlc := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    liveCopyDescription_ready cleanupDescription_ready hl hc
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    (canonicalPrimitiveSeqDescription_subroutineReady
      MarkerAwareCommon.Lowered.rewindDescription_ready
      stagePrefixDescription_ready)
    (canonicalPrimitiveSeqDescription_subroutineReady
      liveCopyDescription_ready cleanupDescription_ready)
    hrs hlc
  simpa [markedLiveDescription] using h

end AcceptMarkedLive
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
namespace AcceptReconstructPrefix

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptFinish AcceptInternalMarker AcceptMarkedLive

namespace MoveTape2LeftOne

def start : Nat := 0
def halt : Nat := 1
def rows : List Transition :=
  allReads3 fun read0 read1 read2 =>
    row start read0 read1 read2 keepS keepS keepL halt

def description : Description :=
  ThreeTape.description 2 start halt rows

theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)
theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem run (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config start T0 T1 T2) =
      config halt T0 T1 (keepL.apply T2) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          cases h2 : T2.head with
          | none => three_tape_step [description, rows, start, halt,
              allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
          | some bit => cases bit <;>
              three_tape_step [description, rows, start, halt,
                allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
      | some bit1 => cases bit1 <;>
          cases h2 : T2.head with
          | none => three_tape_step [description, rows, start, halt,
              allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
          | some bit2 => cases bit2 <;>
              three_tape_step [description, rows, start, halt,
                allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none =>
          cases h2 : T2.head with
          | none => three_tape_step [description, rows, start, halt,
              allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
          | some bit2 => cases bit2 <;>
              three_tape_step [description, rows, start, halt,
                allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
      | some bit1 => cases bit1 <;>
          cases h2 : T2.head with
          | none => three_tape_step [description, rows, start, halt,
              allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
          | some bit2 => cases bit2 <;>
              three_tape_step [description, rows, start, halt,
                allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]

end MoveTape2LeftOne

def moveTape2LeftOneDescription : MachineDescription :=
  lowerStructured3Description MoveTape2LeftOne.description
theorem moveTape2LeftOneDescription_ready :
    moveTape2LeftOneDescription.SubroutineReady := by
  simpa [moveTape2LeftOneDescription] using
    lowerStructured3Description_subroutineReady
      MoveTape2LeftOne.ready.left MoveTape2LeftOne.supports

theorem moveTape2LeftOneDescription_realizes
    (T0 T2 : Tape Bool) :
    moveTape2LeftOneDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank (keepL.apply T2)) := by
  simpa [moveTape2LeftOneDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      MoveTape2LeftOne.ready.left MoveTape2LeftOne.ready.right
      MoveTape2LeftOne.supports
      (c := config MoveTape2LeftOne.start T0 Tape.blank T2)
      (tapes := [T0, Tape.blank, keepL.apply T2])
      rfl rfl ⟨1, MoveTape2LeftOne.run T0 Tape.blank T2⟩

def moveTape2LeftFiveDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveLeftFourDescription
    moveTape2LeftOneDescription
theorem moveTape2LeftFiveDescription_ready :
    moveTape2LeftFiveDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    moveLeftFourDescription_ready moveTape2LeftOneDescription_ready

def internalMarkerBase (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate ((remainingBits L).length + 2)
      (none : Option Bool))
    (some true :: none :: counterBaseTail L)

def liveRewindPadding : List (Option Bool) :=
  List.replicate 5 (none : Option Bool)
def liveRewindSourceTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.sourceTapeWithContext
    (internalMarkerBase L) (keptLiveBits L) liveRewindPadding

def liveRewindTargetTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.targetTapeWithContext
    (internalMarkerBase L) (keptLiveBits L) liveRewindPadding

theorem markedExact_moveLeftFive_eq_liveRewindSource (L : DovetailLayout) :
    keepL.apply (moveLeftFour (markedExactOutputEndTape2 L)) =
      liveRewindSourceTape2 L := by
  have hrep :
      List.replicate ((remainingBits L).length + 3)
          (none : Option Bool) =
        none ::
          List.replicate ((remainingBits L).length + 2)
            (none : Option Bool) := by
    rw [show (remainingBits L).length + 3 =
      ((remainingBits L).length + 2) + 1 by lia]
    rw [List.replicate_succ]
  simp [markedExactOutputEndTape2, moveLeftFour, markedGapPrefix,
    internalMarkerBase, liveRewindSourceTape2, liveRewindPadding,
    Tape2Rewinder.sourceTapeWithContext,
    keepL, TapeAction.apply, HeadMove.apply, Tape.move, Tape.moveLeft,
    tapeAtCells, hrep, List.append_assoc]
theorem moveTape2LeftFiveDescription_realizes (L : DovetailLayout) :
    moveTape2LeftFiveDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (markedExactOutputEndTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (liveRewindSourceTape2 L)) := by
  have h4 := moveLeftFourDescription_realizes
    (afterLiveCopyTape0 L) (markedExactOutputEndTape2 L)
  have h1 := moveTape2LeftOneDescription_realizes
    (afterLiveCopyTape0 L) (moveLeftFour (markedExactOutputEndTape2 L))
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    moveLeftFourDescription_ready moveTape2LeftOneDescription_ready h4 h1
  rw [markedExact_moveLeftFive_eq_liveRewindSource] at h
  simpa [moveTape2LeftFiveDescription] using h

theorem livePaddedRewind_realizes (L : DovetailLayout) :
    Tape2Rewinder.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (liveRewindSourceTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (liveRewindTargetTape2 L)) := by
  exact Tape2Rewinder.loweredDescription_realizes_withContext
    (internalMarkerBase L) (keptLiveBits L) liveRewindPadding
    (afterLiveCopyTape0 L) Tape.blank

theorem move_left_tapeAtCells_none
    (left : List (Option Bool)) (cell : Option Bool)
    (cells : List (Option Bool)) :
    keepL.apply (tapeAtCells (none :: left) (cell :: cells)) =
      tapeAtCells left (none :: cell :: cells) := by
  rfl
def internalScanSourceTape2 (L : DovetailLayout) : Tape Bool :=
  keepL.apply (liveRewindTargetTape2 L)

theorem internalScanSourceTape2_shape (L : DovetailLayout) :
    internalScanSourceTape2 L =
      tapeAtCells (internalMarkerBase L)
        (none ::
          List.append ((keptLiveBits L).map some)
            (none :: liveRewindPadding)) := by
  rw [internalScanSourceTape2, liveRewindTargetTape2,
    Tape2Rewinder.targetTapeWithContext]
  cases hkept : (keptLiveBits L).map some with
  | nil =>
      simpa [hkept] using
        move_left_tapeAtCells_none (internalMarkerBase L) none
          liveRewindPadding
  | cons cell cells =>
      simpa [hkept] using
        move_left_tapeAtCells_none (internalMarkerBase L) cell
          (List.append cells (none :: liveRewindPadding))

namespace MarkerScanLowered

open MarkerScanLeft

theorem run_with_right
    (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    MarkerScanLeft.description.runConfig (n + 2)
        (config MarkerScanLeft.enter T0 T1
          (tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (some true :: left))
            (none :: right))) =
      config MarkerScanLeft.halt T0 T1
        (tapeAtCells left
          (none ::
            List.append (List.replicate (n + 1) (none : Option Bool))
              right)) := by
  rw [show n + 2 = 1 + (n + 1) by lia]
  rw [Description.runConfig_add]
  cases n with
  | zero =>
      simp only [List.replicate_zero, List.append_eq, List.nil_append]
      rw [MarkerScanLeft.enter_step]
      rw [MarkerScanLeft.marker_step]
      rfl
  | succ n =>
      simp only [List.replicate_succ, List.append_eq, List.cons_append]
      rw [MarkerScanLeft.enter_step]
      have h := MarkerScanLeft.scan_blanks_to_marker n T0 T1 left
        (none :: right)
      rw [show n + 1 + 1 = n + 2 by lia]
      have h' :
          MarkerScanLeft.description.runConfig (n + 2)
              (config MarkerScanLeft.scan T0 T1
                (tapeAtCells
                  (List.append (List.replicate n (none : Option Bool))
                    (some true :: left))
                  (none :: none :: right))) =
            config MarkerScanLeft.halt T0 T1
              (tapeAtCells left
                (none :: List.append
                  (List.replicate (n + 1) (none : Option Bool))
                  (none :: right))) := h
      apply Eq.trans h'
      have hshift := MarkerScanLeft.replicate_none_append_cons n right
      simp only [List.append_eq] at hshift
      simp only [List.replicate_succ, List.append_eq, List.cons_append]
      rw [hshift]
def loweredDescription : MachineDescription :=
  lowerStructured3Description MarkerScanLeft.description

theorem ready : MarkerScanLeft.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    MarkerScanLeft.description (by decide)

theorem supports : SupportsReadWriteRows3 MarkerScanLeft.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem loweredDescription_ready : loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady ready.left supports

theorem loweredDescription_realizes
    (n : Nat) (T0 : Tape Bool)
    (left right : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (tapeAtCells
          (List.append (List.replicate n (none : Option Bool))
            (some true :: left))
          (none :: right)))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (tapeAtCells left
          (none ::
            List.append (List.replicate (n + 1) (none : Option Bool))
              right))) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      ready.left ready.right supports
      (c := config MarkerScanLeft.enter T0 Tape.blank
        (tapeAtCells
          (List.append (List.replicate n (none : Option Bool))
            (some true :: left))
          (none :: right)))
      (tapes :=
        [ T0, Tape.blank
        , tapeAtCells left
            (none ::
              List.append (List.replicate (n + 1) (none : Option Bool))
                right) ])
      rfl rfl ⟨n + 2, run_with_right n T0 Tape.blank left right⟩

end MarkerScanLowered

def internalScanTargetTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells (none :: counterBaseTail L)
    (none ::
      List.append
        (List.replicate ((remainingBits L).length + 3)
          (none : Option Bool))
        (List.append ((keptLiveBits L).map some)
          (none :: liveRewindPadding)))
theorem internalMarkerScan_realizes (L : DovetailLayout) :
    MarkerScanLowered.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (internalScanSourceTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (internalScanTargetTape2 L)) := by
  rw [internalScanSourceTape2_shape]
  simpa [internalMarkerBase, internalScanTargetTape2,
    List.append_assoc] using
    MarkerScanLowered.loweredDescription_realizes
      ((remainingBits L).length + 2) (afterLiveCopyTape0 L)
      (none :: counterBaseTail L)
      (List.append ((keptLiveBits L).map some)
        (none :: liveRewindPadding))

def postInternalRightTape2 (L : DovetailLayout) : Tape Bool :=
  keepR.apply (internalScanTargetTape2 L)

theorem moveRightAfterInternal_realizes (L : DovetailLayout) :
    moveRightOneDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (internalScanTargetTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (postInternalRightTape2 L)) := by
  exact moveRightOneDescription_realizes
    (afterLiveCopyTape0 L) (internalScanTargetTape2 L)
theorem rewoundParsed_eq_postPosition (L : DovetailLayout) :
    rewoundParsedTape0 true L = postPositionTape0 true L := by
  unfold rewoundParsedTape0
  exact (postPositionTape0_eq_unmarked_shape true L).symm

theorem rewindT0ForDriver_realizes (L : DovetailLayout) :
    MarkerAwareCommon.Lowered.rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (postInternalRightTape2 L))
      (encodedGuardedStructured3Tapes
        (postPositionTape0 true L) Tape.blank (postInternalRightTape2 L)) := by
  rw [afterLiveCopyTape0_eq_atBoundaryTape0]
  have h := AcceptMarkedLive.rewindFull_realizes_with_tape
    L (postInternalRightTape2 L)
  rw [rewoundParsed_eq_postPosition] at h
  exact h

theorem loweredPrefixDriverDescription_realizes_with_tape
    (useAccept : Bool) (L : DovetailLayout) (T2 : Tape Bool) :
    loweredPrefixDriverDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (postPositionTape0 useAccept L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 useAccept L) Tape.blank
        (Components.eraseRight (driverPrefixBits L).length T2)) := by
  let rawRest : List Bool :=
    false ::
      countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L
  let configRest : List Bool :=
    List.append (AcceptConfigCopy.wrappedBits (configHitBits L)) rawRest
  let cellsStageRest : List Bool :=
    List.append (Components.wrappedCellTokens L.input)
      (List.append (Components.wrappedNatTokens L.stage) configRest)
  let natRest : List Bool :=
    List.append (Components.wrappedNatTokens L.input.length) cellsStageRest
  let headerLeft : List (Option Bool) :=
    List.append ((wrappedKind .transition).reverse.map some)
      (positionTape0Left L)
  let inputLeft : List (Option Bool) :=
    List.append
      ((Components.wrappedNatTokens L.input.length).reverse.map some)
      headerLeft
  have hheader :=
    loweredHeaderDescription_realizes (positionTape0Left L) natRest T2
  have hnat :=
    loweredNatDescription_realizes L.input.length headerLeft cellsStageRest T2
  have hfirst := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    loweredHeaderDescription_subroutineReady
    loweredNatDescription_subroutineReady hheader hnat
  have hcells :=
    loweredCellsNatDescription_realizes L.input L.stage inputLeft configRest
      (Components.eraseRight (4 * L.input.length + 3) T2)
  have hall := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    loweredHeaderNatDescription_subroutineReady
    loweredCellsNatDescription_subroutineReady hfirst hcells
  have hcount :
      4 * L.input.length + 3 +
          (4 * L.input.length + 4 * L.stage + 4) =
        (driverPrefixBits L).length := by
    rw [driverPrefixBits_length]
    lia
  simpa [loweredPrefixDriverDescription, loweredHeaderNatDescription,
    postPositionTape0_eq_scanTape, afterDriverTape0,
    rawRest, configRest, cellsStageRest, natRest, headerLeft, inputLeft,
    wrappedBits_parsedLayoutBits, wrappedBits_prefixThroughStage,
    eraseRight_comp, hcount, List.reverse_append, List.map_append,
    List.append_assoc] using hall
def afterReconstructionDriverTape2 (L : DovetailLayout) : Tape Bool :=
  Components.eraseRight (driverPrefixBits L).length
    (postInternalRightTape2 L)

theorem reconstructionDriver_realizes (L : DovetailLayout) :
    loweredPrefixDriverDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (postPositionTape0 true L) Tape.blank (postInternalRightTape2 L))
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 true L) Tape.blank
        (afterReconstructionDriverTape2 L)) := by
  exact loweredPrefixDriverDescription_realizes_with_tape
    true L (postInternalRightTape2 L)

end AcceptReconstructPrefix
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
