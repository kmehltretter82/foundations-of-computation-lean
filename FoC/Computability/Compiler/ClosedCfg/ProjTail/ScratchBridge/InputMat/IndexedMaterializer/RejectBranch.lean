import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.AcceptCompose

set_option doc.verso true

/-!
Rejecting-route pair selection, continuation, and live-copy phases.
-/

set_option linter.unusedSimpArgs false

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers

namespace RejectBranchShapes

open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open EncRewriters.BoundedLayoutRunner.SelectedProjectionPaddedTailCleanup
open EncRewriters.BoundedLayoutRunner.SelectedProjectionPaddedTailCleanup.InputMat
open EncRewriters.BoundedLayoutRunner.SelectedProjectionPaddedTailCleanup.InputMat.Route
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver

def stageBits (L : DovetailLayout) : List Bool :=
  DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits L.stage

def inputStageBits (L : DovetailLayout) : List Bool :=
  List.append (boolWordFieldBits L.input []).tail (stageBits L)
def prefixThroughStageBits (L : DovetailLayout) : List Bool :=
  List.append transitionPrefixBits (false :: inputStageBits L)

def acceptBits (L : DovetailLayout) : List Bool :=
  configurationFieldBits L.acceptConfig []

def rejectBits (L : DovetailLayout) : List Bool :=
  configurationFieldBits L.rejectConfig []
def acceptHitBits (L : DovetailLayout) : List Bool :=
  boolFieldBits L.acceptHit []

def rejectHitBits (L : DovetailLayout) : List Bool :=
  boolFieldBits L.rejectHit []

def hitBits (L : DovetailLayout) : List Bool :=
  List.append (acceptHitBits L) (rejectHitBits L)
def dataBits (L : DovetailLayout) : List Bool :=
  List.append (inputStageBits L)
    (List.append (acceptBits L)
      (List.append (rejectBits L) (hitBits L)))

def pairSourceBits (L : DovetailLayout) : List Bool :=
  List.append (acceptBits L)
    (List.append (rejectBits L) (hitBits L))

def copiedRejectBits (L : DovetailLayout) : List Bool :=
  List.append (stageBits L) (rejectBits L)
def positionedTape2Left
    (L : DovetailLayout) (base2 : List (Option Bool)) :
    List (Option Bool) :=
  List.append ((stageBits L).reverse.map some) (none :: base2)

def commonCounterBaseTail (L : DovetailLayout) : List (Option Bool) :=
  (MarkerAwareCommon.counterBaseLeft L).tail

def markerOffset (L : DovetailLayout) : Nat :=
  (inputStageBits L).length + (rejectBits L).length
def remainingPairBits (L : DovetailLayout) : List Bool :=
  (pairSourceBits L).drop (rejectBits L).length

def movedBeforeGapMarkerBits (L : DovetailLayout) : List Bool :=
  List.append (prefixThroughStageBits L)
    ((pairSourceBits L).take (rejectBits L).length)


def pairPositionTape0 (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((AcceptConfigCopy.wrappedBits (inputStageBits L)).reverse.map some)
      (MarkerAwareCommon.commonEndpointLeft L))
    (List.append (AcceptConfigCopy.wrappedBits (pairSourceBits L))
      (MarkerAwareCommon.rawBoundaryRest false L))
def pairEndLeft0 (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((AcceptConfigCopy.wrappedBits
      ((pairSourceBits L).take (rejectBits L).length)).reverse.map some)
    (List.append
      ((AcceptConfigCopy.wrappedBits (inputStageBits L)).reverse.map some)
      (MarkerAwareCommon.commonEndpointLeft L))

theorem acceptHitBits_length (L : DovetailLayout) :
    (acceptHitBits L).length = 4 := by
  simpa [acceptHitBits] using boolFieldBits_nil_length L.acceptHit

theorem route_configHitBits_eq_pairSourceBits (L : DovetailLayout) :
    Route.configHitBits L = pairSourceBits L := by
  simp [Route.configHitBits, pairSourceBits, acceptBits, rejectBits,
    hitBits, acceptHitBits, rejectHitBits, List.append_assoc]
theorem common_dataBits_eq_dataBits (L : DovetailLayout) :
    MarkerAwareCommon.dataBits L = dataBits L := by
  simp [MarkerAwareCommon.dataBits, dataBits, inputStageBits,
    route_configHitBits_eq_pairSourceBits, stageBits, pairSourceBits,
    List.append_assoc]

theorem dataBits_eq_inputStage_pairSource (L : DovetailLayout) :
    dataBits L = List.append (inputStageBits L) (pairSourceBits L) := by
  rfl

theorem wrappedRawBit_map_some_cons_tail (bit : Bool) :
    (wrappedRawBit bit).map some =
      some false :: ((wrappedRawBit bit).map some).tail := by
  cases bit <;> rfl
theorem commonCounterBase_eq_none_cons (L : DovetailLayout) :
    MarkerAwareCommon.counterBaseLeft L =
      none :: commonCounterBaseTail L := by
  have hpos :
      0 < (EncRewriters.BoundedLayoutRunner.ParsedLayoutBits L).length := by
    rw [parsedLayoutBits_fieldDecomp]
    simp [transitionPrefixBits_length]
    lia
  unfold commonCounterBaseTail MarkerAwareCommon.counterBaseLeft
  generalize hlength :
    (EncRewriters.BoundedLayoutRunner.ParsedLayoutBits L).length = n
  cases n with
  | zero => simp [hlength] at hpos
  | succ n => simp [List.replicate_succ]

theorem rejectHitBits_length (L : DovetailLayout) :
    (rejectHitBits L).length = 4 := by
  simpa [rejectHitBits] using boolFieldBits_nil_length L.rejectHit

theorem hitBits_length (L : DovetailLayout) :
    (hitBits L).length = 8 := by
  simp [hitBits, acceptHitBits_length, rejectHitBits_length]
theorem dataBits_length (L : DovetailLayout) :
    (dataBits L).length =
      (inputStageBits L).length + (acceptBits L).length +
        (rejectBits L).length + 8 := by
  simp [dataBits, hitBits_length, Nat.add_assoc]

theorem rejectBits_length_lt_pairSourceBits_length (L : DovetailLayout) :
    (rejectBits L).length < (pairSourceBits L).length := by
  simp [pairSourceBits, hitBits_length]
  lia

theorem pairSourceBits_drop_reject_length (L : DovetailLayout) :
    ((pairSourceBits L).drop (rejectBits L).length).length =
      (acceptBits L).length + 8 := by
  simp [pairSourceBits, hitBits_length]
  lia
theorem remainingPairBits_length (L : DovetailLayout) :
    (remainingPairBits L).length = (acceptBits L).length + 8 := by
  exact pairSourceBits_drop_reject_length L

theorem remainingPairBits_ne_nil (L : DovetailLayout) :
    remainingPairBits L ≠ [] := by
  intro hnil
  have hlen := remainingPairBits_length L
  rw [hnil] at hlen
  simp at hlen

theorem remainingPairBits_exists_cons (L : DovetailLayout) :
    ∃ markedBit after, remainingPairBits L = markedBit :: after := by
  cases h : remainingPairBits L with
  | nil => exact False.elim (remainingPairBits_ne_nil L h)
  | cons markedBit after => exact ⟨markedBit, after, rfl⟩
theorem markerOffset_lt_dataBits_length (L : DovetailLayout) :
    markerOffset L < (dataBits L).length := by
  rw [dataBits_length]
  simp [markerOffset]
  lia


theorem reject_pair_counter_end_eq_rewind_source
    (L : DovetailLayout) (base2 : List (Option Bool)) :
    PairStream.counterTape
        (List.append ((rejectBits L).reverse.map some)
          (positionedTape2Left L base2)) [] =
      Tape2Rewinder.sourceTapeWithContext base2 (copiedRejectBits L) [] := by
  simp [PairStream.counterTape, Tape2Rewinder.sourceTapeWithContext,
    positionedTape2Left, copiedRejectBits, List.reverse_append,
    List.map_append, List.append_assoc]


theorem reject_pair_primary_left_shape
    (L : DovetailLayout) (base0 : List (Option Bool)) :
    List.append
        ((AcceptConfigCopy.wrappedBits
          ((pairSourceBits L).take (rejectBits L).length)).reverse.map some)
        (List.append
          ((AcceptConfigCopy.wrappedBits (prefixThroughStageBits L)).reverse.map
            some)
          (none :: base0)) =
      List.append
        ((AcceptConfigCopy.wrappedBits
          (movedBeforeGapMarkerBits L)).reverse.map some)
        (none :: base0) := by
  rw [movedBeforeGapMarkerBits, PrimaryRewind.wrappedBits_append]
  simp [List.reverse_append, List.map_append, List.append_assoc]

namespace GapMarker
def start : Nat := 0
def halt : Nat := 1

def rowsForRead
    (read0 : Option Bool)
    (action0 : CommonGround.FiniteTransducers.Structured.TapeAction) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads2 fun read1 read2 =>
    row start read0 read1 read2 action0 keepS keepS halt

def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  rowsForRead (some false) (writeS none)
def description : CommonGround.FiniteTransducers.Structured.Description :=
  CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.description
    2 start halt rows

theorem run
    (left right : List (Option Bool)) (T1 T2 : Tape Bool) :
    description.runConfig 1
        (config start (tapeAtCells left (some false :: right)) T1 T2) =
      config halt (tapeAtCells left (none :: right)) T1 T2 := by
  cases h1 : T1.head with
  | none =>
      cases h2 : T2.head with
      | none =>
          three_tape_step [description, rows, rowsForRead, start, halt,
            allReads2, allReadCells, List.find?, tapeAtCells, h1, h2]
      | some bit => cases bit <;>
          three_tape_step [description, rows, rowsForRead, start, halt,
            allReads2, allReadCells, List.find?, tapeAtCells, h1, h2]
  | some bit1 => cases bit1 <;>
      cases h2 : T2.head with
      | none =>
          three_tape_step [description, rows, rowsForRead, start, halt,
            allReads2, allReadCells, List.find?, tapeAtCells, h1, h2]
      | some bit2 => cases bit2 <;>
          three_tape_step [description, rows, rowsForRead, start, halt,
            allReads2, allReadCells, List.find?, tapeAtCells, h1, h2]

end GapMarker

namespace PrimaryRewindOptions

syntax "solve_primary_option_tail" ident ident : tactic

macro_rules
  | `(tactic| solve_primary_option_tail $T1:ident $T2:ident) =>
      `(tactic|
        cases h1 : ($T1:ident).head with
        | none =>
            cases h2 : ($T2:ident).head with
            | none => primary_rewind_simp [tapeAtCells, h1, h2]
            | some bit => cases bit <;>
                primary_rewind_simp [tapeAtCells, h1, h2]
        | some bit1 =>
            cases bit1 <;>
              cases h2 : ($T2:ident).head with
              | none => primary_rewind_simp [tapeAtCells, h1, h2]
              | some bit2 => cases bit2 <;>
                  primary_rewind_simp [tapeAtCells, h1, h2])

theorem false_step
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (T1 T2 : Tape Bool) :
    PrimaryRewind.description.runConfig 4
        (config PrimaryRewind.loop
          (tapeAtCells
            (List.append ((wrappedRawBit false).reverse.map some) left)
            (head :: right))
          T1 T2) =
      config PrimaryRewind.loop
        (tapeAtCells left
          (List.append ((wrappedRawBit false).map some) (head :: right)))
        T1 T2 := by
  cases head with
  | none => solve_primary_option_tail T1 T2
  | some bit => cases bit <;> solve_primary_option_tail T1 T2
theorem true_step
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (T1 T2 : Tape Bool) :
    PrimaryRewind.description.runConfig 4
        (config PrimaryRewind.loop
          (tapeAtCells
            (List.append ((wrappedRawBit true).reverse.map some) left)
            (head :: right))
          T1 T2) =
      config PrimaryRewind.loop
        (tapeAtCells left
          (List.append ((wrappedRawBit true).map some) (head :: right)))
        T1 T2 := by
  cases head with
  | none => solve_primary_option_tail T1 T2
  | some bit => cases bit <;> solve_primary_option_tail T1 T2

theorem marker_finish
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (T1 T2 : Tape Bool) :
    PrimaryRewind.description.runConfig 2
        (config PrimaryRewind.loop
          (tapeAtCells (none :: left) (head :: right)) T1 T2) =
      config PrimaryRewind.halt
        (tapeAtCells (some true :: left) (head :: right)) T1 T2 := by
  cases head with
  | none => solve_primary_option_tail T1 T2
  | some bit => cases bit <;> solve_primary_option_tail T1 T2

theorem run_rev
    (revBits : List Bool)
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (T1 T2 : Tape Bool) :
    PrimaryRewind.description.runConfig (PrimaryRewind.fuel revBits)
        (config PrimaryRewind.loop
          (tapeAtCells
            (List.append
              ((AcceptConfigCopy.wrappedBits revBits.reverse).reverse.map some)
              (none :: left))
            (head :: right))
          T1 T2) =
      config PrimaryRewind.halt
        (tapeAtCells (some true :: left)
          (List.append
            ((AcceptConfigCopy.wrappedBits revBits.reverse).map some)
            (head :: right)))
        T1 T2 := by
  induction revBits generalizing head right with
  | nil =>
      simpa [PrimaryRewind.fuel, AcceptConfigCopy.wrappedBits] using
        marker_finish left head right T1 T2
  | cons bit revBits ih =>
      rw [show PrimaryRewind.fuel (bit :: revBits) =
          4 + PrimaryRewind.fuel revBits by
        simp [PrimaryRewind.fuel]
        lia]
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      have hshape :
          List.append
              ((AcceptConfigCopy.wrappedBits
                (bit :: revBits).reverse).reverse.map some)
              (none :: left) =
            List.append ((wrappedRawBit bit).reverse.map some)
              (List.append
                ((AcceptConfigCopy.wrappedBits revBits.reverse).reverse.map
                  some)
                (none :: left)) := by
        rw [PrimaryRewind.wrappedBits_reverse_cons]
        cases bit <;>
          simp [AcceptConfigCopy.wrappedBits,
            AcceptConfigCopy.wrappedBit, wrappedRawBit,
            List.reverse_append, List.map_append, List.append_assoc]
      rw [hshape]
      cases bit with
      | false =>
          rw [false_step]
          change PrimaryRewind.description.runConfig
              (PrimaryRewind.fuel revBits)
              (config PrimaryRewind.loop
                (tapeAtCells
                  (List.append
                    ((AcceptConfigCopy.wrappedBits revBits.reverse).reverse.map
                      some)
                    (none :: left))
                  (some false :: some true :: some false :: some true ::
                    head :: right))
                T1 T2) = _
          rw [ih]
          rw [PrimaryRewind.wrappedBits_reverse_cons]
          simp [List.reverse_cons, AcceptConfigCopy.wrappedBits,
            AcceptConfigCopy.wrappedBit, wrappedRawBit, cellsCodeBits,
            cellCodeBits, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
            encodeCell,
            List.map_append, List.append_assoc]
      | true =>
          rw [true_step]
          change PrimaryRewind.description.runConfig
              (PrimaryRewind.fuel revBits)
              (config PrimaryRewind.loop
                (tapeAtCells
                  (List.append
                    ((AcceptConfigCopy.wrappedBits revBits.reverse).reverse.map
                      some)
                    (none :: left))
                  (some false :: some true :: some true :: some false ::
                    head :: right))
                T1 T2) = _
          rw [ih]
          rw [PrimaryRewind.wrappedBits_reverse_cons]
          simp [List.reverse_cons, AcceptConfigCopy.wrappedBits,
            AcceptConfigCopy.wrappedBit, wrappedRawBit, cellsCodeBits,
            cellCodeBits, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
            encodeCell,
            List.map_append, List.append_assoc]
theorem run_options
    (bits : List Bool)
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (T1 T2 : Tape Bool) :
    PrimaryRewind.description.runConfig (PrimaryRewind.fuel bits)
        (config PrimaryRewind.loop
          (tapeAtCells
            (List.append
              ((AcceptConfigCopy.wrappedBits bits).reverse.map some)
              (none :: left))
            (head :: right))
          T1 T2) =
      config PrimaryRewind.halt
        (tapeAtCells (some true :: left)
          (List.append ((AcceptConfigCopy.wrappedBits bits).map some)
            (head :: right)))
        T1 T2 := by
  simpa [PrimaryRewind.fuel] using
    run_rev bits.reverse left head right T1 T2

end PrimaryRewindOptions

namespace ForwardOptions

syntax "solve_forward_option_tail" ident ident : tactic

macro_rules
  | `(tactic| solve_forward_option_tail $head:ident $T2:ident) =>
      `(tactic|
        cases $head:ident with
        | none =>
            cases h2 : ($T2:ident).head with
            | none => wrapped_stream_simp [tapeAtCells, h2]
            | some bit => cases bit <;>
                wrapped_stream_simp [tapeAtCells, h2]
        | some next =>
            cases next <;>
              cases h2 : ($T2:ident).head with
              | none => wrapped_stream_simp [tapeAtCells, h2]
              | some bit => cases bit <;>
                  wrapped_stream_simp [tapeAtCells, h2])


end ForwardOptions


theorem reject_gap_marker_run
    (L : DovetailLayout) (markedBit : Bool) (after : List Bool)
    (hremaining : remainingPairBits L = markedBit :: after)
    (T2 : Tape Bool) :
    GapMarker.description.runConfig 1
        (config GapMarker.start
          (scanTape (pairEndLeft0 L)
            (List.append (AcceptConfigCopy.wrappedBits (remainingPairBits L))
              (MarkerAwareCommon.rawBoundaryRest false L)))
          Tape.blank T2) =
      config GapMarker.halt
        (MarkedErase.scanOptionTape (pairEndLeft0 L)
          (List.append (MarkedErase.markedOptions markedBit)
            (List.append (MarkedErase.wrappedOptionsWord after)
              ((MarkerAwareCommon.rawBoundaryRest false L).map some))))
        Tape.blank T2 := by
  let restCells : List (Option Bool) :=
    List.append ((wrappedRawBit markedBit).tail.map some)
      (List.append (MarkedErase.wrappedOptionsWord after)
        (List.append
          ((MarkerAwareCommon.rawBoundaryRest false L).map some)
          [none]))
  have hrun := GapMarker.run (pairEndLeft0 L) restCells Tape.blank T2
  have hstart :
      scanTape (pairEndLeft0 L)
          (List.append (AcceptConfigCopy.wrappedBits (remainingPairBits L))
            (MarkerAwareCommon.rawBoundaryRest false L)) =
        tapeAtCells (pairEndLeft0 L) (some false :: restCells) := by
    calc
      scanTape (pairEndLeft0 L)
          (List.append (AcceptConfigCopy.wrappedBits (remainingPairBits L))
            (MarkerAwareCommon.rawBoundaryRest false L)) =
        tapeAtCells (pairEndLeft0 L)
          (List.append
            ((List.append
              (AcceptConfigCopy.wrappedBits (remainingPairBits L))
              (MarkerAwareCommon.rawBoundaryRest false L)).map some)
            [none]) := rfl
      _ = tapeAtCells (pairEndLeft0 L)
          (List.append
            ((wrappedRawBit markedBit).map some)
            (List.append
              ((AcceptConfigCopy.wrappedBits after).map some)
              (List.append
                ((MarkerAwareCommon.rawBoundaryRest false L).map some)
                [none]))) := by
            rw [hremaining]
            simp [AcceptConfigCopy.wrappedBits,
              AcceptConfigCopy.wrappedBit, List.map_append,
              List.append_assoc]
      _ = tapeAtCells (pairEndLeft0 L) (some false :: restCells) := by
            rw [wrappedRawBit_map_some_cons_tail]
            simp [restCells, MarkedErase.wrappedOptionsWord,
              List.map_append, List.append_assoc]
  have htarget :
      MarkedErase.scanOptionTape (pairEndLeft0 L)
          (List.append (MarkedErase.markedOptions markedBit)
            (List.append (MarkedErase.wrappedOptionsWord after)
              ((MarkerAwareCommon.rawBoundaryRest false L).map some))) =
        tapeAtCells (pairEndLeft0 L) (none :: restCells) := by
    simp [MarkedErase.scanOptionTape, MarkedErase.markedOptions,
      restCells, List.append_assoc]
  rw [hstart, htarget]
  exact hrun

end RejectBranchShapes

end Computability
end FoC

set_option maxRecDepth 20000

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectContinuation

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptInternalMarker RejectBranchShapes

def beforeGapBits (L : DovetailLayout) : List Bool :=
  List.append (RejectBranchShapes.inputStageBits L)
    ((pairSourceBits L).take (RejectBranchShapes.rejectBits L).length)
def fixedDataPrefixBits : List Bool :=
  List.append transitionPrefixBits [false]


def rejectAfterPairTape0 (L : DovetailLayout) : Tape Bool :=
  scanTape (pairEndLeft0 L)
    (List.append (AcceptConfigCopy.wrappedBits (remainingPairBits L))
      (rawBoundaryRest false L))

def rejectAfterPairTape2 (L : DovetailLayout) : Tape Bool :=
  PairStream.counterTape
    (List.append ((RejectBranchShapes.rejectBits L).reverse.map some)
      (List.append ((stageBits L).reverse.map some)
        (counterBaseLeft L))) []
def rejectRewoundTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.targetTapeWithContext (commonCounterBaseTail L)
    (copiedRejectBits L) []

def gapMarkedTape0 (L : DovetailLayout) : Tape Bool :=
  match remainingPairBits L with
  | [] => rejectAfterPairTape0 L
  | markedBit :: after =>
      MarkedErase.scanOptionTape (pairEndLeft0 L)
        (List.append (MarkedErase.markedOptions markedBit)
          (List.append (MarkedErase.wrappedOptionsWord after)
            ((rawBoundaryRest false L).map some)))

def primaryRewoundGapTape0 (L : DovetailLayout) : Tape Bool :=
  match remainingPairBits L with
  | [] => rejectAfterPairTape0 L
  | markedBit :: after =>
      MarkedErase.scanOptionTape (some true :: primaryMarkerBaseLeft L)
        (List.append
          (MarkedErase.wrappedOptionsWord (movedBeforeGapMarkerBits L))
          (List.append (MarkedErase.markedOptions markedBit)
            (List.append (MarkedErase.wrappedOptionsWord after)
              ((rawBoundaryRest false L).map some))))
def dataMarkedTape0 (L : DovetailLayout) : Tape Bool :=
  match remainingPairBits L with
  | [] => rejectAfterPairTape0 L
  | markedBit :: after =>
      MarkedErase.scanOptionTape (commonEndpointLeft L)
        (List.append (MarkedErase.wrappedOptionsWord (beforeGapBits L))
          (List.append (MarkedErase.markedOptions markedBit)
            (List.append (MarkedErase.wrappedOptionsWord after)
              ((rawBoundaryRest false L).map some))))

def gapMarkerDescription : MachineDescription :=
  lowerStructured3Description GapMarker.description

theorem gapMarker_ready : GapMarker.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool GapMarker.description
    (by decide)
theorem gapMarker_supports : SupportsReadWriteRows3 GapMarker.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem gapMarkerDescription_ready : gapMarkerDescription.SubroutineReady := by
  simpa [gapMarkerDescription] using
    lowerStructured3Description_subroutineReady
      gapMarker_ready.left gapMarker_supports

def primaryRewindOptionsDescription : MachineDescription :=
  lowerStructured3Description PrimaryRewind.description
theorem primaryRewindOptionsDescription_ready :
    primaryRewindOptionsDescription.SubroutineReady := by
  simpa [primaryRewindOptionsDescription] using
    lowerStructured3Description_subroutineReady
      MarkerAwareCommon.Lowered.rewind_ready.left
      MarkerAwareCommon.Lowered.rewind_supports

namespace ArmAdvanceData

def start : Nat := 0
def arm : Nat := 1
def first : Nat := 2
def halt : Nat := 22

def rowsForRead
    (source : Nat) (read0 : Option Bool)
    (action0 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read1 read2 =>
    row source read0 read1 read2 action0 keepS keepS target
def fixedCells : List Bool :=
  [ false, true, false, true
  , false, true, false, true
  , false, true, false, true
  , false, true, true, false
  , false, true, false, true ]

def forwardRows : List Transition :=
  [ rowsForRead 2 (some false) keepR 3
  , rowsForRead 3 (some true) keepR 4
  , rowsForRead 4 (some false) keepR 5
  , rowsForRead 5 (some true) keepR 6
  , rowsForRead 6 (some false) keepR 7
  , rowsForRead 7 (some true) keepR 8
  , rowsForRead 8 (some false) keepR 9
  , rowsForRead 9 (some true) keepR 10
  , rowsForRead 10 (some false) keepR 11
  , rowsForRead 11 (some true) keepR 12
  , rowsForRead 12 (some false) keepR 13
  , rowsForRead 13 (some true) keepR 14
  , rowsForRead 14 (some false) keepR 15
  , rowsForRead 15 (some true) keepR 16
  , rowsForRead 16 (some true) keepR 17
  , rowsForRead 17 (some false) keepR 18
  , rowsForRead 18 (some false) keepR 19
  , rowsForRead 19 (some true) keepR 20
  , rowsForRead 20 (some false) keepR 21
  , rowsForRead 21 (some true) keepR halt ].flatten

def rows : List Transition :=
  List.append
    [ rowsForRead start (some false) keepL arm
    , rowsForRead arm (some true) (writeR none) first ].flatten
    forwardRows
def description : Description :=
  ThreeTape.description 23 start halt rows

theorem fixedCells_eq_wrappedPrefix :
    fixedCells = AcceptConfigCopy.wrappedBits fixedDataPrefixBits := by
  rfl

theorem run
    (baseLeft rest : List (Option Bool)) (T1 T2 : Tape Bool) :
    description.runConfig 22
        (config start
          (MarkedErase.scanOptionTape (some true :: baseLeft)
            (List.append (fixedCells.map some) rest)) T1 T2) =
      config halt
        (MarkedErase.scanOptionTape
          (List.append (fixedCells.reverse.map some) (none :: baseLeft)) rest)
        T1 T2 := by
  cases rest <;>
    cases h1 : T1.head with
    | none =>
        cases h2 : T2.head with
        | none =>
            three_tape_step [description, rows, forwardRows, rowsForRead,
              start, arm, first, halt, fixedCells, allReads2, allReadCells,
              List.find?, MarkedErase.scanOptionTape, tapeAtCells, h1, h2]
        | some bit => cases bit <;>
            three_tape_step [description, rows, forwardRows, rowsForRead,
              start, arm, first, halt, fixedCells, allReads2, allReadCells,
              List.find?, MarkedErase.scanOptionTape, tapeAtCells, h1, h2]
    | some bit1 => cases bit1 <;>
        cases h2 : T2.head with
        | none =>
            three_tape_step [description, rows, forwardRows, rowsForRead,
              start, arm, first, halt, fixedCells, allReads2, allReadCells,
              List.find?, MarkedErase.scanOptionTape, tapeAtCells, h1, h2]
        | some bit2 => cases bit2 <;>
            three_tape_step [description, rows, forwardRows, rowsForRead,
              start, arm, first, halt, fixedCells, allReads2, allReadCells,
              List.find?, MarkedErase.scanOptionTape, tapeAtCells, h1, h2]

end ArmAdvanceData
def armAdvanceDataDescription : MachineDescription :=
  lowerStructured3Description ArmAdvanceData.description

theorem armAdvanceData_ready : ArmAdvanceData.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool ArmAdvanceData.description
    (by decide)

theorem armAdvanceData_supports :
    SupportsReadWriteRows3 ArmAdvanceData.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem armAdvanceDataDescription_ready :
    armAdvanceDataDescription.SubroutineReady := by
  simpa [armAdvanceDataDescription] using
    lowerStructured3Description_subroutineReady
      armAdvanceData_ready.left armAdvanceData_supports

theorem rejectAfterPairTape2_eq_rewindSource (L : DovetailLayout) :
    rejectAfterPairTape2 L =
      Tape2Rewinder.sourceTapeWithContext (commonCounterBaseTail L)
        (copiedRejectBits L) [] := by
  have h := reject_pair_counter_end_eq_rewind_source L
    (commonCounterBaseTail L)
  simpa [rejectAfterPairTape2, positionedTape2Left,
    commonCounterBase_eq_none_cons, List.append_assoc] using h

theorem gapMarkerDescription_realizes (L : DovetailLayout) :
    gapMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterPairTape0 L) Tape.blank (rejectAfterPairTape2 L))
      (encodedGuardedStructured3Tapes
        (gapMarkedTape0 L) Tape.blank (rejectAfterPairTape2 L)) := by
  rcases remainingPairBits_exists_cons L with ⟨markedBit, after, hremaining⟩
  have hrun := reject_gap_marker_run L markedBit after hremaining
    (rejectAfterPairTape2 L)
  have hrun' :
      GapMarker.description.runConfig 1
          (config GapMarker.start (rejectAfterPairTape0 L) Tape.blank
            (rejectAfterPairTape2 L)) =
        config GapMarker.halt (gapMarkedTape0 L) Tape.blank
          (rejectAfterPairTape2 L) := by
    simpa [rejectAfterPairTape0, gapMarkedTape0, hremaining] using hrun
  simpa [gapMarkerDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      gapMarker_ready.left gapMarker_ready.right gapMarker_supports
      (c := config GapMarker.start (rejectAfterPairTape0 L) Tape.blank
        (rejectAfterPairTape2 L))
      (tapes := [gapMarkedTape0 L, Tape.blank, rejectAfterPairTape2 L])
      rfl rfl ⟨1, hrun'⟩
theorem rejectTape2Rewind_realizes (L : DovetailLayout) :
    AcceptBranch.rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (gapMarkedTape0 L) Tape.blank (rejectAfterPairTape2 L))
      (encodedGuardedStructured3Tapes
        (gapMarkedTape0 L) Tape.blank (rejectRewoundTape2 L)) := by
  rw [rejectAfterPairTape2_eq_rewindSource]
  exact AcceptBranch.rewindDescription_realizes
    (commonCounterBaseTail L) (copiedRejectBits L) (gapMarkedTape0 L)

theorem primaryRewindOptionsDescription_realizes (L : DovetailLayout) :
    primaryRewindOptionsDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (gapMarkedTape0 L) Tape.blank (rejectRewoundTape2 L))
      (encodedGuardedStructured3Tapes
        (primaryRewoundGapTape0 L) Tape.blank (rejectRewoundTape2 L)) := by
  rcases remainingPairBits_exists_cons L with ⟨markedBit, after, hremaining⟩
  let markerRest : List (Option Bool) :=
    List.append ((wrappedRawBit markedBit).tail.map some)
      (List.append (MarkedErase.wrappedOptionsWord after)
        (List.append ((rawBoundaryRest false L).map some) [none]))
  have hrun := PrimaryRewindOptions.run_options
    (movedBeforeGapMarkerBits L) (primaryMarkerBaseLeft L)
    none markerRest Tape.blank (rejectRewoundTape2 L)
  have hleft := reject_pair_primary_left_shape L (primaryMarkerBaseLeft L)
  have hprefixWrapped :
      AcceptConfigCopy.wrappedBits
          (RejectBranchShapes.prefixThroughStageBits L) =
        List.append (wrappedKind .transition)
          (List.append (wrappedRawBit false)
            (AcceptConfigCopy.wrappedBits
              (RejectBranchShapes.inputStageBits L))) := by
    rw [RejectBranchShapes.prefixThroughStageBits]
    rw [Route.wrappedBits_append,
      Route.wrappedBits_transitionPrefixBits]
    rfl
  have hpair : pairEndLeft0 L =
      List.append
        ((AcceptConfigCopy.wrappedBits
          (movedBeforeGapMarkerBits L)).reverse.map some)
        (none :: primaryMarkerBaseLeft L) := by
    calc
      pairEndLeft0 L =
          List.append
            ((AcceptConfigCopy.wrappedBits
              ((pairSourceBits L).take
                (RejectBranchShapes.rejectBits L).length)).reverse.map
              some)
            (List.append
              ((AcceptConfigCopy.wrappedBits
                (RejectBranchShapes.prefixThroughStageBits L)).reverse.map
                some)
              (none :: primaryMarkerBaseLeft L)) := by
        simp [pairEndLeft0, commonEndpointLeft,
          hprefixWrapped,
          List.reverse_append, List.map_append, List.append_assoc]
      _ = _ := hleft
  have hsource : gapMarkedTape0 L =
      tapeAtCells
        (List.append
          ((AcceptConfigCopy.wrappedBits
            (movedBeforeGapMarkerBits L)).reverse.map some)
          (none :: primaryMarkerBaseLeft L))
        (none :: markerRest) := by
    rw [gapMarkedTape0, hremaining, hpair]
    simp [markerRest, MarkedErase.scanOptionTape,
      MarkedErase.markedOptions, MarkedErase.wrappedOptionsWord,
      List.map_append, List.append_assoc]
  have htarget : primaryRewoundGapTape0 L =
      tapeAtCells (some true :: primaryMarkerBaseLeft L)
        (List.append
          ((AcceptConfigCopy.wrappedBits
            (movedBeforeGapMarkerBits L)).map some)
          (none :: markerRest)) := by
    rw [primaryRewoundGapTape0, hremaining]
    simp [markerRest, MarkedErase.scanOptionTape,
      MarkedErase.markedOptions, MarkedErase.wrappedOptionsWord,
      List.map_append, List.append_assoc]
  have hrun' :
      PrimaryRewind.description.runConfig
          (PrimaryRewind.fuel (movedBeforeGapMarkerBits L))
          (config PrimaryRewind.loop (gapMarkedTape0 L) Tape.blank
            (rejectRewoundTape2 L)) =
        config PrimaryRewind.halt (primaryRewoundGapTape0 L) Tape.blank
          (rejectRewoundTape2 L) := by
    rw [hsource, htarget]
    exact hrun
  simpa [primaryRewindOptionsDescription, encodedGuardedStructured3Tapes,
    gapMarkedTape0, primaryRewoundGapTape0, hremaining] using
    lowerStructured3Description_haltsFromConfigWithTapes
      MarkerAwareCommon.Lowered.rewind_ready.left
      MarkerAwareCommon.Lowered.rewind_ready.right
      MarkerAwareCommon.Lowered.rewind_supports
      (c := config PrimaryRewind.loop (gapMarkedTape0 L) Tape.blank
        (rejectRewoundTape2 L))
      (tapes := [primaryRewoundGapTape0 L, Tape.blank,
        rejectRewoundTape2 L])
      rfl rfl ⟨PrimaryRewind.fuel (movedBeforeGapMarkerBits L), hrun'⟩

theorem movedBeforeGapMarkerBits_eq_fixed_before (L : DovetailLayout) :
    movedBeforeGapMarkerBits L =
      List.append fixedDataPrefixBits (beforeGapBits L) := by
  have hp : RejectBranchShapes.prefixThroughStageBits L =
      List.append fixedDataPrefixBits
        (RejectBranchShapes.inputStageBits L) := by
    simp [RejectBranchShapes.prefixThroughStageBits,
      fixedDataPrefixBits, List.append_assoc]
  rw [movedBeforeGapMarkerBits, hp, beforeGapBits]
  simp [List.append_assoc]
theorem armAdvanceDataDescription_realizes (L : DovetailLayout) :
    armAdvanceDataDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (primaryRewoundGapTape0 L) Tape.blank (rejectRewoundTape2 L))
      (encodedGuardedStructured3Tapes
        (dataMarkedTape0 L) Tape.blank (rejectRewoundTape2 L)) := by
  rcases remainingPairBits_exists_cons L with ⟨markedBit, after, hremaining⟩
  let rest : List (Option Bool) :=
    List.append (MarkedErase.wrappedOptionsWord (beforeGapBits L))
      (List.append (MarkedErase.markedOptions markedBit)
        (List.append (MarkedErase.wrappedOptionsWord after)
          ((rawBoundaryRest false L).map some)))
  have hrun := ArmAdvanceData.run (primaryMarkerBaseLeft L) rest
    Tape.blank (rejectRewoundTape2 L)
  have hmoved := movedBeforeGapMarkerBits_eq_fixed_before L
  have hfixed := ArmAdvanceData.fixedCells_eq_wrappedPrefix
  have hfixedDirect : ArmAdvanceData.fixedCells =
      List.append (wrappedKind .transition) (wrappedRawBit false) := by
    rfl
  have hcommon : commonEndpointLeft L =
      List.append (ArmAdvanceData.fixedCells.reverse.map some)
        (none :: primaryMarkerBaseLeft L) := by
    rw [commonEndpointLeft, hfixedDirect]
  have hsource : primaryRewoundGapTape0 L =
      MarkedErase.scanOptionTape (some true :: primaryMarkerBaseLeft L)
        (List.append (ArmAdvanceData.fixedCells.map some) rest) := by
    rw [primaryRewoundGapTape0, hremaining, hmoved]
    unfold MarkedErase.wrappedOptionsWord
    rw [Route.wrappedBits_append, ← hfixed]
    simp [rest, MarkedErase.wrappedOptionsWord,
      MarkedErase.scanOptionTape, List.map_append, List.append_assoc]
  have htarget : dataMarkedTape0 L =
      MarkedErase.scanOptionTape
        (List.append (ArmAdvanceData.fixedCells.reverse.map some)
          (none :: primaryMarkerBaseLeft L)) rest := by
    rw [dataMarkedTape0, hremaining, ← hcommon]
  have hrun' :
      ArmAdvanceData.description.runConfig 22
          (config ArmAdvanceData.start (primaryRewoundGapTape0 L) Tape.blank
            (rejectRewoundTape2 L)) =
        config ArmAdvanceData.halt (dataMarkedTape0 L) Tape.blank
          (rejectRewoundTape2 L) := by
    rw [hsource, htarget]
    exact hrun
  simpa [armAdvanceDataDescription, encodedGuardedStructured3Tapes,
    primaryRewoundGapTape0, dataMarkedTape0, hremaining] using
    lowerStructured3Description_haltsFromConfigWithTapes
      armAdvanceData_ready.left armAdvanceData_ready.right
      armAdvanceData_supports
      (c := config ArmAdvanceData.start (primaryRewoundGapTape0 L)
        Tape.blank (rejectRewoundTape2 L))
      (tapes := [dataMarkedTape0 L, Tape.blank, rejectRewoundTape2 L])
      rfl rfl ⟨22, hrun'⟩

end RejectContinuation
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
namespace RejectLive

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptFinish RejectContinuation

def rejectConfigRest (L : DovetailLayout) : List Bool :=
  List.append (AcceptConfigCopy.wrappedBits (configHitBits L))
    (rawBoundaryRest false L)

def rejectAfterFirstStageTape0 (L : DovetailLayout) : Tape Bool :=
  match L.stage with
  | 0 =>
      scanTape
        (List.append
          ((List.append (Components.wrappedCellTokens L.input)
            (wrappedKind .done)).reverse.map some)
          (postPrefixLeft L))
        (rejectConfigRest L)
  | stage + 1 =>
      scanTape
        (List.append
          ((List.append (Components.wrappedCellTokens L.input)
            (wrappedKind .tick)).reverse.map some)
          (postPrefixLeft L))
        (List.append (Components.wrappedNatTokens stage) (rejectConfigRest L))
def rejectAfterFirstStageLeft (L : DovetailLayout) : List (Option Bool) :=
  afterFirstStageLeft L

def rejectRemainingLiveBits (L : DovetailLayout) : List Bool :=
  remainingLiveBits L

def rejectAtBoundaryTape0 (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((AcceptConfigCopy.wrappedBits (ParsedLayoutBits L)).reverse.map some)
      (none :: primaryMarkerBaseLeft L))
    (rawBoundaryRest false L)
def rejectAfterLiveCopyTape0 (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((AcceptConfigCopy.wrappedBits (rejectRemainingLiveBits L)).reverse.map
        some)
      (rejectAfterFirstStageLeft L))
    (false :: false :: (rawBoundaryRest false L).drop 2)

theorem rawBoundaryRest_reject_eq_false_false_drop (L : DovetailLayout) :
    rawBoundaryRest false L =
      false :: false :: (rawBoundaryRest false L).drop 2 := by
  rcases
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_false_false_tail
        L.stage with
    ⟨tail, htail⟩
  rw [rawBoundaryRest, false_cons_structuredSuffixTail]
  simp [htail]

theorem rejectRewindFull_realizes
    (L : DovetailLayout) (T2 : Tape Bool) :
    MarkerAwareCommon.Lowered.rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAtBoundaryTape0 L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 false L) Tape.blank T2) := by
  exact MarkerAwareCommon.Lowered.rewindDescription_realizes
    (ParsedLayoutBits L) (primaryMarkerBaseLeft L)
    (rawBoundaryRest false L) T2
theorem rejectPrefixGateDescription_realizes_with_tape
    (L : DovetailLayout) (T2 : Tape Bool) :
    prefixGateDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 false L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rejectAfterFirstStageTape0 L) Tape.blank
        (Components.markCurrent (L.stage = 0) T2)) := by
  let cellsRest : List Bool :=
    List.append (Components.wrappedCellTokens L.input)
      (List.append (Components.wrappedNatTokens L.stage) (rejectConfigRest L))
  have ha : MarkerAwareCommon.Lowered.armDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 false L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (remarkedParsedTape0 false L) Tape.blank T2) := by
    unfold rewoundParsedTape0 remarkedParsedTape0
    rw [MarkerAwareCommon.wrappedParsedBoundary_eq_false_cons_tail]
    rw [MarkerAwareCommon.wrappedParsedBoundary_eq_false_cons_tail]
    exact MarkerAwareCommon.Lowered.armDescription_realizes
      (primaryMarkerBaseLeft L)
      (List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
        (rawBoundaryRest false L)).tail T2
  have hp := MarkerAwareCommon.Lowered.prefixDescription_realizes
    L.input.length (none :: primaryMarkerBaseLeft L) cellsRest T2
  have hg : cellStageGateDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape (postPrefixLeft L)
          (List.append (Components.wrappedCellTokens L.input)
            (List.append (Components.wrappedNatTokens L.stage)
              (rejectConfigRest L))))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rejectAfterFirstStageTape0 L) Tape.blank
        (Components.markCurrent (L.stage = 0) T2)) := by
    cases hstage : L.stage with
    | zero =>
        simpa [rejectAfterFirstStageTape0, postPrefixLeft, hstage,
          Components.wrappedNatTokens] using
          cellStageGateDescription_realizes_zero L.input
            (postPrefixLeft L) (rejectConfigRest L) T2
    | succ stage =>
        simpa [rejectAfterFirstStageTape0, hstage,
          Components.wrappedNatTokens, List.append_assoc] using
          cellStageGateDescription_realizes_succ L.input stage
            (postPrefixLeft L) (rejectConfigRest L) T2
  have hcore := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    MarkerAwareCommon.Lowered.prefixDescription_ready
    cellStageGateDescription_ready hp hg
  have hcore' : prefixGateCoreDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (remarkedParsedTape0 false L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rejectAfterFirstStageTape0 L) Tape.blank
        (Components.markCurrent (L.stage = 0) T2)) := by
    simpa [prefixGateCoreDescription, remarkedParsedTape0, cellsRest,
      rejectConfigRest, postPrefixLeft, wrappedBits_parsedLayoutBits,
      List.append_assoc] using hcore
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    MarkerAwareCommon.Lowered.armDescription_ready
    prefixGateCoreDescription_ready ha hcore'
  simpa [prefixGateDescription] using h

def rejectAfterStagePrefixTape2
    (L : DovetailLayout) (T2 : Tape Bool) : Tape Bool :=
  writeWordRight (StagePrefixForward.bits (L.stage = 0)) T2

theorem rejectStagePrefixDescription_realizes
    (L : DovetailLayout) (T2 : Tape Bool) :
    stagePrefixDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 false L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rejectAfterFirstStageTape0 L) Tape.blank
        (rejectAfterStagePrefixTape2 L T2)) := by
  have hg := rejectPrefixGateDescription_realizes_with_tape L T2
  have hf := stagePrefixFillDescription_realizes
    (L.stage = 0) (rejectAfterFirstStageTape0 L) T2
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    prefixGateDescription_ready stagePrefixFillDescription_ready hg hf
  simpa [stagePrefixDescription, rejectAfterStagePrefixTape2] using h
theorem rejectAfterFirstStageTape0_eq_copySource (L : DovetailLayout) :
    rejectAfterFirstStageTape0 L =
      scanTape (rejectAfterFirstStageLeft L)
        (List.append
          (AcceptConfigCopy.wrappedBits (rejectRemainingLiveBits L))
          (false :: false :: (rawBoundaryRest false L).drop 2)) := by
  have hraw := rawBoundaryRest_reject_eq_false_false_drop L
  cases hstage : L.stage with
  | zero =>
      simp [rejectAfterFirstStageTape0, rejectAfterFirstStageLeft,
        rejectRemainingLiveBits, afterFirstStageLeft, remainingLiveBits,
        rejectConfigRest, hstage, List.append_assoc]
      apply congrArg (scanTape _)
      exact congrArg
        (List.append (AcceptConfigCopy.wrappedBits (configHitBits L))) hraw
  | succ stage =>
      simp only [rejectAfterFirstStageTape0, rejectAfterFirstStageLeft,
        rejectRemainingLiveBits, afterFirstStageLeft, remainingLiveBits,
        hstage]
      rw [wrappedBits_append, wrappedBits_stageNatBits]
      simp [rejectConfigRest, List.append_assoc]
      apply congrArg (scanTape _)
      exact congrArg (List.append (Components.wrappedNatTokens stage))
        (congrArg
          (List.append (AcceptConfigCopy.wrappedBits (configHitBits L))) hraw)

def rejectAfterLiveCopyTape2
    (L : DovetailLayout) (T2 : Tape Bool) : Tape Bool :=
  writeWordRight (rejectRemainingLiveBits L)
    (rejectAfterStagePrefixTape2 L T2)

theorem rejectLiveCopyAtStagePrefix_realizes
    (L : DovetailLayout) (T2 : Tape Bool) :
    liveCopyDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterFirstStageTape0 L) Tape.blank
        (rejectAfterStagePrefixTape2 L T2))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectAfterLiveCopyTape2 L T2)) := by
  rw [rejectAfterFirstStageTape0_eq_copySource]
  exact liveCopyDescription_realizes (rejectRemainingLiveBits L)
    (rejectAfterFirstStageLeft L) ((rawBoundaryRest false L).drop 2)
    (rejectAfterStagePrefixTape2 L T2)
theorem rejectAfterLiveCopyTape2_eq_write_live
    (L : DovetailLayout) (T2 : Tape Bool) :
    rejectAfterLiveCopyTape2 L T2 = writeWordRight (liveBits L) T2 := by
  rw [rejectAfterLiveCopyTape2, rejectAfterStagePrefixTape2]
  rw [AcceptFinish.writeWordRight_append]
  unfold rejectRemainingLiveBits
  rw [stagePrefix_append_remaining_eq_liveBits]

def rejectLiveDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    MarkerAwareCommon.Lowered.rewindDescription
    (canonicalPrimitiveSeqDescription stagePrefixDescription liveCopyDescription)

theorem rejectLiveDescription_ready : rejectLiveDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    MarkerAwareCommon.Lowered.rewindDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      stagePrefixDescription_ready liveCopyDescription_ready)
theorem rejectLiveDescription_realizes
    (L : DovetailLayout) (T2 : Tape Bool) :
    rejectLiveDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAtBoundaryTape0 L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (writeWordRight (liveBits L) T2)) := by
  have hr := rejectRewindFull_realizes L T2
  have hs := rejectStagePrefixDescription_realizes L T2
  have hsl := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    stagePrefixDescription_ready liveCopyDescription_ready hs
    (rejectLiveCopyAtStagePrefix_realizes L T2)
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    MarkerAwareCommon.Lowered.rewindDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      stagePrefixDescription_ready liveCopyDescription_ready)
    hr hsl
  rw [rejectAfterLiveCopyTape2_eq_write_live] at h
  simpa [rejectLiveDescription] using h

namespace MoveTape2RightFive

def start : Nat := 0
def halt : Nat := 5

def rowsForState (source target : Nat) : List Transition :=
  allReads3 fun read0 read1 read2 =>
    row source read0 read1 read2 keepS keepS keepR target
def rows : List Transition :=
  [ rowsForState 0 1, rowsForState 1 2, rowsForState 2 3,
    rowsForState 3 4, rowsForState 4 halt ].flatten

def description : Description :=
  ThreeTape.description 6 start halt rows

def apply (T : Tape Bool) : Tape Bool :=
  keepR.apply (keepR.apply (keepR.apply (keepR.apply (keepR.apply T))))

syntax "move_right_five_step" ident ident ident : tactic

macro_rules
  | `(tactic| move_right_five_step $T0:ident $T1:ident $T2:ident) =>
      `(tactic|
        cases h0 : ($T0:ident).head with
        | none =>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForState,
                    start, halt, allReads3, allReads2, allReadCells,
                    List.find?, h0, h1, h2]
                | some bit => cases bit <;>
                    three_tape_step [description, rows, rowsForState,
                      start, halt, allReads3, allReads2, allReadCells,
                      List.find?, h0, h1, h2]
            | some bit1 => cases bit1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForState,
                    start, halt, allReads3, allReads2, allReadCells,
                    List.find?, h0, h1, h2]
                | some bit2 => cases bit2 <;>
                    three_tape_step [description, rows, rowsForState,
                      start, halt, allReads3, allReads2, allReadCells,
                      List.find?, h0, h1, h2]
        | some bit0 => cases bit0 <;>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForState,
                    start, halt, allReads3, allReads2, allReadCells,
                    List.find?, h0, h1, h2]
                | some bit => cases bit <;>
                    three_tape_step [description, rows, rowsForState,
                      start, halt, allReads3, allReads2, allReadCells,
                      List.find?, h0, h1, h2]
            | some bit1 => cases bit1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForState,
                    start, halt, allReads3, allReads2, allReadCells,
                    List.find?, h0, h1, h2]
                | some bit2 => cases bit2 <;>
                    three_tape_step [description, rows, rowsForState,
                      start, halt, allReads3, allReads2, allReadCells,
                      List.find?, h0, h1, h2])
theorem step0 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config 0 T0 T1 T2) =
      config 1 T0 T1 (keepR.apply T2) := by
  move_right_five_step T0 T1 T2

theorem step1 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config 1 T0 T1 T2) =
      config 2 T0 T1 (keepR.apply T2) := by
  move_right_five_step T0 T1 T2

theorem step2 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config 2 T0 T1 T2) =
      config 3 T0 T1 (keepR.apply T2) := by
  move_right_five_step T0 T1 T2
theorem step3 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config 3 T0 T1 T2) =
      config 4 T0 T1 (keepR.apply T2) := by
  move_right_five_step T0 T1 T2

theorem step4 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config 4 T0 T1 T2) =
      config halt T0 T1 (keepR.apply T2) := by
  move_right_five_step T0 T1 T2

theorem run (T0 T1 T2 : Tape Bool) :
    description.runConfig 5 (config start T0 T1 T2) =
      config halt T0 T1 (apply T2) := by
  change description.runConfig 5 (config 0 T0 T1 T2) =
    config halt T0 T1 (apply T2)
  rw [show 5 = 1 + (1 + (1 + (1 + 1))) by rfl]
  rw [Description.runConfig_add, step0]
  rw [Description.runConfig_add, step1]
  rw [Description.runConfig_add, step2]
  rw [Description.runConfig_add, step3, step4]
  rfl

end MoveTape2RightFive
def moveTape2RightFiveDescription : MachineDescription :=
  lowerStructured3Description MoveTape2RightFive.description

theorem moveTape2RightFive_ready :
    MoveTape2RightFive.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    MoveTape2RightFive.description (by decide)

theorem moveTape2RightFive_supports :
    SupportsReadWriteRows3 MoveTape2RightFive.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem moveTape2RightFiveDescription_ready :
    moveTape2RightFiveDescription.SubroutineReady := by
  simpa [moveTape2RightFiveDescription] using
    lowerStructured3Description_subroutineReady
      moveTape2RightFive_ready.left moveTape2RightFive_supports

theorem moveTape2RightFiveDescription_realizes (T0 T2 : Tape Bool) :
    moveTape2RightFiveDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (MoveTape2RightFive.apply T2)) := by
  simpa [moveTape2RightFiveDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      moveTape2RightFive_ready.left moveTape2RightFive_ready.right
      moveTape2RightFive_supports
      (c := config MoveTape2RightFive.start T0 Tape.blank T2)
      (tapes := [T0, Tape.blank, MoveTape2RightFive.apply T2])
      rfl rfl ⟨5, MoveTape2RightFive.run T0 Tape.blank T2⟩

def rejectCleanupApply (T : Tape Bool) : Tape Bool :=
  MoveTape2RightFive.apply
    (Components.eraseRight 4
      (moveLeftFour (moveLeftFour T)))
def rejectCleanupDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription moveLeftFourDescription
      moveLeftFourDescription)
    (canonicalPrimitiveSeqDescription eraseFourDescription
      moveTape2RightFiveDescription)

theorem rejectCleanupDescription_ready :
    rejectCleanupDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      moveLeftFourDescription_ready moveLeftFourDescription_ready)
    (canonicalPrimitiveSeqDescription_subroutineReady
      eraseFourDescription_ready moveTape2RightFiveDescription_ready)

theorem rejectCleanupDescription_realizes (T0 T2 : Tape Bool) :
    rejectCleanupDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (rejectCleanupApply T2)) := by
  have hleft := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    moveLeftFourDescription_ready moveLeftFourDescription_ready
    (moveLeftFourDescription_realizes T0 T2)
    (moveLeftFourDescription_realizes T0 (moveLeftFour T2))
  have hright := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    eraseFourDescription_ready moveTape2RightFiveDescription_ready
    (eraseFourDescription_realizes T0 (moveLeftFour (moveLeftFour T2)))
    (moveTape2RightFiveDescription_realizes T0
      (Components.eraseRight 4 (moveLeftFour (moveLeftFour T2))))
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    (canonicalPrimitiveSeqDescription_subroutineReady
      moveLeftFourDescription_ready moveLeftFourDescription_ready)
    (canonicalPrimitiveSeqDescription_subroutineReady
      eraseFourDescription_ready moveTape2RightFiveDescription_ready)
    hleft hright
  simpa [rejectCleanupDescription, rejectCleanupApply] using h
def rejectKeptPrefixBits (L : DovetailLayout) : List Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)
    (List.append (acceptBits L) (rejectBits L))

def rejectCleanedLiveEndTape2
    (baseLeft : List (Option Bool)) (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append ((rejectHitBits L).reverse.map some)
        (List.append (List.replicate 4 (none : Option Bool))
          (List.append ((rejectKeptPrefixBits L).reverse.map some) baseLeft)))
    [none]

theorem liveBits_reject_decomp (L : DovetailLayout) :
    liveBits L =
      List.append (rejectKeptPrefixBits L)
        (List.append (acceptHitBits L) (rejectHitBits L)) := by
  simp [liveBits, rejectKeptPrefixBits, List.append_assoc]
theorem rejectCleanup_exact
    (baseLeft : List (Option Bool)) (L : DovetailLayout) :
    rejectCleanupApply
        (tapeAtCells
          (List.append ((liveBits L).reverse.map some) baseLeft) [none]) =
      rejectCleanedLiveEndTape2 baseLeft L := by
  have haccept : acceptHitBits L =
      [false, true, L.acceptHit, !L.acceptHit] := by
    cases h : L.acceptHit <;>
      simp [acceptHitBits, boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput, h]
  have hreject : rejectHitBits L =
      [false, true, L.rejectHit, !L.rejectHit] := by
    cases h : L.rejectHit <;>
      simp [rejectHitBits, boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput, h]
  rw [liveBits_reject_decomp, haccept, hreject]
  simp [rejectCleanupApply, rejectCleanedLiveEndTape2,
    rejectKeptPrefixBits, MoveTape2RightFive.apply, moveLeftFour,
    keepR, TapeAction.apply, HeadMove.apply, Components.eraseRight,
    Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write, tapeAtCells,
    haccept, hreject, List.reverse_append, List.map_append,
    List.append_assoc]

end RejectLive
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
