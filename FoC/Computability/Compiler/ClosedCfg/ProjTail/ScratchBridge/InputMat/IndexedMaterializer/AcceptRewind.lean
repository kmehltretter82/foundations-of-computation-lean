import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.AcceptAlloc
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.ShapesInsert

set_option doc.verso true

/-!
Delimiter recovery, tape-0 allocation, and final accepting-route rewinds.
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
namespace AcceptDelimiter

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptFinish AcceptInternalMarker AcceptReconstructPrefix

theorem eraseRight_step_none
    (left rest : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.write none (tapeAtCells left (none :: rest))) =
      tapeAtCells (none :: left) rest := by
  cases rest <;> rfl

theorem eraseRight_replicate_none_prefix
    (n : Nat) (left rest : List (Option Bool)) :
    Components.eraseRight n
        (tapeAtCells left
          (List.append (List.replicate n (none : Option Bool)) rest)) =
      tapeAtCells
        (List.append (List.replicate n (none : Option Bool)) left)
        rest := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [Components.eraseRight]
      simp only [List.replicate_succ, List.append_eq, List.cons_append]
      rw [eraseRight_step_none]
      apply Eq.trans (ih (none :: left))
      rw [AcceptFinish.replicate_none_append_cons]
      simp [List.replicate_succ]
theorem postInternalRightTape2_shape (L : DovetailLayout) :
    postInternalRightTape2 L =
      tapeAtCells (none :: none :: counterBaseTail L)
        (List.append
          (List.replicate ((remainingBits L).length + 3)
            (none : Option Bool))
          (List.append ((keptLiveBits L).map some)
            (none :: liveRewindPadding))) := by
  simp [postInternalRightTape2, internalScanTargetTape2,
    keepR, TapeAction.apply, HeadMove.apply, Tape.move, Tape.moveRight,
    tapeAtCells, List.append_assoc]
  rfl

theorem driverPrefixBits_eq_inputStageBits (L : DovetailLayout) :
    driverPrefixBits L = inputStageBits L := by
  rfl

theorem afterReconstructionDriverTape2_shape (L : DovetailLayout) :
    afterReconstructionDriverTape2 L =
      tapeAtCells
        (List.append
          (List.replicate (driverPrefixBits L).length (none : Option Bool))
          (none :: none :: counterBaseTail L))
        (List.append
          (List.replicate ((acceptBits L).length + 7)
            (none : Option Bool))
          (List.append ((keptLiveBits L).map some)
            (none :: liveRewindPadding))) := by
  unfold afterReconstructionDriverTape2
  rw [postInternalRightTape2_shape]
  have hcount :
      (remainingBits L).length + 3 =
        (driverPrefixBits L).length + ((acceptBits L).length + 7) := by
    rw [markedGap_blank_count, driverPrefixBits_eq_inputStageBits]
    lia
  rw [hcount]
  rw [show List.replicate
        ((driverPrefixBits L).length + ((acceptBits L).length + 7))
          (none : Option Bool) =
      List.append
        (List.replicate (driverPrefixBits L).length none)
        (List.replicate ((acceptBits L).length + 7) none) by
      exact (replicate_none_append_replicate _ _).symm]
  apply Eq.trans
    (congrArg (Components.eraseRight (driverPrefixBits L).length)
      (congrArg (tapeAtCells (none :: none :: counterBaseTail L))
        (List.append_assoc
          (List.replicate (driverPrefixBits L).length none)
          (List.replicate ((acceptBits L).length + 7) none)
          (List.append ((keptLiveBits L).map some)
            (none :: liveRewindPadding)))))
  exact eraseRight_replicate_none_prefix
    (driverPrefixBits L).length
    (none :: none :: counterBaseTail L)
    (List.append
      (List.replicate ((acceptBits L).length + 7) none)
      (List.append ((keptLiveBits L).map some)
        (none :: liveRewindPadding)))
def keptLiveTailBits (L : DovetailLayout) : List Bool :=
  (keptLiveBits L).tail

theorem keptLiveBits_cons_false (L : DovetailLayout) :
    keptLiveBits L = false :: keptLiveTailBits L := by
  rcases stageNatBits_cons_false L.stage with ⟨stageTail, hstage⟩
  simp [keptLiveBits, keptLiveTailBits, hstage]

def delimiterMarkerBase (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate (driverPrefixBits L).length (none : Option Bool))
    (none :: none :: counterBaseTail L)
def delimiterRightTail (L : DovetailLayout) : List (Option Bool) :=
  List.append ((keptLiveTailBits L).map some)
    (none :: liveRewindPadding)

def delimiterSourceTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells (delimiterMarkerBase L)
    (List.append
      (List.replicate ((acceptBits L).length + 7) (none : Option Bool))
      (some false :: delimiterRightTail L))

theorem afterReconstructionDriverTape2_eq_delimiterSource
    (L : DovetailLayout) :
    afterReconstructionDriverTape2 L = delimiterSourceTape2 L := by
  rw [afterReconstructionDriverTape2_shape]
  rw [keptLiveBits_cons_false]
  rfl

namespace SpanDelimiter
def start : Nat := 0
def scan : Nat := 1
def halt : Nat := 2

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action2 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 keepS keepS action2 target

def rows : List Transition :=
  [ rowsForTape2Read start none (writeR (some true)) scan
  , rowsForTape2Read scan none keepR scan
  , rowsForTape2Read scan (some false) (writeS (some true)) halt ].flatten
def description : Description :=
  ThreeTape.description 3 start halt rows

theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

syntax "delimiter_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| delimiter_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape2Read,
          start, scan, halt, allReads2, allReadCells, List.find?,
          tapeAtCells, $lemmas,*])
theorem start_step
    (T0 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        (config start T0 Tape.blank
          (tapeAtCells left (none :: right))) =
      config scan T0 Tape.blank
        (tapeAtCells (some true :: left) right) := by
  cases h0 : T0.head with
  | none => delimiter_step [h0] <;> cases right <;> rfl
  | some bit => cases bit <;>
      delimiter_step [h0] <;> cases right <;> rfl

theorem blank_step
    (T0 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        (config scan T0 Tape.blank
          (tapeAtCells left (none :: right))) =
      config scan T0 Tape.blank
        (tapeAtCells (none :: left) right) := by
  cases h0 : T0.head with
  | none => delimiter_step [h0] <;> cases right <;> rfl
  | some bit => cases bit <;>
      delimiter_step [h0] <;> cases right <;> rfl

theorem end_step
    (T0 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        (config scan T0 Tape.blank
          (tapeAtCells left (some false :: right))) =
      config halt T0 Tape.blank
        (tapeAtCells left (some true :: right)) := by
  cases h0 : T0.head with
  | none => delimiter_step [h0]
  | some bit => cases bit <;> delimiter_step [h0]
theorem scan_run
    (n : Nat) (T0 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig (n + 1)
        (config scan T0 Tape.blank
          (tapeAtCells left
            (List.append (List.replicate n (none : Option Bool))
              (some false :: right)))) =
      config halt T0 Tape.blank
        (tapeAtCells
          (List.append (List.replicate n (none : Option Bool)) left)
          (some true :: right)) := by
  induction n generalizing left with
  | zero =>
      simpa using end_step T0 left right
  | succ n ih =>
      rw [show (n + 1) + 1 = 1 + (n + 1) by lia]
      rw [Description.runConfig_add]
      simp only [List.replicate_succ, List.append_eq, List.cons_append]
      rw [blank_step]
      apply Eq.trans (ih (none :: left))
      rw [AcceptFinish.replicate_none_append_cons]
      simp [List.replicate_succ]

def sourceTape
    (markerBase : List (Option Bool)) (span : Nat)
    (rightTail : List (Option Bool)) : Tape Bool :=
  tapeAtCells markerBase
    (List.append (List.replicate (span + 1) (none : Option Bool))
      (some false :: rightTail))

def targetTape
    (markerBase : List (Option Bool)) (span : Nat)
    (rightTail : List (Option Bool)) : Tape Bool :=
  BlankSpanAllocator.endMarkedTape markerBase span rightTail
def fuel (span : Nat) : Nat := span + 2

theorem run
    (T0 : Tape Bool) (markerBase : List (Option Bool))
    (span : Nat) (rightTail : List (Option Bool)) :
    description.runConfig (fuel span)
        (config start T0 Tape.blank
          (sourceTape markerBase span rightTail)) =
      config halt T0 Tape.blank
        (targetTape markerBase span rightTail) := by
  rw [fuel]
  rw [show span + 2 = 1 + (span + 1) by lia]
  rw [Description.runConfig_add]
  rw [sourceTape, show span + 1 = span + 1 by rfl]
  rw [List.replicate_succ]
  simp only [List.append_eq, List.cons_append]
  rw [start_step]
  simpa [targetTape, BlankSpanAllocator.endMarkedTape] using
    scan_run span T0 (some true :: markerBase) rightTail

end SpanDelimiter

def loweredDelimiterDescription : MachineDescription :=
  lowerStructured3Description SpanDelimiter.description
theorem loweredDelimiterDescription_ready :
    loweredDelimiterDescription.SubroutineReady := by
  simpa [loweredDelimiterDescription] using
    lowerStructured3Description_subroutineReady
      SpanDelimiter.ready.left SpanDelimiter.supports

theorem loweredDelimiterDescription_realizes
    (T0 : Tape Bool) (markerBase : List (Option Bool))
    (span : Nat) (rightTail : List (Option Bool)) :
    loweredDelimiterDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (SpanDelimiter.sourceTape markerBase span rightTail))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (SpanDelimiter.targetTape markerBase span rightTail)) := by
  simpa [loweredDelimiterDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      SpanDelimiter.ready.left SpanDelimiter.ready.right
      SpanDelimiter.supports
      (c := config SpanDelimiter.start T0 Tape.blank
        (SpanDelimiter.sourceTape markerBase span rightTail))
      (tapes := [ T0, Tape.blank
        , SpanDelimiter.targetTape markerBase span rightTail ])
      rfl rfl ⟨SpanDelimiter.fuel span,
        SpanDelimiter.run T0 markerBase span rightTail⟩

def afterDelimiterTape2 (L : DovetailLayout) : Tape Bool :=
  BlankSpanAllocator.endMarkedTape
    (delimiterMarkerBase L) ((acceptBits L).length + 6)
    (delimiterRightTail L)
theorem delimiter_realizes (L : DovetailLayout) :
    loweredDelimiterDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 true L) Tape.blank (delimiterSourceTape2 L))
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 true L) Tape.blank (afterDelimiterTape2 L)) := by
  simpa [SpanDelimiter.sourceTape, SpanDelimiter.targetTape,
    delimiterSourceTape2, afterDelimiterTape2] using
    loweredDelimiterDescription_realizes
      (afterDriverTape0 true L) (delimiterMarkerBase L)
      ((acceptBits L).length + 6) (delimiterRightTail L)

end AcceptDelimiter
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
namespace AcceptT0Allocator

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptFinish AcceptDelimiter

def processedSourceBits (L : DovetailLayout) : List Bool :=
  List.append boolWordRawBitsDecoderHeaderBits
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        (ParsedLayoutBits L).length)
      (AcceptConfigCopy.wrappedBits (prefixThroughStageBits L)))

def remainingSourceBits (L : DovetailLayout) : List Bool :=
  List.append (AcceptConfigCopy.wrappedBits (configHitBits L))
    (false ::
      countWindowPostFieldDecodedPrefixStructuredSuffixTail true L)
theorem sourceWord_eq_processed_remaining (L : DovetailLayout) :
    sourceWord true L =
      List.append (processedSourceBits L) (remainingSourceBits L) := by
  unfold sourceWord processedSourceBits remainingSourceBits
    boolWordRawBitsDecoderEncodedFieldBits
  rw [← wrappedBits_eq_cellsCodeBits_map_some]
  rw [parsedLayoutBits_eq_prefix_configHit, wrappedBits_append]
  simp [List.append_assoc]

theorem afterDriverTape0_eq_processed_scan (L : DovetailLayout) :
    afterDriverTape0 true L =
      tapeAtCells
        (List.append ((processedSourceBits L).reverse.map some) [none])
        (List.append ((remainingSourceBits L).map some) [none]) := by
  simp [afterDriverTape0, processedSourceBits, remainingSourceBits,
    positionTape0Left, scanTape, List.reverse_append, List.map_append,
    List.append_assoc]

namespace Tape0RightEdge

def start : Nat := 0
def halt : Nat := 1
def rowsForTape0Read
    (read0 : Option Bool) (action0 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2 fun read1 read2 =>
    row start read0 read1 read2 action0 keepS keepS target

def rows : List Transition :=
  [ rowsForTape0Read (some false) keepR start
  , rowsForTape0Read (some true) keepR start
  , rowsForTape0Read none keepS halt ].flatten

def description : Description :=
  ThreeTape.description 2 start halt rows
theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def sourceTape
    (left : List (Option Bool)) (bits : List Bool) : Tape Bool :=
  tapeAtCells left (List.append (bits.map some) [none])
def targetTape
    (left : List (Option Bool)) (bits : List Bool) : Tape Bool :=
  tapeAtCells
    (List.append (bits.reverse.map some) left) [none]

syntax "right_edge_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| right_edge_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape0Read,
          start, halt, allReads2, allReadCells, List.find?,
          sourceTape, targetTape, tapeAtCells, $lemmas,*])

theorem bit_step
    (bit : Bool) (rest : List Bool)
    (left : List (Option Bool)) (T1 T2 : Tape Bool) :
    description.runConfig 1
        (config start (sourceTape left (bit :: rest)) T1 T2) =
      config start (sourceTape (some bit :: left) rest) T1 T2 := by
  cases T1 with
  | mk left1 head1 right1 =>
      cases T2 with
      | mk left2 head2 right2 =>
          cases bit <;> cases rest <;>
            cases head1 <;> (try cases ‹Bool›) <;>
              cases head2 <;> (try cases ‹Bool›) <;>
                right_edge_step []

theorem finish_step
    (left : List (Option Bool)) (T1 T2 : Tape Bool) :
    description.runConfig 1
        (config start (sourceTape left []) T1 T2) =
      config halt (targetTape left []) T1 T2 := by
  cases T1 with
  | mk left1 head1 right1 =>
      cases T2 with
      | mk left2 head2 right2 =>
          cases head1 <;> (try cases ‹Bool›) <;>
            cases head2 <;> (try cases ‹Bool›) <;>
              right_edge_step []
def fuel (bits : List Bool) : Nat := bits.length + 1

theorem run
    (bits : List Bool) (left : List (Option Bool))
    (T1 T2 : Tape Bool) :
    description.runConfig (fuel bits)
        (config start (sourceTape left bits) T1 T2) =
      config halt (targetTape left bits) T1 T2 := by
  induction bits generalizing left with
  | nil => exact finish_step left T1 T2
  | cons bit rest ih =>
      rw [fuel, show (bit :: rest).length + 1 =
        1 + (rest.length + 1) by simp; lia]
      rw [Description.runConfig_add]
      rw [bit_step]
      have h := ih (some bit :: left)
      rw [fuel] at h
      simpa [targetTape, List.reverse_cons, List.map_append,
        List.append_assoc] using h

end Tape0RightEdge

def rightEdgeDataBase (L : DovetailLayout) : List (Option Bool) :=
  List.append ((sourceWord true L).reverse.map some) [none]
def rightEdgeDataTape0 (L : DovetailLayout) : Tape Bool :=
  BlankSpanAllocator.dataSourceTape (rightEdgeDataBase L)

theorem tape0RightEdge_target_eq_dataTape (L : DovetailLayout) :
    Tape0RightEdge.targetTape
        (List.append ((processedSourceBits L).reverse.map some) [none])
        (remainingSourceBits L) =
      rightEdgeDataTape0 L := by
  unfold rightEdgeDataTape0 rightEdgeDataBase
  rw [sourceWord_eq_processed_remaining]
  simp [Tape0RightEdge.targetTape,
    BlankSpanAllocator.dataSourceTape,
    List.reverse_append, List.map_append, List.append_assoc]

def loweredRightEdgeDescription : MachineDescription :=
  lowerStructured3Description Tape0RightEdge.description
theorem loweredRightEdgeDescription_ready :
    loweredRightEdgeDescription.SubroutineReady := by
  simpa [loweredRightEdgeDescription] using
    lowerStructured3Description_subroutineReady
      Tape0RightEdge.ready.left Tape0RightEdge.supports

theorem loweredRightEdgeDescription_realizes
    (bits : List Bool) (left : List (Option Bool))
    (T2 : Tape Bool) :
    loweredRightEdgeDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (Tape0RightEdge.sourceTape left bits) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (Tape0RightEdge.targetTape left bits) Tape.blank T2) := by
  simpa [loweredRightEdgeDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      Tape0RightEdge.ready.left Tape0RightEdge.ready.right
      Tape0RightEdge.supports
      (c := config Tape0RightEdge.start
        (Tape0RightEdge.sourceTape left bits) Tape.blank T2)
      (tapes := [ Tape0RightEdge.targetTape left bits, Tape.blank, T2 ])
      rfl rfl ⟨Tape0RightEdge.fuel bits,
        Tape0RightEdge.run bits left Tape.blank T2⟩

theorem rightEdge_realizes (L : DovetailLayout) :
    loweredRightEdgeDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 true L) Tape.blank (afterDelimiterTape2 L))
      (encodedGuardedStructured3Tapes
        (rightEdgeDataTape0 L) Tape.blank (afterDelimiterTape2 L)) := by
  rw [afterDriverTape0_eq_processed_scan]
  have h := loweredRightEdgeDescription_realizes
    (remainingSourceBits L)
    (List.append ((processedSourceBits L).reverse.map some) [none])
    (afterDelimiterTape2 L)
  rw [tape0RightEdge_target_eq_dataTape] at h
  exact h
def allocatorCount (L : DovetailLayout) : Nat :=
  (acceptBits L).length + 5

def afterAllocatorTape0 (L : DovetailLayout) : Tape Bool :=
  BlankSpanAllocator.dataTargetTape
    (rightEdgeDataBase L) ((acceptBits L).length + 6)

def afterAllocatorTape2 (L : DovetailLayout) : Tape Bool :=
  BlankSpanAllocator.restoredTape
    (delimiterMarkerBase L) (allocatorCount L) (delimiterRightTail L)
theorem allocator_realizes (L : DovetailLayout) :
    BlankSpanAllocator.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rightEdgeDataTape0 L) Tape.blank (afterDelimiterTape2 L))
      (encodedGuardedStructured3Tapes
        (afterAllocatorTape0 L) Tape.blank (afterAllocatorTape2 L)) := by
  simpa [rightEdgeDataTape0, afterDelimiterTape2,
    SpanDelimiter.targetTape, afterAllocatorTape0, afterAllocatorTape2,
    allocatorCount] using
    BlankSpanAllocator.loweredDescription_realizes
      (rightEdgeDataBase L) (delimiterMarkerBase L)
      ((acceptBits L).length + 5) (delimiterRightTail L)

end AcceptT0Allocator
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
namespace AcceptFinalTail

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptFinish AcceptDelimiter AcceptT0Allocator AcceptReconstructPrefix

namespace Tape0RewindPadded

def enter : Nat := 0
def rewind : Nat := 1
def halt : Nat := 2

def rowsForTape0Read
    (source : Nat) (read0 : Option Bool)
    (action0 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read1 read2 =>
    row source read0 read1 read2 action0 keepS keepS target
def rows : List Transition :=
  [ rowsForTape0Read enter none keepL rewind
  , rowsForTape0Read rewind (some false) keepL rewind
  , rowsForTape0Read rewind (some true) keepL rewind
  , rowsForTape0Read rewind none keepR halt ].flatten

def description : Description :=
  ThreeTape.description 3 enter halt rows

theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)
theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def sourceTape
    (baseLeft : List (Option Bool)) (bits : List Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (bits.reverse.map some) (none :: baseLeft))
    (none :: rightPadding)

def targetTape
    (baseLeft : List (Option Bool)) (bits : List Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (none :: baseLeft)
    (List.append (bits.map some) (none :: rightPadding))
def rewindTape
    (baseLeft : List (Option Bool))
    (remainingRev processed : List Bool) (current : Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (remainingRev.map some) (none :: baseLeft))
    (some current ::
      List.append (processed.map some) (none :: rightPadding))

syntax "tape0_rewind_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| tape0_rewind_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape0Read,
          enter, rewind, halt, allReads2, allReadCells, List.find?,
          sourceTape, targetTape, rewindTape, tapeAtCells, $lemmas,*])

theorem enter_step
    (baseLeft : List (Option Bool))
    (remainingRev : List Bool) (current : Bool)
    (rightPadding : List (Option Bool))
    (T1 T2 : Tape Bool) :
    description.runConfig 1
        (config enter
          (tapeAtCells
            (some current ::
              List.append (remainingRev.map some) (none :: baseLeft))
            (none :: rightPadding))
          T1 T2) =
      config rewind
        (rewindTape baseLeft remainingRev [] current rightPadding)
        T1 T2 := by
  cases T1 with
  | mk left1 head1 right1 =>
      cases T2 with
      | mk left2 head2 right2 =>
          cases current <;>
            cases head1 <;> (try cases ‹Bool›) <;>
              cases head2 <;> (try cases ‹Bool›) <;>
                tape0_rewind_step []

theorem rewind_step
    (baseLeft : List (Option Bool))
    (remainingRev processed : List Bool) (current : Bool)
    (rightPadding : List (Option Bool))
    (T1 T2 : Tape Bool) :
    description.runConfig 1
        (config rewind
          (rewindTape baseLeft remainingRev processed current rightPadding)
          T1 T2) =
      match remainingRev with
      | [] =>
          config rewind
            (tapeAtCells baseLeft
              (none :: some current ::
                List.append (processed.map some) (none :: rightPadding)))
            T1 T2
      | next :: rest =>
          config rewind
            (rewindTape baseLeft rest (current :: processed) next
              rightPadding)
            T1 T2 := by
  cases remainingRev with
  | nil =>
      cases T1 with
      | mk left1 head1 right1 =>
          cases T2 with
          | mk left2 head2 right2 =>
              cases current <;>
                cases head1 <;> (try cases ‹Bool›) <;>
                  cases head2 <;> (try cases ‹Bool›) <;>
                    tape0_rewind_step []
  | cons next rest =>
      cases T1 with
      | mk left1 head1 right1 =>
          cases T2 with
          | mk left2 head2 right2 =>
              cases current <;> cases next <;>
                cases head1 <;> (try cases ‹Bool›) <;>
                  cases head2 <;> (try cases ‹Bool›) <;>
                    tape0_rewind_step []
theorem rewind_run
    (baseLeft : List (Option Bool))
    (remainingRev processed : List Bool) (current : Bool)
    (rightPadding : List (Option Bool))
    (T1 T2 : Tape Bool) :
    description.runConfig (remainingRev.length + 1)
        (config rewind
          (rewindTape baseLeft remainingRev processed current rightPadding)
          T1 T2) =
      config rewind
        (tapeAtCells baseLeft
          (none :: List.append
            ((List.append remainingRev.reverse
              (current :: processed)).map some)
            (none :: rightPadding)))
        T1 T2 := by
  induction remainingRev generalizing current processed with
  | nil =>
      simpa [List.append_assoc] using
        rewind_step baseLeft [] processed current rightPadding T1 T2
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [rewind_step]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem finish_step
    (baseLeft : List (Option Bool)) (bits : List Bool)
    (rightPadding : List (Option Bool))
    (T1 T2 : Tape Bool) :
    description.runConfig 1
        (config rewind
          (tapeAtCells baseLeft
            (none :: List.append (bits.map some)
              (none :: rightPadding)))
          T1 T2) =
      config halt (targetTape baseLeft bits rightPadding) T1 T2 := by
  cases T1 with
  | mk left1 head1 right1 =>
      cases T2 with
      | mk left2 head2 right2 =>
          cases bits <;>
            cases head1 <;> (try cases ‹Bool›) <;>
              cases head2 <;> (try cases ‹Bool›) <;>
                tape0_rewind_step []

def fuel (bits : List Bool) : Nat := bits.length + 2
theorem run
    (baseLeft : List (Option Bool)) (bits : List Bool)
    (rightPadding : List (Option Bool))
    (T1 T2 : Tape Bool) :
    description.runConfig (fuel bits)
        (config enter (sourceTape baseLeft bits rightPadding) T1 T2) =
      config halt (targetTape baseLeft bits rightPadding) T1 T2 := by
  cases hrev : bits.reverse with
  | nil =>
      have hbits : bits = [] := by
        apply List.eq_nil_of_length_eq_zero
        have h := congrArg List.length hrev
        simpa using h
      subst bits
      rw [show fuel [] = 1 + 1 by rfl]
      rw [Description.runConfig_add]
      change description.runConfig 1
        (description.runConfig 1
          (config enter
            (tapeAtCells (none :: baseLeft) (none :: rightPadding))
            T1 T2)) = _
      have henter :
          description.runConfig 1
              (config enter
                (tapeAtCells (none :: baseLeft) (none :: rightPadding))
                T1 T2) =
            config rewind
              (tapeAtCells baseLeft (none :: none :: rightPadding))
              T1 T2 := by
        cases T1 with
        | mk left1 head1 right1 =>
            cases T2 with
            | mk left2 head2 right2 =>
                cases head1 <;> (try cases ‹Bool›) <;>
                  cases head2 <;> (try cases ‹Bool›) <;>
                    tape0_rewind_step []
      rw [henter]
      simpa using finish_step baseLeft [] rightPadding T1 T2
  | cons current remainingRev =>
      have hbits : (current :: remainingRev).reverse = bits := by
        rw [← hrev]
        simp
      have hlen : bits.length = remainingRev.length + 1 := by
        have h := congrArg List.length hrev
        simpa using h
      have hfuel :
          fuel bits = 1 + ((remainingRev.length + 1) + 1) := by
        simp [fuel, hlen]
        lia
      rw [hfuel]
      rw [Description.runConfig_add]
      simp only [sourceTape, hrev, List.map_cons, List.append_eq,
        List.cons_append]
      apply Eq.trans
        (congrArg (description.runConfig (remainingRev.length + 1 + 1))
          (enter_step baseLeft remainingRev current rightPadding T1 T2))
      rw [Description.runConfig_add]
      rw [rewind_run]
      rw [show List.append remainingRev.reverse [current] = bits by
        simpa using hbits]
      exact finish_step baseLeft bits rightPadding T1 T2

end Tape0RewindPadded

def loweredTape0RewindDescription : MachineDescription :=
  lowerStructured3Description Tape0RewindPadded.description

theorem loweredTape0RewindDescription_ready :
    loweredTape0RewindDescription.SubroutineReady := by
  simpa [loweredTape0RewindDescription] using
    lowerStructured3Description_subroutineReady
      Tape0RewindPadded.ready.left Tape0RewindPadded.supports
theorem loweredTape0RewindDescription_realizes
    (baseLeft : List (Option Bool)) (bits : List Bool)
    (rightPadding : List (Option Bool)) (T2 : Tape Bool) :
    loweredTape0RewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (Tape0RewindPadded.sourceTape baseLeft bits rightPadding)
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (Tape0RewindPadded.targetTape baseLeft bits rightPadding)
        Tape.blank T2) := by
  simpa [loweredTape0RewindDescription,
    encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      Tape0RewindPadded.ready.left Tape0RewindPadded.ready.right
      Tape0RewindPadded.supports
      (c := config Tape0RewindPadded.enter
        (Tape0RewindPadded.sourceTape baseLeft bits rightPadding)
        Tape.blank T2)
      (tapes := [ Tape0RewindPadded.targetTape baseLeft bits rightPadding
        , Tape.blank, T2 ])
      rfl rfl ⟨Tape0RewindPadded.fuel bits,
        Tape0RewindPadded.run baseLeft bits rightPadding Tape.blank T2⟩

def acceptRightPadding (L : DovetailLayout) : List (Option Bool) :=
  List.replicate ((acceptBits L).length + 6) (none : Option Bool)

def rewoundSourceTape0 (L : DovetailLayout) : Tape Bool :=
  Tape0RewindPadded.targetTape [] (sourceWord true L)
    (acceptRightPadding L)
theorem afterAllocatorTape0_eq_rewindSource (L : DovetailLayout) :
    afterAllocatorTape0 L =
      Tape0RewindPadded.sourceTape [] (sourceWord true L)
        (acceptRightPadding L) := by
  rfl

theorem tape0Rewind_realizes (L : DovetailLayout) :
    loweredTape0RewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterAllocatorTape0 L) Tape.blank (afterAllocatorTape2 L))
      (encodedGuardedStructured3Tapes
        (rewoundSourceTape0 L) Tape.blank (afterAllocatorTape2 L)) := by
  rw [afterAllocatorTape0_eq_rewindSource]
  exact loweredTape0RewindDescription_realizes [] (sourceWord true L)
    (acceptRightPadding L) (afterAllocatorTape2 L)

def outerMarkerScanCount (L : DovetailLayout) : Nat :=
  (ParsedLayoutBits L).length + (driverPrefixBits L).length + 2
def outerMarkerRight (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate (allocatorCount L) (none : Option Bool))
    (some false :: delimiterRightTail L)

def outerMarkerScanSourceTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (outerMarkerScanCount L) (none : Option Bool))
      [some true])
    (none :: outerMarkerRight L)

theorem outerMarkerLeft_shape
    (p d : Nat) (hp : 0 < p) :
    List.append (List.replicate d (none : Option Bool))
        (none :: none ::
          List.append (List.replicate (p - 1) none) [some true]) =
      List.append (List.replicate (p + d + 1) none) [some true] := by
  cases p with
  | zero => simp at hp
  | succ p =>
      simp only [Nat.add_sub_cancel]
      rw [show none ::
            List.append (List.replicate p (none : Option Bool)) [some true] =
          List.append (List.replicate (p + 1) none) [some true] by
        rw [List.replicate_succ]
        rfl]
      rw [replicate_none_append_none_marked]
      congr 2
      lia
theorem afterAllocatorTape2_eq_outerMarkerSource (L : DovetailLayout) :
    afterAllocatorTape2 L = outerMarkerScanSourceTape2 L := by
  unfold afterAllocatorTape2 outerMarkerScanSourceTape2
    outerMarkerScanCount outerMarkerRight delimiterMarkerBase
    allocatorCount
  rw [counterBaseTail_eq_marked_replicate]
  have hpos : 0 < (ParsedLayoutBits L).length := by
    rw [parsedLayoutBits_fieldDecomp]
    simp [transitionPrefixBits_length]
    lia
  congr 1
  exact outerMarkerLeft_shape _ _ hpos

def afterOuterMarkerScanTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append
        (List.replicate (outerMarkerScanCount L + 1)
          (none : Option Bool))
        (outerMarkerRight L))

theorem outerMarkerScan_realizes (L : DovetailLayout) :
    MarkerScanLowered.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundSourceTape0 L) Tape.blank (outerMarkerScanSourceTape2 L))
      (encodedGuardedStructured3Tapes
        (rewoundSourceTape0 L) Tape.blank (afterOuterMarkerScanTape2 L)) := by
  simpa [outerMarkerScanSourceTape2, afterOuterMarkerScanTape2] using
    MarkerScanLowered.loweredDescription_realizes
      (outerMarkerScanCount L) (rewoundSourceTape0 L)
      ([] : List (Option Bool)) (outerMarkerRight L)
def finalOutputTape2 (L : DovetailLayout) : Tape Bool :=
  keepR.apply (afterOuterMarkerScanTape2 L)

theorem moveRightAfterOuter_realizes (L : DovetailLayout) :
    moveRightOneDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundSourceTape0 L) Tape.blank (afterOuterMarkerScanTape2 L))
      (encodedGuardedStructured3Tapes
        (rewoundSourceTape0 L) Tape.blank (finalOutputTape2 L)) := by
  exact moveRightOneDescription_realizes
    (rewoundSourceTape0 L) (afterOuterMarkerScanTape2 L)

theorem keepR_tapeAtCells_nil_none
    (right : List (Option Bool)) :
    keepR.apply (tapeAtCells [] (none :: right)) =
      tapeAtCells [none] right := by
  cases right <;> rfl
theorem finalOutputTape2_shape (L : DovetailLayout) :
    finalOutputTape2 L =
      tapeAtCells [none]
        (List.append
          (List.replicate
            ((ParsedLayoutBits L).length + (driverPrefixBits L).length +
              (acceptBits L).length + 8)
            (none : Option Bool))
          (List.append ((keptLiveBits L).map some)
            (none :: List.replicate 5 (none : Option Bool)))) := by
  have hkept :
      some false ::
          List.append ((keptLiveTailBits L).map some)
            (none :: liveRewindPadding) =
        List.append ((keptLiveBits L).map some)
          (none :: liveRewindPadding) := by
    rw [keptLiveBits_cons_false]
    rfl
  have hblank :
      List.append
          (List.replicate
            ((ParsedLayoutBits L).length + (driverPrefixBits L).length +
              2 + 1)
            (none : Option Bool))
          (List.replicate ((acceptBits L).length + 5) none) =
        List.replicate
          ((ParsedLayoutBits L).length + (driverPrefixBits L).length +
            (acceptBits L).length + 8)
          none := by
    rw [replicate_none_append_replicate]
    congr 1
    lia
  unfold finalOutputTape2 afterOuterMarkerScanTape2 outerMarkerRight
    outerMarkerScanCount allocatorCount delimiterRightTail
  rw [keepR_tapeAtCells_nil_none]
  have hkept' :
      some false ::
          List.append ((keptLiveTailBits L).map some)
            (none :: List.replicate 5 (none : Option Bool)) =
        List.append ((keptLiveBits L).map some)
          (none :: List.replicate 5 (none : Option Bool)) := by
    simpa [liveRewindPadding] using hkept
  apply Eq.trans
    (congrArg (tapeAtCells [none])
      (List.append_assoc
        (List.replicate
          ((ParsedLayoutBits L).length + (driverPrefixBits L).length +
            2 + 1) (none : Option Bool))
        (List.replicate ((acceptBits L).length + 5) none)
        (some false ::
          List.append ((keptLiveTailBits L).map some)
            (none :: liveRewindPadding))).symm)
  apply Eq.trans
    (congrArg (tapeAtCells [none])
      (congrArg
        (fun xs => List.append xs
          (some false ::
            List.append ((keptLiveTailBits L).map some)
              (none :: liveRewindPadding)))
        hblank))
  simpa [liveRewindPadding] using
    congrArg (tapeAtCells [none])
      (congrArg
        (List.append
          (List.replicate
            ((ParsedLayoutBits L).length + (driverPrefixBits L).length +
              (acceptBits L).length + 8)
            (none : Option Bool)))
        hkept')

theorem publicTarget_shape (L : DovetailLayout) :
    structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
        (ParsedLayoutBits L).length
        (postFieldDecodedPrefixScanPadding true L) =
      tapeAtCells [none]
        (List.append
          (List.replicate
            ((ParsedLayoutBits L).length + (driverPrefixBits L).length +
              (acceptBits L).length + 8)
            (none : Option Bool))
          (List.append ((keptLiveBits L).map some)
            (none :: List.replicate 5 (none : Option Bool)))) := by
  have hblank :
      (selectedProjectionPaddedTailCleanupScratchCountBits true L).length +
          2 =
        (driverPrefixBits L).length + (acceptBits L).length + 8 := by
    rw [← directScratchBlankDriverBits_length true L]
    simp [directScratchBlankDriverBits, driverPrefixBits_eq_inputStageBits,
      inputStageBits, acceptBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      boolFieldBits_nil_length]
    lia
  have hprefix :
      List.append
          (List.replicate ((ParsedLayoutBits L).length + 1)
            (none : Option Bool))
          (none ::
            List.replicate
              (selectedProjectionPaddedTailCleanupScratchCountBits
                true L).length
              none) =
        List.replicate
          ((ParsedLayoutBits L).length + (driverPrefixBits L).length +
            (acceptBits L).length + 8)
          none := by
    rw [show none ::
          List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits
              true L).length (none : Option Bool) =
        List.replicate
          ((selectedProjectionPaddedTailCleanupScratchCountBits
            true L).length + 1) none by
      rw [List.replicate_succ]]
    rw [replicate_none_append_replicate]
    congr 1
    lia
  have hlive :
      List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).map some)
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedConfigBits
              true L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L).map some)
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  true L).map some)
                (none :: List.replicate 5 (none : Option Bool))))) =
        List.append ((keptLiveBits L).map some)
          (none :: List.replicate 5 (none : Option Bool)) := by
    simp [keptLiveBits, acceptBits, rejectBits, acceptHitBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      List.map_append, List.append_assoc]
  rw [postFieldDecodedPrefixScanPadding_accept_decomp]
  unfold structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
  apply Eq.trans
    (congrArg (tapeAtCells [none])
      (List.append_assoc
        (List.replicate ((ParsedLayoutBits L).length + 1)
          (none : Option Bool))
        (none ::
          List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits
              true L).length none)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).map some)
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedConfigBits
              true L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L).map some)
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  true L).map some)
                (none :: List.replicate 5 (none : Option Bool))))))).symm)
  apply Eq.trans
    (congrArg (tapeAtCells [none])
      (congrArg
        (fun xs => List.append xs
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedConfigBits
                true L).map some)
              (List.append
                ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  true L).map some)
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    true L).map some)
                  (none :: List.replicate 5 (none : Option Bool)))))))
        hprefix))
  exact congrArg (tapeAtCells [none])
    (congrArg
      (List.append
        (List.replicate
          ((ParsedLayoutBits L).length + (driverPrefixBits L).length +
            (acceptBits L).length + 8)
          (none : Option Bool)))
      hlive)

theorem finalOutputTape2_eq_publicTarget (L : DovetailLayout) :
    finalOutputTape2 L =
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
        (ParsedLayoutBits L).length
        (postFieldDecodedPrefixScanPadding true L) := by
  rw [finalOutputTape2_shape, publicTarget_shape]

end AcceptFinalTail
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
