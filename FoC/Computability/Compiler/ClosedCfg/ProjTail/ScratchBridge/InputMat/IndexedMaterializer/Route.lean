import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.ShapesInsert
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.TokenNav
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.PrefixPipeline

set_option doc.verso true

/-!
Composed token route from the decoded prefix to the branch handoff.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver

namespace OutputOriginMarker

def start : Nat := 0
def mark : Nat := 1
def halt : Nat := 2

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action2 : CommonGround.FiniteTransducers.Structured.TapeAction)
    (target : Nat) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 keepS keepS action2 target

abbrev rowsForRead := rowsForTape2Read
def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  [ rowsForTape2Read start none keepL mark
  , rowsForTape2Read start (some false) keepL mark
  , rowsForTape2Read start (some true) keepL mark
  , rowsForTape2Read mark none (writeR (some true)) halt
  , rowsForTape2Read mark (some false) (writeR (some true)) halt
  , rowsForTape2Read mark (some true) (writeR (some true)) halt ].flatten

def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 3 start halt rows

theorem run
    (T0 T1 : Tape Bool) (bits : List Bool) :
    description.runConfig 2
        (config start T0 T1
          (AcceptConfigInserter.scanTape [none] bits)) =
      config halt T0 T1
        (AcceptConfigInserter.scanTape [some true] bits) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          cases bits with
          | nil =>
              three_tape_step [description, rows, rowsForRead, rowsForTape2Read,
                start, mark, halt, allReads3, allReads2, allReadCells,
                List.find?, AcceptConfigInserter.scanTape,
                tapeAtCells, h0, h1]
          | cons bit bits => cases bit <;>
              three_tape_step [description, rows, rowsForRead, rowsForTape2Read,
                start, mark, halt, allReads3, allReads2, allReadCells,
                List.find?, AcceptConfigInserter.scanTape,
                tapeAtCells, h0, h1]
      | some bit1 => cases bit1 <;>
          cases bits with
          | nil =>
              three_tape_step [description, rows, rowsForRead, rowsForTape2Read,
                start, mark, halt, allReads3, allReads2, allReadCells,
                List.find?, AcceptConfigInserter.scanTape,
                tapeAtCells, h0, h1]
          | cons bit bits => cases bit <;>
              three_tape_step [description, rows, rowsForRead, rowsForTape2Read,
                start, mark, halt, allReads3, allReads2, allReadCells,
                List.find?, AcceptConfigInserter.scanTape,
                tapeAtCells, h0, h1]
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none =>
          cases bits with
          | nil =>
              three_tape_step [description, rows, rowsForRead, rowsForTape2Read,
                start, mark, halt, allReads3, allReads2, allReadCells,
                List.find?, AcceptConfigInserter.scanTape,
                tapeAtCells, h0, h1]
          | cons bit bits => cases bit <;>
              three_tape_step [description, rows, rowsForRead, rowsForTape2Read,
                start, mark, halt, allReads3, allReads2, allReadCells,
                List.find?, AcceptConfigInserter.scanTape,
                tapeAtCells, h0, h1]
      | some bit1 => cases bit1 <;>
          cases bits with
          | nil =>
              three_tape_step [description, rows, rowsForRead, rowsForTape2Read,
                start, mark, halt, allReads3, allReads2, allReadCells,
                List.find?, AcceptConfigInserter.scanTape,
                tapeAtCells, h0, h1]
          | cons bit bits => cases bit <;>
              three_tape_step [description, rows, rowsForRead, rowsForTape2Read,
                start, mark, halt, allReads3, allReads2, allReadCells,
                List.find?, AcceptConfigInserter.scanTape,
                tapeAtCells, h0, h1]

end OutputOriginMarker
def outputOriginMarkerDescription : MachineDescription :=
  lowerStructured3Description OutputOriginMarker.description

theorem outputOriginMarker_ready :
    OutputOriginMarker.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    OutputOriginMarker.description (by decide)

theorem outputOriginMarker_supports :
    SupportsReadWriteRows3 OutputOriginMarker.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem outputOriginMarkerDescription_subroutineReady :
    outputOriginMarkerDescription.SubroutineReady := by
  simpa [outputOriginMarkerDescription] using
    lowerStructured3Description_subroutineReady
      outputOriginMarker_ready.left outputOriginMarker_supports

theorem outputOriginMarkerDescription_realizes
    (T0 : Tape Bool) (bits : List Bool) :
    outputOriginMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (AcceptConfigInserter.scanTape [none] bits))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (AcceptConfigInserter.scanTape [some true] bits)) := by
  simpa [outputOriginMarkerDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      outputOriginMarker_ready.left outputOriginMarker_ready.right
      outputOriginMarker_supports
      (c := config OutputOriginMarker.start T0 Tape.blank
        (AcceptConfigInserter.scanTape [none] bits))
      (tapes :=
        [T0, Tape.blank,
          AcceptConfigInserter.scanTape [some true] bits])
      rfl rfl ⟨2, OutputOriginMarker.run T0 Tape.blank bits⟩

def positionLoweredDescription : MachineDescription :=
  lowerStructured3Description AcceptConfigInserter.description
theorem positionLoweredDescription_subroutineReady :
    positionLoweredDescription.SubroutineReady := by
  simpa [positionLoweredDescription] using
    lowerStructured3Description_subroutineReady
      AcceptConfigInserter.description_subroutineReady.left
      AcceptConfigInserter.description_supports

theorem positionLoweredDescription_realizes_with_outputBase
    (bits suffixTail outputRest : Word Bool) (stage : Nat)
    (outputBase : List (Option Bool)) :
    positionLoweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape bits suffixTail [])
        Tape.blank
        (AcceptConfigInserter.scanTape outputBase
          (List.append bits
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              outputRest))))
      (encodedGuardedStructured3Tapes
        (AcceptConfigInserter.sourceCellStartTape
          bits.length bits suffixTail)
        Tape.blank
        (AcceptConfigInserter.scanTape
          (List.append
            (List.replicate bits.length (none : Option Bool)) outputBase)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            outputRest))) := by
  simpa [positionLoweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      AcceptConfigInserter.description_subroutineReady.left
      AcceptConfigInserter.description_subroutineReady.right
      AcceptConfigInserter.description_supports
      (c := ThreeTape.config AcceptConfigInserter.rewind
        (structuredBoolWordRawBitsDecoderSourceTargetTape bits suffixTail [])
        Tape.blank
        (AcceptConfigInserter.scanTape outputBase
          (List.append bits
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              outputRest))))
      (tapes :=
        [ AcceptConfigInserter.sourceCellStartTape
            bits.length bits suffixTail
        , Tape.blank
        , AcceptConfigInserter.scanTape
            (List.append
              (List.replicate bits.length (none : Option Bool)) outputBase)
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              outputRest) ])
      rfl rfl
      ⟨AcceptConfigInserter.positionFuel bits,
        AcceptConfigInserter.position_erase_run_with_outputBase
          bits suffixTail outputRest stage outputBase⟩

def acceptOutputRest (L : DovetailLayout) : Word Bool :=
  List.append (configurationFieldBits L.rejectConfig [])
    (selectedProjectionPaddedTailCleanupSelectedHitBits true L)
def rejectOutputRest (L : DovetailLayout) : Word Bool :=
  configurationFieldBits L.rejectConfig []

def postPositionTape0
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  AcceptConfigInserter.sourceCellStartTape
    (ParsedLayoutBits L).length
    (ParsedLayoutBits L)
    (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)

def postPositionTape2
    (outputRest : Word Bool) (L : DovetailLayout) : Tape Bool :=
  AcceptConfigInserter.scanTape
    (List.append
      (List.replicate (ParsedLayoutBits L).length (none : Option Bool))
      [some true])
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage)
      outputRest)
def acceptMarkedPrefixDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    embeddedPrefixDescription outputOriginMarkerDescription

theorem acceptMarkedPrefixDescription_subroutineReady :
    acceptMarkedPrefixDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    embeddedPrefixDescription_subroutineReady
    outputOriginMarkerDescription_subroutineReady

def acceptPositionDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    acceptMarkedPrefixDescription positionLoweredDescription
theorem acceptPositionDescription_subroutineReady :
    acceptPositionDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    acceptMarkedPrefixDescription_subroutineReady
    positionLoweredDescription_subroutineReady

theorem outputOriginMarkerDescription_realizes_accept (L : DovetailLayout) :
    outputOriginMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail true L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (copiedDataWord true L) []))
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail true L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [some true]
          (copiedDataWord true L) [])) := by
  simpa [rightEdgeScanSourceTapeFromLeft,
    AcceptConfigInserter.scanTape] using
    outputOriginMarkerDescription_realizes
      (structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail true L) [])
      (copiedDataWord true L)

theorem positionLoweredDescription_realizes_accept (L : DovetailLayout) :
    positionLoweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail true L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [some true]
          (copiedDataWord true L) []))
      (encodedGuardedStructured3Tapes
        (postPositionTape0 true L) Tape.blank
        (postPositionTape2 (acceptOutputRest L) L)) := by
  simpa [copiedDataWord_accept_decomp, acceptOutputRest,
      postPositionTape0, postPositionTape2,
      rightEdgeScanSourceTapeFromLeft,
      AcceptConfigInserter.scanTape] using
    positionLoweredDescription_realizes_with_outputBase
      (ParsedLayoutBits L)
      (countWindowPostFieldDecodedPrefixStructuredSuffixTail true L)
      (acceptOutputRest L) L.stage [some true]
theorem acceptPositionDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput true) :
    acceptPositionDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        true input)
      (encodedGuardedStructured3Tapes
        (postPositionTape0 true input.L) Tape.blank
        (postPositionTape2 (acceptOutputRest input.L) input.L)) := by
  have hp := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    embeddedPrefixDescription_subroutineReady
    outputOriginMarkerDescription_subroutineReady
    (embeddedPrefixDescription_haltsFromTapeEquiv_accept input)
    (outputOriginMarkerDescription_realizes_accept input.L)
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    acceptMarkedPrefixDescription_subroutineReady
    positionLoweredDescription_subroutineReady
    hp
    (positionLoweredDescription_realizes_accept input.L)
  simpa [acceptPositionDescription, acceptMarkedPrefixDescription] using h

def rejectMarkedPrefixDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    rejectPrefixDescription outputOriginMarkerDescription

theorem rejectMarkedPrefixDescription_subroutineReady :
    rejectMarkedPrefixDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    rejectPrefixDescription_subroutineReady
    outputOriginMarkerDescription_subroutineReady
def rejectPositionDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    rejectMarkedPrefixDescription positionLoweredDescription

theorem rejectPositionDescription_subroutineReady :
    rejectPositionDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    rejectMarkedPrefixDescription_subroutineReady
    positionLoweredDescription_subroutineReady

theorem outputOriginMarkerDescription_realizes_reject (L : DovetailLayout) :
    outputOriginMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail false L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (copiedDataWord false L) []))
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail false L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [some true]
          (copiedDataWord false L) [])) := by
  simpa [rightEdgeScanSourceTapeFromLeft,
    AcceptConfigInserter.scanTape] using
    outputOriginMarkerDescription_realizes
      (structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail false L) [])
      (copiedDataWord false L)
theorem positionLoweredDescription_realizes_reject (L : DovetailLayout) :
    positionLoweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail false L)
          [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [some true]
          (copiedDataWord false L) []))
      (encodedGuardedStructured3Tapes
        (postPositionTape0 false L) Tape.blank
        (postPositionTape2 (rejectOutputRest L) L)) := by
  simpa [copiedDataWord_reject_decomp, rejectOutputRest,
      postPositionTape0, postPositionTape2,
      rightEdgeScanSourceTapeFromLeft,
      AcceptConfigInserter.scanTape] using
    positionLoweredDescription_realizes_with_outputBase
      (ParsedLayoutBits L)
      (countWindowPostFieldDecodedPrefixStructuredSuffixTail false L)
      (rejectOutputRest L) L.stage [some true]

theorem rejectPositionDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput false) :
    rejectPositionDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (postPositionTape0 false input.L) Tape.blank
        (postPositionTape2 (rejectOutputRest input.L) input.L)) := by
  have hp := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    rejectPrefixDescription_subroutineReady
    outputOriginMarkerDescription_subroutineReady
    (rejectPrefixDescription_haltsFromTapeEquiv input)
    (outputOriginMarkerDescription_realizes_reject input.L)
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    rejectMarkedPrefixDescription_subroutineReady
    positionLoweredDescription_subroutineReady
    hp
    (positionLoweredDescription_realizes_reject input.L)
  simpa [rejectPositionDescription, rejectMarkedPrefixDescription] using h

theorem wrappedBits_append
    (a b : List Bool) :
    AcceptConfigCopy.wrappedBits (List.append a b) =
      List.append (AcceptConfigCopy.wrappedBits a)
        (AcceptConfigCopy.wrappedBits b) :=
  PrimaryRewind.wrappedBits_append a b
theorem wrappedBits_transitionPrefixBits :
    AcceptConfigCopy.wrappedBits transitionPrefixBits =
      wrappedKind .transition := by
  rfl

theorem wrappedBits_stageNatBits (n : Nat) :
    AcceptConfigCopy.wrappedBits
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          n) =
      Components.wrappedNatTokens n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl]
      change
        List.append (wrappedRawBit false)
          (List.append (wrappedRawBit false)
            (List.append (wrappedRawBit true)
              (List.append (wrappedRawBit false)
                (AcceptConfigCopy.wrappedBits
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    n))))) = _
      rw [ih]
      rw [← wrappedKind_tick_append (Components.wrappedNatTokens n)]
      rfl

theorem wrappedBits_cellsCodeBits_map_some (bits : List Bool) :
    AcceptConfigCopy.wrappedBits (cellsCodeBits (bits.map some)) =
      Components.wrappedCellTokens bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit with
      | false =>
          change
            AcceptConfigCopy.wrappedBits
                (List.append (cellCodeBits (some false))
                  (cellsCodeBits (bits.map some))) =
              List.append (wrappedKind .zero)
                (Components.wrappedCellTokens bits)
          rw [wrappedBits_append, ih]
          rfl
      | true =>
          change
            AcceptConfigCopy.wrappedBits
                (List.append (cellCodeBits (some true))
                  (cellsCodeBits (bits.map some))) =
              List.append (wrappedKind .one)
                (Components.wrappedCellTokens bits)
          rw [wrappedBits_append, ih]
          rfl
theorem wrappedBits_boolWordFieldBits (bits : List Bool) :
    AcceptConfigCopy.wrappedBits (boolWordFieldBits bits []) =
      List.append (Components.wrappedNatTokens bits.length)
        (Components.wrappedCellTokens bits) := by
  rw [boolWordFieldBits, cellListFieldBits]
  rw [wrappedBits_append, wrappedBits_append]
  rw [wrappedBits_stageNatBits, wrappedBits_cellsCodeBits_map_some]
  simp [AcceptConfigCopy.wrappedBits]

def driverPrefixBits (L : DovetailLayout) : Word Bool :=
  List.append (boolWordFieldBits L.input []).tail
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)

theorem driverPrefixBits_length (L : DovetailLayout) :
    (driverPrefixBits L).length =
      8 * L.input.length + 4 * L.stage + 7 := by
  have hinput := boolWordFieldBits_nil_length L.input
  have hpos : 0 < (boolWordFieldBits L.input []).length := by
    rw [hinput]
    lia
  simp [driverPrefixBits,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length]
  rw [hinput]
  lia
def loweredHeaderDescription : MachineDescription :=
  lowerStructured3Description Components.headerDescription

def loweredFirstDescription : MachineDescription :=
  lowerStructured3Description Components.firstDescription

def loweredLengthDescription : MachineDescription :=
  lowerStructured3Description Components.lengthDescription
def loweredCellsDescription : MachineDescription :=
  lowerStructured3Description Components.cellsDescription

theorem headerDescription_subroutineReady :
    Components.headerDescription.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    Components.headerDescription (by decide)

theorem headerDescription_supports :
    SupportsReadWriteRows3 Components.headerDescription :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem firstDescription_subroutineReady :
    Components.firstDescription.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    Components.firstDescription (by decide)

theorem firstDescription_supports :
    SupportsReadWriteRows3 Components.firstDescription :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem lengthDescription_subroutineReady :
    Components.lengthDescription.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    Components.lengthDescription (by decide)
theorem lengthDescription_supports :
    SupportsReadWriteRows3 Components.lengthDescription :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem cellsDescription_subroutineReady :
    Components.cellsDescription.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    Components.cellsDescription (by decide)

theorem cellsDescription_supports :
    SupportsReadWriteRows3 Components.cellsDescription :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem loweredHeaderDescription_subroutineReady :
    loweredHeaderDescription.SubroutineReady := by
  simpa [loweredHeaderDescription] using
    lowerStructured3Description_subroutineReady
      headerDescription_subroutineReady.left headerDescription_supports

theorem loweredFirstDescription_subroutineReady :
    loweredFirstDescription.SubroutineReady := by
  simpa [loweredFirstDescription] using
    lowerStructured3Description_subroutineReady
      firstDescription_subroutineReady.left firstDescription_supports

theorem loweredLengthDescription_subroutineReady :
    loweredLengthDescription.SubroutineReady := by
  simpa [loweredLengthDescription] using
    lowerStructured3Description_subroutineReady
      lengthDescription_subroutineReady.left lengthDescription_supports
theorem loweredCellsDescription_subroutineReady :
    loweredCellsDescription.SubroutineReady := by
  simpa [loweredCellsDescription] using
    lowerStructured3Description_subroutineReady
      cellsDescription_subroutineReady.left cellsDescription_supports

theorem loweredFirstDescription_tick
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    loweredFirstDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (wrappedKind .tick) rest)) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append ((wrappedKind .tick).reverse.map some) left) rest)
        Tape.blank
        (Components.markCurrent false (Components.eraseRight 2 T2))) := by
  simpa [loweredFirstDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      firstDescription_subroutineReady.left
      firstDescription_subroutineReady.right
      firstDescription_supports
      (c := config 0
        (scanTape left (List.append (wrappedKind .tick) rest))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append ((wrappedKind .tick).reverse.map some) left) rest
        , Tape.blank
        , Components.markCurrent false (Components.eraseRight 2 T2) ])
      rfl rfl ⟨16, Components.first_tick_run left rest T2⟩

theorem loweredFirstDescription_done
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    loweredFirstDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (wrappedKind .done) rest)) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append ((wrappedKind .done).reverse.map some) left) rest)
        Tape.blank
        (Components.markCurrent true (Components.eraseRight 2 T2))) := by
  simpa [loweredFirstDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      firstDescription_subroutineReady.left
      firstDescription_subroutineReady.right
      firstDescription_supports
      (c := config 0
        (scanTape left (List.append (wrappedKind .done) rest))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append ((wrappedKind .done).reverse.map some) left) rest
        , Tape.blank
        , Components.markCurrent true (Components.eraseRight 2 T2) ])
      rfl rfl ⟨16, Components.first_done_run left rest T2⟩
theorem loweredLengthDescription_after_tick
    (n : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    loweredLengthDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (Components.wrappedNatTokens n) rest)) Tape.blank
        (Components.markCurrent false T2))
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((Components.wrappedNatTokens n).reverse.map some) left)
          rest)
        Tape.blank
        (Components.eraseRight (1 + Components.natOutputCount n) T2)) := by
  simpa [loweredLengthDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      lengthDescription_subroutineReady.left
      lengthDescription_subroutineReady.right
      lengthDescription_supports
      (c := config Components.dispatch
        (scanTape left (List.append (Components.wrappedNatTokens n) rest))
        Tape.blank (Components.markCurrent false T2))
      (tapes :=
        [ scanTape
            (List.append
              ((Components.wrappedNatTokens n).reverse.map some) left)
            rest
        , Tape.blank
        , Components.eraseRight (1 + Components.natOutputCount n) T2 ])
      rfl rfl
      ⟨1 + Components.natFuel n,
        Components.length_after_first_tick_run n left rest T2⟩

theorem loweredLengthDescription_after_done
    (T0 T2 : Tape Bool) :
    loweredLengthDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        T0 Tape.blank (Components.markCurrent true T2))
      (encodedGuardedStructured3Tapes
        T0 Tape.blank (Components.eraseRight 1 T2)) := by
  simpa [loweredLengthDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      lengthDescription_subroutineReady.left
      lengthDescription_subroutineReady.right
      lengthDescription_supports
      (c := config Components.dispatch T0 Tape.blank
        (Components.markCurrent true T2))
      (tapes := [T0, Tape.blank, Components.eraseRight 1 T2])
      rfl rfl ⟨1, Components.length_after_first_done_run T0 T2⟩

theorem natOutputCount_eq (n : Nat) :
    Components.natOutputCount n = 4 * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Components.natOutputCount, ih]
      lia
theorem eraseRight_comp (m n : Nat) (T : Tape Bool) :
    Components.eraseRight m (Components.eraseRight n T) =
      Components.eraseRight (n + m) T := by
  exact (Components.eraseRight_add n m T).symm

def loweredNatDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    loweredFirstDescription loweredLengthDescription

theorem loweredNatDescription_subroutineReady :
    loweredNatDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    loweredFirstDescription_subroutineReady
    loweredLengthDescription_subroutineReady
theorem loweredNatDescription_realizes
    (n : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    loweredNatDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (Components.wrappedNatTokens n) rest))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((Components.wrappedNatTokens n).reverse.map some) left)
          rest)
        Tape.blank
        (Components.eraseRight (4 * n + 3) T2)) := by
  cases n with
  | zero =>
      have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        loweredFirstDescription_subroutineReady
        loweredLengthDescription_subroutineReady
        (loweredFirstDescription_done left rest T2)
        (loweredLengthDescription_after_done
          (scanTape
            (List.append ((wrappedKind .done).reverse.map some) left) rest)
          (Components.eraseRight 2 T2))
      simpa [loweredNatDescription, Components.wrappedNatTokens,
        eraseRight_comp] using h
  | succ n =>
      let left' :=
        List.append ((wrappedKind .tick).reverse.map some) left
      let rest' :=
        List.append (Components.wrappedNatTokens n) rest
      have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        loweredFirstDescription_subroutineReady
        loweredLengthDescription_subroutineReady
        (loweredFirstDescription_tick left rest' T2)
        (loweredLengthDescription_after_tick n left' rest
          (Components.eraseRight 2 T2))
      have hcount : 2 + (1 + 4 * (n + 1)) = 4 * (n + 1) + 3 := by
        lia
      simpa [loweredNatDescription, Components.wrappedNatTokens,
        left', rest', natOutputCount_eq, eraseRight_comp, hcount,
        List.reverse_append, List.map_append, List.append_assoc] using h

theorem cellOutputCount_eq (bits : List Bool) :
    Components.cellOutputCount bits = 4 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp [Components.cellOutputCount, ih]
      lia

theorem loweredCellsDescription_then_tick
    (bits : List Bool) (left : List (Option Bool))
    (rest : List Bool) (T2 : Tape Bool) :
    loweredCellsDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (wrappedKind .tick) rest))) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (wrappedKind .tick)).reverse.map some)
            left)
          rest)
        Tape.blank
        (Components.markCurrent false
          (Components.eraseRight
            (Components.cellOutputCount bits + 3) T2))) := by
  simpa [loweredCellsDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      cellsDescription_subroutineReady.left
      cellsDescription_subroutineReady.right
      cellsDescription_supports
      (c := config 0
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (wrappedKind .tick) rest))) Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append
              ((List.append (Components.wrappedCellTokens bits)
                (wrappedKind .tick)).reverse.map some)
              left)
            rest
        , Tape.blank
        , Components.markCurrent false
            (Components.eraseRight
              (Components.cellOutputCount bits + 3) T2) ])
      rfl rfl
      ⟨Components.cellFuel bits + 16,
        Components.cells_then_tick_run bits left rest T2⟩
theorem loweredCellsDescription_then_done
    (bits : List Bool) (left : List (Option Bool))
    (rest : List Bool) (T2 : Tape Bool) :
    loweredCellsDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (wrappedKind .done) rest))) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (wrappedKind .done)).reverse.map some)
            left)
          rest)
        Tape.blank
        (Components.markCurrent true
          (Components.eraseRight
            (Components.cellOutputCount bits + 3) T2))) := by
  simpa [loweredCellsDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      cellsDescription_subroutineReady.left
      cellsDescription_subroutineReady.right
      cellsDescription_supports
      (c := config 0
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (wrappedKind .done) rest))) Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append
              ((List.append (Components.wrappedCellTokens bits)
                (wrappedKind .done)).reverse.map some)
              left)
            rest
        , Tape.blank
        , Components.markCurrent true
            (Components.eraseRight
              (Components.cellOutputCount bits + 3) T2) ])
      rfl rfl
      ⟨Components.cellFuel bits + 16,
        Components.cells_then_done_run bits left rest T2⟩

def loweredCellsNatDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    loweredCellsDescription loweredLengthDescription

theorem loweredCellsNatDescription_subroutineReady :
    loweredCellsNatDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    loweredCellsDescription_subroutineReady
    loweredLengthDescription_subroutineReady
theorem loweredCellsNatDescription_realizes
    (bits : List Bool) (n : Nat)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    loweredCellsNatDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (Components.wrappedNatTokens n) rest)))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (Components.wrappedNatTokens n)).reverse.map some)
            left)
          rest)
        Tape.blank
        (Components.eraseRight (4 * bits.length + 4 * n + 4) T2)) := by
  cases n with
  | zero =>
      let left' :=
        List.append
          ((List.append (Components.wrappedCellTokens bits)
            (wrappedKind .done)).reverse.map some) left
      have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        loweredCellsDescription_subroutineReady
        loweredLengthDescription_subroutineReady
        (loweredCellsDescription_then_done bits left rest T2)
        (loweredLengthDescription_after_done
          (scanTape left' rest)
          (Components.eraseRight
            (Components.cellOutputCount bits + 3) T2))
      have hcount :
          Components.cellOutputCount bits + 3 + 1 =
            4 * bits.length + 4 := by
        rw [cellOutputCount_eq]
      simpa [loweredCellsNatDescription, Components.wrappedNatTokens,
        left', eraseRight_comp, hcount] using h
  | succ n =>
      let first :=
        List.append (Components.wrappedCellTokens bits)
          (wrappedKind .tick)
      let left' := List.append (first.reverse.map some) left
      let rest' := List.append (Components.wrappedNatTokens n) rest
      have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        loweredCellsDescription_subroutineReady
        loweredLengthDescription_subroutineReady
        (loweredCellsDescription_then_tick bits left rest' T2)
        (loweredLengthDescription_after_tick n left' rest
          (Components.eraseRight
            (Components.cellOutputCount bits + 3) T2))
      have hcount :
          Components.cellOutputCount bits + 3 +
              (1 + 4 * (n + 1)) =
            4 * bits.length + 4 * (n + 1) + 4 := by
        rw [cellOutputCount_eq]
        lia
      simpa [loweredCellsNatDescription, Components.wrappedNatTokens,
        first, left', rest', natOutputCount_eq, eraseRight_comp,
        hcount, List.reverse_append, List.map_append,
        List.append_assoc] using h

theorem loweredHeaderDescription_realizes
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    loweredHeaderDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (wrappedKind .transition) rest)) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append ((wrappedKind .transition).reverse.map some) left)
          rest)
        Tape.blank T2) := by
  simpa [loweredHeaderDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      headerDescription_subroutineReady.left
      headerDescription_subroutineReady.right
      headerDescription_supports
      (c := config 0
        (scanTape left (List.append (wrappedKind .transition) rest))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append
              ((wrappedKind .transition).reverse.map some) left) rest
        , Tape.blank
        , T2 ])
      rfl rfl ⟨16, Components.header_run left rest T2⟩

def configHitBits (L : DovetailLayout) : Word Bool :=
  List.append (configurationFieldBits L.acceptConfig [])
    (List.append (configurationFieldBits L.rejectConfig [])
      (List.append (boolFieldBits L.acceptHit [])
        (boolFieldBits L.rejectHit [])))
def prefixThroughStageBits (L : DovetailLayout) : Word Bool :=
  List.append transitionPrefixBits
    (List.append (boolWordFieldBits L.input [])
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage))

theorem parsedLayoutBits_eq_prefix_configHit (L : DovetailLayout) :
    ParsedLayoutBits L =
      List.append (prefixThroughStageBits L) (configHitBits L) := by
  rw [parsedLayoutBits_fieldDecomp]
  simp [prefixThroughStageBits, configHitBits, List.append_assoc]

theorem wrappedBits_eq_cellsCodeBits_map_some (bits : List Bool) :
    AcceptConfigCopy.wrappedBits bits = cellsCodeBits (bits.map some) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      change
        List.append (wrappedRawBit bit)
            (AcceptConfigCopy.wrappedBits bits) =
          List.append (cellCodeBits (some bit))
            (cellsCodeBits (bits.map some))
      rw [ih]
      simp [wrappedRawBit, cellsCodeBits]
theorem wrappedBits_prefixThroughStage (L : DovetailLayout) :
    AcceptConfigCopy.wrappedBits (prefixThroughStageBits L) =
      List.append (wrappedKind .transition)
        (List.append (Components.wrappedNatTokens L.input.length)
          (List.append (Components.wrappedCellTokens L.input)
            (Components.wrappedNatTokens L.stage))) := by
  simp only [prefixThroughStageBits]
  rw [wrappedBits_append, wrappedBits_append,
    wrappedBits_transitionPrefixBits, wrappedBits_boolWordFieldBits,
    wrappedBits_stageNatBits]
  simp [List.append_assoc]

theorem wrappedBits_parsedLayoutBits (L : DovetailLayout) :
    AcceptConfigCopy.wrappedBits (ParsedLayoutBits L) =
      List.append (wrappedKind .transition)
        (List.append (Components.wrappedNatTokens L.input.length)
          (List.append (Components.wrappedCellTokens L.input)
            (List.append (Components.wrappedNatTokens L.stage)
              (AcceptConfigCopy.wrappedBits (configHitBits L))))) := by
  rw [parsedLayoutBits_eq_prefix_configHit, wrappedBits_append,
    wrappedBits_prefixThroughStage]
  simp [List.append_assoc]

def positionTape0Left (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((List.append boolWordRawBitsDecoderHeaderBits
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        (ParsedLayoutBits L).length)).reverse.map some)
    [none]
theorem postPositionTape0_eq_scanTape
    (useAccept : Bool) (L : DovetailLayout) :
    postPositionTape0 useAccept L =
      scanTape (positionTape0Left L)
        (List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
          (false ::
            countWindowPostFieldDecodedPrefixStructuredSuffixTail
              useAccept L)) := by
  simp [postPositionTape0,
    AcceptConfigInserter.sourceCellStartTape,
    positionTape0Left, scanTape, wrappedBits_eq_cellsCodeBits_map_some,
    List.append_assoc]

def afterDriverTape0
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((AcceptConfigCopy.wrappedBits (prefixThroughStageBits L)).reverse.map
        some)
      (positionTape0Left L))
    (List.append (AcceptConfigCopy.wrappedBits (configHitBits L))
      (false ::
        countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L))

def loweredHeaderNatDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    loweredHeaderDescription loweredNatDescription
theorem loweredHeaderNatDescription_subroutineReady :
    loweredHeaderNatDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    loweredHeaderDescription_subroutineReady
    loweredNatDescription_subroutineReady

def loweredPrefixDriverDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    loweredHeaderNatDescription loweredCellsNatDescription

theorem loweredPrefixDriverDescription_subroutineReady :
    loweredPrefixDriverDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    loweredHeaderNatDescription_subroutineReady
    loweredCellsNatDescription_subroutineReady

end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
