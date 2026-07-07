import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterStructured
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option doc.verso true

/-!
# Structured live-tail quote phase

This module continues the three-logical-tape live-tail emitter construction
after the count, length-header, and rewind phases proved in
{module}`FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterStructured`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

/--
Cell-pass quoting configuration using the scratch shape left by the rewind
phase.  Tape 1 is on the blank to the right of the unary marker block, so the
cell-pass table, which reads a blank on tape 1 and leaves it untouched, can run
without clearing scratch first.
-/
def structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
    (state : Nat) (processedRev remaining : Word Bool) (markers : Nat)
    (outputBits : Word Bool) : Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
      processedRev remaining)
    (structuredMixedOptionCellQuoteLiveTailRewindScratchTape 0 markers)
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_bit
    (bit : Bool) (processedRev rest : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          0 processedRev (bit :: rest) markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        0 (bit :: processedRev) rest markers
        (List.append outputBits
          (structuredMixedOptionCellQuoteLiveTailCellChunkBits bit)) := by
  cases bit <;> cases rest <;> (try cases ‹Bool›) <;>
    simp [structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription,
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig,
      structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
      structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
      structuredMixedOptionCellQuoteLiveTailOutputTape,
      structuredMixedOptionCellQuoteLiveTailCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      structuredLiveTailCellPassInitialRow,
      structuredLiveTailCellPassWriteRows,
      structuredLiveTailCellPassWriteRow,
      structuredLiveTailCellPassHaltRow,
      structuredAnyReadRows,
      structuredPreserve, structuredWriteBit,
      Structured.MultiTapeLowering.ThreeTape.description,
      Structured.MultiTapeLowering.ThreeTape.config,
      Structured.MultiTapeLowering.ThreeTape.outputFromBits,
      Structured.Description.runConfig,
      Structured.Description.stepConfig,
      Structured.Description.lookupTransition,
      Structured.Description.Matches,
      Structured.TapeAction.stay,
      Structured.TapeAction.apply, Structured.HeadMove.apply,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      tapeAtCells, List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_done
    (processedRev : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          0 processedRev [] markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        processedRev [] markers outputBits := by
  simp [structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription,
    structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig,
    structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
    structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
    structuredMixedOptionCellQuoteLiveTailOutputTape,
    structuredLiveTailCellPassInitialRow,
    structuredLiveTailCellPassWriteRows,
    structuredLiveTailCellPassWriteRow,
    structuredLiveTailCellPassHaltRow,
    structuredAnyReadRows,
    structuredPreserve, structuredWriteBit,
    Structured.MultiTapeLowering.ThreeTape.description,
    Structured.MultiTapeLowering.ThreeTape.config,
    Structured.MultiTapeLowering.ThreeTape.outputFromBits,
    Structured.Description.runConfig,
    Structured.Description.stepConfig,
    Structured.Description.lookupTransition,
    Structured.Description.Matches,
    Structured.TapeAction.stay,
    Structured.TapeAction.apply, Structured.HeadMove.apply,
    Tape.read, tapeAtCells]

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_loop
    (processedRev remaining : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        (4 * remaining.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          0 processedRev remaining markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        (List.append remaining.reverse processedRev)
        []
        markers
        (List.append outputBits
          (preservingCellPassCellBits remaining)) := by
  induction remaining generalizing processedRev outputBits with
  | nil =>
      simpa [preservingCellPassCellBits] using
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_done
          processedRev markers outputBits
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription)
          (m := 4 * rest.length + 1)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_bit
            bit processedRev rest markers outputBits)
          ?_
      · simp
        lia
      cases bit
      · simpa [structuredMixedOptionCellQuoteLiveTailCellChunkBits,
          preservingCellPassCellBits,
          preservingCellPassZeroBits,
          preservingCellPassOneBits,
          List.append_assoc] using
          ih (false :: processedRev)
            (List.append outputBits
              (structuredMixedOptionCellQuoteLiveTailCellChunkBits false))
      · simpa [structuredMixedOptionCellQuoteLiveTailCellChunkBits,
          preservingCellPassCellBits,
          preservingCellPassZeroBits,
          preservingCellPassOneBits,
          List.append_assoc] using
          ih (true :: processedRev)
            (List.append outputBits
              (structuredMixedOptionCellQuoteLiveTailCellChunkBits true))

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind
    (bits : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        (4 * bits.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          0 [] bits markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        bits.reverse
        []
        markers
        (List.append outputBits
          (preservingCellPassCellBits bits)) := by
  simpa using
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_loop
      [] bits markers outputBits

/--
Single structured three-tape row table for the proved live-tail emitter
prefix phases.

The count+length table runs in states `0..199`, the rewind phase in
`300..399`, and the quote phase in `400..499`.  The gaps leave room for local
debug states without changing the externally named phase starts.
-/
def structuredMixedOptionCellQuoteLiveTailEmitterDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 500 0 499
    (Structured.MultiTapeLowering.ThreeTape.phaseRows 0
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
        300
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions ++
      Structured.MultiTapeLowering.ThreeTape.phaseRows 300
        structuredMixedOptionCellQuoteLiveTailRewindDescription.halt 400
        structuredMixedOptionCellQuoteLiveTailRewindDescription.transitions ++
      Structured.MultiTapeLowering.ThreeTape.offsetRows 400
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.transitions)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailEmitterDescription =
        true := by
  apply
    Structured.MultiTapeLowering.ThreeTape.description_supportsReadWriteRows3
  intro t ht
  simp at ht
  rcases ht with hcountLength | hrewind | hquote
  · exact
      Structured.MultiTapeLowering.ThreeTape.phaseRows_supportsReadWriteRow3
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_supported.rows_supported
        t hcountLength
  · exact
      Structured.MultiTapeLowering.ThreeTape.phaseRows_supportsReadWriteRow3
        structuredMixedOptionCellQuoteLiveTailRewindDescription_supported.rows_supported
        t hrewind
  · exact
      Structured.MultiTapeLowering.ThreeTape.offsetRows_supportsReadWriteRow3
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_supported.rows_supported
        t hquote

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_supportsReadWriteRows3

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_bit
    (bit : Bool) (processedRev rest : Word Bool)
    (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev (bit :: rest) markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountConfig
        0 (bit :: processedRev) rest markers.succ outputBits := by
  simpa [structuredMixedOptionCellQuoteLiveTailEmitterDescription] using
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_bit
      bit processedRev rest markers outputBits

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_done
    (processedRev : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev [] markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig
        processedRev markers outputBits := by
  simpa [structuredMixedOptionCellQuoteLiveTailEmitterDescription] using
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_done
      processedRev markers outputBits

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_loop
    (processedRev remaining : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (remaining.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev remaining markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig
        (List.append remaining.reverse processedRev)
        (markers + remaining.length)
        outputBits := by
  induction remaining generalizing processedRev markers with
  | nil =>
      simpa using
        structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_done
          processedRev markers outputBits
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
          (n := 1)
          (m := rest.length + 1)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_bit
            bit processedRev rest markers outputBits)
          ?_
      · simp [Nat.add_comm, Nat.add_left_comm]
      · have hmarkers :
            markers.succ + rest.length =
              markers + (rest.length + 1) := by
          simp [Nat.succ_eq_add_one, Nat.add_comm,
            Nat.add_left_comm]
        simpa [Nat.succ_eq_add_one, hmarkers, List.append_assoc] using
          ih (bit :: processedRev) markers.succ

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (bits.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig
        bits.reverse bits.length outputBits := by
  simpa using
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_loop
      [] bits 0 outputBits

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length_header
    (source : Tape Bool) (remaining emitted : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          100 source remaining emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        110 source remaining emitted
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailHeaderBits) := by
  cases source with
  | mk sourceLeft sourceHead sourceRight =>
      cases remaining with
      | zero =>
          cases emitted <;>
            cases sourceHead <;> (try cases ‹Bool›) <;>
              three_tape_phase_step [
                structuredMixedOptionCellQuoteLiveTailEmitterDescription,
                structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
                structuredMixedOptionCellQuoteLiveTailCountDescription,
                structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
                structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
                structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
                structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
                structuredMixedOptionCellQuoteLiveTailOutputTape,
                structuredMixedOptionCellQuoteLiveTailHeaderBits,
                structuredLiveTailCountRow,
                structuredLiveTailCountDoneRow,
                structuredLiveTailPreserveWriteOutputRows,
                structuredLiveTailPreserveWriteOutputRow,
                structuredAnySourceScratchReadRows,
                structuredLiveTailLengthMarkerRows,
                structuredLiveTailLengthFinalRows,
                structuredLiveTailWriteOutputRow,
                structuredAnyReadRows,
                structuredPreserve, structuredWriteBit,
                List.replicate_succ, List.reverse_append]
      | succ remaining =>
          cases sourceHead <;> (try cases ‹Bool›) <;>
            three_tape_phase_step [
              structuredMixedOptionCellQuoteLiveTailEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
              structuredMixedOptionCellQuoteLiveTailCountDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailHeaderBits,
              structuredLiveTailCountRow,
              structuredLiveTailCountDoneRow,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length_marker
    (remaining emitted : Nat) (source : Tape Bool)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          110 source remaining.succ emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        110 source remaining emitted.succ
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailLengthTickBits) := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          cases remaining <;>
            three_tape_phase_step [
              structuredMixedOptionCellQuoteLiveTailEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
              structuredMixedOptionCellQuoteLiveTailCountDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthTickBits,
              structuredLiveTailCountRow,
              structuredLiveTailCountDoneRow,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              List.replicate_succ,
              List.reverse_append]
      | some bit =>
          cases bit <;> cases remaining <;>
            three_tape_phase_step [
              structuredMixedOptionCellQuoteLiveTailEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
              structuredMixedOptionCellQuoteLiveTailCountDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthTickBits,
              structuredLiveTailCountRow,
              structuredLiveTailCountDoneRow,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              List.replicate_succ,
              List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length_final
    (emitted : Nat) (source : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          110 source 0 emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        300 source 0 emitted
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailLengthDoneBits) := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          three_tape_phase_step [
            structuredMixedOptionCellQuoteLiveTailEmitterDescription,
            structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
            structuredMixedOptionCellQuoteLiveTailCountDescription,
            structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
            structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
            structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
            structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
            structuredMixedOptionCellQuoteLiveTailOutputTape,
            structuredMixedOptionCellQuoteLiveTailLengthDoneBits,
            structuredLiveTailCountRow,
            structuredLiveTailCountDoneRow,
            structuredLiveTailPreserveWriteOutputRows,
            structuredLiveTailPreserveWriteOutputRow,
            structuredAnySourceScratchReadRows,
            structuredLiveTailLengthMarkerRows,
            structuredLiveTailLengthFinalRows,
            structuredLiveTailWriteOutputRow,
            structuredAnyReadRows,
            structuredPreserve, structuredWriteBit,
            List.reverse_append]
      | some bit =>
          cases bit <;>
            three_tape_phase_step [
              structuredMixedOptionCellQuoteLiveTailEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
              structuredMixedOptionCellQuoteLiveTailCountDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneBits,
              structuredLiveTailCountRow,
              structuredLiveTailCountDoneRow,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length_loop
    (remaining emitted : Nat) (source : Tape Bool)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (4 * remaining + 4)
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          110 source remaining emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        300 source 0 (emitted + remaining)
        (List.append outputBits
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            remaining)) := by
  induction remaining generalizing emitted outputBits with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length_final
          emitted source outputBits
  | succ remaining ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
          (m := 4 * remaining + 4)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length_marker
            remaining emitted source outputBits)
          ?_
      · lia
      · simpa [structuredMixedOptionCellQuoteLiveTailLengthTickBits,
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
          List.append_assoc, Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using
          ih emitted.succ
            (List.append outputBits
              structuredMixedOptionCellQuoteLiveTailLengthTickBits)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length
    (markers : Nat) (source : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (4 * markers + 8)
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          100 source markers 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        300 source 0 markers
        (List.append (List.append outputBits
            structuredMixedOptionCellQuoteLiveTailHeaderBits)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            markers)) := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
      (n := 4)
      (m := 4 * markers + 4)
      (htotal := ?_)
      (structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length_header
        source markers 0 outputBits)
      ?_
  · lia
  · simpa [Nat.zero_add] using
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length_loop
        markers 0 source
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailHeaderBits)

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRows_no_state300
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 300 [read0, read1, read2])
        (Structured.MultiTapeLowering.ThreeTape.phaseRows 0
          structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
          300
          structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions) =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state300
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 300 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 301 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state400
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 400 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state400
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 400 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              (300 +
                structuredMixedOptionCellQuoteLiveTailRewindDescription.halt)
              400 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 300)
        structuredMixedOptionCellQuoteLiveTailRewindDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state410
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 410 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state411
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 411 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state412
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 412 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state420
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 420 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state421
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 421 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state422
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 422 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
              300 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 0)
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state410
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 410 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              (300 +
                structuredMixedOptionCellQuoteLiveTailRewindDescription.halt)
              400 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 300)
        structuredMixedOptionCellQuoteLiveTailRewindDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state411
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 411 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              (300 +
                structuredMixedOptionCellQuoteLiveTailRewindDescription.halt)
              400 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 300)
        structuredMixedOptionCellQuoteLiveTailRewindDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state412
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 412 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              (300 +
                structuredMixedOptionCellQuoteLiveTailRewindDescription.halt)
              400 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 300)
        structuredMixedOptionCellQuoteLiveTailRewindDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state420
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 420 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              (300 +
                structuredMixedOptionCellQuoteLiveTailRewindDescription.halt)
              400 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 300)
        structuredMixedOptionCellQuoteLiveTailRewindDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state421
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 421 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              (300 +
                structuredMixedOptionCellQuoteLiveTailRewindDescription.halt)
              400 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 300)
        structuredMixedOptionCellQuoteLiveTailRewindDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state422
    (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches 422 [read0, read1, read2] ∘
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget
              (300 +
                structuredMixedOptionCellQuoteLiveTailRewindDescription.halt)
              400 ∘
            Structured.MultiTapeLowering.ThreeTape.offsetTransition 300)
        structuredMixedOptionCellQuoteLiveTailRewindDescription.transitions =
      none := by
  cases read0 <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        decide

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_init
    (leftRev right outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        1
        (Structured.MultiTapeLowering.ThreeTape.config 300
          (structuredMixedOptionCellQuoteLiveTailRewindSourceTape
            leftRev right)
          (structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape
            leftRev.length)
          (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        301 leftRev right 0 outputBits := by
  cases right with
  | nil =>
      three_tape_phase_step [
        structuredMixedOptionCellQuoteLiveTailEmitterDescription,
        structuredMixedOptionCellQuoteLiveTailRewindDescription,
        structuredMixedOptionCellQuoteLiveTailRewindConfig,
        structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
        structuredMixedOptionCellQuoteLiveTailRewindScratchTape_initial,
        structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
        structuredMixedOptionCellQuoteLiveTailOutputTape,
        structuredLiveTailRewindInitRow,
        structuredLiveTailRewindLoopRow,
        structuredLiveTailRewindDoneRow,
        structuredAnySourceOutputReadRows,
        structuredPreserve,
        structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state300]
  | cons bit right =>
      cases bit <;>
        three_tape_phase_step [
          structuredMixedOptionCellQuoteLiveTailEmitterDescription,
          structuredMixedOptionCellQuoteLiveTailRewindDescription,
          structuredMixedOptionCellQuoteLiveTailRewindConfig,
          structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
          structuredMixedOptionCellQuoteLiveTailRewindScratchTape_initial,
          structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
          structuredMixedOptionCellQuoteLiveTailOutputTape,
          structuredLiveTailRewindInitRow,
          structuredLiveTailRewindLoopRow,
          structuredLiveTailRewindDoneRow,
          structuredAnySourceOutputReadRows,
          structuredPreserve,
          structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state300]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_loop_step
    (bit : Bool) (leftRev right outputBits : Word Bool) (moved : Nat) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailRewindConfig
          301 (bit :: leftRev) right moved outputBits) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        301 leftRev (bit :: right) moved.succ outputBits := by
  cases leftRev <;> cases bit <;> cases right with
  | nil =>
      three_tape_phase_step [
        structuredMixedOptionCellQuoteLiveTailEmitterDescription,
        structuredMixedOptionCellQuoteLiveTailRewindDescription,
        structuredMixedOptionCellQuoteLiveTailRewindConfig,
        structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
        structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
        structuredMixedOptionCellQuoteLiveTailOutputTape,
        structuredLiveTailRewindInitRow,
        structuredLiveTailRewindLoopRow,
        structuredLiveTailRewindDoneRow,
        structuredAnySourceOutputReadRows,
        structuredPreserve,
        structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301,
        List.replicate_succ]
  | cons head tail =>
      cases head <;>
        three_tape_phase_step [
          structuredMixedOptionCellQuoteLiveTailEmitterDescription,
          structuredMixedOptionCellQuoteLiveTailRewindDescription,
          structuredMixedOptionCellQuoteLiveTailRewindConfig,
          structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
          structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
          structuredMixedOptionCellQuoteLiveTailOutputTape,
          structuredLiveTailRewindInitRow,
          structuredLiveTailRewindLoopRow,
          structuredLiveTailRewindDoneRow,
          structuredAnySourceOutputReadRows,
          structuredPreserve,
          structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301,
          List.replicate_succ]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_loop_done
    (right outputBits : Word Bool) (moved : Nat) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailRewindConfig
          301 [] right moved outputBits) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        400 [] right moved outputBits := by
  cases right with
  | nil =>
      three_tape_phase_step [
        structuredMixedOptionCellQuoteLiveTailEmitterDescription,
        structuredMixedOptionCellQuoteLiveTailRewindDescription,
        structuredMixedOptionCellQuoteLiveTailRewindConfig,
        structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
        structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
        structuredMixedOptionCellQuoteLiveTailOutputTape,
        structuredLiveTailRewindInitRow,
        structuredLiveTailRewindLoopRow,
        structuredLiveTailRewindDoneRow,
        structuredAnySourceOutputReadRows,
        structuredPreserve,
        structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301]
  | cons bit right =>
      cases bit <;>
        three_tape_phase_step [
          structuredMixedOptionCellQuoteLiveTailEmitterDescription,
          structuredMixedOptionCellQuoteLiveTailRewindDescription,
          structuredMixedOptionCellQuoteLiveTailRewindConfig,
          structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
          structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
          structuredMixedOptionCellQuoteLiveTailOutputTape,
          structuredLiveTailRewindInitRow,
          structuredLiveTailRewindLoopRow,
          structuredLiveTailRewindDoneRow,
          structuredAnySourceOutputReadRows,
          structuredPreserve,
          structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_loop
    (leftRev right outputBits : Word Bool) (moved : Nat) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (leftRev.length + 1)
        (structuredMixedOptionCellQuoteLiveTailRewindConfig
          301 leftRev right moved outputBits) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        400 [] (List.append leftRev.reverse right)
        (moved + leftRev.length) outputBits := by
  induction leftRev generalizing right moved with
  | nil =>
      simpa using
        structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_loop_done
          right outputBits moved
  | cons bit leftRev ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
          (n := 1)
          (m := leftRev.length + 1)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_loop_step
            bit leftRev right outputBits moved)
          ?_
      · simp [Nat.add_comm, Nat.add_left_comm]
      · have hmoved :
            moved.succ + leftRev.length =
              moved + (leftRev.length + 1) := by
          simp [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
        simpa [List.append_assoc, hmoved] using
          ih (bit :: right) moved.succ

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (bits.length + 2)
        (Structured.MultiTapeLowering.ThreeTape.config 300
          (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
            bits.reverse [])
          (structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape
            bits.length)
          (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        400 [] bits bits.length outputBits := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
      (n := 1)
      (m := bits.reverse.length + 1)
      (c1 :=
        structuredMixedOptionCellQuoteLiveTailRewindConfig
          301 bits.reverse [] 0 outputBits)
      (htotal := ?_)
      ?_
      ?_
  · simp [List.length_reverse]
    lia
  · simpa [structuredMixedOptionCellQuoteLiveTailRewindSourceTape_initial] using
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_init
        bits.reverse [] outputBits
  · simpa [List.length_reverse, List.reverse_reverse, Nat.zero_add,
      structuredMixedOptionCellQuoteLiveTailRewindSourceTape_done] using
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_loop
        bits.reverse [] outputBits 0

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_bit
    (bit : Bool) (processedRev rest : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          400 processedRev (bit :: rest) markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        400 (bit :: processedRev) rest markers
        (List.append outputBits
          (structuredMixedOptionCellQuoteLiveTailCellChunkBits bit)) := by
  cases bit <;> cases rest <;> (try cases ‹Bool›) <;>
    three_tape_phase_step [
      structuredMixedOptionCellQuoteLiveTailEmitterDescription,
      structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription,
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig,
      structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
      structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
      structuredMixedOptionCellQuoteLiveTailOutputTape,
      structuredMixedOptionCellQuoteLiveTailCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      structuredLiveTailCellPassInitialRow,
      structuredLiveTailCellPassWriteRows,
      structuredLiveTailCellPassWriteRow,
      structuredLiveTailCellPassHaltRow,
      structuredAnyReadRows,
      structuredPreserve, structuredWriteBit,
      Structured.MultiTapeLowering.ThreeTape.description,
      Structured.MultiTapeLowering.ThreeTape.phaseRows,
      Structured.MultiTapeLowering.ThreeTape.offsetRows,
      Structured.MultiTapeLowering.ThreeTape.offsetTransition,
      Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
      Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
      structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state400,
      structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state410,
      structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state411,
      structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state412,
      structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state420,
      structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state421,
      structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state422,
      structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state400,
      structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state410,
      structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state411,
      structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state412,
      structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state420,
      structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state421,
      structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state422,
      List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_done
    (processedRev : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          400 processedRev [] markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499 processedRev [] markers outputBits := by
  three_tape_phase_step [
    structuredMixedOptionCellQuoteLiveTailEmitterDescription,
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription,
    structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig,
    structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
    structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
    structuredMixedOptionCellQuoteLiveTailOutputTape,
    structuredLiveTailCellPassInitialRow,
    structuredLiveTailCellPassWriteRows,
    structuredLiveTailCellPassWriteRow,
    structuredLiveTailCellPassHaltRow,
    structuredAnyReadRows,
    structuredPreserve, structuredWriteBit,
    structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state400,
    structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state400]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_loop
    (processedRev remaining : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (4 * remaining.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          400 processedRev remaining markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499
        (List.append remaining.reverse processedRev)
        []
        markers
        (List.append outputBits
          (preservingCellPassCellBits remaining)) := by
  induction remaining generalizing processedRev outputBits with
  | nil =>
      simpa [preservingCellPassCellBits] using
        structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_done
          processedRev markers outputBits
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
          (m := 4 * rest.length + 1)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_bit
            bit processedRev rest markers outputBits)
          ?_
      · simp
        lia
      cases bit
      · simpa [structuredMixedOptionCellQuoteLiveTailCellChunkBits,
          preservingCellPassCellBits,
          preservingCellPassZeroBits,
          preservingCellPassOneBits,
          List.append_assoc] using
          ih (false :: processedRev)
            (List.append outputBits
              (structuredMixedOptionCellQuoteLiveTailCellChunkBits false))
      · simpa [structuredMixedOptionCellQuoteLiveTailCellChunkBits,
          preservingCellPassCellBits,
          preservingCellPassZeroBits,
          preservingCellPassOneBits,
          List.append_assoc] using
          ih (true :: processedRev)
            (List.append outputBits
              (structuredMixedOptionCellQuoteLiveTailCellChunkBits true))

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote
    (bits : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (4 * bits.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          400 [] bits markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499
        bits.reverse
        []
        markers
        (List.append outputBits
          (preservingCellPassCellBits bits)) := by
  simpa using
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_loop
      [] bits markers outputBits

def structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits
    (bits outputBits : Word Bool) : Word Bool :=
  List.append
    (List.append outputBits
      structuredMixedOptionCellQuoteLiveTailHeaderBits)
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        bits.length)
      (preservingCellPassCellBits bits))

def structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps
    (bits : Word Bool) : Nat :=
  bits.length + 1 + (4 * bits.length + 8)

def structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
    (bits outputBits : Word Bool) : Word Bool :=
  List.append
    (List.append outputBits
      structuredMixedOptionCellQuoteLiveTailHeaderBits)
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      bits.length)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_length
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps bits)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        300
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          bits.reverse [])
        0 bits.length
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
          bits outputBits) := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
      (n := bits.length + 1)
      (m := 4 * bits.length + 8)
      (htotal := ?_)
      (structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count
        bits outputBits)
      ?_
  · rw [structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps]
  · rw [
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig_eq_lengthHeaderConfig]
    exact
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length
        bits.length
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          bits.reverse [])
        outputBits

def structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps
    (bits : Word Bool) : Nat :=
  structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps bits +
    (bits.length + 2)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_length_rewind
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps
          bits)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        400 [] bits bits.length
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
          bits outputBits) := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
      (n := structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps
        bits)
      (m := bits.length + 2)
      (htotal := ?_)
      (structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_length
        bits outputBits)
      ?_
  · rw [structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps]
  · simpa [structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
      structuredMixedOptionCellQuoteLiveTailLengthPhaseTape] using
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind
        bits
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
          bits outputBits)

def structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
    (bits : Word Bool) : Nat :=
  structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps bits +
    (4 * bits.length + 1)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_fullSource
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps bits)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499 bits.reverse [] bits.length
        (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits
          bits outputBits) := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
      (n := structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps
        bits)
      (m := 4 * bits.length + 1)
      (htotal := ?_)
      (structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_length_rewind
        bits outputBits)
      ?_
  · rw [structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps]
  · simpa [
      structuredMixedOptionCellQuoteLiveTailRewindConfig,
      structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
      structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig,
      structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits,
      structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits,
      List.append_assoc] using
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote
        bits bits.length
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
          bits outputBits)

theorem structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits_eq_targetPrefix
    (w sourceRestBits : Word Bool) (stage : Nat) :
    structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits
        (assemblySourceRestFinishSourceBits w sourceRestBits stage) [] =
      assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage := by
  rw [structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits,
    structuredMixedOptionCellQuoteLiveTailHeaderBits_eq,
    assemblySourceRestFinishTargetPrefixBits]
  rfl

theorem structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits_eq_append_targetPrefix
    (w sourceRestBits outputBits : Word Bool) (stage : Nat) :
    structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        outputBits =
      List.append outputBits
        (assemblySourceRestFinishTargetPrefixBits
          w sourceRestBits stage) := by
  rw [structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits,
    structuredMixedOptionCellQuoteLiveTailHeaderBits_eq,
    assemblySourceRestFinishTargetPrefixBits]
  simp [List.append_assoc]

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_assemblyFullSource
    (w sourceRestBits outputBits : Word Bool) (stage : Nat) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
          (assemblySourceRestFinishSourceBits w sourceRestBits stage))
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 []
          (assemblySourceRestFinishSourceBits w sourceRestBits stage)
          0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499
        (assemblySourceRestFinishSourceBits w sourceRestBits stage).reverse
        []
        (assemblySourceRestFinishSourceBits w sourceRestBits stage).length
        (List.append outputBits
          (assemblySourceRestFinishTargetPrefixBits
            w sourceRestBits stage)) := by
  simpa [
    structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits_eq_append_targetPrefix]
    using
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_fullSource
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        outputBits

def StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthSpec
    (D : Structured.Description) : Prop :=
  Structured.MultiTapeLowering.SupportsReadWriteRows3 D ∧
    forall (bits outputBits : Word Bool),
      D.runConfig
          (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps bits)
          (structuredMixedOptionCellQuoteLiveTailCountConfig
            0 [] bits 0 outputBits) =
        structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          300
          (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
            bits.reverse [])
          0 bits.length
          (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
            bits outputBits)

theorem StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthSpec.run
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthSpec D)
    (bits outputBits : Word Bool) :
    D.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps bits)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        300
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          bits.reverse [])
        0 bits.length
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
          bits outputBits) :=
  hD.right bits outputBits

theorem StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthSpec.supported
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthSpec D) :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 D :=
  hD.left

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_countLengthSpec :
    StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthSpec
      structuredMixedOptionCellQuoteLiveTailEmitterDescription := by
  refine ⟨structuredMixedOptionCellQuoteLiveTailEmitterDescription_supported, ?_⟩
  intro bits outputBits
  exact
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_length
      bits outputBits

def StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSpec
    (D : Structured.Description) : Prop :=
  StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthSpec D ∧
    forall (bits outputBits : Word Bool),
      D.runConfig
          (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps
            bits)
          (structuredMixedOptionCellQuoteLiveTailCountConfig
            0 [] bits 0 outputBits) =
        structuredMixedOptionCellQuoteLiveTailRewindConfig
          400 [] bits bits.length
          (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
            bits outputBits)

theorem StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSpec.run
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSpec D)
    (bits outputBits : Word Bool) :
    D.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps
          bits)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        400 [] bits bits.length
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthOutputBits
          bits outputBits) :=
  hD.right bits outputBits

theorem StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSpec.supported
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSpec
      D) :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 D :=
  hD.left.supported

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_countLengthRewindSpec :
    StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSpec
      structuredMixedOptionCellQuoteLiveTailEmitterDescription := by
  refine
    ⟨structuredMixedOptionCellQuoteLiveTailEmitterDescription_countLengthSpec,
      ?_⟩
  intro bits outputBits
  exact
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count_length_rewind
      bits outputBits

def StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec
    (D : Structured.Description) : Prop :=
  StructuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSpec D ∧
    forall (bits outputBits : Word Bool),
      D.runConfig
          (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps bits)
          (structuredMixedOptionCellQuoteLiveTailCountConfig
            0 [] bits 0 outputBits) =
        structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          499 bits.reverse [] bits.length
          (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits
            bits outputBits)

theorem StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec.run
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec D)
    (bits outputBits : Word Bool) :
    D.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps bits)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499 bits.reverse [] bits.length
        (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits
          bits outputBits) :=
  hD.right bits outputBits

theorem StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec.supported
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec D) :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 D :=
  hD.left.supported

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_fullSourceSpec :
    StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec
      structuredMixedOptionCellQuoteLiveTailEmitterDescription := by
  refine
    ⟨structuredMixedOptionCellQuoteLiveTailEmitterDescription_countLengthRewindSpec,
      ?_⟩
  intro bits outputBits
  exact
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_fullSource
      bits outputBits

def StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec
    (D : Structured.Description) : Prop :=
  StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec D ∧
    forall (w sourceRestBits outputBits : Word Bool) (stage : Nat),
      D.runConfig
          (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
            (assemblySourceRestFinishSourceBits w sourceRestBits stage))
          (structuredMixedOptionCellQuoteLiveTailCountConfig
            0 []
            (assemblySourceRestFinishSourceBits w sourceRestBits stage)
            0 outputBits) =
        structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          499
          (assemblySourceRestFinishSourceBits w sourceRestBits stage).reverse
          []
          (assemblySourceRestFinishSourceBits w sourceRestBits stage).length
          (List.append outputBits
            (assemblySourceRestFinishTargetPrefixBits
              w sourceRestBits stage))

theorem StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec.run
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec
      D)
    (w sourceRestBits outputBits : Word Bool) (stage : Nat) :
    D.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
          (assemblySourceRestFinishSourceBits w sourceRestBits stage))
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 []
          (assemblySourceRestFinishSourceBits w sourceRestBits stage)
          0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499
        (assemblySourceRestFinishSourceBits w sourceRestBits stage).reverse
        []
        (assemblySourceRestFinishSourceBits w sourceRestBits stage).length
        (List.append outputBits
          (assemblySourceRestFinishTargetPrefixBits
            w sourceRestBits stage)) :=
  hD.right w sourceRestBits outputBits stage

theorem StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec.supported
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec
      D) :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 D :=
  hD.left.supported

theorem StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec_of_fullSource
    {D : Structured.Description}
    (hD : StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec D) :
    StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec
      D := by
  refine ⟨hD, ?_⟩
  intro w sourceRestBits outputBits stage
  simpa [
    structuredMixedOptionCellQuoteLiveTailEmitterFullSourceOutputBits_eq_append_targetPrefix]
    using
      hD.run
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        outputBits

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_assemblyTargetPrefixSpec :
    StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec
      structuredMixedOptionCellQuoteLiveTailEmitterDescription :=
  StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec_of_fullSource
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_fullSourceSpec

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
