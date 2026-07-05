import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.EmitterStructured

set_option doc.verso true

/-!
# Structured live-tail quote phase

This module continues the three-logical-tape live-tail emitter construction
after the count, length-header, and rewind phases proved in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.EmitterStructured`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
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

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_assemblyTargetPrefix
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        (4 *
            (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
          1)
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          0 [] (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
          (assemblySourceRestFinishLengthHeaderBits
            p.w p.sourceRestBits p.stage)) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
        []
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
        (assemblySourceRestFinishTargetPrefixBits
          p.w p.sourceRestBits p.stage) := by
  rw [structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote,
    assemblySourceRestFinishLengthHeaderBits]
  simpa [assemblySourceRestFinishSourceBits_length_eq_prefix_add,
    List.append_assoc] using
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind
      (assemblySourceRestFinishSourceBits p.w p.sourceRestBits p.stage)
      (assemblySourceRestFinishSourceBits p.w p.sourceRestBits p.stage).length
      (List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          ((assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
            p.sourceRestBits.length)))

-- Prefix-only quoting is useful only after a separate phase has isolated the
-- parsed prefix. The assembly rewind phase leaves the full counted source word,
-- so the composable post-rewind theorem is the target-prefix theorem above.
theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_isolatedAssemblyPrefix
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        (4 *
            (assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
          1)
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          0 [] (assemblySourceRestFinishSourcePrefixBits p.w p.stage)
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
          (assemblySourceRestFinishLengthHeaderBits
            p.w p.sourceRestBits p.stage)) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        (assemblySourceRestFinishSourcePrefixBits p.w p.stage).reverse
        []
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
        (assemblySourceRestLiveTailEmitterEmittedPrefix p) := by
  rw [assemblySourceRestLiveTailEmitterEmittedPrefix,
    assemblySourceRestFinishPrefixQuoteOutputBits,
    assemblySourceRestFinishQuotedPrefixBits]
  exact
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind
      (assemblySourceRestFinishSourcePrefixBits p.w p.stage)
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
      (assemblySourceRestFinishLengthHeaderBits
        p.w p.sourceRestBits p.stage)

theorem structuredMixedOptionCellQuoteLiveTailRewindConfig_eq_cellPassAfterRewindConfig
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailRewindConfig
        structuredMixedOptionCellQuoteLiveTailRewindDescription.halt
        [] bits bits.length outputBits =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        structuredMixedOptionCellQuoteLiveTailRewindDescription.halt
        [] bits bits.length outputBits := by
  simp [structuredMixedOptionCellQuoteLiveTailRewindConfig,
    structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig,
    structuredMixedOptionCellQuoteLiveTailRewindSourceTape_done]

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
              simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
                Structured.MultiTapeLowering.ThreeTape.description,
                Structured.MultiTapeLowering.ThreeTape.config,
                Structured.MultiTapeLowering.ThreeTape.outputFromBits,
                Structured.MultiTapeLowering.ThreeTape.phaseRows,
                Structured.MultiTapeLowering.ThreeTape.offsetRows,
                Structured.MultiTapeLowering.ThreeTape.offsetTransition,
                Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
                Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
                Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
                Structured.Description.runConfig,
                Structured.Description.stepConfig,
                Structured.Description.lookupTransition,
                Structured.Description.Matches,
                Structured.TapeAction.stay,
                Structured.TapeAction.apply, Structured.HeadMove.apply,
                Tape.read, Tape.write, Tape.move, Tape.moveRight,
                tapeAtCells, List.replicate_succ, List.reverse_append]
      | succ remaining =>
          cases sourceHead <;> (try cases ‹Bool›) <;>
            simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.MultiTapeLowering.ThreeTape.phaseRows,
              Structured.MultiTapeLowering.ThreeTape.offsetRows,
              Structured.MultiTapeLowering.ThreeTape.offsetTransition,
              Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
              Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
              Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveRight,
              tapeAtCells, List.reverse_append]

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
            simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.MultiTapeLowering.ThreeTape.phaseRows,
              Structured.MultiTapeLowering.ThreeTape.offsetRows,
              Structured.MultiTapeLowering.ThreeTape.offsetTransition,
              Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
              Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
              Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells, List.replicate_succ,
              List.reverse_append]
      | some bit =>
          cases bit <;> cases remaining <;>
            simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.MultiTapeLowering.ThreeTape.phaseRows,
              Structured.MultiTapeLowering.ThreeTape.offsetRows,
              Structured.MultiTapeLowering.ThreeTape.offsetTransition,
              Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
              Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
              Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells, List.replicate_succ,
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
          simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
            Structured.MultiTapeLowering.ThreeTape.description,
            Structured.MultiTapeLowering.ThreeTape.config,
            Structured.MultiTapeLowering.ThreeTape.outputFromBits,
            Structured.MultiTapeLowering.ThreeTape.phaseRows,
            Structured.MultiTapeLowering.ThreeTape.offsetRows,
            Structured.MultiTapeLowering.ThreeTape.offsetTransition,
            Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
            Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
            Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
            Structured.Description.runConfig,
            Structured.Description.stepConfig,
            Structured.Description.lookupTransition,
            Structured.Description.Matches,
            Structured.TapeAction.stay,
            Structured.TapeAction.apply, Structured.HeadMove.apply,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells, List.reverse_append]
      | some bit =>
          cases bit <;>
            simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.MultiTapeLowering.ThreeTape.phaseRows,
              Structured.MultiTapeLowering.ThreeTape.offsetRows,
              Structured.MultiTapeLowering.ThreeTape.offsetTransition,
              Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
              Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
              Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveRight,
              tapeAtCells, List.reverse_append]

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

def structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps
    (p : AssemblySourceRestLiveTailEmitterParam) : Nat :=
  ((structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
    1) +
  (4 *
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
    8)

def structuredMixedOptionCellQuoteLiveTailEmitterRewindSteps
    (p : AssemblySourceRestLiveTailEmitterParam) : Nat :=
  (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
    2

def structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps
    (p : AssemblySourceRestLiveTailEmitterParam) : Nat :=
  structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps p +
    structuredMixedOptionCellQuoteLiveTailEmitterRewindSteps p

def structuredMixedOptionCellQuoteLiveTailEmitterQuoteSteps
    (p : AssemblySourceRestLiveTailEmitterParam) : Nat :=
  4 * (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
    1

def structuredMixedOptionCellQuoteLiveTailEmitterSteps
    (p : AssemblySourceRestLiveTailEmitterParam) : Nat :=
  structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps p +
    structuredMixedOptionCellQuoteLiveTailEmitterQuoteSteps p

def structuredMixedOptionCellQuoteLiveTailEmitterInitialConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCountConfig
    0 [] (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
    0 []

def structuredMixedOptionCellQuoteLiveTailEmitterAfterCountLengthConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
    (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
      [])
    0
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishLengthHeaderBits
      p.w p.sourceRestBits p.stage)

def structuredMixedOptionCellQuoteLiveTailEmitterAfterCountLengthStaticConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
    300
    (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
      [])
    0
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishLengthHeaderBits
      p.w p.sourceRestBits p.stage)

def structuredMixedOptionCellQuoteLiveTailEmitterRewindStartConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
    0
    (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
      [])
    0
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishLengthHeaderBits
      p.w p.sourceRestBits p.stage)

def structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailRewindConfig
    structuredMixedOptionCellQuoteLiveTailRewindDescription.halt
    []
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishLengthHeaderBits
      p.w p.sourceRestBits p.stage)

def structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindStaticConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailRewindConfig
    400
    []
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishLengthHeaderBits
      p.w p.sourceRestBits p.stage)

def structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
    0 []
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishLengthHeaderBits
      p.w p.sourceRestBits p.stage)

def structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartStaticConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
    400 []
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishLengthHeaderBits
      p.w p.sourceRestBits p.stage)

def structuredMixedOptionCellQuoteLiveTailEmitterFinalConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
    []
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishTargetPrefixBits
      p.w p.sourceRestBits p.stage)

def structuredMixedOptionCellQuoteLiveTailEmitterFinalStaticConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
    499
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
    []
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
    (assemblySourceRestFinishTargetPrefixBits
      p.w p.sourceRestBits p.stage)

theorem structuredMixedOptionCellQuoteLiveTailEmitterRewindStartConfig_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailEmitterRewindStartConfig p =
      Structured.MultiTapeLowering.ThreeTape.config 0
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
            p).reverse [])
        (structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
            p).length)
        (structuredMixedOptionCellQuoteLiveTailOutputTape
          (assemblySourceRestFinishLengthHeaderBits
            p.w p.sourceRestBits p.stage)) := by
  simp [structuredMixedOptionCellQuoteLiveTailEmitterRewindStartConfig,
    structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
    structuredMixedOptionCellQuoteLiveTailLengthPhaseTape]

theorem structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindStaticConfig_eq_quoteStartStaticConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindStaticConfig p =
      structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartStaticConfig p := by
  simp [structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindStaticConfig,
    structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartStaticConfig,
    structuredMixedOptionCellQuoteLiveTailRewindConfig,
    structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig,
    structuredMixedOptionCellQuoteLiveTailRewindSourceTape_done]

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
      simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
        Structured.MultiTapeLowering.ThreeTape.description,
        Structured.MultiTapeLowering.ThreeTape.phaseRows,
        Structured.MultiTapeLowering.ThreeTape.offsetRows,
        Structured.MultiTapeLowering.ThreeTape.offsetTransition,
        Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
        Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
        Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
        structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state300,
        Structured.MultiTapeLowering.ThreeTape.config,
        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.stay,
        Structured.TapeAction.apply, Structured.HeadMove.apply,
        Tape.read, Tape.move, Tape.moveRight,
        tapeAtCells]
  | cons bit right =>
      cases bit <;>
        simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
          Structured.MultiTapeLowering.ThreeTape.description,
          Structured.MultiTapeLowering.ThreeTape.phaseRows,
          Structured.MultiTapeLowering.ThreeTape.offsetRows,
          Structured.MultiTapeLowering.ThreeTape.offsetTransition,
          Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
          Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
          structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state300,
          Structured.MultiTapeLowering.ThreeTape.config,
          Structured.MultiTapeLowering.ThreeTape.outputFromBits,
          Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.stay,
          Structured.TapeAction.apply, Structured.HeadMove.apply,
          Tape.read, Tape.move, Tape.moveRight,
          tapeAtCells]

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
      simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
        Structured.MultiTapeLowering.ThreeTape.description,
        Structured.MultiTapeLowering.ThreeTape.phaseRows,
        Structured.MultiTapeLowering.ThreeTape.offsetRows,
        Structured.MultiTapeLowering.ThreeTape.offsetTransition,
        Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
        Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
        Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
        structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301,
        Structured.MultiTapeLowering.ThreeTape.config,
        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.stay,
        Structured.TapeAction.apply, Structured.HeadMove.apply,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
        tapeAtCells, List.replicate_succ]
  | cons head tail =>
      cases head <;>
        simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
          Structured.MultiTapeLowering.ThreeTape.description,
          Structured.MultiTapeLowering.ThreeTape.phaseRows,
          Structured.MultiTapeLowering.ThreeTape.offsetRows,
          Structured.MultiTapeLowering.ThreeTape.offsetTransition,
          Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
          Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
          structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301,
          Structured.MultiTapeLowering.ThreeTape.config,
          Structured.MultiTapeLowering.ThreeTape.outputFromBits,
          Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.stay,
          Structured.TapeAction.apply, Structured.HeadMove.apply,
          Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
          tapeAtCells, List.replicate_succ]

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
      simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
        Structured.MultiTapeLowering.ThreeTape.description,
        Structured.MultiTapeLowering.ThreeTape.phaseRows,
        Structured.MultiTapeLowering.ThreeTape.offsetRows,
        Structured.MultiTapeLowering.ThreeTape.offsetTransition,
        Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
        Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
        Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
        structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301,
        Structured.MultiTapeLowering.ThreeTape.config,
        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.stay,
        Structured.TapeAction.apply, Structured.HeadMove.apply,
        Tape.read, tapeAtCells]
  | cons bit right =>
      cases bit <;>
        simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
          Structured.MultiTapeLowering.ThreeTape.description,
          Structured.MultiTapeLowering.ThreeTape.phaseRows,
          Structured.MultiTapeLowering.ThreeTape.offsetRows,
          Structured.MultiTapeLowering.ThreeTape.offsetTransition,
          Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
          Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
          structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state301,
          Structured.MultiTapeLowering.ThreeTape.config,
          Structured.MultiTapeLowering.ThreeTape.outputFromBits,
          Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.stay,
          Structured.TapeAction.apply, Structured.HeadMove.apply,
          Tape.read, tapeAtCells]

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

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterRewindSteps p)
        (structuredMixedOptionCellQuoteLiveTailEmitterAfterCountLengthStaticConfig
          p) =
      structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindStaticConfig p := by
  simpa [structuredMixedOptionCellQuoteLiveTailEmitterRewindSteps,
    structuredMixedOptionCellQuoteLiveTailEmitterAfterCountLengthStaticConfig,
    structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindStaticConfig,
    structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
    structuredMixedOptionCellQuoteLiveTailLengthPhaseTape] using
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
      (assemblySourceRestFinishLengthHeaderBits
        p.w p.sourceRestBits p.stage)

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
    simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_done
    (processedRev : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          400 processedRev [] markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499 processedRev [] markers outputBits := by
  simp [structuredMixedOptionCellQuoteLiveTailEmitterDescription,
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
    Structured.MultiTapeLowering.ThreeTape.description,
    Structured.MultiTapeLowering.ThreeTape.phaseRows,
    Structured.MultiTapeLowering.ThreeTape.offsetRows,
    Structured.MultiTapeLowering.ThreeTape.offsetTransition,
    Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
    Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
    structuredMixedOptionCellQuoteLiveTailEmitterCountLengthTransitions_no_state400,
    structuredMixedOptionCellQuoteLiveTailEmitterRewindTransitions_no_state400,
    Structured.MultiTapeLowering.ThreeTape.config,
    Structured.MultiTapeLowering.ThreeTape.outputFromBits,
    Structured.Description.runConfig,
    Structured.Description.stepConfig,
    Structured.Description.lookupTransition,
    Structured.Description.Matches,
    Structured.TapeAction.stay,
    Structured.TapeAction.apply, Structured.HeadMove.apply,
    Tape.read, tapeAtCells]

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

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterQuoteSteps p)
        (structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartStaticConfig
          p) =
      structuredMixedOptionCellQuoteLiveTailEmitterFinalStaticConfig p := by
  rw [structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartStaticConfig,
    structuredMixedOptionCellQuoteLiveTailEmitterFinalStaticConfig,
    structuredMixedOptionCellQuoteLiveTailEmitterQuoteSteps]
  rw [structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote,
    assemblySourceRestFinishLengthHeaderBits]
  simpa [assemblySourceRestFinishSourceBits_length_eq_prefix_add,
    List.append_assoc] using
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote
      (assemblySourceRestFinishSourceBits p.w p.sourceRestBits p.stage)
      (assemblySourceRestFinishSourceBits p.w p.sourceRestBits p.stage).length
      (List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          ((assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
            p.sourceRestBits.length)))

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_countLength_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps p)
        (structuredMixedOptionCellQuoteLiveTailEmitterInitialConfig p) =
      structuredMixedOptionCellQuoteLiveTailEmitterAfterCountLengthStaticConfig
        p := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
      (n :=
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
          1)
      (m :=
        4 *
            (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
              p).length +
          8)
      (c1 :=
        structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          100
          (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
            (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
              p).reverse [])
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
            p).length
          0 [])
      (htotal := rfl)
      ?_
      ?_
  · rw [structuredMixedOptionCellQuoteLiveTailEmitterInitialConfig,
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_count]
    exact
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig_eq_lengthHeaderConfig
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
        []
  · simpa [structuredMixedOptionCellQuoteLiveTailEmitterAfterCountLengthStaticConfig,
      assemblySourceRestFinishLengthHeaderBits,
      structuredMixedOptionCellQuoteLiveTailHeaderBits_eq,
      structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits_length] using
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_length
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
            p).reverse [])
        []

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_countLengthRewind_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps
          p)
        (structuredMixedOptionCellQuoteLiveTailEmitterInitialConfig p) =
      structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindStaticConfig
        p := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
      (n :=
        structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps p)
      (m :=
        structuredMixedOptionCellQuoteLiveTailEmitterRewindSteps p)
      (c1 :=
        structuredMixedOptionCellQuoteLiveTailEmitterAfterCountLengthStaticConfig
          p)
      (htotal := rfl)
      ?_
      ?_
  · exact
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_countLength_assembly
        p
  · exact
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_rewind_assembly
        p

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterSteps p)
        (structuredMixedOptionCellQuoteLiveTailEmitterInitialConfig p) =
      structuredMixedOptionCellQuoteLiveTailEmitterFinalStaticConfig p := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailEmitterDescription)
      (n :=
        structuredMixedOptionCellQuoteLiveTailEmitterCountLengthRewindSteps
          p)
      (m :=
        structuredMixedOptionCellQuoteLiveTailEmitterQuoteSteps p)
      (c1 :=
        structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartStaticConfig
          p)
      (htotal := rfl)
      ?_
      ?_
  · simpa
      [structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindStaticConfig_eq_quoteStartStaticConfig
        p] using
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_countLengthRewind_assembly
        p
  · exact
      structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_quote_assembly
        p

/--
Separated structured phase run for the assembly live-tail emitter prefix.

This theorem composes the already-proved structured descriptions at their
semantic handoff points.  A later single-table theorem can replace these
description boundaries once the phase packaging for the three-tape lowerer is
ready.
-/
theorem structuredMixedOptionCellQuoteLiveTailEmitterSeparatedPhases_run
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterCountLengthSteps p)
        (structuredMixedOptionCellQuoteLiveTailEmitterInitialConfig p) =
      structuredMixedOptionCellQuoteLiveTailEmitterAfterCountLengthConfig p ∧
    structuredMixedOptionCellQuoteLiveTailRewindDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterRewindSteps p)
        (structuredMixedOptionCellQuoteLiveTailEmitterRewindStartConfig p) =
      structuredMixedOptionCellQuoteLiveTailEmitterAfterRewindConfig p ∧
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterQuoteSteps p)
        (structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartConfig p) =
      structuredMixedOptionCellQuoteLiveTailEmitterFinalConfig p := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_assembly
        p
  · rw [structuredMixedOptionCellQuoteLiveTailEmitterRewindStartConfig_eq]
    exact
      structuredMixedOptionCellQuoteLiveTailRewindDescription_run
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
        (assemblySourceRestFinishLengthHeaderBits
          p.w p.sourceRestBits p.stage)
  · simpa [structuredMixedOptionCellQuoteLiveTailEmitterQuoteSteps,
      structuredMixedOptionCellQuoteLiveTailEmitterQuoteStartConfig,
      structuredMixedOptionCellQuoteLiveTailEmitterFinalConfig] using
      structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_assemblyTargetPrefix
        p

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
