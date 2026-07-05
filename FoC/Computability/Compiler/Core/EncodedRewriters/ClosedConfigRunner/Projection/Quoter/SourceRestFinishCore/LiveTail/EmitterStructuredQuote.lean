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

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_afterRewind_assemblyPrefix
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

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
