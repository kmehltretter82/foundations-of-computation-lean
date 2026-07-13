import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.TapeFieldSerializer

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.TapeFieldPipeline

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector
open RawPairQuoter RawPairDecoder

/-!
The production guarded-egress tape-field route, composed bottom-up from the
checked raw-pair phases.  Every handoff uses the canonical right/left bounce;
the viable contract therefore records intermediate and final tapes up to
`Tape.Equiv`.
-/

def pairRightEdgeAndSerializeDescription : MachineDescription :=
  SeqViaCanonical rightEdgeRewindDescription
    TapeFieldSerializer.markedTapeFieldSerializerDescription

theorem pairRightEdgeAndSerializeDescription_subroutineReady :
    pairRightEdgeAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    rightEdgeRewindDescription_subroutineReady
    TapeFieldSerializer.markedTapeFieldSerializerDescription_subroutineReady

theorem pairRightEdgeAndSerializeDescription_haltsFrom_pairRewind
    (i : Index) :
    pairRightEdgeAndSerializeDescription.HaltsFromTapeEquiv
      (rightEdgeRewindSourceTapeWithBase []
        (quotedPairBits (pairList i)) (rewindPadding i))
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    rightEdgeRewindDescription_subroutineReady
    TapeFieldSerializer.markedTapeFieldSerializerDescription_subroutineReady
    (RawPairMarker.rightEdgeRewindDescription_haltsFrom_pairRewind i)
    (moveLeft_moveRight_equiv_self _)
    (TapeFieldSerializer.markedTapeFieldSerializerDescription_haltsFrom_source i)

def pairRewindAndSerializeDescription : MachineDescription :=
  SeqViaCanonical rightBlankRewindDescription
    pairRightEdgeAndSerializeDescription

theorem pairRewindAndSerializeDescription_subroutineReady :
    pairRewindAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    rightBlankRewindDescription_subroutineReady
    pairRightEdgeAndSerializeDescription_subroutineReady

theorem pairRewindAndSerializeDescription_haltsFrom_pairTarget
    (i : Index) :
    pairRewindAndSerializeDescription.HaltsFromTapeEquiv
      (pairRewriteTargetTape (pairList i) (rewindPadding i))
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    rightBlankRewindDescription_subroutineReady
    pairRightEdgeAndSerializeDescription_subroutineReady
    (RawPairMarker.rightBlankRewindDescription_haltsFrom_pairTarget i).toEquiv
    (moveLeft_moveRight_equiv_self _)
    (pairRightEdgeAndSerializeDescription_haltsFrom_pairRewind i)

def pairRewriteAndSerializeDescription : MachineDescription :=
  SeqViaCanonical pairRewriterDescription
    pairRewindAndSerializeDescription

theorem pairRewriteAndSerializeDescription_subroutineReady :
    pairRewriteAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    pairRewriterDescription_subroutineReady
    pairRewindAndSerializeDescription_subroutineReady

theorem pairRewriteAndSerializeDescription_haltsFrom_decoder
    (i : Index) :
    pairRewriteAndSerializeDescription.HaltsFromTapeEquiv
      (pairRewriteSourceTape (pairList i) (rewindPadding i))
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    pairRewriterDescription_subroutineReady
    pairRewindAndSerializeDescription_subroutineReady
    (RawPairDecoder.pairRewriterDescription_haltsFrom_decoder i).toEquiv
    (moveLeft_moveRight_equiv_self _)
    (pairRewindAndSerializeDescription_haltsFrom_pairTarget i)

def decoderRightEdgeAndSerializeDescription : MachineDescription :=
  SeqViaCanonical rightEdgeRewindDescription
    pairRewriteAndSerializeDescription

theorem decoderRightEdgeAndSerializeDescription_subroutineReady :
    decoderRightEdgeAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    rightEdgeRewindDescription_subroutineReady
    pairRewriteAndSerializeDescription_subroutineReady

theorem decoderRightEdgeAndSerializeDescription_haltsFrom_rewind
    (i : Index) :
    decoderRightEdgeAndSerializeDescription.HaltsFromTapeEquiv
      (rewindSourceTape i)
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    rightEdgeRewindDescription_subroutineReady
    pairRewriteAndSerializeDescription_subroutineReady
    (RawPairDecoder.rightEdgeRewindDescription_haltsFrom_decoderRewind i).toEquiv
    (moveLeft_moveRight_equiv_self _)
    (pairRewriteAndSerializeDescription_haltsFrom_decoder i)

def decoderRewindAndSerializeDescription : MachineDescription :=
  SeqViaCanonical rightBlankRewindDescription
    decoderRightEdgeAndSerializeDescription

theorem decoderRewindAndSerializeDescription_subroutineReady :
    decoderRewindAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    rightBlankRewindDescription_subroutineReady
    decoderRightEdgeAndSerializeDescription_subroutineReady

theorem decoderRewindAndSerializeDescription_haltsFrom_target
    (i : Index) :
    decoderRewindAndSerializeDescription.HaltsFromTapeEquiv
      (decoderTargetTape i)
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    rightBlankRewindDescription_subroutineReady
    decoderRightEdgeAndSerializeDescription_subroutineReady
    (RawPairDecoder.rightBlankRewindDescription_haltsFrom_decoderTarget i)
    (moveLeft_moveRight_equiv_self _)
    (decoderRightEdgeAndSerializeDescription_haltsFrom_rewind i)

def decoderAndSerializeDescription : MachineDescription :=
  SeqViaCanonical decoderDescription
    decoderRewindAndSerializeDescription

theorem decoderAndSerializeDescription_subroutineReady :
    decoderAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    decoderDescription_subroutineReady
    decoderRewindAndSerializeDescription_subroutineReady

theorem decoderAndSerializeDescription_haltsFrom_source
    (i : Index) :
    decoderAndSerializeDescription.HaltsFromTapeEquiv
      (decoderSourceTape i)
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    decoderDescription_subroutineReady
    decoderRewindAndSerializeDescription_subroutineReady
    (RawPairDecoder.decoderDescription_haltsFromTape i).toEquiv
    (moveLeft_moveRight_equiv_self _)
    (decoderRewindAndSerializeDescription_haltsFrom_target i)

def seededDecoderAndSerializeDescription : MachineDescription :=
  SeqViaCanonical seedDecoderDescription
    decoderAndSerializeDescription

theorem seededDecoderAndSerializeDescription_subroutineReady :
    seededDecoderAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    seedDecoderDescription_subroutineReady
    decoderAndSerializeDescription_subroutineReady

theorem seededDecoderAndSerializeDescription_haltsFrom_rewoundChunk
    (i : Index) :
    seededDecoderAndSerializeDescription.HaltsFromTapeEquiv
      (rewoundChunkTape i)
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    seedDecoderDescription_subroutineReady
    decoderAndSerializeDescription_subroutineReady
    (RawPairDecoder.seedDecoderDescription_haltsFromTape i).toEquiv
    (moveLeft_moveRight_equiv_self _)
    (decoderAndSerializeDescription_haltsFrom_source i)

def rewindChunkAndSerializeDescription : MachineDescription :=
  SeqViaCanonical rightEdgeRewindDescription
    seededDecoderAndSerializeDescription

theorem rewindChunkAndSerializeDescription_subroutineReady :
    rewindChunkAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    rightEdgeRewindDescription_subroutineReady
    seededDecoderAndSerializeDescription_subroutineReady

theorem rewindChunkAndSerializeDescription_haltsFrom_sentinel
    (i : Index) :
    rewindChunkAndSerializeDescription.HaltsFromTapeEquiv
      (sentinelTape i)
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    rightEdgeRewindDescription_subroutineReady
    seededDecoderAndSerializeDescription_subroutineReady
    (RawPairDecoder.rightEdgeRewindDescription_haltsFrom_sentinel i).toEquiv
    (moveLeft_moveRight_equiv_self _)
    (seededDecoderAndSerializeDescription_haltsFrom_rewoundChunk i)

def installSentinelAndSerializeDescription : MachineDescription :=
  SeqViaCanonical installSentinelDescription
    rewindChunkAndSerializeDescription

theorem installSentinelAndSerializeDescription_subroutineReady :
    installSentinelAndSerializeDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    installSentinelDescription_subroutineReady
    rewindChunkAndSerializeDescription_subroutineReady

theorem installSentinelAndSerializeDescription_haltsFrom_chunkTarget
    (i : Index) :
    installSentinelAndSerializeDescription.HaltsFromTapeEquiv
      (RawPairQuoter.targetTape i)
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    installSentinelDescription_subroutineReady
    rewindChunkAndSerializeDescription_subroutineReady
    (RawPairDecoder.installSentinelDescription_haltsFromTape i).toEquiv
    (moveLeft_moveRight_equiv_self _)
    (rewindChunkAndSerializeDescription_haltsFrom_sentinel i)

def description : MachineDescription :=
  SeqViaCanonical rawBoundaryChunkExpandLoopDescription
    installSentinelAndSerializeDescription

theorem description_subroutineReady : description.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    RawPairQuoter.chunkExpandDescription_subroutineReady
    installSentinelAndSerializeDescription_subroutineReady

theorem description_haltsFrom_source (i : Index) :
    description.HaltsFromTapeEquiv i.source
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) := by
  exact SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    RawPairQuoter.chunkExpandDescription_subroutineReady
    installSentinelAndSerializeDescription_subroutineReady
    (RawPairQuoter.chunkExpandDescription_haltsFromTape i).toEquiv
    (moveLeft_moveRight_equiv_self _)
    (installSentinelAndSerializeDescription_haltsFrom_chunkTarget i)

end GuardedEgress.TapeFieldPipeline
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
