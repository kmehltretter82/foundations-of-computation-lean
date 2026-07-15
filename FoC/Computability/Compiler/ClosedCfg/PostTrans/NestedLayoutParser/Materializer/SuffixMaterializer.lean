import FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutParser.Materializer.DecoderSetup
import FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutParser.Materializer.PostDecodeSuffixCopier
import FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutParser.Materializer.RightEdgeTape2Projector
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace NestedLayoutMaterializerInternal
namespace CanonicalBoolWordSuffixMaterializer

private abbrev EMIT : MachineDescription :=
  StructuredConstructionTargets.structured3InputEmbeddingEmitterDescription

private abbrev SETUP : MachineDescription :=
  ThreeTape.NestedLayoutMaterializerInternal.CanonicalBoolWordDecoderSetup.loweredDescription

private abbrev DECODE : MachineDescription :=
  loweredStructuredBoolWordRawBitsDecoderDescription

private abbrev COPY : MachineDescription :=
  ThreeTape.NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.loweredDescription

private abbrev PROJECT : MachineDescription :=
  Tape2Projector.rightEdgeEndpointTape2ProjectorDescription

private theorem emitReady : EMIT.SubroutineReady :=
  StructuredConstructionTargets.structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.left

private theorem setupReady : SETUP.SubroutineReady :=
  ThreeTape.NestedLayoutMaterializerInternal.CanonicalBoolWordDecoderSetup.loweredDescription_subroutineReady

private theorem decodeReady : DECODE.SubroutineReady :=
  loweredStructuredBoolWordRawBitsDecoderDescription_subroutineReady

private theorem copyReady : COPY.SubroutineReady :=
  ThreeTape.NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.loweredDescription_subroutineReady

private theorem projectReady : PROJECT.SubroutineReady :=
  Tape2Projector.rightEdgeEndpointTape2ProjectorDescription_subroutineReady

def description : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription EMIT SETUP)
        DECODE)
      COPY)
    PROJECT

theorem description_subroutineReady : description.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        (canonicalPrimitiveSeqDescription_subroutineReady
          emitReady setupReady)
        decodeReady)
      copyReady)
    projectReady

theorem emitter_haltsFromTapeEquiv
    (bits suffix : Word Bool) :
    EMIT.HaltsFromTapeEquiv
      (boolWordRawBitsDecoderSourceTape bits suffix [none])
      (encodedGuardedStructured3Tapes
        (Tape.input
          (ThreeTape.NestedLayoutMaterializerInternal.CanonicalBoolWordDecoderSetup.canonicalRawWord
            bits suffix))
        Tape.blank Tape.blank) := by
  have hemit :=
    HaltsFromTapeEquiv_of_input_equiv
      (Tape.Equiv.symm
        (ThreeTape.NestedLayoutMaterializerInternal.CanonicalBoolWordDecoderSetup.decoderSource_singleBlank_equiv_input
          bits suffix))
      (StructuredConstructionTargets.structured3InputEmbeddingEmitterDescription_targetCellsRunSpec.right
        (ThreeTape.NestedLayoutMaterializerInternal.CanonicalBoolWordDecoderSetup.canonicalRawWord bits suffix))
  simpa [EMIT,
    StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget,
    structured3InputMaterializerTargetTape] using hemit

theorem projector_haltsFromTapeEquiv
    (bits suffix : Word Bool) :
    PROJECT.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape bits suffix [])
        (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
          (bits.length + 1))
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append bits (false :: suffix)) []))
      (Tape.input (List.append bits (false :: suffix))) := by
  cases bits with
  | nil =>
      simpa using
        Tape2Projector.rightEdgeEndpointTape2ProjectorDescription_haltsFromTapeEquiv
          (structuredBoolWordRawBitsDecoderSourceTargetTape [] suffix [])
          (structuredBoolWordRawBitsDecoderCounterDecodeTape 0 1)
          false suffix
  | cons bit rest =>
      simpa [List.append_assoc] using
        Tape2Projector.rightEdgeEndpointTape2ProjectorDescription_haltsFromTapeEquiv
          (structuredBoolWordRawBitsDecoderSourceTargetTape
            (bit :: rest) suffix [])
          (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
            ((bit :: rest).length + 1))
          bit (List.append rest (false :: suffix))

theorem description_haltsFromTapeEquiv
    (bits suffix : Word Bool) :
    description.HaltsFromTapeEquiv
      (boolWordRawBitsDecoderSourceTape bits suffix [none])
      (Tape.input (List.append bits (false :: suffix))) := by
  apply canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    (canonicalPrimitiveSeqDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        (canonicalPrimitiveSeqDescription_subroutineReady
          emitReady setupReady) decodeReady) copyReady)
    projectReady
  · apply canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        (canonicalPrimitiveSeqDescription_subroutineReady
          emitReady setupReady) decodeReady)
      copyReady
    · apply canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (canonicalPrimitiveSeqDescription_subroutineReady emitReady setupReady)
        decodeReady
      · exact canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
          emitReady setupReady
          (emitter_haltsFromTapeEquiv bits suffix)
          (ThreeTape.NestedLayoutMaterializerInternal.CanonicalBoolWordDecoderSetup.loweredDescription_haltsFrom_decoderInput
            bits suffix)
      · simpa [encodedGuardedStructured3Tapes] using
          loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTape
            bits suffix []
    · exact
        ThreeTape.NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.loweredDescription_haltsFromTapeEquiv
          bits suffix []
  · exact projector_haltsFromTapeEquiv bits suffix

end CanonicalBoolWordSuffixMaterializer
end NestedLayoutMaterializerInternal
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
