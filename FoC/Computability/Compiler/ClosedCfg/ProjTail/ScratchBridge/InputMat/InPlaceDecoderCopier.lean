import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.InPlaceDecoder
import FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutParser.Materializer.PostDecodeSuffixCopier
import FoC.Computability.Compiler.Structured.Lowering.Composition

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape
namespace CountWindowInputMat
namespace InPlaceDecoderCopier

open NestedLayoutMaterializerInternal.PostDecodeSuffixCopier

theorem copier_description_run_with_counter
    (counter : Tape Bool) (hcounter : counter.head = none)
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description.runConfig
        (2 * bits.length + 2 * (false :: suffixTail).length + 4)
        (config seekDecodedStop
          (structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding)
          counter
          (rightEdgeScanSourceTapeFromLeft [none] bits [])) =
      config halt
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail rightPadding)
        counter
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append bits (false :: suffixTail)) []) := by
  let source := structuredBoolWordRawBitsDecoderSourceTargetTape
    bits suffixTail rightPadding
  have hsource : source.head = some false := by
    exact sourceTargetTape_head bits suffixTail rightPadding
  rw [show
      2 * bits.length + 2 * (false :: suffixTail).length + 4 =
        (bits.length + 1) +
          ((2 * (false :: suffixTail).length + 2) +
            (bits.length + 1)) by
    lia]
  rw [Description.runConfig_add]
  change
    NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description.runConfig
        ((2 * (false :: suffixTail).length + 2) +
          (bits.length + 1))
      (NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description.runConfig
        (bits.length + 1)
        (config seekDecodedStop source counter
          (rightEdgeScanSourceTapeFromLeft [none] bits []))) = _
  have hseek :=
    seekDecodedStop_run source counter hsource hcounter [none] bits
  change
    NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description.runConfig
        (bits.length + 1)
        (config seekDecodedStop source counter
          (rightEdgeScanSourceTapeFromLeft [none] bits [])) =
      config copySuffix source counter
        (decodedStopTape [none] bits) at hseek
  rw [hseek]
  rw [Description.runConfig_add]
  change
    NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description.runConfig
      (bits.length + 1)
      (NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description.runConfig
        (2 * (false :: suffixTail).length + 2)
        (config copySuffix source counter
          (decodedStopTape [none] bits))) = _
  rw [copyRestore_run_actual counter hcounter bits suffixTail rightPadding]
  rw [rewindDecoded_run source counter hsource hcounter bits]
  simp [source, rightEdgeScanSourceTapeFromLeft, List.map_append,
    List.append_assoc]

theorem copier_description_run_with_blank_counter
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description.runConfig
        (2 * bits.length + 2 * (false :: suffixTail).length + 4)
        (config seekDecodedStop
          (structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding)
          Tape.blank
          (rightEdgeScanSourceTapeFromLeft [none] bits [])) =
      config halt
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail rightPadding)
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append bits (false :: suffixTail)) []) := by
  exact copier_description_run_with_counter Tape.blank rfl
    bits suffixTail rightPadding

theorem copier_loweredDescription_haltsFromTapeEquiv_with_blank_counter
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail rightPadding)
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none] bits []))
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail rightPadding)
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append bits (false :: suffixTail)) [])) := by
  simpa [NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.loweredDescription,
    encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description_wellFormed
      NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description_haltTransitionFree
      NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.description_supported
      (c := config seekDecodedStop
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail rightPadding)
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none] bits []))
      (tapes :=
        [ structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding
        , Tape.blank
        , rightEdgeScanSourceTapeFromLeft [none]
            (List.append bits (false :: suffixTail)) [] ])
      rfl rfl
      ⟨2 * bits.length + 2 * (false :: suffixTail).length + 4,
        copier_description_run_with_blank_counter
          bits suffixTail rightPadding⟩

def loweredDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    InPlaceDecoder.loweredDescription
    NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.loweredDescription

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  exact
    canonicalPrimitiveSeqDescription_subroutineReady
      InPlaceDecoder.loweredDescription_subroutineReady
      NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.loweredDescription_subroutineReady

theorem loweredDescription_haltsFromTapeEquiv
    (bits suffixTail : Word Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rightEdgeRewindTargetTape
          (OutputLengthAllocator.rawWord bits.length
            (InPlaceDecoder.fieldTail bits suffixTail)) [])
        Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          bits.length []))
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append bits (false :: suffixTail)) [])) := by
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      InPlaceDecoder.loweredDescription_subroutineReady
      NestedLayoutMaterializerInternal.PostDecodeSuffixCopier.loweredDescription_subroutineReady
      (InPlaceDecoder.loweredDescription_haltsFromTapeEquiv bits suffixTail)
      (copier_loweredDescription_haltsFromTapeEquiv_with_blank_counter
        bits suffixTail [])

end InPlaceDecoderCopier
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
