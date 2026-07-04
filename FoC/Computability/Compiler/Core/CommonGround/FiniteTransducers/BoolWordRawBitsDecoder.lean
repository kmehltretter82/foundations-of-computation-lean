import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWord

set_option doc.verso true

/-!
# Boolean-word raw-bits decoder

This module packages the generic part of the encoded Boolean-word to raw-bits
materializer.  The finite-machine leaf starts at a caller prefix, decodes the
following encoded Boolean-word field, and rewrites the surrounding suffix area
into the caller's target scan-source padding.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace CommonGround
namespace FiniteTransducers

/--
The encoded Boolean-word field as raw tape bits, without any surrounding code
symbol or caller suffix.
-/
def boolWordRawBitsDecoderEncodedFieldBits
    (bits : Word Bool) : Word Bool :=
  List.append
    (stageNatBits bits.length)
    (cellsCodeBits (bits.map some))

/--
Source tape for the generic Boolean-word raw-bits decoder.  The finite leaf
starts at the left edge of a caller prefix, decodes the following encoded
Boolean-word field, and may use the caller suffix/padding to materialize the
target boundary.
-/
def boolWordRawBitsDecoderSourceTape
    (prefixBits : Word Bool) (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindTargetTape
    (List.append prefixBits
      (List.append
        (boolWordRawBitsDecoderEncodedFieldBits bits)
        suffixTail))
    rightPadding

/--
Final raw-bits target: decoded Boolean bits in right-edge scan-source shape,
with caller-owned padding.
-/
def boolWordRawBitsDecoderTargetTape
    (bits : Word Bool) (targetPadding : List (Option Bool)) : Tape Bool :=
  rightEdgeScanSourceTapeFromLeft [none] bits targetPadding

def BoolWordRawBitsDecoderSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (prefixBits bits suffixTail : Word Bool)
      (rightPadding targetPadding : List (Option Bool)),
      decoder.HaltsFromTape
        (boolWordRawBitsDecoderSourceTape
          prefixBits bits suffixTail rightPadding)
        (boolWordRawBitsDecoderTargetTape
          bits targetPadding)

def BoolWordRawBitsDecoderConstruction : Prop :=
  exists decoder : MachineDescription,
    BoolWordRawBitsDecoderSpec decoder

/--
The finite-machine leaf for a prefix-aware Boolean-word materializer.  It
decodes the encoded Boolean-word field and rewrites the caller-owned suffix
area into the requested scan-source padding.
-/
theorem boolWordRawBitsDecoderConstruction_core :
    BoolWordRawBitsDecoderConstruction := by
  sorry

end FiniteTransducers
end CommonGround

end Computability
end FoC
