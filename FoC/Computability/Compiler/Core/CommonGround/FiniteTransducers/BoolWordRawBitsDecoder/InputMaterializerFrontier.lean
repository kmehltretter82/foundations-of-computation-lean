import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder.EndpointAdapters

set_option doc.verso true

/-!
# Boolean-word raw-bits input materializer frontier

Reusable indexed input-materializer leaf for callers that need to preload a
guarded structured raw-bits decoder input.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers

theorem structuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction_core
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool)) :
    StructuredBoolWordRawBitsDecoderIndexedInputMaterializerConstruction
      bits suffixTail rightPadding outputPadding := by
  -- REFUTED AS STATED: arbitrary indexed `outputPadding` is not functional in
  -- the source.  Two indices can have the same source tape but require
  -- non-equivalent structured targets, e.g. output padding `[]` versus
  -- `[some true]`, contradicting determinism of a `SubroutineReady` machine.
  sorry

end FiniteTransducers
end CommonGround

end Computability
end FoC
