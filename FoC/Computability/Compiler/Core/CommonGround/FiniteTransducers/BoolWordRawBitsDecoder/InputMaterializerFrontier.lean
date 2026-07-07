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
  -- Remaining finite-machine leaf: materialize the indexed raw-bits source
  -- family into the guarded three-tape decoder input with matching output
  -- padding for the same index.
  sorry

end FiniteTransducers
end CommonGround

end Computability
end FoC
