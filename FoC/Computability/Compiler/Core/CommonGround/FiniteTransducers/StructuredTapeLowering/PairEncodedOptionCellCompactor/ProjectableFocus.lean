import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.PairEncodedOptionCellCompactor.Base

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace PairEncodedOptionCellCompactor

theorem splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction_core :
    SplitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction := by
  -- Reusable finite-machine egress: use the pair-encoded source/marker
  -- structure to focus tape 2 at the semantic separator of
  -- bits.map some ++ none :: padding.  The scan may leave tapes 0 and 1 in
  -- noncanonical positions; only tape 2 must be projectable.
  sorry

theorem splitTargetProjectableRightEdgeRewindOutputConstruction_core :
    SplitTargetProjectableRightEdgeRewindOutputConstruction := by
  exact
    splitTargetProjectableRightEdgeRewindOutputConstruction_of_splitPadSymbolCases
      splitTargetProjectableRightEdgeRewindOutputSplitPadSymbolCaseConstruction_core


end PairEncodedOptionCellCompactor
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
