import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridge.InputMaterializerContracts

set_option doc.verso true

/-!
# Count-window input materializer frontier

Concrete count-window materializer leaves kept near the top for proof work.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

theorem countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  -- Remaining finite-machine leaf: materialize the bool-word raw-bits source
  -- family into the guarded three-tape decoder input with the output padding
  -- indexed by the same count-window source.
  sorry

theorem countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_of_indexed
      countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction_core

theorem countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_of_boolWord
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerConstruction_core

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_of_structured3InputMaterializer
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerConstruction_core

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
