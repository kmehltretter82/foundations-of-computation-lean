import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerOutputLevelSimulator

set_option doc.verso true

/-!
# Controller fuel-pair search bridge

This module isolates the bounded {lit}`(limit, fuel)` pair enumerator and the
classifier handoff used by the controller search driver.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

private theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction_finite_leaf :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction := by
  intro runner hrunner
  -- Remaining finite-table obligation: enumerate bounded `(limit, fuel)`
  -- pairs, invoke the exact-fuel runner, preserve its encoded boolean-word
  -- output, and halt one cell right of that output for classifier handoff.
  sorry

theorem pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_finite_leaf :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction :=
  pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_of_boundedRightShiftedEnumerator_emitter
    pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction_finite_leaf
    pairedRecognizerDovetailControllerBoolWordRawOutputEmitterConstruction_scaffold

end Computability
end FoC
