import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter.Shape

set_option doc.verso true

/-!
# Original simulator-input scratch width

The exact #18 target retains a blank reservoir whose width is measured from
the original encoded simulator-layout input, not from the final encoded
configuration.  This module records the simple but essential length identity
that the physical field parser and serializer must share.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterTheory

/-- Every encoded simulator layout contains at least the leading header
symbol, hence at least two physical Boolean bits. -/
theorem simulatorLayout_asBoolInput_length_ge_two
    (L : SimulatorLayout) :
    2 <= (SimulatorLayout.asBoolInput L).length := by
  rw [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend]
  simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem simulatorLayout_asBoolInput_ne_nil
    (L : SimulatorLayout) :
    SimulatorLayout.asBoolInput L ≠ [] := by
  intro hnil
  have hlen := simulatorLayout_asBoolInput_length_ge_two L
  simp [hnil] at hlen

/-- The stored context of a nonempty input word consists of every bit except
the bit under the head. -/
theorem input_contextLength_eq_length_sub_one
    (bits : Word Bool) (hbits : bits ≠ []) :
    Tape.contextLength (Tape.input bits) = bits.length - 1 := by
  cases bits with
  | nil => contradiction
  | cons bit rest =>
      simp [Tape.input, Tape.contextLength]

/-- Required #18 scratch width in purely syntactic input-length currency. -/
theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_eq_length_sub_one
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner L =
      (SimulatorLayout.asBoolInput L).length - 1 := by
  rw [FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
    FixedDescriptionBoundedSimulatorInput]
  exact input_contextLength_eq_length_sub_one
    (SimulatorLayout.asBoolInput L)
    (simulatorLayout_asBoolInput_ne_nil L)

/-- Equivalent successor form convenient for a parser that emits one marker
for every source bit after the first. -/
theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_add_one
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner L + 1 =
      (SimulatorLayout.asBoolInput L).length := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_eq_length_sub_one]
  have hlen := simulatorLayout_asBoolInput_length_ge_two L
  lia

/-- Unary marker block that can carry the original scratch width through the
destructive simulation and serializer phases. -/
def scratchWidthMarkers (L : SimulatorLayout) : List (Option Bool) :=
  List.replicate
    (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner L)
    (some true)

@[simp] theorem scratchWidthMarkers_length (L : SimulatorLayout) :
    (scratchWidthMarkers L).length =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner L := by
  simp [scratchWidthMarkers]

end RunConfigEmitterTheory
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
