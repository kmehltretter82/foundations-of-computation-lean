import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Core

set_option doc.verso true

/-!
# Exact target-specific run-config closeout

The fixed-description loop computes four semantic fields: the preserved input
word, the preserved stage, the final configuration, and the accumulated hit
bit.  This module packages those fields independently of physical
representation and exposes the two scratch-padded target presentations used by
the guarded serializer.  The serializer boundary uses tape-equivalence while
fixing the exact normalized output word.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace ExactCloseout

/-- Semantic fields that survive the execution loop and are serialized at the
run-config emitter endpoint.  The scratch width is separate because it describes the
physical blank reservoir, not a simulator-layout field. -/
structure Fields where
  input : Word Bool
  stage : Nat
  config : Configuration
  hit : Bool

/-- Reassemble the ordinary simulator layout represented by closeout fields. -/
def Fields.asLayout (F : Fields) : SimulatorLayout where
  input := F.input
  stage := F.stage
  config := F.config
  hit := F.hit

/-- Read closeout fields from an ordinary simulator layout. -/
def Fields.ofLayout (L : SimulatorLayout) : Fields where
  input := L.input
  stage := L.stage
  config := L.config
  hit := L.hit

/-- Canonical encoded Boolean word determined by the four closeout fields. -/
def Fields.outputBits (F : Fields) : Word Bool :=
  SimulatorLayout.asBoolInput F.asLayout

/-- Exact scratch-padded output with a caller-supplied blank reservoir. -/
def Fields.scratchTape (scratchWidth : Nat) (F : Fields) : Tape Bool :=
  inputWithTrailingBlankPadding F.outputBits scratchWidth

/-- The convenient one-cell-right serializer target used before final
parking. -/
def Fields.rightScratchTape (scratchWidth : Nat) (F : Fields) : Tape Bool :=
  Tape.move Direction.right (F.scratchTape scratchWidth)

/-- Trailing scratch blanks do not change the normalized emitted word. -/
theorem Fields.scratchTape_normalizedOutput
    (scratchWidth : Nat) (F : Fields) :
    Tape.normalizedOutput (F.scratchTape scratchWidth) = F.outputBits := by
  exact inputWithTrailingBlankPadding_normalizedOutput
    F.outputBits scratchWidth

theorem Fields.scratchTape_equiv_input
    (scratchWidth : Nat) (F : Fields) :
    Tape.Equiv (F.scratchTape scratchWidth) (Tape.input F.outputBits) := by
  exact inputWithTrailingBlankPadding_equiv_input
    F.outputBits scratchWidth

/-- Semantic fields required by the fixed-description bounded run. -/
def semanticFields
    (D : MachineDescription) (L : SimulatorLayout) : Fields :=
  Fields.ofLayout (SimulatorLayout.run D L.stage L)

theorem semanticFields_rightScratchTape_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    (semanticFields D L).rightScratchTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
        D L := by
  rfl

end ExactCloseout
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
