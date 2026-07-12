import FoC.Computability.Compiler.Structured.HeadRoutes.RepresentativeCleanup
import FoC.Computability.Compiler.Structured.Lowering.EncodedInjectivity

set_option doc.verso true

/-!
# Selected-head cleanup contract guardrails

The generated selected-segment scanner erases the physical head-marker pair.
Consequently, its post-scan tape does not determine an arbitrary logical tape,
even up to {lit}`Tape.Equiv`.  This module records a concrete collision for
the retired cleanup route and proves source-equivalence functionality for the
marker-preserving tape-2 projector contract that replaces it.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace SelectedSegmentLogicalTapeDecoderCleanupContractGuardrails

/-- A logical tape whose nonblank left cell precedes a blank head. -/
def markerCollisionTargetA : Tape Bool :=
  { left := [some true]
    head := none
    right := [some false] }

/-- A different logical tape with the same lossy post-scanner footprint. -/
def markerCollisionTargetB : Tape Bool :=
  { left := [none, some true]
    head := some false
    right := [] }

/-- Erasing the head marker makes the two concrete scanner handoffs equal. -/
theorem markerCollisionSource_eq :
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        markerCollisionTargetA [] [] =
      selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        markerCollisionTargetB [] [] := by
  decide

/-- The two requested public targets are not tape-equivalent. -/
theorem markerCollisionTarget_not_equiv :
    ¬ Tape.Equiv markerCollisionTargetA markerCollisionTargetB := by
  intro h
  cases h.2.1

/--
No deterministic subroutine can recover every logical tape from the lossy
post-scanner source, even when the requested result is only tape-equivalent.
-/
theorem paddedCleanupConstruction_impossible :
    ¬ SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction := by
  rintro ⟨cleanup, hready, hrun⟩
  rcases hrun markerCollisionTargetA [] [] with
    ⟨actualA, hhaltA, hequivA⟩
  rcases hrun markerCollisionTargetB [] [] with
    ⟨actualB, hhaltB, hequivB⟩
  rw [markerCollisionSource_eq] at hhaltA
  have hactual : actualA = actualB :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hready.right hhaltA hhaltB
  subst actualA
  exact markerCollisionTarget_not_equiv
    (Tape.Equiv.trans (Tape.Equiv.symm hequivA) hequivB)

/-- Padding does not hide the distinct head cells of the exact representatives. -/
theorem markerCollisionRepresentativeOutput_ne :
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
        markerCollisionTargetA [] [] ≠
      selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
        markerCollisionTargetB [] [] := by
  intro h
  have hhead := congrArg Tape.head h
  cases hhead

/--
The exact representative forward-split frontier is impossible for the same
collision; splitting on padding cannot restore the erased head marker.
-/
theorem paddedRepresentativeCleanupForwardSplitConstruction_impossible :
    ¬ SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction := by
  rintro ⟨cleanup, hnil, _hcons⟩
  rcases hnil with ⟨hready, hrun⟩
  have hhaltA := hrun markerCollisionTargetA []
  have hhaltB := hrun markerCollisionTargetB []
  rw [markerCollisionSource_eq] at hhaltA
  apply markerCollisionRepresentativeOutput_ne
  exact
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hready.right hhaltA hhaltB

/-!
## Repaired marker-preserving projector contract
-/

/--
Equivalent canonical guarded three-tape sources carry the same logical tape 2.
This is the source-class functionality required by the repaired #17 target.
-/
theorem tape2ProjectorTarget_eq_of_source_equiv
    {T0 T1 T2 U0 U1 U2 : Tape Bool}
    (hsource :
      Tape.Equiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (encodedGuardedStructured3Tapes U0 U1 U2)) :
    T2 = U2 := by
  exact
    (encodedGuardedStructuredTapes_three_equiv_inj
      (by
        simpa [encodedGuardedStructured3Tapes] using hsource)).2.2

/-- Equivalence-facing form matching {name}`StructuredTape2ProjectorSpec`. -/
theorem tape2ProjectorTarget_equiv_of_source_equiv
    {T0 T1 T2 U0 U1 U2 : Tape Bool}
    (hsource :
      Tape.Equiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (encodedGuardedStructured3Tapes U0 U1 U2)) :
    Tape.Equiv T2 U2 := by
  rw [tape2ProjectorTarget_eq_of_source_equiv hsource]
  exact Tape.Equiv.refl _

#print axioms paddedCleanupConstruction_impossible
#print axioms paddedRepresentativeCleanupForwardSplitConstruction_impossible
#print axioms tape2ProjectorTarget_equiv_of_source_equiv

end SelectedSegmentLogicalTapeDecoderCleanupContractGuardrails

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
