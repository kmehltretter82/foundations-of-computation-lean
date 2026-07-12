import FoC.Computability.Compiler.Structured.HeadRoutes.RepresentativeCleanup
import FoC.Computability.Compiler.Structured.Lowering.EncodedInjectivity
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer

set_option doc.verso true

/-!
# Selected-head cleanup contract guardrails

The generated selected-segment scanner erases the physical head-marker pair.
Consequently, its post-scan tape does not determine an arbitrary logical tape,
even up to {lit}`Tape.Equiv`.  This module records a concrete collision for
the retired cleanup route and proves source-equivalence functionality for the
marker-preserving tape-2 projector contract that replaces it.

The retired raw-head ingress target family has a separate collision: adding
one outer blank leaves the public source tape equivalent but changes the
requested guarded structured encoding.  That impossible #16 contract is
recorded here independently of the deleted, unconsumed route.
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

namespace SelectedSegmentLogicalTapeDecoderRawHeadIngressContractGuardrails

/-- Historical #16 index family, retained only to state its impossibility. -/
abbrev HistoricalRawHeadIngressIndex : Type :=
  Tape Bool × (List (Tape Bool) × List (Option Bool))

/-- Historical raw selected-head source shape. -/
def historicalRawHeadSourceTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  tapeAtEncodedSplit encodedPrefix
    (encodedStructuredTapeCells (guardLogicalTape target :: rest))

/-- Historical #16 guarded structured target shape. -/
def historicalRawHeadStructuredInputTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (historicalRawHeadSourceTape target rest encodedPrefix)
    Tape.blank
    Tape.blank

/-- Historical #16 public source family. -/
def historicalRawHeadIngressSource
    (input : HistoricalRawHeadIngressIndex) : Tape Bool :=
  historicalRawHeadSourceTape input.1 input.2.1 input.2.2

/-- Historical #16 requested target family. -/
def historicalRawHeadIngressTarget
    (input : HistoricalRawHeadIngressIndex) : Tape Bool :=
  historicalRawHeadStructuredInputTape input.1 input.2.1 input.2.2

/-- Minimal raw-head source with no represented outer blank. -/
def outerBlankCollisionSourceA : Tape Bool :=
  historicalRawHeadSourceTape Tape.blank [] []

/-- The same raw-head source with one represented outer blank. -/
def outerBlankCollisionSourceB : Tape Bool :=
  historicalRawHeadSourceTape Tape.blank [] [none]

/-- Requested guarded target for the source without an outer blank. -/
def outerBlankCollisionTargetA : Tape Bool :=
  historicalRawHeadStructuredInputTape Tape.blank [] []

/-- Requested guarded target for the source with one outer blank. -/
def outerBlankCollisionTargetB : Tape Bool :=
  historicalRawHeadStructuredInputTape Tape.blank [] [none]

def outerBlankCollisionIndexA :
    HistoricalRawHeadIngressIndex :=
  (Tape.blank, ([], []))

def outerBlankCollisionIndexB :
    HistoricalRawHeadIngressIndex :=
  (Tape.blank, ([], [none]))

/-- The extra outer blank is invisible modulo tape equivalence. -/
theorem outerBlankCollisionSource_equiv :
    Tape.Equiv outerBlankCollisionSourceA outerBlankCollisionSourceB := by
  simp [outerBlankCollisionSourceA, outerBlankCollisionSourceB,
    historicalRawHeadSourceTape,
    tapeAtEncodedSplit, tapeAtCells, encodedStructuredTapeCells,
    tapeSeparatorCells, logicalTapeCode, logicalCellCode, headMarkerCells,
    guardLogicalTape, Tape.blank, Tape.Equiv, Tape.dropTrailingNone]

/-- The requested guarded targets expose different normalized words. -/
theorem outerBlankCollisionTarget_normalizedOutput_ne :
    Tape.normalizedOutput outerBlankCollisionTargetA ≠
      Tape.normalizedOutput outerBlankCollisionTargetB := by
  decide

/-- The requested targets are therefore not tape-equivalent. -/
theorem outerBlankCollisionTarget_not_equiv :
    ¬ Tape.Equiv outerBlankCollisionTargetA outerBlankCollisionTargetB := by
  intro h
  exact outerBlankCollisionTarget_normalizedOutput_ne
    (Tape.Equiv.normalizedOutput_eq h)

/-- The retired #16 target family is inconsistent with deterministic tape
equivalence semantics. -/
theorem rawHeadStructuredInputTargetFamilyConstruction_impossible :
    ¬ Structured3InputTargetFamilyConstruction
      historicalRawHeadIngressSource
      historicalRawHeadIngressTarget := by
  rintro ⟨materializer, hready, hrun⟩
  rcases hrun outerBlankCollisionIndexA with
    ⟨actualA, hhaltA, hequivA⟩
  have hhaltA' :
      materializer.HaltsFromTape outerBlankCollisionSourceA actualA := by
    simpa [outerBlankCollisionIndexA, outerBlankCollisionSourceA,
      historicalRawHeadIngressSource]
      using hhaltA
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := materializer)
        (Tin := outerBlankCollisionSourceA)
        (Tin' := outerBlankCollisionSourceB)
        (Tout := actualA)
        outerBlankCollisionSource_equiv hhaltA' with
    ⟨actualFromB, hhaltFromB, hequivFromB⟩
  rcases hrun outerBlankCollisionIndexB with
    ⟨actualB, hhaltB, hequivB⟩
  have hhaltB' :
      materializer.HaltsFromTape outerBlankCollisionSourceB actualB := by
    simpa [outerBlankCollisionIndexB, outerBlankCollisionSourceB,
      historicalRawHeadIngressSource]
      using hhaltB
  have hactual : actualFromB = actualB :=
    haltsFromTape_functional_of_haltTransitionFree
      hready.right hhaltFromB hhaltB'
  have hequivA' : Tape.Equiv actualA outerBlankCollisionTargetA := by
    simpa [outerBlankCollisionIndexA, outerBlankCollisionTargetA,
      historicalRawHeadIngressTarget]
      using hequivA
  have hequivB' : Tape.Equiv actualB outerBlankCollisionTargetB := by
    simpa [outerBlankCollisionIndexB, outerBlankCollisionTargetB,
      historicalRawHeadIngressTarget]
      using hequivB
  apply outerBlankCollisionTarget_not_equiv
  rw [hactual] at hequivFromB
  exact Tape.Equiv.trans (Tape.Equiv.symm hequivA')
    (Tape.Equiv.trans (Tape.Equiv.symm hequivFromB) hequivB')

#print axioms rawHeadStructuredInputTargetFamilyConstruction_impossible

end SelectedSegmentLogicalTapeDecoderRawHeadIngressContractGuardrails

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
