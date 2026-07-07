import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EndpointSupport
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependEncodedLayoutBlankSentinel

set_option doc.verso true

/-!
# Raw-boundary blank-sentinel finalizer endpoint

This module exposes the delimiter-preserving encoded-layout finalizer against
the public {lit}`rightEdgeTape` endpoint.  It is the reusable last stage for
raw-boundary routes that first reduce the compact source layout to a blank
sentinel while remembering the live tail head in finite control.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def tailHeadErasedBlankSentinelTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.replicate
      (tailHeadImmediateScratchCellCount count +
        (tailHeadRawBaseLeft skipped count).length)
      (none : Option Bool))
    (none :: tail)

theorem tailHeadErasedBlankSentinelTape_left_length
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    (tailHeadErasedBlankSentinelTape skipped count tail).left.length =
      tailHeadImmediateScratchCellCount count +
        (tailHeadRawBaseLeft skipped count).length := by
  simp [tailHeadErasedBlankSentinelTape, tapeAtCells]

theorem tailHeadErasedBlankSentinelTape_left_length_eq_tailHeadHandoffTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadErasedBlankSentinelTape skipped count tail).left.length =
      (tailHeadHandoffTape skipped count tailFirst tail).left.length := by
  rw [tailHeadErasedBlankSentinelTape_left_length]
  rw [tailHeadHandoffTape_eq_tapeAtCells_scratchBase]
  simp [tapeAtCells]

def rawBoundaryBlankSentinelFinalizerDescription
    (skipped count : Word Bool) (tailFirst : Bool) :
    MachineDescription :=
  prependEncodedLayoutLeftOfBlankSentinelThenRestoreDescription
    (List.append skipped count) tailFirst

theorem rawBoundaryBlankSentinelFinalizerDescription_subroutineReady
    (skipped count : Word Bool) (tailFirst : Bool) :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).SubroutineReady := by
  simpa [rawBoundaryBlankSentinelFinalizerDescription] using
    prependEncodedLayoutLeftOfBlankSentinelThenRestoreDescription_subroutineReady
      (List.append skipped count) tailFirst

theorem rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_rightEdgeTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).HaltsFromTape
      (tapeAtCells [] (none :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  simpa [rawBoundaryBlankSentinelFinalizerDescription, rightEdgeTape,
    encodedLayoutChunkBits_eq_encodedLayoutBits] using
    prependEncodedLayoutLeftOfBlankSentinelThenRestoreDescription_haltsFrom
      (List.append skipped count) tailFirst tail

theorem rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_blankLeft_rightEdgeTapeEquiv
    (skipped count : Word Bool) (tailFirst : Bool)
    (padding : Nat) (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).HaltsFromTapeEquiv
      (tapeAtCells
        (List.replicate padding (none : Option Bool))
        (none :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  exact
    MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      (Tape.Equiv.symm
        (tapeAtCells_replicate_none_left_equiv_empty
          padding (none :: tail)))
      (rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_rightEdgeTape
        skipped count tailFirst tail)

theorem tailHeadErasedBlankSentinelTape_equiv_empty
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.Equiv
      (tailHeadErasedBlankSentinelTape skipped count tail)
      (tapeAtCells [] (none :: tail)) := by
  simpa [tailHeadErasedBlankSentinelTape] using
    tapeAtCells_replicate_none_left_equiv_empty
      (tailHeadImmediateScratchCellCount count +
        (tailHeadRawBaseLeft skipped count).length)
      (none :: tail)

theorem rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_erasedTailHeadHandoff_rightEdgeTapeEquiv
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).HaltsFromTapeEquiv
      (tailHeadErasedBlankSentinelTape skipped count tail)
      (rightEdgeTape skipped count tailFirst tail) := by
  exact
    MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      (Tape.Equiv.symm
        (tailHeadErasedBlankSentinelTape_equiv_empty
          skipped count tail))
      (rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_rightEdgeTape
        skipped count tailFirst tail)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
