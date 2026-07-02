import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind

set_option doc.verso true

/-!
# Counted suffix-boundary locator

This module packages the reusable finite-machine obligation for locating the
boundary before a suffix when the right padding contains a blank count window
whose length is exactly the suffix length.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def countedSuffixBoundaryLocatorPadding
    (guard : Option Bool) (suffix : Word Bool)
    (tail : List (Option Bool)) : List (Option Bool) :=
  guard ::
    List.append
      (List.replicate suffix.length (none : Option Bool))
      tail

def countedSuffixBoundaryLocatorSourceTape
    (pref suffix : Word Bool) (guard : Option Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  rightEdgeScanTargetTapeFromLeft [none] (List.append pref suffix)
    (countedSuffixBoundaryLocatorPadding guard suffix tail)

def countedSuffixBoundaryLocatorTargetTape
    (pref suffix : Word Bool) (guard : Option Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  rightEdgeScanSourceTapeFromLeft
    (none :: pref.reverse.map some) suffix
    (countedSuffixBoundaryLocatorPadding guard suffix tail)

def CountedSuffixBoundaryLocatorSpec
    (locator : MachineDescription) : Prop :=
  locator.SubroutineReady ∧
    forall (pref suffixRest : Word Bool)
      (suffixFirst : Bool) (guard : Option Bool)
      (tail : List (Option Bool)),
      locator.HaltsFromTape
        (countedSuffixBoundaryLocatorSourceTape
          pref (suffixFirst :: suffixRest) guard tail)
        (countedSuffixBoundaryLocatorTargetTape
          pref (suffixFirst :: suffixRest) guard tail)

def CountedSuffixBoundaryLocatorConstruction : Prop :=
  exists locator : MachineDescription,
    CountedSuffixBoundaryLocatorSpec locator

theorem countedSuffixBoundaryLocatorConstruction_core :
    CountedSuffixBoundaryLocatorConstruction := by
  sorry

end FiniteTransducers
end CommonGround

end Computability
end FoC
