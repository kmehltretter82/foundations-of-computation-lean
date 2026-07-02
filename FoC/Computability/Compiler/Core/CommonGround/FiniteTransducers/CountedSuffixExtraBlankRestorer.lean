import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

/-!
# Counted suffix extra-blank restorer

This module packages the reusable finite-machine obligation for restoring a
counted suffix window after a temporary extra blank has been introduced at the
right edge of the payload.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def countedSuffixExtraBlankRightGapSourceTape
    (pref suffixRest : Word Bool) (suffixFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindSourceTapeWithBase []
    (List.append pref (suffixFirst :: suffixRest))
    (none ::
      none ::
      none ::
      List.append
        (List.replicate suffixRest.length (none : Option Bool))
        tail)

def countedSuffixExtraBlankRestoredSourceTape
    (pref suffixRest : Word Bool) (suffixFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindTargetTapeWithBase []
    (List.append pref (suffixFirst :: suffixRest))
    (none ::
      none ::
      none ::
      List.append
        (List.replicate suffixRest.length (none : Option Bool))
        tail)

def CountedSuffixExtraBlankRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall (pref suffixRest : Word Bool)
      (suffixFirst : Bool) (tail : List (Option Bool)),
      restorer.HaltsFromTape
        (countedSuffixExtraBlankRightGapSourceTape
          pref suffixRest suffixFirst tail)
        (countedSuffixExtraBlankRestoredSourceTape
          pref suffixRest suffixFirst tail)

def CountedSuffixExtraBlankRestorerConstruction : Prop :=
  exists restorer : MachineDescription,
    CountedSuffixExtraBlankRestorerSpec restorer

theorem countedSuffixExtraBlankRestorerConstruction_core :
    CountedSuffixExtraBlankRestorerConstruction := by
  exact
    ⟨rightEdgeRewindDescription,
      rightEdgeRewindDescription_subroutineReady,
      fun pref suffixRest suffixFirst tail =>
        rightEdgeRewindDescription_haltsFromTapeWithBase []
          (List.append pref (suffixFirst :: suffixRest))
          (none ::
            none ::
            none ::
            List.append
              (List.replicate suffixRest.length (none : Option Bool))
              tail)⟩

end FiniteTransducers
end CommonGround

end Computability
end FoC
