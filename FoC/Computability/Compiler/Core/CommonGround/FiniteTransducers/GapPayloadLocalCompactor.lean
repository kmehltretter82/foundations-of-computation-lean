import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadScan
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

/-!
# Gap-payload scan to local compactor source

This module records the tape-shape bridge between the gap-to-payload scanner
and the local right-blank gap compactor.  It is useful when an erased field is
followed by a nonempty payload whose last bit has already been exposed.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

theorem rightBlankGapPayloadScanTargetTape_move_right_eq_localGapSource
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current leftBit : Bool) (payloadRest pref : Word Bool)
    (padding : List (Option Bool))
    (hpayload :
      current :: payloadRest =
        List.append pref [leftBit]) :
    Tape.move Direction.right
        (rightBlankGapPayloadScanTargetTape baseLeft (Nat.succ gap)
          current payloadRest padding) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft gap baseLeft)
        leftBit pref.reverse 0 padding := by
  have hrev :
      ((current :: payloadRest).reverse.map some) =
        some leftBit :: (pref.reverse.map some) := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some) hpayload
    simpa [List.reverse_append, List.map_append] using h
  rw [rightBlankGapPayloadScanTargetTape]
  rw [hrev]
  simp [rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
    rightBlankLocalGapBaseLeft, Tape.move, Tape.moveLeft,
    Tape.moveRight, tapeAtCells, List.replicate_succ]

end FiniteTransducers
end CommonGround

end Computability
end FoC
