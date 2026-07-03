import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner.Basic
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Basic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind

set_option doc.verso true

/-!
# Count-window raw-source encoder

This module packages the reusable finite-machine obligation for re-encoding a
raw split layout window.  The input contains the parsed layout bits directly,
followed by a blank count window, one repaired extra count-window blank, and a
tail.  The output restores the encoded header, layout length, skipped-cell
field, counted-cell field, consumes the repaired blank, and preserves the tail.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def countWindowRawSourceEncoderHeaderCells : List (Option Bool) :=
  (encodeCodeSymbolAsInput MachineCodeSymbol.header).map some

def countWindowRawSourceEncoderLayoutLengthCells
    (layout : Word Bool) : List (Option Bool) :=
  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
    layout.length).map some

def countWindowRawSourceEncoderCellFieldCells
    (cells : List (Option Bool)) : List (Option Bool) :=
  (EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
    cells).map some

def countWindowRawSourceEncoderSourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((List.append skipped count).map some)
      (none ::
        none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail))

def countWindowRawSourceEncoderTargetTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append
      countWindowRawSourceEncoderHeaderCells
      (List.append
        (countWindowRawSourceEncoderLayoutLengthCells
          (List.append skipped count))
        (List.append
          (countWindowRawSourceEncoderCellFieldCells
            (skipped.map some))
          (List.append
            (countWindowRawSourceEncoderCellFieldCells
              (count.map some))
            (List.append tail
              (List.replicate count.length
                (none : Option Bool)))))))

def CountWindowRawSourceEncoderSpec
    (encoder : MachineDescription) : Prop :=
  encoder.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tail : List (Option Bool)),
      encoder.HaltsFromTape
        (countWindowRawSourceEncoderSourceTape skipped count tail)
        (countWindowRawSourceEncoderTargetTape skipped count tail)

def CountWindowRawSourceEncoderConstruction : Prop :=
  exists encoder : MachineDescription,
    CountWindowRawSourceEncoderSpec encoder

theorem countWindowRawSourceEncoderConstruction_core :
    CountWindowRawSourceEncoderConstruction := by
  sorry

end FiniteTransducers
end CommonGround

end Computability
end FoC
