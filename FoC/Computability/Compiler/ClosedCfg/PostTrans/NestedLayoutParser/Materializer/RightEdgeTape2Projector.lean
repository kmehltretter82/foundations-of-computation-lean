import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.Assembly
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind

set_option maxRecDepth 10000

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
open Tape2Projector
namespace NestedLayoutMaterializerInternal
namespace Tape2Projector

def rightEdgeEndpointCells (first : Bool) (rest : Word Bool) :
    List (Option Bool) :=
  List.append ((first :: rest).map some) [none, none]

theorem logicalTapeBits_guard_rightEdgeScanSourceTapeFromLeft
    (first : Bool) (rest : Word Bool) :
    logicalTapeBits
        (guardLogicalTape
          (rightEdgeScanSourceTapeFromLeft [none]
            (first :: rest) [])) =
      List.append [false, false]
        (List.append [false, false, true, true]
          (logicalCellListBits (rightEdgeEndpointCells first rest))) := by
  cases first <;> cases rest <;>
    simp [rightEdgeScanSourceTapeFromLeft, tapeAtCells,
      guardLogicalTape, logicalTapeBits, logicalCellListBits,
      logicalCellBits, rightEdgeEndpointCells, List.append_assoc]

def extraLeftBlankCellEraserDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 (some false) none Direction.right 1
    , transition 1 (some false) none Direction.right 2 ]

theorem extraLeftBlankCellEraserDescription_subroutineReady :
    extraLeftBlankCellEraserDescription.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    extraLeftBlankCellEraserDescription
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem extraLeftBlankCellEraserDescription_haltsFromTape
    (padding : Nat) (remaining : Word Bool) :
    extraLeftBlankCellEraserDescription.HaltsFromTape
      (tapeAtCells
        (List.append
          (List.replicate padding (none : Option Bool)) [some false])
        (List.append
          ((List.append [false, false]
            (List.append [false, false, true, true] remaining)).map some)
          [none]))
      (parserExactSourceTape (padding + 2) remaining) := by
  refine ⟨2, ?_⟩
  constructor <;>
    simp [extraLeftBlankCellEraserDescription, parserExactSourceTape,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

theorem prefixTargetTape_rightEdge_eq_extraLeftBlankCellEraserSource
    (tape0Bits tape1Bits : Word Bool)
    (first : Bool) (rest : Word Bool) :
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits
          (guardLogicalTape
            (rightEdgeScanSourceTapeFromLeft [none]
              (first :: rest) []))) =
      tapeAtCells
        (List.append
          (List.replicate
            (tape0Bits.length + tape1Bits.length + 2)
            (none : Option Bool))
          [some false])
        (List.append
          ((List.append [false, false]
            (List.append [false, false, true, true]
              (logicalCellListBits
                (rightEdgeEndpointCells first rest)))).map some)
          [none]) := by
  rw [logicalTapeBits_guard_rightEdgeScanSourceTapeFromLeft]
  rfl

@[simp] theorem rightEdgeEndpointCells_filterMap
    (first : Bool) (rest : Word Bool) :
    (rightEdgeEndpointCells first rest).filterMap
        (fun cell => cell) = first :: rest := by
  simp [rightEdgeEndpointCells, Function.comp_def]

theorem decoderDescription_haltsFrom_rightEdgeEndpointParserTarget
    (first : Bool) (rest : Word Bool) (gap : Nat) :
    decoderDescription.HaltsFromTape
      (parserTargetTape [false, false] gap
        (logicalCellListBits (rightEdgeEndpointCells first rest)))
      (decoderHaltTape
        (List.append [false, false] (first :: rest))
        (decoderFinalGap gap (rightEdgeEndpointCells first rest))) := by
  simpa [parserTargetTape, decoderSourceTape, decodedLogicalCells] using
    decoderDescription_haltsFromTape false [false] gap
      (rightEdgeEndpointCells first rest)

theorem parserDescription_haltsFromTape_exactRemaining
    (padding : Nat) (first : Bool) (rest : Word Bool) :
    parserDescription.HaltsFromTape
      (parserExactSourceTape padding (first :: rest))
      (parserTargetTape [false, false] (padding + 3)
        (first :: rest)) := by
  refine ⟨2 * padding + 2 * (first :: rest).length + 14, ?_⟩
  have hrun := parserDescription_run_exact padding first rest
  constructor
  · simpa using congrArg (fun c => c.state) hrun
  · simpa using congrArg (fun c => c.tape) hrun

theorem parserDescription_haltsFromTape_rightEdgeEndpointCells
    (padding : Nat) (first : Bool) (rest : Word Bool) :
    parserDescription.HaltsFromTape
      (parserExactSourceTape padding
        (logicalCellListBits (rightEdgeEndpointCells first rest)))
      (parserTargetTape [false, false] (padding + 3)
        (logicalCellListBits (rightEdgeEndpointCells first rest))) := by
  cases hremaining :
      logicalCellListBits (rightEdgeEndpointCells first rest) with
  | nil =>
      cases first <;> cases rest <;>
        simp [rightEdgeEndpointCells, logicalCellListBits,
          logicalCellBits] at hremaining
  | cons remainingFirst remainingRest =>
      simpa [hremaining] using
        parserDescription_haltsFromTape_exactRemaining padding
          remainingFirst remainingRest

def rightEdgeEndpointTape2ProjectorDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          prefixEraserDescription
          extraLeftBlankCellEraserDescription)
        parserDescription)
      decoderDescription)
    finalizerDescription

theorem rightEdgeEndpointTape2ProjectorDescription_subroutineReady :
    rightEdgeEndpointTape2ProjectorDescription.SubroutineReady := by
  exact
    canonicalPrimitiveSeqDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        (canonicalPrimitiveSeqDescription_subroutineReady
          (canonicalPrimitiveSeqDescription_subroutineReady
            prefixEraserDescription_subroutineReady
            extraLeftBlankCellEraserDescription_subroutineReady)
          parserDescription_subroutineReady)
        decoderDescription_subroutineReady)
      finalizerDescription_subroutineReady

theorem rightEdgeEndpointTape2ProjectorDescription_haltsFromTapeEquiv
    (T0 T1 : Tape Bool) (first : Bool) (rest : Word Bool) :
    rightEdgeEndpointTape2ProjectorDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1
        (rightEdgeScanSourceTapeFromLeft [none]
          (first :: rest) []))
      (Tape.input (first :: rest)) := by
  let tape0Bits := logicalTapeBits (guardLogicalTape T0)
  let tape1Bits := logicalTapeBits (guardLogicalTape T1)
  let padding := tape0Bits.length + tape1Bits.length + 2
  let cells := rightEdgeEndpointCells first rest
  let remaining := logicalCellListBits cells
  have hprefix :=
    prefixEraserDescription_haltsFrom_encodedGuardedStructured3Tapes
      T0 T1
        (rightEdgeScanSourceTapeFromLeft [none] (first :: rest) [])
  have hprefixShape :=
    prefixTargetTape_rightEdge_eq_extraLeftBlankCellEraserSource
      tape0Bits tape1Bits first rest
  change
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits
          (guardLogicalTape
            (rightEdgeScanSourceTapeFromLeft [none]
              (first :: rest) []))) = _ at hprefixShape
  rw [hprefixShape] at hprefix
  have herase :=
    extraLeftBlankCellEraserDescription_haltsFromTape
      padding remaining
  have hprefixErase :
      (canonicalPrimitiveSeqDescription
        prefixEraserDescription
        extraLeftBlankCellEraserDescription).HaltsFromTapeEquiv
          (encodedGuardedStructured3Tapes T0 T1
            (rightEdgeScanSourceTapeFromLeft [none]
              (first :: rest) []))
          (parserExactSourceTape (padding + 2) remaining) := by
    exact canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      prefixEraserDescription_subroutineReady
      extraLeftBlankCellEraserDescription_subroutineReady
      hprefix.toEquiv herase.toEquiv
  have hparser :=
    parserDescription_haltsFromTape_rightEdgeEndpointCells
      (padding + 2) first rest
  change
    parserDescription.HaltsFromTape
      (parserExactSourceTape (padding + 2) remaining)
      (parserTargetTape [false, false] (padding + 2 + 3)
        remaining) at hparser
  have hprefixParser :
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          prefixEraserDescription
          extraLeftBlankCellEraserDescription)
        parserDescription).HaltsFromTapeEquiv
          (encodedGuardedStructured3Tapes T0 T1
            (rightEdgeScanSourceTapeFromLeft [none]
              (first :: rest) []))
          (parserTargetTape [false, false] (padding + 2 + 3)
            remaining) := by
    exact canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        prefixEraserDescription_subroutineReady
        extraLeftBlankCellEraserDescription_subroutineReady)
      parserDescription_subroutineReady
      hprefixErase hparser.toEquiv
  have hdecoder :=
    decoderDescription_haltsFrom_rightEdgeEndpointParserTarget
      first rest (padding + 2 + 3)
  change
    decoderDescription.HaltsFromTape
      (parserTargetTape [false, false] (padding + 2 + 3)
        remaining)
      (decoderHaltTape
        (List.append [false, false] (first :: rest))
        (decoderFinalGap (padding + 2 + 3) cells)) at hdecoder
  have hprefixParserDecoder :
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          (canonicalPrimitiveSeqDescription
            prefixEraserDescription
            extraLeftBlankCellEraserDescription)
          parserDescription)
        decoderDescription).HaltsFromTapeEquiv
          (encodedGuardedStructured3Tapes T0 T1
            (rightEdgeScanSourceTapeFromLeft [none]
              (first :: rest) []))
          (decoderHaltTape
            (List.append [false, false] (first :: rest))
            (decoderFinalGap (padding + 2 + 3) cells)) := by
    exact canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        (canonicalPrimitiveSeqDescription_subroutineReady
          prefixEraserDescription_subroutineReady
          extraLeftBlankCellEraserDescription_subroutineReady)
        parserDescription_subroutineReady)
      decoderDescription_subroutineReady
      hprefixParser hdecoder.toEquiv
  have hfinalizer :=
    finalizerDescription_haltsFromTapeEquiv_exact
      (first :: rest)
      (decoderFinalGap (padding + 2 + 3) cells)
  exact canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    (canonicalPrimitiveSeqDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        (canonicalPrimitiveSeqDescription_subroutineReady
          prefixEraserDescription_subroutineReady
          extraLeftBlankCellEraserDescription_subroutineReady)
        parserDescription_subroutineReady)
      decoderDescription_subroutineReady)
    finalizerDescription_subroutineReady
    hprefixParserDecoder hfinalizer

end Tape2Projector
end NestedLayoutMaterializerInternal
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
