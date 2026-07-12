import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.RawPairQuoter
import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.DecoderRuns

set_option doc.verso true

/-!
# Guarded #18 raw-pair decoder seam

This module connects the checked raw-pair chunk expander to the shared
marker-preserving logical-cell decoder.  The first guaranteed {lit}`01` cell
chunk becomes the decoder's nonempty output seed, so the decoded word is
exactly the interleaved raw-pair stream without an artificial leading pair.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress
namespace RawPairDecoder

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter
open RawPairQuoter

def decoderRightPadding (i : Index) : List (Option Bool) :=
  List.append
    (List.replicate (rawBits i).length (none : Option Bool))
    (suffixCells i)

def installSentinelDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none (some false) Direction.right 1
    , transition 1 none none Direction.left 2 ]

theorem installSentinelDescription_subroutineReady :
    installSentinelDescription.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    installSentinelDescription
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def sentinelTape (i : Index) : Tape Bool :=
  tapeAtCells
    ((preservingCellPassCellBits (rawBits i)).reverse.map some)
    (some false :: none :: decoderRightPadding i)

private theorem installSentinelDescription_run
    (left right : List (Option Bool)) :
    installSentinelDescription.runConfig 2
        { state := installSentinelDescription.start
          tape := tapeAtCells left (none :: none :: right) } =
      { state := installSentinelDescription.halt
        tape := tapeAtCells left (some false :: none :: right) } := by
  cases left <;> cases right <;>
    simp [installSentinelDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem installSentinelDescription_haltsFromTape (i : Index) :
    installSentinelDescription.HaltsFromTape
      (targetTape i) (sentinelTape i) := by
  refine ⟨2, ?_⟩
  have hrun :
      installSentinelDescription.runConfig 2
          { state := installSentinelDescription.start
            tape := targetTape i } =
        { state := installSentinelDescription.halt
          tape := sentinelTape i } := by
    simpa [targetTape, sentinelTape, decoderRightPadding,
      rawBoundaryChunkExpandSeparatorTape, List.replicate_succ] using
      installSentinelDescription_run
        ((preservingCellPassCellBits (rawBits i)).reverse.map some)
        (decoderRightPadding i)
  constructor
  · simpa using congrArg MachineDescription.Configuration.state hrun
  · simpa using congrArg MachineDescription.Configuration.tape hrun

def rewoundChunkTape (i : Index) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((preservingCellPassCellBits (rawBits i)).map some)
      (some false :: none :: decoderRightPadding i))

theorem rightEdgeRewindDescription_haltsFrom_sentinel (i : Index) :
    rightEdgeRewindDescription.HaltsFromTape
      (sentinelTape i) (rewoundChunkTape i) := by
  simpa [sentinelTape, rewoundChunkTape] using
    rightEdgeRewindDescription_haltsFrom_rightEdge_noDelimiter
      (preservingCellPassCellBits (rawBits i)) false
      (none :: decoderRightPadding i)

def remainingExpandedCells : Word Bool -> List (Option Bool)
  | [] => []
  | bit :: rest => some bit :: expandedCells rest

def seedDecoderDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 1 none (some false) Direction.right 2
    , transition 2 (some false) none Direction.right 3
    , transition 3 (some true) none Direction.right 4 ]

theorem seedDecoderDescription_subroutineReady :
    seedDecoderDescription.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    seedDecoderDescription
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def decoderSourceTape (i : Index) : Tape Bool :=
  decoderPaddedSourceTape [false] 2
    (remainingExpandedCells (rawBits i)) (decoderRightPadding i)

private theorem seedDecoderDescription_run
    (bit : Bool) (rest : Word Bool) (right : List (Option Bool)) :
    seedDecoderDescription.runConfig 4
        { state := seedDecoderDescription.start
          tape := tapeAtCells [none]
            (List.append
              ((preservingCellPassCellBits (bit :: rest)).map some)
              (some false :: none :: right)) } =
      { state := seedDecoderDescription.halt
        tape := decoderPaddedSourceTape [false] 2
          (some bit :: expandedCells rest) right } := by
  cases bit <;>
    simp [seedDecoderDescription, decoderPaddedSourceTape,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, logicalCellListBits_expandedCells,
      logicalCellListBits, logicalCellBits, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rawBits_ne_nil (i : Index) : rawBits i ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [rawBits, logicalTapeBits] at hlength

theorem seedDecoderDescription_haltsFromTape (i : Index) :
    seedDecoderDescription.HaltsFromTape
      (rewoundChunkTape i) (decoderSourceTape i) := by
  cases hraw : rawBits i with
  | nil => exact False.elim ((rawBits_ne_nil i) hraw)
  | cons bit rest =>
      refine ⟨4, ?_⟩
      have hrun :
          seedDecoderDescription.runConfig 4
              { state := seedDecoderDescription.start
                tape := rewoundChunkTape i } =
            { state := seedDecoderDescription.halt
              tape := decoderSourceTape i } := by
        simpa [rewoundChunkTape, decoderSourceTape,
          remainingExpandedCells, hraw] using
          seedDecoderDescription_run bit rest (decoderRightPadding i)
      constructor
      · simpa using congrArg MachineDescription.Configuration.state hrun
      · simpa using congrArg MachineDescription.Configuration.tape hrun

def decodedBits (i : Index) : Word Bool :=
  interleavedBits (rawBits i)

def decoderTargetTape (i : Index) : Tape Bool :=
  decoderPaddedHaltTape (decodedBits i)
    (decoderFinalGap 2 (remainingExpandedCells (rawBits i)))
    (decoderRightPadding i)

theorem decoderDescription_haltsFromTape (i : Index) :
    decoderDescription.HaltsFromTape
      (decoderSourceTape i) (decoderTargetTape i) := by
  cases hraw : rawBits i with
  | nil => exact False.elim ((rawBits_ne_nil i) hraw)
  | cons bit rest =>
      simpa [decoderSourceTape, decoderTargetTape, decodedBits,
        remainingExpandedCells, hraw, decodedLogicalCells,
        filterMap_expandedCells, interleavedBits] using
        decoderDescription_haltsFromTape_withRight false [] 2
          (remainingExpandedCells (rawBits i)) (decoderRightPadding i)

end RawPairDecoder
end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
