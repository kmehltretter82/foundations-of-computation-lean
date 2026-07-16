import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary

set_option doc.verso true

/-!
# Raw pair quoter for guarded run-config egress

The first guarded logical tape is already a blank-delimited Boolean word at
the physical level.  This module reuses the checked CountWindow raw-boundary
emitter to expand that complete word into four-bit cell chunks.  No logical
head information is discarded: the {lit}`11` head marker is quoted just like
the three ordinary two-bit cell codes and remains distinguishable downstream.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress
namespace RawPairQuoter

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter

/-- Exact raw bit stream of the guarded final configuration tape. -/
def rawBits (i : Index) : Word Bool :=
  logicalTapeBits (guardLogicalTape i.finalTape)

/-- The untouched physical suffix beginning after the closing tape-0
separator. -/
def suffixCells (i : Index) : List (Option Bool) :=
  List.append
    (logicalTapeCode (guardLogicalTape i.consumedStageTape))
    (List.append tapeSeparatorCells
      (List.append
        (logicalTapeCode (guardLogicalTape i.doneWitnessTape))
        tapeSeparatorCells))

/-- CountWindow separator view of the real guarded source. -/
def sourceTape (i : Index) : Tape Bool :=
  rawBoundaryChunkExpandSeparatorTape
    [] (rawBits i) 0 (suffixCells i)

/-- Exact endpoint after every raw tape-0 bit has been expanded into its
four-bit Boolean-cell chunk.  The erased source footprint remains as harmless
blank workspace before the untouched tape-1/tape-2 suffix. -/
def targetTape (i : Index) : Tape Bool :=
  rawBoundaryChunkExpandSeparatorTape
    (preservingCellPassCellBits (rawBits i)) []
    (rawBits i).length (suffixCells i)

theorem index_source_eq_sourceTape (i : Index) :
    i.source = sourceTape i := by
  change
    encodedGuardedStructuredTapes
        [i.finalTape, i.consumedStageTape, i.doneWitnessTape] = _
  simp [sourceTape, rawBits, suffixCells,
    rawBoundaryChunkExpandSeparatorTape,
    encodedGuardedStructuredTapes, encodedStructuredTapes,
    guardLogicalTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, tapeSeparatorCells]

theorem chunkExpandDescription_haltsFromTape (i : Index) :
    rawBoundaryChunkExpandLoopDescription.HaltsFromTape
      i.source (targetTape i) := by
  rw [index_source_eq_sourceTape]
  simpa [sourceTape, targetTape, Nat.zero_add] using
    rawBoundaryChunkExpandLoopDescription_haltsFrom_separator_obligation
      (rawBits i) [] 0 (suffixCells i)

/-!
## Chunk semantics

Each expanded raw bit is the pair-code of two present Boolean cells: a fixed
{lit}`false` cell followed by the original bit.  The existing compact cell-list
decoder can therefore turn the expanded stream into two contiguous bits per
raw bit without any marker ambiguity.
-/

def expandedCellsForBit (bit : Bool) : List (Option Bool) :=
  [some false, some bit]

def expandedCells : Word Bool -> List (Option Bool)
  | [] => []
  | bit :: rest =>
      List.append (expandedCellsForBit bit) (expandedCells rest)

def interleavedBits : Word Bool -> Word Bool
  | [] => []
  | bit :: rest =>
      false :: bit :: interleavedBits rest

theorem logicalCellListBits_expandedCellsForBit (bit : Bool) :
    logicalCellListBits (expandedCellsForBit bit) =
      if bit then preservingCellPassOneBits
      else preservingCellPassZeroBits := by
  cases bit <;>
    rfl

theorem logicalCellListBits_expandedCells (bits : Word Bool) :
    logicalCellListBits (expandedCells bits) =
      preservingCellPassCellBits bits := by
  induction bits with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases bit <;>
        simp [expandedCells, expandedCellsForBit,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, logicalCellListBits,
          logicalCellBits, ih]

theorem filterMap_expandedCells (bits : Word Bool) :
    (expandedCells bits).filterMap (fun cell => cell) =
      interleavedBits bits := by
  induction bits with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases bit <;>
        simp [expandedCells, expandedCellsForBit, interleavedBits, ih]

/-!
## Pair-chunk rewrite

After the ordinary cell-list decoder, one raw pair {lit}`a,b` is represented
by the four contiguous bits {lit}`0,a,0,b`.  The finite table below rewrites
that block in place to {lit}`0,1,a,b`, exactly the Boolean input encoding of
the option cell denoted by the original pair.
-/

def pairStream : List (Bool × Bool) -> Word Bool
  | [] => []
  | (first, second) :: rest =>
      first :: second :: pairStream rest

def quotedPairBits : List (Bool × Bool) -> Word Bool
  | [] => []
  | (first, second) :: rest =>
      false :: true :: first :: second :: quotedPairBits rest

def logicalCellPair : Option Bool -> Bool × Bool
  | none => (false, false)
  | some false => (false, true)
  | some true => (true, false)

def logicalTapePairs (T : Tape Bool) : List (Bool × Bool) :=
  List.append (T.left.reverse.map logicalCellPair)
    (List.append [(true, true)]
      (logicalCellPair T.head :: T.right.map logicalCellPair))

theorem pairStream_append
    (left right : List (Bool × Bool)) :
    pairStream (List.append left right) =
      List.append (pairStream left) (pairStream right) := by
  induction left with
  | nil =>
      rfl
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      change
        first :: second :: pairStream (List.append rest right) =
          first :: second ::
            List.append (pairStream rest) (pairStream right)
      rw [ih]

theorem quotedPairBits_append
    (left right : List (Bool × Bool)) :
    quotedPairBits (List.append left right) =
      List.append (quotedPairBits left) (quotedPairBits right) := by
  induction left with
  | nil =>
      rfl
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      change
        false :: true :: first :: second ::
            quotedPairBits (List.append rest right) =
          false :: true :: first :: second ::
            List.append (quotedPairBits rest) (quotedPairBits right)
      rw [ih]

theorem pairStream_map_logicalCellPair
    (cells : List (Option Bool)) :
    pairStream (cells.map logicalCellPair) =
      logicalCellListBits cells := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp [logicalCellPair, pairStream, logicalCellListBits,
            logicalCellBits, ih]
      | some bit =>
          cases bit <;>
            simp [logicalCellPair, pairStream, logicalCellListBits,
              logicalCellBits, ih]

theorem pairStream_logicalTapePairs (T : Tape Bool) :
    pairStream (logicalTapePairs T) = logicalTapeBits T := by
  cases T with
  | mk left head right =>
      unfold logicalTapePairs logicalTapeBits
      rw [pairStream_append]
      rw [pairStream_map_logicalCellPair]
      rw [pairStream_append]
      cases head with
      | none =>
          simp [pairStream, logicalCellPair,
            pairStream_map_logicalCellPair, logicalCellBits]
      | some bit =>
          cases bit <;>
            simp [pairStream, logicalCellPair,
              pairStream_map_logicalCellPair, logicalCellBits]

theorem rawBits_eq_pairStream (i : Index) :
    rawBits i =
      pairStream (logicalTapePairs (guardLogicalTape i.finalTape)) := by
  exact (pairStream_logicalTapePairs _).symm

theorem quotedPairBits_map_logicalCellPair
    (cells : List (Option Bool)) :
    quotedPairBits (cells.map logicalCellPair) =
      EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
        cells := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp [logicalCellPair, quotedPairBits,
            EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits,
            EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
            encodeCell, encodeCodeWordAsInput,
            encodeCodeSymbolAsInput, ih]
      | some bit =>
          cases bit <;>
            simp [logicalCellPair, quotedPairBits,
              EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits,
              EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
              encodeCell, encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, ih]

def pairRewriterHalt : Nat := 5

def pairRewriterDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := pairRewriterHalt
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 0 none none Direction.right pairRewriterHalt
    , transition 1 (some false) (some true) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 3
    , transition 2 (some false) (some false) Direction.right 4
    , transition 2 (some true) (some false) Direction.right 4
    , transition 3 (some false) (some true) Direction.right 4
    , transition 3 (some true) (some true) Direction.right 4
    , transition 4 (some false) (some false) Direction.right 0
    , transition 4 (some true) (some true) Direction.right 0 ]

theorem pairRewriterDescription_wellFormed :
    pairRewriterDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := pairRewriterDescription.transitions)
      (stateCount := pairRewriterDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := pairRewriterDescription.transitions)
      (by decide)

theorem pairRewriterDescription_haltTransitionFree :
    pairRewriterDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := pairRewriterDescription.transitions)
    (state := pairRewriterDescription.halt)
    (by decide)

theorem pairRewriterDescription_subroutineReady :
    pairRewriterDescription.SubroutineReady :=
  ⟨pairRewriterDescription_wellFormed,
    pairRewriterDescription_haltTransitionFree⟩

def pairRewriteScanTape
    (baseLeft : List (Option Bool))
    (emitted : Word Bool) (remaining : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (emitted.reverse.map some) baseLeft)
    (List.append
      ((interleavedBits (pairStream remaining)).map some)
      (none :: padding))

private theorem pairRewriterDescription_run_pair
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (first second : Bool) (remaining : List (Bool × Bool))
    (padding : List (Option Bool)) :
    pairRewriterDescription.runConfig 4
        { state := pairRewriterDescription.start
          tape :=
            pairRewriteScanTape baseLeft emitted
              ((first, second) :: remaining) padding } =
      { state := pairRewriterDescription.start
        tape :=
      pairRewriteScanTape baseLeft
            (List.append emitted [false, true, first, second])
            remaining padding } := by
  cases first <;> cases second <;>
    cases htail : (interleavedBits (pairStream remaining)).map some <;>
      simp [pairRewriterDescription, pairRewriterHalt,
        pairRewriteScanTape, pairStream, interleavedBits,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
        List.reverse_append, htail]

private theorem pairRewriterDescription_run_pairs
    (baseLeft : List (Option Bool)) (emitted : Word Bool)
    (remaining : List (Bool × Bool))
    (padding : List (Option Bool)) :
    pairRewriterDescription.runConfig (4 * remaining.length)
        { state := pairRewriterDescription.start
          tape := pairRewriteScanTape baseLeft emitted remaining padding } =
      { state := pairRewriterDescription.start
        tape :=
          pairRewriteScanTape baseLeft
            (List.append emitted (quotedPairBits remaining)) [] padding } := by
  induction remaining generalizing emitted with
  | nil =>
      simp [runConfig, quotedPairBits]
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      rw [show 4 * ((first, second) :: rest).length =
          4 + 4 * rest.length by simp; lia]
      rw [runConfig_add]
      rw [pairRewriterDescription_run_pair]
      rw [ih]
      simp [quotedPairBits, List.append_assoc]

def pairRewriteSourceTape
    (pairs : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  pairRewriteScanTape [none] [] pairs padding

def pairRewriteBoundaryTape
    (pairs : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  pairRewriteScanTape [none] (quotedPairBits pairs) [] padding

def pairRewriteTargetTape
    (pairs : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.right (pairRewriteBoundaryTape pairs padding)

theorem pairRewriterDescription_haltsFromTape
    (pairs : List (Bool × Bool))
    (padding : List (Option Bool)) :
    pairRewriterDescription.HaltsFromTape
      (pairRewriteSourceTape pairs padding)
      (pairRewriteTargetTape pairs padding) := by
  refine ⟨4 * pairs.length + 1, ?_⟩
  have hrun :
      pairRewriterDescription.runConfig (4 * pairs.length + 1)
          { state := pairRewriterDescription.start
            tape := pairRewriteSourceTape pairs padding } =
        { state := pairRewriterDescription.halt
          tape := pairRewriteTargetTape pairs padding } := by
    rw [runConfig_add]
    rw [show
        ({ state := pairRewriterDescription.start
           tape := pairRewriteSourceTape pairs padding } :
          MachineDescription.Configuration) =
          { state := pairRewriterDescription.start
            tape := pairRewriteScanTape [none] [] pairs padding } by
        rfl]
    rw [pairRewriterDescription_run_pairs]
    change
      pairRewriterDescription.runConfig 1
          { state := pairRewriterDescription.start
            tape := pairRewriteBoundaryTape pairs padding } =
        { state := pairRewriterDescription.halt
          tape := pairRewriteTargetTape pairs padding }
    cases padding <;>
      simp [pairRewriterDescription, pairRewriterHalt,
        pairRewriteBoundaryTape, pairRewriteScanTape,
        pairRewriteTargetTape, pairStream, interleavedBits,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  constructor
  · simpa using congrArg MachineDescription.Configuration.state hrun
  · simpa using congrArg MachineDescription.Configuration.tape hrun

end RawPairQuoter
end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
