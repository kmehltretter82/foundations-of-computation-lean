import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Spec
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsRuns.Basic

set_option doc.verso true

/-!
# Exact-code validator: pairwise determinism block machine

This module defines the aligned four-bit machine for M4 leaf 5.  It marks the
final {lit}`done` block, selects outer rows from left to right, and compares
each outer row with every later row.  Unary source and target fields are paired
with {lit}`marker010`; the current outer and inner transition boundaries use
{lit}`marker001`.  A successful pass restores all markers and halts on the
same blank boundary at which it started.

State 100 is an explicit nonhalting conflict state.  It has no outgoing rows,
while state 101 is the successful halt.  Keeping those endpoints distinct
allows the later Boolean closeout to route conflicts to {lit}`false` without
changing the successful leaf contract.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

private def keep
    (source : Nat) (read : ValidatorBlockSymbol)
    (move : Direction) (target : Nat) : ValidatorBlockTransition where
  source := source
  read := read
  write := read
  move := move
  target := target

private def write
    (source : Nat) (read replacement : ValidatorBlockSymbol)
    (move : Direction) (target : Nat) : ValidatorBlockTransition where
  source := source
  read := read
  write := replacement
  move := move
  target := target

private def keepRows
    (source : Nat) (symbols : List ValidatorBlockSymbol)
    (move : Direction) (target : Nat) : List ValidatorBlockTransition :=
  symbols.map (fun symbol => keep source symbol move target)

private def canonicalSymbols : List ValidatorBlockSymbol :=
  [.header, .transition, .tick, .done, .blank, .zero, .one,
    .moveLeft, .moveRight]

private def rowSymbols : List ValidatorBlockSymbol :=
  [.transition, .tick, .done, .blank, .zero, .one,
    .moveLeft, .moveRight]

private def rowNonTransitionSymbols : List ValidatorBlockSymbol :=
  [.tick, .done, .blank, .zero, .one, .moveLeft, .moveRight]

private def markerCorridorSymbols : List ValidatorBlockSymbol :=
  canonicalSymbols ++ [.marker010]

private def cellValues : List (Option Bool) :=
  [none, some false, some true]

private def moveValues : List Direction :=
  [Direction.left, Direction.right]

private def cellSymbol : Option Bool -> ValidatorBlockSymbol
  | none => .blank
  | some false => .zero
  | some true => .one

private def moveSymbol : Direction -> ValidatorBlockSymbol
  | Direction.left => .moveLeft
  | Direction.right => .moveRight

/-- Finite-control rank of a Boolean tape-cell value. -/
def cellIndex : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

/-- Finite-control rank of a head direction. -/
def moveIndex : Direction -> Nat
  | Direction.left => 0
  | Direction.right => 1

/-!
Action fields are compared sequentially.  Only one cell value or direction is
carried at a time; this avoids the 18-way product of action triples across each
shuttle phase and keeps the generated Boolean table within elaboration limits.
-/

/-- State carrying an outer read value while seeking the inner marker. -/
def readSeekMarkerState (read : Option Bool) : Nat :=
  16 + cellIndex read

/-- State carrying an outer read value across the inner source. -/
def readSeekSourceState (read : Option Bool) : Nat :=
  19 + cellIndex read

/-- State comparing the selected rows' read symbols. -/
def compareInnerReadState (read : Option Bool) : Nat :=
  22 + cellIndex read

/-- State carrying an outer write value while seeking the inner marker. -/
def writeSeekMarkerState (written : Option Bool) : Nat :=
  30 + cellIndex written

/-- State carrying an outer write value across the inner source. -/
def writeSeekSourceState (written : Option Bool) : Nat :=
  33 + cellIndex written

/-- State carrying an outer write value while skipping the inner read cell. -/
def writeSkipReadState (written : Option Bool) : Nat :=
  36 + cellIndex written

/-- State comparing the selected rows' write symbols. -/
def compareInnerWriteState (written : Option Bool) : Nat :=
  39 + cellIndex written

/-- State carrying an outer move while seeking the inner marker. -/
def moveSeekMarkerState (move : Direction) : Nat :=
  48 + moveIndex move

/-- State carrying an outer move across the inner source. -/
def moveSeekSourceState (move : Direction) : Nat :=
  50 + moveIndex move

/-- State carrying an outer move while skipping the inner read cell. -/
def moveSkipReadState (move : Direction) : Nat :=
  52 + moveIndex move

/-- State carrying an outer move while skipping the inner write cell. -/
def moveSkipWriteState (move : Direction) : Nat :=
  54 + moveIndex move

/-- State comparing the selected rows' move directions. -/
def compareInnerMoveState (move : Direction) : Nat :=
  56 + moveIndex move

private def readComparisonRows : List ValidatorBlockTransition :=
  cellValues.flatMap (fun expected =>
    [keep 15 (cellSymbol expected) Direction.right
      (readSeekMarkerState expected)] ++
    keepRows (readSeekMarkerState expected) markerCorridorSymbols
      Direction.right (readSeekMarkerState expected) ++
    [keep (readSeekMarkerState expected) .marker001 Direction.right
      (readSeekSourceState expected)] ++
    keepRows (readSeekSourceState expected) [.tick, .marker010]
      Direction.right (readSeekSourceState expected) ++
    [keep (readSeekSourceState expected) .done Direction.right
      (compareInnerReadState expected)] ++
    cellValues.map (fun actual =>
      keep (compareInnerReadState expected) (cellSymbol actual)
        (if actual = expected then Direction.left else Direction.right)
        (if actual = expected then 25 else 85)))

private def writeComparisonRows : List ValidatorBlockTransition :=
  cellValues.flatMap (fun expected =>
    [keep 29 (cellSymbol expected) Direction.right
      (writeSeekMarkerState expected)] ++
    keepRows (writeSeekMarkerState expected) markerCorridorSymbols
      Direction.right (writeSeekMarkerState expected) ++
    [keep (writeSeekMarkerState expected) .marker001 Direction.right
      (writeSeekSourceState expected)] ++
    keepRows (writeSeekSourceState expected) [.tick, .marker010]
      Direction.right (writeSeekSourceState expected) ++
    [keep (writeSeekSourceState expected) .done Direction.right
      (writeSkipReadState expected)] ++
    keepRows (writeSkipReadState expected) [.blank, .zero, .one]
      Direction.right (compareInnerWriteState expected) ++
    cellValues.map (fun actual =>
      keep (compareInnerWriteState expected) (cellSymbol actual)
        (if actual = expected then Direction.left else Direction.right)
        (if actual = expected then 42 else 100)))

private def moveComparisonRows : List ValidatorBlockTransition :=
  moveValues.flatMap (fun expected =>
    [keep 47 (moveSymbol expected) Direction.right
      (moveSeekMarkerState expected)] ++
    keepRows (moveSeekMarkerState expected) markerCorridorSymbols
      Direction.right (moveSeekMarkerState expected) ++
    [keep (moveSeekMarkerState expected) .marker001 Direction.right
      (moveSeekSourceState expected)] ++
    keepRows (moveSeekSourceState expected) [.tick, .marker010]
      Direction.right (moveSeekSourceState expected) ++
    [keep (moveSeekSourceState expected) .done Direction.right
      (moveSkipReadState expected)] ++
    keepRows (moveSkipReadState expected) [.blank, .zero, .one]
      Direction.right (moveSkipWriteState expected) ++
    keepRows (moveSkipWriteState expected) [.blank, .zero, .one]
      Direction.right (compareInnerMoveState expected) ++
    moveValues.map (fun actual =>
      keep (compareInnerMoveState expected) (moveSymbol actual)
        (if actual = expected then Direction.left else Direction.right)
        (if actual = expected then 58 else 100)))

private def fixedRows : List ValidatorBlockTransition :=
  [ write 0 .done .marker011 Direction.left 1
  , keep 1 .header Direction.right 2

  , write 2 .transition .marker001 Direction.right 3
  , keep 2 .marker011 Direction.left 98

  , write 3 .transition .marker001 Direction.left 4
  , keep 3 .marker011 Direction.left 97

  , keep 4 .marker001 Direction.right 5

  , keep 5 .marker010 Direction.right 5
  , write 5 .tick .marker010 Direction.right 6
  , keep 5 .done Direction.right 10

  , keep 6 .marker001 Direction.right 7

  , keep 7 .marker010 Direction.right 7
  , write 7 .tick .marker010 Direction.left 8
  , keep 7 .done Direction.right 84

  , keep 8 .marker001 Direction.left 9
  , keep 9 .marker001 Direction.right 5

  , keep 10 .marker001 Direction.right 11
  , keep 11 .marker010 Direction.right 11
  , keep 11 .tick Direction.right 83
  , keep 11 .done Direction.left 12
  , keep 12 .marker001 Direction.left 13
  , keep 13 .marker001 Direction.right 14

  , keep 14 .tick Direction.right 14
  , keep 14 .marker010 Direction.right 14
  , keep 14 .done Direction.right 15

  , keep 25 .marker001 Direction.left 26
  , keep 26 .marker001 Direction.right 27
  , keep 27 .tick Direction.right 27
  , keep 27 .marker010 Direction.right 27
  , keep 27 .done Direction.right 28
  , keep 28 .blank Direction.right 29
  , keep 28 .zero Direction.right 29
  , keep 28 .one Direction.right 29

  , keep 42 .marker001 Direction.left 43
  , keep 43 .marker001 Direction.right 44
  , keep 44 .tick Direction.right 44
  , keep 44 .marker010 Direction.right 44
  , keep 44 .done Direction.right 45
  , keep 45 .blank Direction.right 46
  , keep 45 .zero Direction.right 46
  , keep 45 .one Direction.right 46
  , keep 46 .blank Direction.right 47
  , keep 46 .zero Direction.right 47
  , keep 46 .one Direction.right 47

  , keep 58 .marker001 Direction.left 59
  , keep 59 .marker001 Direction.right 60
  , keep 60 .tick Direction.right 60
  , keep 60 .marker010 Direction.right 60
  , keep 60 .done Direction.right 61
  , keep 61 .blank Direction.right 62
  , keep 61 .zero Direction.right 62
  , keep 61 .one Direction.right 62
  , keep 62 .blank Direction.right 63
  , keep 62 .zero Direction.right 63
  , keep 62 .one Direction.right 63
  , keep 63 .moveLeft Direction.right 64
  , keep 63 .moveRight Direction.right 64

  , keep 64 .marker010 Direction.right 64
  , write 64 .tick .marker010 Direction.right 65
  , keep 64 .done Direction.right 77
  , keep 65 .marker001 Direction.right 66
  , keep 66 .tick Direction.right 66
  , keep 66 .marker010 Direction.right 66
  , keep 66 .done Direction.right 67
  , keep 67 .blank Direction.right 68
  , keep 67 .zero Direction.right 68
  , keep 67 .one Direction.right 68
  , keep 68 .blank Direction.right 69
  , keep 68 .zero Direction.right 69
  , keep 68 .one Direction.right 69
  , keep 69 .moveLeft Direction.right 70
  , keep 69 .moveRight Direction.right 70
  , keep 70 .marker010 Direction.right 70
  , write 70 .tick .marker010 Direction.left 71
  , keep 70 .done Direction.right 100
  , keep 70 .marker011 Direction.right 100

  , keep 71 .marker001 Direction.left 72
  , keep 72 .marker001 Direction.right 73
  , keep 73 .tick Direction.right 73
  , keep 73 .marker010 Direction.right 73
  , keep 73 .done Direction.right 74
  , keep 74 .blank Direction.right 75
  , keep 74 .zero Direction.right 75
  , keep 74 .one Direction.right 75
  , keep 75 .blank Direction.right 76
  , keep 75 .zero Direction.right 76
  , keep 75 .one Direction.right 76
  , keep 76 .moveLeft Direction.right 64
  , keep 76 .moveRight Direction.right 64

  , keep 77 .marker001 Direction.right 78
  , keep 78 .tick Direction.right 78
  , keep 78 .marker010 Direction.right 78
  , keep 78 .done Direction.right 79
  , keep 79 .blank Direction.right 80
  , keep 79 .zero Direction.right 80
  , keep 79 .one Direction.right 80
  , keep 80 .blank Direction.right 81
  , keep 80 .zero Direction.right 81
  , keep 80 .one Direction.right 81
  , keep 81 .moveLeft Direction.right 82
  , keep 81 .moveRight Direction.right 82
  , keep 82 .marker010 Direction.right 82
  , keep 82 .tick Direction.right 100
  , keep 82 .done Direction.left 88
  , keep 82 .marker011 Direction.left 88

  , keep 83 .tick Direction.right 83
  , keep 83 .marker010 Direction.right 83
  , keep 83 .done Direction.right 84
  , keep 84 .blank Direction.right 85
  , keep 84 .zero Direction.right 85
  , keep 84 .one Direction.right 85
  , keep 85 .blank Direction.right 86
  , keep 85 .zero Direction.right 86
  , keep 85 .one Direction.right 86
  , keep 86 .moveLeft Direction.right 87
  , keep 86 .moveRight Direction.right 87
  , keep 87 .tick Direction.right 87
  , keep 87 .marker010 Direction.right 87
  , keep 87 .done Direction.left 88
  , keep 87 .marker011 Direction.left 88

  , write 88 .marker010 .tick Direction.left 88
  , keep 88 .marker001 Direction.left 89
  , write 89 .marker010 .tick Direction.left 89
  , keep 89 .marker001 Direction.right 90
  , write 90 .marker001 .transition Direction.right 91
  , keep 91 .tick Direction.right 91
  , keep 91 .marker010 Direction.right 91
  , keep 91 .done Direction.right 92
  , keep 92 .blank Direction.right 93
  , keep 92 .zero Direction.right 93
  , keep 92 .one Direction.right 93
  , keep 93 .blank Direction.right 94
  , keep 93 .zero Direction.right 94
  , keep 93 .one Direction.right 94
  , keep 94 .moveLeft Direction.right 95
  , keep 94 .moveRight Direction.right 95
  , keep 95 .tick Direction.right 95
  , keep 95 .marker010 Direction.right 95
  , keep 95 .done Direction.right 3
  , keep 95 .marker011 Direction.left 96
  , keep 96 .tick Direction.right 3
  , keep 96 .moveLeft Direction.right 3
  , keep 96 .moveRight Direction.right 3

  , keep 97 .header Direction.right 2
  , keep 98 .header Direction.right 99
  , write 99 .marker001 .transition Direction.right 99
  , write 99 .marker011 .done Direction.right 101
  ] ++
    keepRows 1 rowSymbols Direction.left 1 ++
    keepRows 2 (rowNonTransitionSymbols ++ [.marker001]) Direction.right 2 ++
    keepRows 3 rowNonTransitionSymbols Direction.right 3 ++
    keepRows 4 markerCorridorSymbols Direction.left 4 ++
    keepRows 6 markerCorridorSymbols Direction.right 6 ++
    keepRows 8 [.tick, .marker010] Direction.left 8 ++
    keepRows 9 markerCorridorSymbols Direction.left 9 ++
    keepRows 10 markerCorridorSymbols Direction.right 10 ++
    keepRows 12 [.tick, .marker010] Direction.left 12 ++
    keepRows 13 markerCorridorSymbols Direction.left 13 ++
    keepRows 25 markerCorridorSymbols Direction.left 25 ++
    keepRows 26 markerCorridorSymbols Direction.left 26 ++
    keepRows 42 markerCorridorSymbols Direction.left 42 ++
    keepRows 43 markerCorridorSymbols Direction.left 43 ++
    keepRows 58 markerCorridorSymbols Direction.left 58 ++
    keepRows 59 markerCorridorSymbols Direction.left 59 ++
    keepRows 65 markerCorridorSymbols Direction.right 65 ++
    keepRows 71 markerCorridorSymbols Direction.left 71 ++
    keepRows 72 markerCorridorSymbols Direction.left 72 ++
    keepRows 77 markerCorridorSymbols Direction.right 77 ++
    keepRows 88 canonicalSymbols Direction.left 88 ++
    keepRows 89 canonicalSymbols Direction.left 89 ++
    keepRows 90 markerCorridorSymbols Direction.right 90 ++
    keepRows 97 (rowSymbols ++ [.marker001]) Direction.left 97 ++
    keepRows 98 (rowSymbols ++ [.marker001]) Direction.left 98 ++
    keepRows 99 canonicalSymbols Direction.right 99

/-- Logical aligned-block table for the pairwise determinism gate. -/
def blockDescription : ValidatorBlockDescription where
  stateCount := 102
  start := 0
  halt := 101
  transitions :=
    fixedRows ++ readComparisonRows ++ writeComparisonRows ++
      moveComparisonRows

/-- Generated Boolean core before the shared four-cell entry wrapper. -/
def physicalCoreDescription : MachineDescription :=
  compileValidatorBlockDescription blockDescription

/-- Concrete Boolean description with four raw left-entry moves from the blank
suffix boundary to the first bit of the final block. -/
def Description : MachineDescription :=
  withValidatorFourLeftEntry physicalCoreDescription

/-- Every generated block-core row remains a row of the entry-extended machine. -/
theorem compiledRow_mem_description
    {row : TransitionDescription}
    (hrow : row ∈
      (compileValidatorBlockDescription blockDescription).transitions) :
    row ∈ Description.transitions := by
  exact List.mem_append_left
    (validatorFourLeftEntryRows physicalCoreDescription) hrow

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
