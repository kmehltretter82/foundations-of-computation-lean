import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.RefreshedRows

set_option doc.verso true

/-!
# Lowerer-facing three-tape structured helpers

This module contains small constructors and proof wrappers for three-logical-tape
structured machines that are meant to stay in the fragment recognized by
{lit}`supportsReadWriteRows3`.  The helpers are ordinary definitions rather
than syntax so downstream proofs can still unfold them and reuse the existing
lowerer theorems directly.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape

/-!
## Lowerable actions
-/

/-- Preserve the current logical cell and move the head left. -/
def keepL : TapeAction :=
  TapeAction.preserveMove HeadMove.left

@[simp] theorem keepL_eq :
    keepL = TapeAction.preserveMove HeadMove.left := by
  rfl

/-- Preserve the current logical cell and move the head right. -/
def keepR : TapeAction :=
  TapeAction.preserveMove HeadMove.right

@[simp] theorem keepR_eq :
    keepR = TapeAction.preserveMove HeadMove.right := by
  rfl

/-- Preserve the current logical cell without moving the head. -/
def keepS : TapeAction :=
  TapeAction.stay

@[simp] theorem keepS_eq :
    keepS = TapeAction.stay := by
  rfl

/-- Write a logical cell and move the head left. -/
def writeL (cell : Option Bool) : TapeAction :=
  TapeAction.writeMove cell HeadMove.left

@[simp] theorem writeL_eq
    (cell : Option Bool) :
    writeL cell = TapeAction.writeMove cell HeadMove.left := by
  rfl

/-- Write a logical cell and move the head right. -/
def writeR (cell : Option Bool) : TapeAction :=
  TapeAction.writeMove cell HeadMove.right

@[simp] theorem writeR_eq
    (cell : Option Bool) :
    writeR cell = TapeAction.writeMove cell HeadMove.right := by
  rfl

/-- Write a logical cell without moving the head. -/
def writeS (cell : Option Bool) : TapeAction :=
  TapeAction.writeMove cell HeadMove.stay

@[simp] theorem writeS_eq
    (cell : Option Bool) :
    writeS cell = TapeAction.writeMove cell HeadMove.stay := by
  rfl

/-- Erase the current logical cell and move the head left. -/
def eraseL : TapeAction :=
  writeL none

@[simp] theorem eraseL_eq :
    eraseL = TapeAction.writeMove none HeadMove.left := by
  rfl

/-- Erase the current logical cell and move the head right. -/
def eraseR : TapeAction :=
  writeR none

@[simp] theorem eraseR_eq :
    eraseR = TapeAction.writeMove none HeadMove.right := by
  rfl

/-- Write a bit and move the head left. -/
def writeBitL (bit : Bool) : TapeAction :=
  writeL (some bit)

@[simp] theorem writeBitL_eq
    (bit : Bool) :
    writeBitL bit = TapeAction.writeMove (some bit) HeadMove.left := by
  rfl

/-- Write a bit and move the head right. -/
def writeBitR (bit : Bool) : TapeAction :=
  writeR (some bit)

@[simp] theorem writeBitR_eq
    (bit : Bool) :
    writeBitR bit = TapeAction.writeMove (some bit) HeadMove.right := by
  rfl

/-!
## Three-tape rows and descriptions
-/

/--
Build one lowerer-facing three-tape transition row.

Rows built by this constructor have exactly three reads and exactly three
actions, hence satisfy {name}`supportsReadWriteRow3`.
-/
def row
    (source : Nat)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : Transition where
  source := source
  reads := [read0, read1, read2]
  actions := [action0, action1, action2]
  target := target

@[simp] theorem row_eq
    (source : Nat)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) :
    row source read0 read1 read2 action0 action1 action2 target =
      { source := source
        reads := [read0, read1, read2]
        actions := [action0, action1, action2]
        target := target } := by
  rfl

theorem row_supportedReadWriteRow3
    (source target : Nat)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction) :
    SupportedReadWriteRow3
      (row source read0 read1 read2 action0 action1 action2 target) := by
  cases action0 with
  | mk write0? move0 =>
      cases action1 with
      | mk write1? move1 =>
          cases action2 with
          | mk write2? move2 =>
              exact
                SupportedReadWriteRow3.mk
                  read0 read1 read2 write0? write1? write2?
                  move0 move1 move2 rfl rfl

theorem row_supportsReadWriteRow3
    (source target : Nat)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction) :
    supportsReadWriteRow3
      (row source read0 read1 read2 action0 action1 action2 target) =
        true :=
  supportsReadWriteRow3_eq_true_of_supported
    (row_supportedReadWriteRow3 source target read0 read1 read2
      action0 action1 action2)

/--
Build a three-tape structured description from a concrete transition table.

Use {lit}`description_supported` or {lit}`description_supportsReadWriteRows3`
with a table-membership proof to expose lowerer compatibility.
-/
def description
    (stateCount start halt : Nat)
    (transitions : List Transition) : Description where
  tapeCount := 3
  stateCount := stateCount
  start := start
  halt := halt
  transitions := transitions

theorem description_supported
    (stateCount start halt : Nat)
    (transitions : List Transition)
    (hrows :
      forall t : Transition,
        t ∈ transitions ->
          supportsReadWriteRow3 t = true) :
    SupportsReadWriteRows3
      (description stateCount start halt transitions) where
  tapeCount_eq := rfl
  rows_supported := by
    intro t ht
    exact hrows t ht

theorem description_supportsReadWriteRows3
    (stateCount start halt : Nat)
    (transitions : List Transition)
    (hrows :
      forall t : Transition,
        t ∈ transitions ->
          supportsReadWriteRow3 t = true) :
    supportsReadWriteRows3
      (description stateCount start halt transitions) = true :=
  supportsReadWriteRows3_eq_true_of_supported
    (description_supported stateCount start halt transitions hrows)

/-!
## Three-tape configurations
-/

/-- A structured configuration with exactly three logical tapes. -/
def config
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    Configuration where
  state := state
  tapes := [tape0, tape1, tape2]

@[simp] theorem config_state
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    (config state tape0 tape1 tape2).state = state := by
  rfl

@[simp] theorem config_tapes
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    (config state tape0 tape1 tape2).tapes =
      [tape0, tape1, tape2] := by
  rfl

@[simp] theorem tapeAt_config_zero
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    Description.tapeAt
        (config state tape0 tape1 tape2).tapes 0 =
      tape0 := by
  rfl

@[simp] theorem tapeAt_config_one
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    Description.tapeAt
        (config state tape0 tape1 tape2).tapes 1 =
      tape1 := by
  rfl

@[simp] theorem tapeAt_config_two
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    Description.tapeAt
        (config state tape0 tape1 tape2).tapes 2 =
      tape2 := by
  rfl

@[simp] theorem currentReads_config
    (D : Description) (hD : D.tapeCount = 3)
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    D.currentReads (config state tape0 tape1 tape2) =
      [Tape.read tape0, Tape.read tape1, Tape.read tape2] := by
  exact Description.currentReads_three D hD state tape0 tape1 tape2

@[simp] theorem applyActions_config
    (D : Description) (hD : D.tapeCount = 3)
    (state : Nat) (action0 action1 action2 : TapeAction)
    (tape0 tape1 tape2 : Tape Bool) :
    D.applyActions [action0, action1, action2]
        (config state tape0 tape1 tape2).tapes =
      [action0.apply tape0, action1.apply tape1, action2.apply tape2] := by
  exact
    Description.applyActions_three D hD action0 action1 action2
      tape0 tape1 tape2

/-!
## Common tape views
-/

/--
Source tape view with a {lit}`live` middle segment and a blank-separated suffix.

The head is at the first cell of
{lit}`prefix ++ live ++ none :: suffix ++ [none]`, or at a blank if both
{lit}`prefix` and {lit}`live` are empty.
-/
def inputWithLiveTail
    (leftRev : List (Option Bool))
    (prefixBits live suffix : Word Bool) : Tape Bool :=
  tapeAtCells leftRev
    (List.append (prefixBits.map some)
      (List.append (live.map some)
        (none :: List.append (suffix.map some) [none])))

theorem inputWithLiveTail_cells
    (leftRev : List (Option Bool))
    (prefixBits live suffix : Word Bool) :
    Tape.cells (inputWithLiveTail leftRev prefixBits live suffix) =
      List.append leftRev.reverse
        (List.append (prefixBits.map some)
          (List.append (live.map some)
            (none :: List.append (suffix.map some) [none]))) := by
  cases prefixBits <;> cases live <;>
    simp [inputWithLiveTail, tapeAtCells, Tape.cells]

/-- Output tape with all emitted bits to the left of a blank head. -/
def outputFromBits (bits : Word Bool) : Tape Bool where
  left := bits.reverse.map some
  head := none
  right := []

theorem outputFromBits_cells
    (bits : Word Bool) :
    Tape.cells (outputFromBits bits) =
      List.append (bits.map some) [none] := by
  simp [outputFromBits, Tape.cells, List.map_reverse]

theorem outputFromBits_normalizedOutput
    (bits : Word Bool) :
    Tape.normalizedOutput (outputFromBits bits) = bits := by
  simp [Tape.normalizedOutput, outputFromBits_cells, Function.comp_def]

/-- Scratch tape with {lit}`n` marker cells to the left of a blank head. -/
def markerScratch (n : Nat) : Tape Bool :=
  tapeAtCells (List.replicate n (some true)) []

theorem markerScratch_cells
    (n : Nat) :
    Tape.cells (markerScratch n) =
      List.append (List.replicate n (some true)) [none] := by
  simp [markerScratch, tapeAtCells, Tape.cells]

/-!
## Phase composition
-/

theorem runConfig_chain2
    {D : Description} {n m : Nat}
    {c c1 c2 : Configuration}
    (h1 : D.runConfig n c = c1)
    (h2 : D.runConfig m c1 = c2) :
    D.runConfig (n + m) c = c2 := by
  rw [Description.runConfig_add, h1, h2]

theorem runConfig_chain3
    {D : Description} {n m k : Nat}
    {c c1 c2 c3 : Configuration}
    (h1 : D.runConfig n c = c1)
    (h2 : D.runConfig m c1 = c2)
    (h3 : D.runConfig k c2 = c3) :
    D.runConfig ((n + m) + k) c = c3 := by
  rw [Description.runConfig_add]
  rw [runConfig_chain2 h1 h2]
  exact h3

theorem runConfig_chain4
    {D : Description} {n m k l : Nat}
    {c c1 c2 c3 c4 : Configuration}
    (h1 : D.runConfig n c = c1)
    (h2 : D.runConfig m c1 = c2)
    (h3 : D.runConfig k c2 = c3)
    (h4 : D.runConfig l c3 = c4) :
    D.runConfig (((n + m) + k) + l) c = c4 := by
  rw [Description.runConfig_add]
  rw [runConfig_chain3 h1 h2 h3]
  exact h4

end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
