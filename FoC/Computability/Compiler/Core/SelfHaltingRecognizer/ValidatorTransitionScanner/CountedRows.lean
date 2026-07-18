import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.HeaderBounds

set_option doc.verso true

/-!
# Exact-code validator: counted transition rows

This module defines the aligned four-bit machine for the second leaf-3
subphase.  Its initial logical head is on the terminator immediately before
the first unprocessed row.  The machine marks that terminator, consumes one
tick from the declared transition count, parses one complete transition row,
and compares both unary endpoints with the preserved state-count field.

Three invalid blocks have disjoint roles:

* {lit}`1011` marks the current row boundary ({lit}`0011`);
* {lit}`1001` marks the current transition token ({lit}`0001`);
* {lit}`1010` marks paired unary ticks ({lit}`0010`).

Every successful pass restores all three marker families.  Once the declared
count is exhausted, the machine restores the count field and halts at the
first suffix token.  The four raw Boolean entry moves needed to reach the
preceding terminator are added below the logical core.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

namespace ValidatorCountedRows

private def keep
    (source : Nat) (read : ValidatorBlockSymbol)
    (move : Direction) (target : Nat) : ValidatorBlockTransition where
  source := source
  read := read
  write := read
  move := move
  target := target

private def write
    (source : Nat) (read write : ValidatorBlockSymbol)
    (move : Direction) (target : Nat) : ValidatorBlockTransition where
  source := source
  read := read
  write := write
  move := move
  target := target

private def keepRows
    (source : Nat) (symbols : List ValidatorBlockSymbol)
    (move : Direction) (target : Nat) :
    List ValidatorBlockTransition :=
  symbols.map (fun symbol => keep source symbol move target)

/-- Canonical non-header symbols that may occur in a scan corridor. -/
def canonicalCorridorSymbols : List ValidatorBlockSymbol :=
  [.transition, .tick, .done, .blank, .zero, .one,
    .moveLeft, .moveRight]

/-- Corridors may additionally contain paired unary markers. -/
def corridorSymbols : List ValidatorBlockSymbol :=
  canonicalCorridorSymbols ++ [.marker010]

/-- A leftward trip may cross the marked current transition as well. -/
def leftCorridorSymbols : List ValidatorBlockSymbol :=
  corridorSymbols ++ [.marker001]

/-!
Logical states:

* 0--7 select one declared row and mark its transition token;
* 8--19 check and restore the source field, then parse fixed row tokens;
* 20--37 check and restore the target field and return to the row boundary;
* 38--40 restore the count and halt at the arbitrary suffix.
-/

/-- Aligned block table for counted row parsing and endpoint bounds. -/
def blockDescription : ValidatorBlockDescription where
  stateCount := 41
  start := 0
  halt := 40
  transitions :=
    [ write 0 .done .marker011 Direction.left 1
    , keep 1 .header Direction.right 2

    , keep 2 .tick Direction.right 2
    , keep 2 .done Direction.right 3
    , keep 3 .tick Direction.right 3
    , keep 3 .done Direction.right 4
    , keep 4 .tick Direction.right 4
    , keep 4 .done Direction.right 5

    , keep 5 .marker010 Direction.right 5
    , write 5 .tick .marker010 Direction.right 6
    , keep 5 .done Direction.left 38
    , write 5 .marker011 .done Direction.right 40

    , write 6 .marker011 .done Direction.right 7
    , write 7 .transition .marker001 Direction.right 8

    , keep 8 .marker010 Direction.right 8
    , write 8 .tick .marker010 Direction.left 9
    , keep 8 .done Direction.left 12
    , keep 9 .header Direction.right 10
    , keep 10 .marker010 Direction.right 10
    , write 10 .tick .marker010 Direction.right 11
    , keep 11 .marker001 Direction.right 8

    , keep 12 .header Direction.right 13
    , keep 13 .marker010 Direction.right 13
    , keep 13 .tick Direction.left 14
    , write 14 .marker010 .tick Direction.left 14
    , keep 14 .header Direction.right 15
    , keep 15 .marker001 Direction.right 16
    , write 16 .marker010 .tick Direction.right 16
    , keep 16 .done Direction.right 17

    , keep 17 .blank Direction.right 18
    , keep 17 .zero Direction.right 18
    , keep 17 .one Direction.right 18
    , keep 18 .blank Direction.right 19
    , keep 18 .zero Direction.right 19
    , keep 18 .one Direction.right 19
    , keep 19 .moveLeft Direction.right 20
    , keep 19 .moveRight Direction.right 20

    , keep 20 .marker010 Direction.right 20
    , write 20 .tick .marker010 Direction.left 21
    , keep 20 .done Direction.left 28
    , keep 21 .header Direction.right 22
    , keep 22 .marker010 Direction.right 22
    , write 22 .tick .marker010 Direction.right 23
    , keep 23 .marker001 Direction.right 24
    , keep 24 .tick Direction.right 24
    , keep 24 .done Direction.right 25
    , keep 25 .blank Direction.right 26
    , keep 25 .zero Direction.right 26
    , keep 25 .one Direction.right 26
    , keep 26 .blank Direction.right 27
    , keep 26 .zero Direction.right 27
    , keep 26 .one Direction.right 27
    , keep 27 .moveLeft Direction.right 20
    , keep 27 .moveRight Direction.right 20

    , keep 28 .header Direction.right 29
    , keep 29 .marker010 Direction.right 29
    , keep 29 .tick Direction.left 30
    , write 30 .marker010 .tick Direction.left 30
    , keep 30 .header Direction.right 31
    , write 31 .marker001 .transition Direction.right 32
    , keep 32 .tick Direction.right 32
    , keep 32 .done Direction.right 33
    , keep 33 .blank Direction.right 34
    , keep 33 .zero Direction.right 34
    , keep 33 .one Direction.right 34
    , keep 34 .blank Direction.right 35
    , keep 34 .zero Direction.right 35
    , keep 34 .one Direction.right 35
    , keep 35 .moveLeft Direction.right 36
    , keep 35 .moveRight Direction.right 36
    , write 36 .marker010 .tick Direction.right 36
    , keep 36 .done Direction.left 37
    , keep 37 .tick Direction.right 0
    , keep 37 .moveLeft Direction.right 0
    , keep 37 .moveRight Direction.right 0

    , write 38 .marker010 .tick Direction.left 38
    , keep 38 .done Direction.right 39
    , write 39 .marker011 .done Direction.right 40
    ] ++
      keepRows 1 leftCorridorSymbols Direction.left 1 ++
      keepRows 6 corridorSymbols Direction.right 6 ++
      keepRows 9 leftCorridorSymbols Direction.left 9 ++
      keepRows 11 corridorSymbols Direction.right 11 ++
      keepRows 12 leftCorridorSymbols Direction.left 12 ++
      keepRows 15 corridorSymbols Direction.right 15 ++
      keepRows 21 leftCorridorSymbols Direction.left 21 ++
      keepRows 23 corridorSymbols Direction.right 23 ++
      keepRows 28 leftCorridorSymbols Direction.left 28 ++
      keepRows 31 corridorSymbols Direction.right 31 ++
      keepRows 39 corridorSymbols Direction.right 39

private def coreDescription : MachineDescription :=
  compileValidatorBlockDescription blockDescription

private def entryState (phase : Nat) : Nat :=
  coreDescription.stateCount + phase

private def entryRow
    (phase : Nat) (read : Option Bool) (target : Nat) :
    TransitionDescription where
  source := entryState phase
  read := read
  write := read
  move := Direction.left
  target := target

private def entryRowsAt (phase target : Nat) :
    List TransitionDescription :=
  [entryRow phase none target,
    entryRow phase (some false) target,
    entryRow phase (some true) target]

private def entryRows : List TransitionDescription :=
  entryRowsAt 0 (entryState 1) ++
    entryRowsAt 1 (entryState 2) ++
    entryRowsAt 2 (entryState 3) ++
    entryRowsAt 3 coreDescription.start

/-- Concrete Boolean description for the counted-row subphase. -/
def Description : MachineDescription where
  stateCount := coreDescription.stateCount + 4
  start := entryState 0
  halt := coreDescription.halt
  transitions := coreDescription.transitions ++ entryRows

private def transitionChunks : List (List TransitionDescription) :=
  validatorBlockTransitionChunks blockDescription ++ [entryRows]

set_option maxRecDepth 100000 in
private theorem description_transitions_eq_chunks :
    Description.transitions = transitionChunks.flatten := by
  rfl

private def transitionReadRank : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

private def transitionKeyRank (row : TransitionDescription) : Nat :=
  3 * row.source + transitionReadRank row.read

private def natAdjacentIncreasing : List Nat -> Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first < second ∧ natAdjacentIncreasing (second :: rest)

private def natAdjacentIncreasingBool : List Nat -> Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first < second) &&
        natAdjacentIncreasingBool (second :: rest)

private theorem natAdjacentIncreasing_of_bool
    {values : List Nat}
    (h : natAdjacentIncreasingBool values = true) :
    natAdjacentIncreasing values := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      cases rest with
      | nil => trivial
      | cons second tail =>
          simp only [natAdjacentIncreasingBool, Bool.and_eq_true,
            decide_eq_true_eq] at h
          exact ⟨h.1, ih h.2⟩

private theorem natAdjacentIncreasing_tail
    {first : Nat} {rest : List Nat}
    (h : natAdjacentIncreasing (first :: rest)) :
    natAdjacentIncreasing rest := by
  cases rest with
  | nil => trivial
  | cons second tail => exact h.2

private theorem natAdjacentIncreasing_head_lt_of_mem
    {first value : Nat} {rest : List Nat}
    (h : natAdjacentIncreasing (first :: rest))
    (hvalue : value ∈ rest) :
    first < value := by
  induction rest generalizing first with
  | nil => simp at hvalue
  | cons second tail ih =>
      rcases h with ⟨hfirst, htail⟩
      simp only [List.mem_cons] at hvalue
      rcases hvalue with rfl | hvalue
      · exact hfirst
      · exact Nat.lt_trans hfirst (ih htail hvalue)

private theorem nat_nodup_of_adjacentIncreasing
    {values : List Nat}
    (h : natAdjacentIncreasing values) : values.Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih (natAdjacentIncreasing_tail h)⟩
      intro hmem
      exact (Nat.lt_irrefl first)
        (natAdjacentIncreasing_head_lt_of_mem h hmem)

private theorem eq_of_mem_of_mem_of_transitionKeyRank_eq
    {rows : List TransitionDescription} {left right : TransitionDescription}
    (hnodup : (rows.map transitionKeyRank).Nodup)
    (hleft : left ∈ rows) (hright : right ∈ rows)
    (hkey : transitionKeyRank left = transitionKeyRank right) :
    left = right := by
  induction rows with
  | nil =>
      simp at hleft
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hfirst, hrest⟩
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · rfl
        · exfalso
          apply hfirst
          rw [hkey]
          exact List.mem_map.mpr ⟨right, hright, rfl⟩
      · rcases hright with rfl | hright
        · exfalso
          apply hfirst
          rw [← hkey]
          exact List.mem_map.mpr ⟨left, hleft, rfl⟩
        · exact ih hrest hleft hright

set_option maxRecDepth 100000 in
private theorem description_transitionKeyRanks_adjacentIncreasing :
    natAdjacentIncreasing
      (Description.transitions.map transitionKeyRank) := by
  apply natAdjacentIncreasing_of_bool
  decide

private theorem description_transitionKeyRanks_nodup :
    (Description.transitions.map transitionKeyRank).Nodup :=
  nat_nodup_of_adjacentIncreasing
    description_transitionKeyRanks_adjacentIncreasing

set_option maxRecDepth 10000 in
theorem description_subroutineReady : Description.SubroutineReady := by
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · rw [description_transitions_eq_chunks]
      exact transition_wellFormed_of_chunk_all
        (chunks := transitionChunks) (by decide)
    · unfold MachineDescription.Deterministic
      intro left right hleft hright hsameKey
      have hkey : transitionKeyRank left = transitionKeyRank right := by
        simp [transitionKeyRank, hsameKey.1, hsameKey.2]
      have heq := eq_of_mem_of_mem_of_transitionKeyRank_eq
        description_transitionKeyRanks_nodup hleft hright hkey
      subst right
      exact ⟨rfl, rfl, rfl⟩
  · unfold MachineDescription.HaltTransitionFree
    rw [description_transitions_eq_chunks]
    exact transition_notFrom_of_chunk_all
      (chunks := transitionChunks) (by decide)

/-- Every generated block-core row remains a row of the entry-extended machine. -/
theorem compiledRow_mem_description
    {row : TransitionDescription}
    (hrow : row ∈
      (compileValidatorBlockDescription blockDescription).transitions) :
    row ∈ Description.transitions := by
  exact List.mem_append_left entryRows hrow

/-- Block occupied by one encoded tape-cell value. -/
def cellBlock : Option Bool -> ValidatorBlockSymbol
  | none => .blank
  | some false => .zero
  | some true => .one

/-- Block occupied by one encoded head direction. -/
def directionBlock : Direction -> ValidatorBlockSymbol
  | Direction.left => .moveLeft
  | Direction.right => .moveRight

private theorem validatorCanonicalBlocks_encodeCell
    (cell : Option Bool) :
    validatorCanonicalBlocks (encodeCell cell) = [cellBlock cell] := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl

private theorem validatorCanonicalBlocks_encodeDirection
    (move : Direction) :
    validatorCanonicalBlocks (encodeDirection move) =
      [directionBlock move] := by
  cases move <;> rfl

private theorem validatorCanonicalBlocks_encodeCellAppend
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    validatorCanonicalBlocks (encodeCellAppend cell suffix) =
      cellBlock cell :: validatorCanonicalBlocks suffix := by
  unfold encodeCellAppend
  rw [validatorCanonicalBlocks_append,
    validatorCanonicalBlocks_encodeCell]
  rfl

private theorem validatorCanonicalBlocks_encodeDirectionAppend
    (move : Direction) (suffix : Word MachineCodeSymbol) :
    validatorCanonicalBlocks (encodeDirectionAppend move suffix) =
      directionBlock move :: validatorCanonicalBlocks suffix := by
  unfold encodeDirectionAppend
  rw [validatorCanonicalBlocks_append,
    validatorCanonicalBlocks_encodeDirection]
  rfl

/-- Canonical aligned blocks of one transition row. -/
def rowBlocks (row : TransitionDescription) :
    Word ValidatorBlockSymbol :=
  .transition ::
    List.append (ValidatorHeaderBounds.natBlocks row.source)
      (List.append
        [cellBlock row.read, cellBlock row.write, directionBlock row.move]
        (ValidatorHeaderBounds.natBlocks row.target))

/-- Canonical blocks of one encoded transition followed by an arbitrary suffix. -/
theorem validatorCanonicalBlocks_encodeTransitionAppend
    (row : TransitionDescription) (suffix : Word MachineCodeSymbol) :
    validatorCanonicalBlocks (encodeTransitionAppend row suffix) =
      List.append (rowBlocks row) (validatorCanonicalBlocks suffix) := by
  unfold encodeTransitionAppend
  change .transition ::
      validatorCanonicalBlocks
        (encodeNatAppend row.source
          (encodeCellAppend row.read
            (encodeCellAppend row.write
              (encodeDirectionAppend row.move
                (encodeNatAppend row.target suffix))))) = _
  rw [validatorCanonicalBlocks_encodeNatAppend,
    ValidatorHeaderBounds.validatorCanonicalBlocks_encodeNat,
    validatorCanonicalBlocks_encodeCellAppend,
    validatorCanonicalBlocks_encodeCellAppend,
    validatorCanonicalBlocks_encodeDirectionAppend,
    validatorCanonicalBlocks_encodeNatAppend,
    ValidatorHeaderBounds.validatorCanonicalBlocks_encodeNat]
  simp [rowBlocks, List.append_assoc]

/-- Canonical aligned blocks of a list of transition rows. -/
def rowsBlocks : List TransitionDescription ->
    Word ValidatorBlockSymbol
  | [] => []
  | row :: rest => List.append (rowBlocks row) (rowsBlocks rest)

/-- Canonical blocks of a counted transition prefix and its suffix. -/
theorem validatorCanonicalBlocks_encodeTransitionsAppend
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    validatorCanonicalBlocks (encodeTransitionsAppend rows suffix) =
      List.append (rowsBlocks rows) (validatorCanonicalBlocks suffix) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      unfold encodeTransitionsAppend rowsBlocks
      rw [validatorCanonicalBlocks_encodeTransitionAppend, ih]
      simp [List.append_assoc]

/-- Logical configuration reached by the four raw entry moves. -/
def logicalStartConfig
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    ValidatorBlockDescription.Configuration :=
  { state := blockDescription.start
    tape := validatorLogicalBlockTape
      (ValidatorHeaderBounds.startLeftBlocks
        stateCount start halt transitionCount)
      (.done :: List.append (rowsBlocks rows)
        (validatorCanonicalBlocks suffix)) }

/-- Restored logical endpoint at the first suffix token. -/
def logicalHandoffConfig
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    ValidatorBlockDescription.Configuration :=
  { state := blockDescription.halt
    tape := validatorLogicalBlockTape
      (List.append
        (ValidatorHeaderBounds.prefixBlocks
          stateCount start halt transitionCount)
        (rowsBlocks rows))
      (validatorCanonicalBlocks suffix) }

/-- Physical source at the first declared transition token. -/
def validatorCountedRowsStartTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Tape Bool :=
  validatorBlockTape
    (ValidatorHeaderBounds.prefixBlocks
      stateCount start halt transitionCount)
    (List.append (rowsBlocks rows) (validatorCanonicalBlocks suffix))

/-- Restored physical endpoint at the first suffix token. -/
def validatorCountedRowsHandoffTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Tape Bool :=
  validatorBlockTape
    (List.append
      (ValidatorHeaderBounds.prefixBlocks
        stateCount start halt transitionCount)
      (rowsBlocks rows))
    (validatorCanonicalBlocks suffix)

private theorem description_lookupTransition_eq_some_of_mem
    {row : TransitionDescription} (hrow : row ∈ Description.transitions) :
    Description.lookupTransition row.source row.read = some row := by
  cases hlookup : Description.lookupTransition row.source row.read with
  | none =>
      unfold MachineDescription.lookupTransition at hlookup
      have hmiss := List.find?_eq_none.mp hlookup row hrow
      have hmatches :
          MachineDescription.Matches row.source row.read row = true := by
        simp [MachineDescription.Matches]
      rw [hmatches] at hmiss
      contradiction
  | some found =>
      have hfoundMem : found ∈ Description.transitions :=
        MachineDescription.lookupTransition_mem hlookup
      have hfoundMatches :=
        MachineDescription.lookupTransition_matches hlookup
      have haction := description_subroutineReady.1.2.2.2.2
        row found hrow hfoundMem
        ⟨hfoundMatches.1.symm, hfoundMatches.2.symm⟩
      cases row
      cases found
      simp_all [TransitionDescription.SameAction]

private theorem runConfig_one_entryRow
    {phase target : Nat} {read : Option Bool} (tape : Tape Bool)
    (hrow : entryRow phase read target ∈ entryRows)
    (hread : Tape.read tape = read) :
    Description.runConfig 1
        { state := entryState phase, tape := tape } =
      { state := target, tape := Tape.move Direction.left tape } := by
  have hrowDescription : entryRow phase read target ∈
      Description.transitions :=
    List.mem_append_right coreDescription.transitions hrow
  have hlookup :=
    description_lookupTransition_eq_some_of_mem hrowDescription
  change Description.lookupTransition (entryState phase) read =
    some (entryRow phase read target) at hlookup
  have hwrite : Tape.write read tape = tape := by
    rw [← hread]
    exact Tape.write_read_eq_self tape
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    entryRow, hread, hlookup, hwrite]

private theorem entryRow_zero_mem (read : Option Bool) :
    entryRow 0 read (entryState 1) ∈ entryRows := by
  cases read with
  | none => simp [entryRows, entryRowsAt]
  | some bit => cases bit <;> simp [entryRows, entryRowsAt]

private theorem entryRow_one_mem (read : Option Bool) :
    entryRow 1 read (entryState 2) ∈ entryRows := by
  cases read with
  | none => simp [entryRows, entryRowsAt]
  | some bit => cases bit <;> simp [entryRows, entryRowsAt]

private theorem entryRow_two_mem (read : Option Bool) :
    entryRow 2 read (entryState 3) ∈ entryRows := by
  cases read with
  | none => simp [entryRows, entryRowsAt]
  | some bit => cases bit <;> simp [entryRows, entryRowsAt]

private theorem entryRow_three_mem (read : Option Bool) :
    entryRow 3 read coreDescription.start ∈ entryRows := by
  cases read with
  | none => simp [entryRows, entryRowsAt]
  | some bit => cases bit <;> simp [entryRows, entryRowsAt]

/-- Four raw left moves enter the aligned counted-row core. -/
theorem runConfig_entry_to_logicalStart
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    Description.runConfig 4
        { state := Description.start
          tape := validatorCountedRowsStartTape
            stateCount start halt transitionCount rows suffix } =
      validatorPhysicalBlockConfiguration
        (logicalStartConfig
          stateCount start halt transitionCount rows suffix) := by
  let tape0 := validatorCountedRowsStartTape
    stateCount start halt transitionCount rows suffix
  let tape1 := Tape.move Direction.left tape0
  let tape2 := Tape.move Direction.left tape1
  let tape3 := Tape.move Direction.left tape2
  let tape4 := Tape.move Direction.left tape3
  have hstep0 : Description.runConfig 1
      { state := entryState 0, tape := tape0 } =
      { state := entryState 1, tape := tape1 } := by
    simpa [tape1] using runConfig_one_entryRow tape0
      (entryRow_zero_mem (Tape.read tape0)) rfl
  have hstep1 : Description.runConfig 1
      { state := entryState 1, tape := tape1 } =
      { state := entryState 2, tape := tape2 } := by
    simpa [tape2] using runConfig_one_entryRow tape1
      (entryRow_one_mem (Tape.read tape1)) rfl
  have hstep2 : Description.runConfig 1
      { state := entryState 2, tape := tape2 } =
      { state := entryState 3, tape := tape3 } := by
    simpa [tape3] using runConfig_one_entryRow tape2
      (entryRow_two_mem (Tape.read tape2)) rfl
  have hstep3 : Description.runConfig 1
      { state := entryState 3, tape := tape3 } =
      { state := coreDescription.start, tape := tape4 } := by
    simpa [tape4] using runConfig_one_entryRow tape3
      (entryRow_three_mem (Tape.read tape3)) rfl
  have hrun : Description.runConfig 4
      { state := entryState 0, tape := tape0 } =
      { state := coreDescription.start, tape := tape4 } := by
    rw [show 4 = 1 + 3 by decide,
      MachineDescription.runConfig_add, hstep0]
    rw [show 3 = 1 + 2 by decide,
      MachineDescription.runConfig_add, hstep1]
    rw [show 2 = 1 + 1 by decide,
      MachineDescription.runConfig_add, hstep2, hstep3]
  have htape4 : tape4 = validatorBlockTape
      (ValidatorHeaderBounds.startLeftBlocks
        stateCount start halt transitionCount)
      (.done :: List.append (rowsBlocks rows)
        (validatorCanonicalBlocks suffix)) := by
    dsimp [tape4, tape3, tape2, tape1, tape0]
    unfold validatorCountedRowsStartTape
    rw [ValidatorHeaderBounds.prefixBlocks_eq_startLeftBlocks_append_done]
    exact validatorBlockTape_moveLeft_four
      (ValidatorHeaderBounds.startLeftBlocks
        stateCount start halt transitionCount)
      (List.append (rowsBlocks rows) (validatorCanonicalBlocks suffix))
      .done
  change Description.runConfig 4
      { state := entryState 0, tape := tape0 } = _
  rw [hrun]
  simp only [validatorPhysicalBlockConfiguration, logicalStartConfig]
  rw [validatorPhysicalizeBlockTape_logical, htape4]
  rfl

end ValidatorCountedRows

end SelfHaltingRecognizer
end Computability
end FoC
