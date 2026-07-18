import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockSimulation

set_option doc.verso true

/-!
# Exact-code validator: physical header-bound pass

This module supplies the first executable subphase of M4 leaf 3.  Starting at
the header parser's transition-region handoff, it moves left over the four
preserved unary fields, checks

* {lit}`0 < stateCount`,
* {lit}`start < stateCount`, and
* {lit}`halt < stateCount`,

then restores every temporary marker and returns to the same transition-region
head position.  The transition count and the arbitrary suffix are preserved.

The comparison loop pairs rightmost unary ticks.  A processed tick is changed
from canonical {lit}`0010` to invalid {lit}`1010`; field boundaries determine
which logical value a marker belongs to.  Strictness is witnessed by requiring
one unmarked state-count tick after all ticks of the compared field have been
paired.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace ValidatorHeaderBounds

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

/-!
Logical states:

* 0--6 locate the state-count/start fields and prove state-count nonempty;
* 7--15 pair and restore the start/state-count ticks;
* 16--28 pair and restore the halt/state-count ticks;
* 29 returns across the transition-count field; 30 is the halt state.
-/

/-- Aligned block table for the fixed header-bound checks. -/
def blockDescription : ValidatorBlockDescription where
  stateCount := 31
  start := 0
  halt := 30
  transitions :=
    [ keep 0 .done Direction.left 1

    , keep 1 .tick Direction.left 1
    , keep 1 .done Direction.left 2
    , keep 2 .tick Direction.left 2
    , keep 2 .done Direction.left 3
    , keep 3 .tick Direction.left 3
    , keep 3 .done Direction.left 4
    , keep 4 .tick Direction.right 5

    , keep 5 .tick Direction.right 5
    , keep 5 .done Direction.right 6
    , keep 6 .tick Direction.right 6
    , keep 6 .marker010 Direction.right 6
    , keep 6 .done Direction.left 7

    , keep 7 .marker010 Direction.left 7
    , write 7 .tick .marker010 Direction.left 8
    , keep 7 .done Direction.left 12
    , keep 8 .tick Direction.left 8
    , keep 8 .marker010 Direction.left 8
    , keep 8 .done Direction.left 9
    , keep 9 .marker010 Direction.left 9
    , write 9 .tick .marker010 Direction.right 10
    , keep 10 .tick Direction.right 10
    , keep 10 .marker010 Direction.right 10
    , keep 10 .done Direction.right 6

    , keep 12 .marker010 Direction.left 12
    , keep 12 .tick Direction.left 13
    , keep 13 .tick Direction.left 13
    , keep 13 .marker010 Direction.left 13
    , keep 13 .header Direction.right 14
    , keep 14 .tick Direction.right 14
    , write 14 .marker010 .tick Direction.right 14
    , keep 14 .done Direction.right 15
    , keep 15 .tick Direction.right 15
    , write 15 .marker010 .tick Direction.right 15
    , keep 15 .done Direction.right 16

    , keep 16 .tick Direction.right 16
    , keep 16 .marker010 Direction.right 16
    , keep 16 .done Direction.left 17
    , keep 17 .marker010 Direction.left 17
    , write 17 .tick .marker010 Direction.left 18
    , keep 17 .done Direction.left 22
    , keep 18 .tick Direction.left 18
    , keep 18 .marker010 Direction.left 18
    , keep 18 .done Direction.left 19
    , keep 19 .tick Direction.left 19
    , keep 19 .done Direction.left 20
    , keep 20 .marker010 Direction.left 20
    , write 20 .tick .marker010 Direction.right 21
    , keep 21 .tick Direction.right 21
    , keep 21 .marker010 Direction.right 21
    , keep 21 .done Direction.right 23
    , keep 23 .tick Direction.right 23
    , keep 23 .done Direction.right 16

    , keep 22 .tick Direction.left 22
    , keep 22 .done Direction.left 24
    , keep 24 .marker010 Direction.left 24
    , keep 24 .tick Direction.left 25
    , keep 25 .tick Direction.left 25
    , keep 25 .marker010 Direction.left 25
    , keep 25 .header Direction.right 26
    , keep 26 .tick Direction.right 26
    , write 26 .marker010 .tick Direction.right 26
    , keep 26 .done Direction.right 27
    , keep 27 .tick Direction.right 27
    , keep 27 .done Direction.right 28
    , keep 28 .tick Direction.right 28
    , write 28 .marker010 .tick Direction.right 28
    , keep 28 .done Direction.right 29
    , keep 29 .tick Direction.right 29
    , keep 29 .done Direction.right 30
    ]

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

/--
Concrete Boolean machine for the header-bound pass.

The four entry states move from the first suffix block (or the blank cell of an
empty suffix) to the first bit of the final transition-count {lit}`done` token.
The aligned block core then performs both strict unary comparisons.
-/
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

set_option maxRecDepth 100000 in
private theorem description_transitionKeyRanksAdjacentIncreasingBool :
    transitionKeyRanksAdjacentIncreasingBool Description.transitions = true := by
  decide

set_option maxRecDepth 10000 in
theorem description_subroutineReady : Description.SubroutineReady := by
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · rw [description_transitions_eq_chunks]
      exact transition_wellFormed_of_chunk_all
        (chunks := transitionChunks) (by decide)
    · exact transition_deterministic_of_keyRanksAdjacentIncreasingBool
        description_transitionKeyRanksAdjacentIncreasingBool
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

/-!
## Logical block layouts

These views are the proof boundary between the compact 31-state block table
and its generated Boolean table.  The logical start is reached after the four
raw entry moves, with the head on the final transition-count terminator.
-/

/-- Canonical block view of one unary natural-number field. -/
def natBlocks (value : Nat) : Word ValidatorBlockSymbol :=
  List.append (List.replicate value .tick) [.done]

theorem validatorCanonicalBlocks_encodeNat (value : Nat) :
    validatorCanonicalBlocks (encodeNat value) = natBlocks value := by
  induction value with
  | zero =>
      rfl
  | succ value ih =>
      change .tick :: validatorCanonicalBlocks (encodeNat value) = _
      rw [ih]
      rfl

/-- Complete canonical header prefix as aligned logical blocks. -/
def prefixBlocks
    (stateCount start halt transitionCount : Nat) :
    Word ValidatorBlockSymbol :=
  .header ::
    List.append (natBlocks stateCount)
      (List.append (natBlocks start)
        (List.append (natBlocks halt) (natBlocks transitionCount)))

/-- Blocks strictly left of the logical core's initial head position. -/
def startLeftBlocks
    (stateCount start halt transitionCount : Nat) :
    Word ValidatorBlockSymbol :=
  .header ::
    List.append (natBlocks stateCount)
      (List.append (natBlocks start)
        (List.append (natBlocks halt)
          (List.replicate transitionCount .tick)))

theorem prefixBlocks_eq_startLeftBlocks_append_done
    (stateCount start halt transitionCount : Nat) :
    prefixBlocks stateCount start halt transitionCount =
      List.append
        (startLeftBlocks stateCount start halt transitionCount) [.done] := by
  simp [prefixBlocks, startLeftBlocks, natBlocks, List.append_assoc]

theorem validatorCanonicalBlocks_headerFieldsPrefix
    (stateCount start halt transitionCount : Nat) :
    validatorCanonicalBlocks
        (validatorHeaderFieldsPrefix
          stateCount start halt transitionCount) =
      prefixBlocks stateCount start halt transitionCount := by
  unfold validatorHeaderFieldsPrefix prefixBlocks
  change .header ::
      validatorCanonicalBlocks
        (encodeNatAppend stateCount
          (encodeNatAppend start
            (encodeNatAppend halt (encodeNatAppend transitionCount [])))) = _
  rw [validatorCanonicalBlocks_encodeNatAppend,
    validatorCanonicalBlocks_encodeNatAppend,
    validatorCanonicalBlocks_encodeNatAppend,
    validatorCanonicalBlocks_encodeNatAppend]
  rw [validatorCanonicalBlocks_encodeNat,
    validatorCanonicalBlocks_encodeNat,
    validatorCanonicalBlocks_encodeNat,
    validatorCanonicalBlocks_encodeNat]
  simp [validatorCanonicalBlocks]

/-- Logical configuration entered by the aligned block core. -/
def logicalStartConfig
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    ValidatorBlockDescription.Configuration :=
  { state := blockDescription.start
    tape := validatorLogicalBlockTape
      (startLeftBlocks stateCount start halt transitionCount)
      (.done :: validatorCanonicalBlocks tokens) }

/-- Successful logical endpoint, with the restored prefix left of the suffix. -/
def logicalHandoffConfig
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    ValidatorBlockDescription.Configuration :=
  { state := blockDescription.halt
    tape := validatorLogicalBlockTape
      (prefixBlocks stateCount start halt transitionCount)
      (validatorCanonicalBlocks tokens) }

end ValidatorHeaderBounds

/-!
## Semantic and exact physical contract
-/

/-- Boolean currency checked by the first physical leaf-3 subphase. -/
def validatorHeaderBoundsBool
    (stateCount start halt : Nat) : Bool :=
  decide (0 < stateCount) &&
    decide (start < stateCount) &&
    decide (halt < stateCount)

theorem validatorHeaderBoundsBool_eq_true_iff
    (stateCount start halt : Nat) :
    validatorHeaderBoundsBool stateCount start halt = true <->
      0 < stateCount ∧ start < stateCount ∧ halt < stateCount := by
  simp [validatorHeaderBoundsBool, and_assoc]

/-- The successful header-bound pass restores the leaf-3 source exactly. -/
def validatorHeaderBoundsHandoffTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) : Tape Bool :=
  validatorTransitionScannerStartTape
    stateCount start halt transitionCount tokens

theorem validatorHeaderBoundsHandoffTape_eq_blockTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    validatorHeaderBoundsHandoffTape
        stateCount start halt transitionCount tokens =
      validatorBlockTape
        (ValidatorHeaderBounds.prefixBlocks
          stateCount start halt transitionCount)
        (validatorCanonicalBlocks tokens) := by
  unfold validatorHeaderBoundsHandoffTape
  unfold validatorTransitionScannerStartTape
  unfold validatorHeaderFieldsHandoffTape validatorBlockTape
  rw [← ValidatorHeaderBounds.validatorCanonicalBlocks_headerFieldsPrefix]
  rw [validatorBlockBits_canonical, validatorBlockBits_canonical]

namespace ValidatorHeaderBounds

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

/-- The four raw entry moves reach the first aligned logical core state. -/
theorem runConfig_entry_to_logicalStart
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    Description.runConfig 4
        { state := Description.start
          tape := validatorHeaderBoundsHandoffTape
            stateCount start halt transitionCount tokens } =
      validatorPhysicalBlockConfiguration
        (logicalStartConfig
          stateCount start halt transitionCount tokens) := by
  let tape0 := validatorHeaderBoundsHandoffTape
    stateCount start halt transitionCount tokens
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
      (startLeftBlocks stateCount start halt transitionCount)
      (.done :: validatorCanonicalBlocks tokens) := by
    dsimp [tape4, tape3, tape2, tape1, tape0]
    rw [validatorHeaderBoundsHandoffTape_eq_blockTape]
    rw [prefixBlocks_eq_startLeftBlocks_append_done]
    exact validatorBlockTape_moveLeft_four
      (startLeftBlocks stateCount start halt transitionCount)
      (validatorCanonicalBlocks tokens) .done
  change Description.runConfig 4
      { state := entryState 0, tape := tape0 } = _
  rw [hrun]
  simp only [validatorPhysicalBlockConfiguration, logicalStartConfig]
  rw [validatorPhysicalizeBlockTape_logical, htape4]
  rfl

end ValidatorHeaderBounds

end SelfHaltingRecognizer
end Computability
end FoC
