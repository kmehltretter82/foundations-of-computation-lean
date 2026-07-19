import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Ready
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.Rows
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachine.Lookup
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachineInversion
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsPhysical

set_option doc.verso true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Exact-code validator: physical determinism-gate execution

This module composes the shared four-cell entry wrapper with the generated
Boolean simulation of the complete nested logical row scan.  Compatible tables
restore the exact encoded description and halt on the original blank boundary.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

/-- Every logical determinism-gate row has an in-range source state. -/
theorem blockDescription_sourceBound
    (row : ValidatorBlockTransition)
    (hrow : row ∈ blockDescription.transitions) :
    row.source < blockDescription.stateCount := by
  have hall : blockDescription.transitions.all
      (fun candidate =>
        decide (candidate.source < blockDescription.stateCount)) = true := by
    decide
  have hbool := List.all_eq_true.mp hall row hrow
  simpa only [decide_eq_true_eq] using hbool

/-- No logical row leaves the successful halt state. -/
theorem blockDescription_haltFree
    (row : ValidatorBlockTransition)
    (hrow : row ∈ blockDescription.transitions) :
    row.source ≠ blockDescription.halt := by
  have hall : blockDescription.transitions.all
      (fun candidate =>
        decide (candidate.source ≠ blockDescription.halt)) = true := by
    decide
  have hbool := List.all_eq_true.mp hall row hrow
  simpa only [decide_eq_true_eq] using hbool

/-- Every logical rewrite preserves the three non-leading physical bits. -/
theorem blockDescription_tailCompatible
    (state : Nat) (read : ValidatorBlockSymbol)
    (row : ValidatorBlockTransition)
    (hlookup : blockDescription.lookup state read = some row) :
    row.read.tailBits = row.write.tailBits := by
  have hall : blockDescription.transitions.all
      (fun candidate =>
        decide (candidate.read.tailBits = candidate.write.tailBits)) = true := by
    decide
  have hbool := List.all_eq_true.mp hall row
    (ValidatorBlockDescription.lookup_mem hlookup)
  simpa only [decide_eq_true_eq] using hbool

/-- Lift any complete logical determinism-gate run through the generated
Boolean block compiler. -/
theorem physicallyReaches_of_logicalReaches
    {source target : ValidatorBlockDescription.Configuration}
    (hrun : blockDescription.Reaches source target) :
    ValidatorBlockPhysicalReaches Description
      (validatorPhysicalBlockConfiguration source)
      (validatorPhysicalBlockConfiguration target) := by
  apply validatorBlockPhysicalReaches_of_logicalReaches
    (D := blockDescription) (M := Description)
  · intro row hrow
    exact compiledRow_mem_description hrow
  · exact description_subroutineReady.1.2.2.2.2
  · exact blockDescription_sourceBound
  · exact blockDescription_haltFree
  · exact blockDescription_tailCompatible
  · exact hrun

/-- A logical conflict path reaches a contiguous concrete missing physical
transition. -/
theorem physicalExistsContiguousReachesStuck_of_conflict
    {source : ValidatorBlockDescription.Configuration}
    (hconflict : ReachesConflict source) :
    exists stuck : Tape Bool,
      Description.ReachesStuck
          (validatorPhysicalBlockConfiguration source) stuck ∧
        ContiguousTape stuck := by
  rcases hconflict with ⟨left, right, hreaches⟩
  change List ValidatorBlockSymbol at right
  cases right with
  | nil =>
      let witness : ValidatorBlockRootBlankStuckWitness
          blockDescription Description source :=
        { logical := 100
          left := left
          reaches := by
            simpa [configuration,
              ValidatorBlockDescription.blockConfiguration] using hreaches
          logical_lt := by decide
          logical_ne_halt := by decide
          root_none := by
            apply lookupTransition_withValidatorFourLeftEntry_eq_none
              physicalCoreDescription
            · decide
            · simpa [physicalCoreDescription] using
                compileValidatorBlockDescription_lookup_root_none
                  blockDescription 100
          root_ne_halt := by decide }
      exact ⟨validatorBlockTape witness.left [],
        validatorBlockPhysical_reachesStuck_of_rootBlankStuckWitness
          (D := blockDescription) (M := Description)
          (fun row hrow => compiledRow_mem_description hrow)
          description_subroutineReady.1.2.2.2.2
          blockDescription_sourceBound
          blockDescription_haltFree
          blockDescription_tailCompatible witness,
        validatorBlockRootStuckTape_contiguous witness.left⟩
  | cons read right =>
      let witness : ValidatorBlockLeafStuckWitness
          blockDescription Description source :=
        { logical := 100
          left := left
          right := right
          read := read
          reaches := by
            simpa [configuration,
              ValidatorBlockDescription.blockConfiguration] using hreaches
          logical_lt := by decide
          logical_ne_halt := by decide
          leaf_none := by
            apply lookupTransition_withValidatorFourLeftEntry_eq_none
              physicalCoreDescription
            · cases read <;> decide
            · apply compileValidatorBlockDescription_lookup_leaf_none
              cases read <;> decide
          leaf_ne_halt := by cases read <;> decide }
      exact ⟨Tape.move Direction.right
          (Tape.move Direction.right
            (Tape.move Direction.right
              (validatorBlockTape witness.left
                (witness.read :: witness.right)))),
        validatorBlockPhysical_reachesStuck_of_leafStuckWitness
          (D := blockDescription) (M := Description)
          (fun row hrow => compiledRow_mem_description hrow)
          description_subroutineReady.1.2.2.2.2
          blockDescription_sourceBound
          blockDescription_haltFree
          blockDescription_tailCompatible witness,
        validatorBlockLeafStuckTape_contiguous
          witness.left witness.right witness.read⟩

/-- A logical conflict path reaches a concrete missing physical transition. -/
theorem physicalReachesStuck_of_conflict
    {source : ValidatorBlockDescription.Configuration}
    (hconflict : ReachesConflict source) :
    exists stuck : Tape Bool,
      Description.ReachesStuck
        (validatorPhysicalBlockConfiguration source) stuck := by
  rcases physicalExistsContiguousReachesStuck_of_conflict hconflict with
    ⟨stuck, hstuck, _hcontiguous⟩
  exact ⟨stuck, hstuck⟩

/-- A logical conflict path prevents every generated physical run from
reaching the successful halt. -/
theorem physicalState_ne_halt_of_conflict
    {source : ValidatorBlockDescription.Configuration}
    (hconflict : ReachesConflict source) :
    forall steps : Nat,
      (Description.runConfig steps
        (validatorPhysicalBlockConfiguration source)).state ≠
          Description.halt := by
  rcases physicalReachesStuck_of_conflict hconflict with
    ⟨_stuck, steps, state, hrun, hstep, hstate⟩
  intro n
  exact
    CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      description_subroutineReady.2 hrun hstep hstate

private theorem sourceTape_eq_blockTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) :
    sourceTape stateCount start halt transitionCount rows =
      validatorBlockTape
        (List.append
          (ValidatorHeaderBounds.prefixBlocks
            stateCount start halt transitionCount)
          (ValidatorCountedRows.rowsBlocks rows)) [] := by
  unfold sourceTape
  rw [← ValidatorCountedRows.validatorCountedRowsHandoffTape_eq_scannerHandoffTape]
  rfl

private theorem runConfig_entry_to_logicalStart
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (left : Word ValidatorBlockSymbol)
    (hsource :
      sourceTape stateCount start halt transitionCount rows =
        validatorBlockTape (List.append left [.done]) []) :
    Description.runConfig 4
        { state := Description.start
          tape := sourceTape
            stateCount start halt transitionCount rows } =
      validatorPhysicalBlockConfiguration
        (configuration 0 left [.done]) := by
  have hdet :
      (withValidatorFourLeftEntry physicalCoreDescription).Deterministic := by
    simpa [Description] using
      description_subroutineReady.1.2.2.2.2
  have hrun := runConfig_withValidatorFourLeftEntry
    physicalCoreDescription hdet
    (sourceTape stateCount start halt transitionCount rows)
  have htape :
      Tape.move Direction.left
          (Tape.move Direction.left
            (Tape.move Direction.left
              (Tape.move Direction.left
                (sourceTape stateCount start halt transitionCount rows)))) =
        validatorBlockTape left [.done] := by
    rw [hsource]
    exact validatorBlockTape_moveLeft_four left [] .done
  simpa [Description, validatorPhysicalBlockConfiguration,
    configuration, ValidatorBlockDescription.blockConfiguration,
    physicalCoreDescription, blockDescription,
    validatorPhysicalizeBlockTape_logical, htape] using hrun

private def nonemptyStartLeftBlocks
    (stateCount start halt transitionCount : Nat)
    (front : List TransitionDescription)
    (last : TransitionDescription) : Word ValidatorBlockSymbol :=
  List.append
    (ValidatorHeaderBounds.prefixBlocks
      stateCount start halt transitionCount)
    (List.append (ValidatorCountedRows.rowsBlocks front)
      (.transition :: rowInteriorBlocks last))

private theorem sourceTape_nonempty_split
    (stateCount start halt transitionCount : Nat)
    (front : List TransitionDescription)
    (last : TransitionDescription) :
    sourceTape stateCount start halt transitionCount (front ++ [last]) =
      validatorBlockTape
        (List.append
          (nonemptyStartLeftBlocks
            stateCount start halt transitionCount front last)
          [.done]) [] := by
  rw [sourceTape_eq_blockTape,
    ValidatorCountedRows.rowsBlocks_append]
  simp [nonemptyStartLeftBlocks, ValidatorCountedRows.rowsBlocks,
    rowBlocks_eq_transition_cons_interior_append_done,
    List.append_assoc]

private theorem sourceTape_empty_split
    (stateCount start halt transitionCount : Nat) :
    sourceTape stateCount start halt transitionCount [] =
      validatorBlockTape
        (List.append
          (ValidatorHeaderBounds.startLeftBlocks
            stateCount start halt transitionCount) [.done]) [] := by
  rw [sourceTape_eq_blockTape]
  simp [ValidatorCountedRows.rowsBlocks,
    ValidatorHeaderBounds.prefixBlocks_eq_startLeftBlocks_append_done]

/-- A conflicting transition table reaches a contiguous concrete missing
physical row from the public determinism-gate source. -/
theorem exists_contiguous_stuckFromTape_of_upperPairs_false
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (hupper : transitionUpperPairsBool rows = false) :
    exists stuck : Tape Bool,
      Description.StuckFromTape
          (sourceTape stateCount start halt transitionCount rows) stuck ∧
        ContiguousTape stuck := by
  have hnil : rows ≠ [] := by
    intro hrows
    subst rows
    simp [transitionUpperPairsBool] at hupper
  have hsplit := List.dropLast_concat_getLast hnil
  have hupperSplit := hupper
  rw [← hsplit] at hupperSplit
  have hconflict : ReachesConflict
      (configuration 0
        (nonemptyStartLeftBlocks stateCount start halt transitionCount
          rows.dropLast (rows.getLast hnil)) [.done]) := by
    simpa [nonemptyStartLeftBlocks] using
      reaches_encoded_nonempty_table_conflict
        stateCount start halt transitionCount
        rows.dropLast (rows.getLast hnil) [] hupperSplit
  have hentrySplit := runConfig_entry_to_logicalStart
    stateCount start halt transitionCount
    (rows.dropLast ++ [rows.getLast hnil])
    (nonemptyStartLeftBlocks stateCount start halt transitionCount
      rows.dropLast (rows.getLast hnil))
    (sourceTape_nonempty_split stateCount start halt transitionCount
      rows.dropLast (rows.getLast hnil))
  have hentry : Description.runConfig 4
      { state := Description.start
        tape := sourceTape stateCount start halt transitionCount rows } =
      validatorPhysicalBlockConfiguration
        (configuration 0
          (nonemptyStartLeftBlocks stateCount start halt transitionCount
            rows.dropLast (rows.getLast hnil)) [.done]) := by
    simpa [hsplit] using hentrySplit
  rcases physicalExistsContiguousReachesStuck_of_conflict hconflict with
    ⟨stuck, hstuck, hcontiguous⟩
  exact ⟨stuck,
    MachineDescription.ReachesStuck.prepend hentry hstuck, hcontiguous⟩

/-- A conflicting transition table reaches a concrete missing physical row
from the public determinism-gate source. -/
theorem exists_stuckFromTape_of_upperPairs_false
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (hupper : transitionUpperPairsBool rows = false) :
    exists stuck : Tape Bool,
      Description.StuckFromTape
        (sourceTape stateCount start halt transitionCount rows) stuck := by
  rcases exists_contiguous_stuckFromTape_of_upperPairs_false
      stateCount start halt transitionCount rows hupper with
    ⟨stuck, hstuck, _hcontiguous⟩
  exact ⟨stuck, hstuck⟩

/-- A compatible nonempty encoded table reaches the restored physical source. -/
theorem physicallyReaches_nonemptyTable
    (stateCount start halt transitionCount : Nat)
    (front : List TransitionDescription)
    (last : TransitionDescription)
    (hupper : transitionUpperPairsBool (front ++ [last]) = true) :
    ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := sourceTape stateCount start halt transitionCount
          (front ++ [last]) }
      { state := Description.halt
        tape := targetTape stateCount start halt transitionCount
          (front ++ [last]) } := by
  have hentry : ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := sourceTape stateCount start halt transitionCount
          (front ++ [last]) }
      (validatorPhysicalBlockConfiguration
        (configuration 0
          (nonemptyStartLeftBlocks
            stateCount start halt transitionCount front last)
          [.done])) :=
    ⟨4, runConfig_entry_to_logicalStart
      stateCount start halt transitionCount (front ++ [last])
      (nonemptyStartLeftBlocks
        stateCount start halt transitionCount front last)
      (sourceTape_nonempty_split
        stateCount start halt transitionCount front last)⟩
  have hlogical := reaches_encoded_nonempty_table_from_start
    stateCount start halt transitionCount front last [] hupper
  have hcore := physicallyReaches_of_logicalReaches hlogical
  have hrun := hentry.trans hcore
  have hsource := sourceTape_eq_blockTape
    stateCount start halt transitionCount (front ++ [last])
  have hhaltState : Description.halt =
      validatorBlockRootState 101 := rfl
  simpa [nonemptyStartLeftBlocks, validatorPhysicalBlockConfiguration,
    configuration, ValidatorBlockDescription.blockConfiguration,
    validatorPhysicalizeBlockTape_logical, targetTape, hsource, hhaltState]
    using hrun

/-- The empty encoded table reaches the restored physical source. -/
theorem physicallyReaches_emptyTable
    (stateCount start halt transitionCount : Nat) :
    ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := sourceTape stateCount start halt transitionCount [] }
      { state := Description.halt
        tape := targetTape stateCount start halt transitionCount [] } := by
  have hentry : ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := sourceTape stateCount start halt transitionCount [] }
      (validatorPhysicalBlockConfiguration
        (configuration 0
          (ValidatorHeaderBounds.startLeftBlocks
            stateCount start halt transitionCount) [.done])) :=
    ⟨4, runConfig_entry_to_logicalStart
      stateCount start halt transitionCount []
      (ValidatorHeaderBounds.startLeftBlocks
        stateCount start halt transitionCount)
      (sourceTape_empty_split stateCount start halt transitionCount)⟩
  have hlogical := reaches_encoded_empty_table_from_start
    stateCount start halt transitionCount []
  have hcore := physicallyReaches_of_logicalReaches hlogical
  have hrun := hentry.trans hcore
  have hsource := sourceTape_eq_blockTape
    stateCount start halt transitionCount []
  have hhaltState : Description.halt =
      validatorBlockRootState 101 := rfl
  simpa [validatorPhysicalBlockConfiguration, configuration,
    ValidatorBlockDescription.blockConfiguration,
    validatorPhysicalizeBlockTape_logical, targetTape, hsource, hhaltState,
    ValidatorCountedRows.rowsBlocks]
    using hrun

/-- Every table passing the triangular Boolean check reaches the exact
successful physical endpoint. -/
theorem physicallyReaches_of_upperPairs
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (hupper : transitionUpperPairsBool rows = true) :
    ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := sourceTape stateCount start halt transitionCount rows }
      { state := Description.halt
        tape := targetTape stateCount start halt transitionCount rows } := by
  by_cases hnil : rows = []
  · subst rows
    exact physicallyReaches_emptyTable
      stateCount start halt transitionCount
  · have hsplit := List.dropLast_concat_getLast hnil
    rw [← hsplit] at hupper ⊢
    exact physicallyReaches_nonemptyTable
      stateCount start halt transitionCount
      rows.dropLast (rows.getLast hnil) hupper

/-- Exact-tape forward contract for a compatible transition table. -/
theorem haltsFromTape_of_upperPairs
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (hupper : transitionUpperPairsBool rows = true) :
    Description.HaltsFromTape
      (sourceTape stateCount start halt transitionCount rows)
      (targetTape stateCount start halt transitionCount rows) := by
  rcases physicallyReaches_of_upperPairs
      stateCount start halt transitionCount rows hupper with ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  unfold MachineDescription.HaltsFromTapeIn
  rw [hrun]
  simp

/-- Every canonical determinism-gate source either restores and halts or
reaches a contiguous concrete missing row on a conflicting table. -/
theorem haltsOrContiguousStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (sourceTape stateCount start halt transitionCount rows) output) ∨
    (exists stuck : Tape Bool,
      Description.StuckFromTape
          (sourceTape stateCount start halt transitionCount rows) stuck ∧
        ContiguousTape stuck) := by
  cases hupper : transitionUpperPairsBool rows with
  | true =>
      exact Or.inl ⟨_, haltsFromTape_of_upperPairs
        stateCount start halt transitionCount rows hupper⟩
  | false =>
      exact Or.inr (exists_contiguous_stuckFromTape_of_upperPairs_false
        stateCount start halt transitionCount rows hupper)

/-- Every canonical determinism-gate source either restores and halts or
reaches a concrete missing row on a conflicting table. -/
theorem haltsOrStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (sourceTape stateCount start halt transitionCount rows) output) ∨
    (exists stuck : Tape Bool,
      Description.StuckFromTape
        (sourceTape stateCount start halt transitionCount rows) stuck) := by
  rcases haltsOrContiguousStuckFromTape
      stateCount start halt transitionCount rows with hhalts | hstuck
  · exact Or.inl hhalts
  · rcases hstuck with ⟨stuck, hstuck, _hcontiguous⟩
    exact Or.inr ⟨stuck, hstuck⟩

/-- Any physical halt certifies that every pair of equal transition keys has
the same action. -/
theorem transitionUpperPairsBool_eq_true_of_haltsFromTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    {output : Tape Bool}
    (hhalts : Description.HaltsFromTape
      (sourceTape stateCount start halt transitionCount rows) output) :
    transitionUpperPairsBool rows = true := by
  cases hupper : transitionUpperPairsBool rows with
  | true => rfl
  | false =>
      rcases exists_stuckFromTape_of_upperPairs_false
          stateCount start halt transitionCount rows hupper with
        ⟨_stuck, stuckSteps, stuckState, hstuckRun, hstuckStep,
          hstuckState⟩
      rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalts with
        ⟨steps, hrun⟩
      have hne :=
        CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
          (n := steps) description_subroutineReady.2
          hstuckRun hstuckStep hstuckState
      rw [hrun] at hne
      exact False.elim (hne rfl)

/-- Exact closed contract for the pairwise determinism leaf. -/
theorem haltsFromTape_iff_upperPairs_and_target
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (output : Tape Bool) :
    Description.HaltsFromTape
        (sourceTape stateCount start halt transitionCount rows) output <->
      transitionUpperPairsBool rows = true ∧
        output = targetTape stateCount start halt transitionCount rows := by
  constructor
  · intro hhalts
    have hupper := transitionUpperPairsBool_eq_true_of_haltsFromTape
      stateCount start halt transitionCount rows hhalts
    have hcanonical := haltsFromTape_of_upperPairs
      stateCount start halt transitionCount rows hupper
    exact ⟨hupper,
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        description_subroutineReady.2 hhalts hcanonical⟩
  · rintro ⟨hupper, rfl⟩
    exact haltsFromTape_of_upperPairs
      stateCount start halt transitionCount rows hupper

/-- Existential halting characterization, independent of the exact output
witness selected by a caller. -/
theorem exists_haltsFromTape_iff_upperPairs
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (sourceTape stateCount start halt transitionCount rows) output) <->
      transitionUpperPairsBool rows = true := by
  constructor
  · rintro ⟨output, hhalts⟩
    exact transitionUpperPairsBool_eq_true_of_haltsFromTape
      stateCount start halt transitionCount rows hhalts
  · intro hupper
    exact ⟨targetTape stateCount start halt transitionCount rows,
      haltsFromTape_of_upperPairs
        stateCount start halt transitionCount rows hupper⟩

/-- The physical leaf matches the canonical full nested determinism Boolean
used by description well-formedness. -/
theorem haltsFromTape_iff_fullPairs_and_target
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (output : Tape Bool) :
    Description.HaltsFromTape
        (sourceTape stateCount start halt transitionCount rows) output <->
      rows.all (fun left =>
          rows.all (fun right =>
            transitionDeterministicPairBool left right)) = true ∧
        output = targetTape stateCount start halt transitionCount rows := by
  simpa only [transitionUpperPairsBool_eq_true_iff] using
    haltsFromTape_iff_upperPairs_and_target
      stateCount start halt transitionCount rows output

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
