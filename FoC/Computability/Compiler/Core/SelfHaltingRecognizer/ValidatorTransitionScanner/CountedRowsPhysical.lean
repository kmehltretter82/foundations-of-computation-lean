import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsLoopRuns

set_option doc.verso true

/-!
# Exact-code validator: physical counted-row execution

This module lifts the complete counted-row logical run through the generated
Boolean block machine and its four raw entry moves.  Successful executions
restore the complete encoded description and halt at the first suffix token.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

namespace ValidatorCountedRows

/-- The block-level source is the semantic scanner source on encoded rows. -/
theorem validatorCountedRowsStartTape_eq_scannerStartTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    validatorCountedRowsStartTape
        stateCount start halt transitionCount rows suffix =
      validatorTransitionScannerStartTape
        stateCount start halt transitionCount
        (encodeTransitionsAppend rows suffix) := by
  change validatorBlockTape
      (ValidatorHeaderBounds.prefixBlocks
        stateCount start halt transitionCount)
      (List.append (rowsBlocks rows) (validatorCanonicalBlocks suffix)) =
    validatorHeaderBoundsHandoffTape
      stateCount start halt transitionCount
      (encodeTransitionsAppend rows suffix)
  rw [validatorHeaderBoundsHandoffTape_eq_blockTape,
    validatorCanonicalBlocks_encodeTransitionsAppend]

/-- The block-level endpoint is the semantic exact scanner handoff. -/
theorem validatorCountedRowsHandoffTape_eq_scannerHandoffTape
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    validatorCountedRowsHandoffTape
        stateCount start halt transitionCount rows suffix =
      validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount rows suffix := by
  have hrows : validatorCanonicalBlocks (encodeTransitions rows) =
      rowsBlocks rows := by
    simpa [encodeTransitions, validatorCanonicalBlocks] using
      validatorCanonicalBlocks_encodeTransitionsAppend rows []
  have hleft :
      List.append
          (ValidatorHeaderBounds.prefixBlocks
            stateCount start halt transitionCount)
          (rowsBlocks rows) =
        validatorCanonicalBlocks
          (validatorTransitionScannerPrefix
            stateCount start halt transitionCount rows) := by
    unfold validatorTransitionScannerPrefix
    rw [validatorCanonicalBlocks_append,
      ValidatorHeaderBounds.validatorCanonicalBlocks_headerFieldsPrefix,
      hrows]
  unfold validatorCountedRowsHandoffTape
  rw [hleft]
  unfold validatorTransitionScannerHandoffTape validatorBlockTape
  rw [validatorBlockBits_canonical, validatorBlockBits_canonical]

/-- Every counted-row block transition has an in-range logical source. -/
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

/-- The counted-row logical halt has no outgoing block transition. -/
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

/-- Every counted-row block rewrite preserves the three unread block bits. -/
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

/-- The generated Boolean core simulates every bounded counted-row pass. -/
theorem physicallyReaches_logicalCountedRows
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hcount : rows.length = transitionCount)
    (hbounds : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    ValidatorBlockPhysicalReaches Description
      (validatorPhysicalBlockConfiguration
        (logicalStartConfig
          stateCount start halt transitionCount rows suffix))
      (validatorPhysicalBlockConfiguration
        (logicalHandoffConfig
          stateCount start halt transitionCount rows suffix)) := by
  apply validatorBlockPhysicalReaches_of_logicalReaches
    (D := blockDescription) (M := Description)
  · intro row hrow
    exact compiledRow_mem_description hrow
  · exact description_subroutineReady.1.2.2.2.2
  · exact blockDescription_sourceBound
  · exact blockDescription_haltFree
  · exact blockDescription_tailCompatible
  · exact reaches_logical_handoff_of_count
      stateCount start halt transitionCount rows suffix hcount hbounds

/-- Exact block-tape form of the generated counted-row core run. -/
theorem physicallyReaches_blockCountedRows
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hcount : rows.length = transitionCount)
    (hbounds : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    ValidatorBlockPhysicalReaches Description
      { state := validatorBlockRootState blockDescription.start
        tape := validatorBlockTape
          (ValidatorHeaderBounds.startLeftBlocks
            stateCount start halt transitionCount)
          (.done :: List.append (rowsBlocks rows)
            (validatorCanonicalBlocks suffix)) }
      { state := validatorBlockRootState blockDescription.halt
        tape := validatorCountedRowsHandoffTape
          stateCount start halt transitionCount rows suffix } := by
  have hrun := physicallyReaches_logicalCountedRows
    stateCount start halt transitionCount rows suffix hcount hbounds
  simpa [validatorPhysicalBlockConfiguration, logicalStartConfig,
    logicalHandoffConfig, validatorCountedRowsHandoffTape,
    validatorPhysicalizeBlockTape_logical]
    using hrun

/-- The complete counted-row subphase reaches the restored suffix handoff. -/
theorem physicallyReaches_countedRowsHandoff
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hcount : rows.length = transitionCount)
    (hbounds : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := validatorCountedRowsStartTape
          stateCount start halt transitionCount rows suffix }
      { state := Description.halt
        tape := validatorCountedRowsHandoffTape
          stateCount start halt transitionCount rows suffix } := by
  have hentry : ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := validatorCountedRowsStartTape
          stateCount start halt transitionCount rows suffix }
      (validatorPhysicalBlockConfiguration
        (logicalStartConfig
          stateCount start halt transitionCount rows suffix)) :=
    ⟨4, runConfig_entry_to_logicalStart
      stateCount start halt transitionCount rows suffix⟩
  have hcore := physicallyReaches_logicalCountedRows
    stateCount start halt transitionCount rows suffix hcount hbounds
  have hrun := hentry.trans hcore
  have hhaltState : Description.halt =
      validatorBlockRootState blockDescription.halt := rfl
  simpa [validatorPhysicalBlockConfiguration, logicalHandoffConfig,
    validatorCountedRowsHandoffTape,
    validatorPhysicalizeBlockTape_logical, hhaltState]
    using hrun

/-- Exact-tape forward contract for the complete counted-row subphase. -/
theorem haltsFromTape_countedRowsHandoff
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hcount : rows.length = transitionCount)
    (hbounds : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    Description.HaltsFromTape
      (validatorCountedRowsStartTape
        stateCount start halt transitionCount rows suffix)
      (validatorCountedRowsHandoffTape
        stateCount start halt transitionCount rows suffix) := by
  rcases physicallyReaches_countedRowsHandoff
      stateCount start halt transitionCount rows suffix hcount hbounds with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  unfold MachineDescription.HaltsFromTapeIn
  rw [hrun]
  simp

/-- Semantic encoded-row form of the counted scanner's exact forward run. -/
theorem haltsFromTape_transitionScannerRows
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hcount : transitionCount = rows.length)
    (hbounds : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    Description.HaltsFromTape
      (validatorTransitionScannerStartTape
        stateCount start halt transitionCount
        (encodeTransitionsAppend rows suffix))
      (validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount rows suffix) := by
  rw [← validatorCountedRowsStartTape_eq_scannerStartTape,
    ← validatorCountedRowsHandoffTape_eq_scannerHandoffTape]
  exact haltsFromTape_countedRowsHandoff
    stateCount start halt transitionCount rows suffix hcount.symm hbounds

end ValidatorCountedRows

end SelfHaltingRecognizer
end Computability
end FoC
