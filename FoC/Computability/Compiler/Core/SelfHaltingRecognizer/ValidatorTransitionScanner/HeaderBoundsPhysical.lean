import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockSimulation
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.HeaderBoundsRuns

set_option doc.verso true

/-!
# Exact-code validator: physical header-bound execution

This module applies the local four-bit-block compiler simulation to the full
31-state logical header-bound run.  It then relates the generic physicalized
tapes to the exact block tapes used by the leaf-3 public contract.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

namespace ValidatorHeaderBounds

/-- Every logical header-bound row has an in-range source state. -/
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

/-- No logical header-bound row leaves the designated halt state. -/
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

/-- Header-bound rewrites preserve the three non-leading block bits. -/
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

/-- The generated Boolean core exactly simulates the complete logical pass. -/
theorem physicallyReaches_logicalHeaderBounds
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hpositive : 0 < stateCount)
    (hstart : start < stateCount)
    (hhalt : halt < stateCount) :
    ValidatorBlockPhysicalReaches Description
      (validatorPhysicalBlockConfiguration
        (logicalStartConfig
          stateCount start halt transitionCount tokens))
      (validatorPhysicalBlockConfiguration
        (logicalHandoffConfig
          stateCount start halt transitionCount tokens)) := by
  apply validatorBlockPhysicalReaches_of_logicalReaches
    (D := blockDescription) (M := Description)
  · intro row hrow
    exact compiledRow_mem_description hrow
  · exact description_subroutineReady.1.2.2.2.2
  · exact blockDescription_sourceBound
  · exact blockDescription_haltFree
  · exact blockDescription_tailCompatible
  · exact reaches_logicalHeaderBounds
      stateCount start halt transitionCount tokens
      hpositive hstart hhalt

/-- Exact block-tape form of the generated core run. -/
theorem physicallyReaches_blockHeaderBounds
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hpositive : 0 < stateCount)
    (hstart : start < stateCount)
    (hhalt : halt < stateCount) :
    ValidatorBlockPhysicalReaches Description
      { state := validatorBlockRootState blockDescription.start
        tape := validatorBlockTape
          (startLeftBlocks stateCount start halt transitionCount)
          (.done :: validatorCanonicalBlocks tokens) }
      { state := validatorBlockRootState blockDescription.halt
        tape := validatorBlockTape
          (prefixBlocks stateCount start halt transitionCount)
          (validatorCanonicalBlocks tokens) } := by
  have hrun := physicallyReaches_logicalHeaderBounds
    stateCount start halt transitionCount tokens
    hpositive hstart hhalt
  simpa [validatorPhysicalBlockConfiguration, logicalStartConfig,
    logicalHandoffConfig, validatorPhysicalizeBlockTape_logical]
    using hrun

/-- The complete Boolean header-bound subphase restores its source tape. -/
theorem physicallyReaches_headerBoundsHandoff
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hpositive : 0 < stateCount)
    (hstart : start < stateCount)
    (hhalt : halt < stateCount) :
    ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := validatorHeaderBoundsHandoffTape
          stateCount start halt transitionCount tokens }
      { state := Description.halt
        tape := validatorHeaderBoundsHandoffTape
          stateCount start halt transitionCount tokens } := by
  have hentry : ValidatorBlockPhysicalReaches Description
      { state := Description.start
        tape := validatorHeaderBoundsHandoffTape
          stateCount start halt transitionCount tokens }
      (validatorPhysicalBlockConfiguration
        (logicalStartConfig
          stateCount start halt transitionCount tokens)) :=
    ⟨4, runConfig_entry_to_logicalStart
      stateCount start halt transitionCount tokens⟩
  have hcore := physicallyReaches_logicalHeaderBounds
    stateCount start halt transitionCount tokens
    hpositive hstart hhalt
  have hrun := hentry.trans hcore
  have hhaltState : Description.halt =
      validatorBlockRootState blockDescription.halt := rfl
  simpa [validatorPhysicalBlockConfiguration, logicalHandoffConfig,
    validatorPhysicalizeBlockTape_logical,
    validatorHeaderBoundsHandoffTape_eq_blockTape, hhaltState]
    using hrun

/-- Exact-tape forward contract for the complete header-bound subphase. -/
theorem haltsFromTape_headerBoundsHandoff
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hpositive : 0 < stateCount)
    (hstart : start < stateCount)
    (hhalt : halt < stateCount) :
    Description.HaltsFromTape
      (validatorHeaderBoundsHandoffTape
        stateCount start halt transitionCount tokens)
      (validatorHeaderBoundsHandoffTape
        stateCount start halt transitionCount tokens) := by
  rcases physicallyReaches_headerBoundsHandoff
      stateCount start halt transitionCount tokens
      hpositive hstart hhalt with ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  unfold MachineDescription.HaltsFromTapeIn
  rw [hrun]
  simp

end ValidatorHeaderBounds

end SelfHaltingRecognizer
end Computability
end FoC
