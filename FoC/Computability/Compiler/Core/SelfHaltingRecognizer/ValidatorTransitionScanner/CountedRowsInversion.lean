import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsPhysical
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowInversion

set_option doc.verso true

/-!
# Exact-code validator: closed counted-row inversion

The constructive logical inversion either returns the declared number of
bounded transition rows or a concrete stuck block state.  This module lifts
the stuck branch through the generated Boolean block machine and its four raw
entry moves.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorCountedRows

open Languages
open MachineDescription

private theorem runConfig_entry_to_inversionSource
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    Description.runConfig 4
        { state := Description.start
          tape := validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens } =
      validatorPhysicalBlockConfiguration
        (configuration 0
          (loopLeftBlocks stateCount start halt 0 transitionCount [])
          (.done :: validatorCanonicalBlocks tokens)) := by
  have hentry := runConfig_entry_to_logicalStart
    stateCount start halt transitionCount [] tokens
  have htape := validatorCountedRowsStartTape_eq_scannerStartTape
    stateCount start halt transitionCount [] tokens
  have hlogical :
      logicalStartConfig stateCount start halt transitionCount [] tokens =
        configuration 0
          (loopLeftBlocks stateCount start halt 0 transitionCount [])
          (.done :: validatorCanonicalBlocks tokens) := by
    unfold logicalStartConfig configuration loopLeftBlocks
    rw [startLeftBlocks_eq_fixedPrefix_append_ticks]
    have hblockStart : blockDescription.start = 0 := rfl
    simp [hblockStart, rowsBlocks]
  rw [htape, hlogical] at hentry
  exact hentry

/-- A logical counted-row rejection witness reaches a concrete contiguous
missing-row endpoint from the public source. -/
theorem exists_contiguous_stuckFromTape_of_stuck
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (witness : ValidatorBlockStuckWitness blockDescription Description
      (configuration 0
        (loopLeftBlocks stateCount start halt 0 transitionCount [])
        (.done :: validatorCanonicalBlocks tokens))) :
    exists stuck : Tape Bool,
      Description.StuckFromTape
          (validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens) stuck ∧
        ContiguousTape stuck := by
  have hphysical :=
    validatorBlockPhysical_exists_contiguous_reachesStuck_of_stuckWitness
    (D := blockDescription) (M := Description)
    (fun _ hrow => compiledRow_mem_description hrow)
    description_subroutineReady.1.2.2.2.2
    blockDescription_sourceBound
    blockDescription_haltFree
    blockDescription_tailCompatible
    witness
  have hentry := runConfig_entry_to_inversionSource
    stateCount start halt transitionCount tokens
  rcases hphysical with ⟨stuck, hstuck, hcontiguous⟩
  exact ⟨stuck,
    MachineDescription.ReachesStuck.prepend hentry hstuck, hcontiguous⟩

/-- A logical counted-row rejection witness reaches a concrete missing
generated Boolean row from the public source. -/
theorem exists_stuckFromTape_of_stuck
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (witness : ValidatorBlockStuckWitness blockDescription Description
      (configuration 0
        (loopLeftBlocks stateCount start halt 0 transitionCount [])
        (.done :: validatorCanonicalBlocks tokens))) :
    exists stuck : Tape Bool,
      Description.StuckFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) stuck := by
  rcases exists_contiguous_stuckFromTape_of_stuck
      stateCount start halt transitionCount tokens witness with
    ⟨stuck, hstuck, _hcontiguous⟩
  exact ⟨stuck, hstuck⟩

/-- A concrete logical rejection witness prevents the complete counted-row
subphase from ever reaching its physical halt state. -/
theorem runConfig_state_ne_halt_of_stuck
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (witness : ValidatorBlockStuckWitness blockDescription Description
      (configuration 0
        (loopLeftBlocks stateCount start halt 0 transitionCount [])
        (.done :: validatorCanonicalBlocks tokens))) :
    forall steps : Nat,
      (Description.runConfig steps
        { state := Description.start
          tape := validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens }).state ≠
        Description.halt := by
  rcases exists_stuckFromTape_of_stuck
      stateCount start halt transitionCount tokens witness with
    ⟨_stuck, stuckSteps, stuckState, hrun, hstep, hstate⟩
  intro steps
  exact
    CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      (n := steps) description_subroutineReady.2 hrun hstep hstate

/-- Any physical halt of the counted-row pass decodes exactly the declared
number of transition rows, all with bounded endpoints. -/
theorem exists_bounded_rows_of_haltsFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    {output : Tape Bool}
    (hhalts : Description.HaltsFromTape
      (validatorTransitionScannerStartTape
        stateCount start halt transitionCount tokens)
      output) :
    exists rows : List TransitionDescription,
    exists suffix : Word MachineCodeSymbol,
      decodeTransitions transitionCount tokens = some (rows, suffix) ∧
        forall row : TransitionDescription,
          row ∈ rows ->
            row.source < stateCount ∧ row.target < stateCount := by
  cases checkedRowsInversion
      stateCount start halt transitionCount tokens with
  | accepted rows suffix hcount htokens hbounds =>
      refine ⟨rows, suffix, ?_, hbounds⟩
      rw [htokens, ← hcount]
      exact decodeTransitions_encodeTransitions_append rows suffix
  | stuck witness =>
      rcases hhalts with ⟨steps, hstate, _htape⟩
      exact False.elim
        ((runConfig_state_ne_halt_of_stuck
          stateCount start halt transitionCount tokens witness steps) hstate)

/-- Every canonical counted-row source either reaches its exact restored
handoff or a contiguous concrete missing generated row. -/
theorem haltsOrContiguousStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) output) ∨
    (exists stuck : Tape Bool,
      Description.StuckFromTape
          (validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens) stuck ∧
        ContiguousTape stuck) := by
  cases checkedRowsInversion
      stateCount start halt transitionCount tokens with
  | accepted rows suffix hcount htokens hbounds =>
      subst tokens
      exact Or.inl ⟨_, haltsFromTape_transitionScannerRows
        stateCount start halt transitionCount rows suffix
        hcount.symm hbounds⟩
  | stuck witness =>
      exact Or.inr (exists_contiguous_stuckFromTape_of_stuck
        stateCount start halt transitionCount tokens witness)

/-- Every canonical counted-row source either reaches its exact restored
handoff or a concrete missing generated row. -/
theorem haltsOrStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) output) ∨
    (exists stuck : Tape Bool,
      Description.StuckFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) stuck) := by
  rcases haltsOrContiguousStuckFromTape
      stateCount start halt transitionCount tokens with hhalts | hstuck
  · exact Or.inl hhalts
  · rcases hstuck with ⟨stuck, hstuck, _hcontiguous⟩
    exact Or.inr ⟨stuck, hstuck⟩

end ValidatorCountedRows
end SelfHaltingRecognizer
end Computability
end FoC
