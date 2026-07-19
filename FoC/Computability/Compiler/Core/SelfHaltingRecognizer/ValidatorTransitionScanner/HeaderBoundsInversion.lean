import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.HeaderBoundsPhysical

set_option doc.verso true

/-!
# Exact-code validator: closed header-bound inversion

The logical failure runs identify a concrete missing generated leaf for each
failed bound.  This module transports that evidence through the four-bit block
compiler and across the four raw entry moves.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorHeaderBounds

open Languages
open MachineDescription

/-- A failed header bound reaches a concrete contiguous missing generated
Boolean leaf. -/
theorem exists_contiguous_stuckFromTape_of_bounds_false
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hfalse :
      validatorHeaderBoundsBool stateCount start halt = false) :
    exists stuck : Tape Bool,
      Description.StuckFromTape
          (validatorHeaderBoundsHandoffTape
            stateCount start halt transitionCount tokens) stuck ∧
        ContiguousTape stuck := by
  let witness := leafStuckWitness_of_bounds_false
    stateCount start halt transitionCount tokens hfalse
  have hcore :=
    validatorBlockPhysical_exists_contiguous_reachesStuck_of_stuckWitness
    (D := blockDescription) (M := Description)
    (fun _ hrow => compiledRow_mem_description hrow)
    description_subroutineReady.1.2.2.2.2
    blockDescription_sourceBound
    blockDescription_haltFree
    blockDescription_tailCompatible
    (.leaf witness)
  have hentry := runConfig_entry_to_logicalStart
    stateCount start halt transitionCount tokens
  rcases hcore with ⟨stuck, hstuck, hcontiguous⟩
  exact ⟨stuck,
    MachineDescription.ReachesStuck.prepend hentry hstuck, hcontiguous⟩

/-- A failed header bound reaches a concrete missing generated Boolean leaf. -/
theorem exists_stuckFromTape_of_bounds_false
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hfalse :
      validatorHeaderBoundsBool stateCount start halt = false) :
    exists stuck : Tape Bool,
      Description.StuckFromTape
        (validatorHeaderBoundsHandoffTape
          stateCount start halt transitionCount tokens) stuck := by
  rcases exists_contiguous_stuckFromTape_of_bounds_false
      stateCount start halt transitionCount tokens hfalse with
    ⟨stuck, hstuck, _hcontiguous⟩
  exact ⟨stuck, hstuck⟩

/-- A failed header bound prevents the physical subphase from ever reaching
its halt state. -/
theorem runConfig_state_ne_halt_of_bounds_false
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hfalse :
      validatorHeaderBoundsBool stateCount start halt = false) :
    forall steps : Nat,
      (Description.runConfig steps
        { state := Description.start
          tape := validatorHeaderBoundsHandoffTape
            stateCount start halt transitionCount tokens }).state ≠
        Description.halt := by
  rcases exists_stuckFromTape_of_bounds_false
      stateCount start halt transitionCount tokens hfalse with
    ⟨_stuck, stuckSteps, stuckState, hrun, hstep, hstate⟩
  intro steps
  exact
    CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      (n := steps) description_subroutineReady.2 hrun hstep hstate

/-- Any physical halt of the header-bound pass certifies all three bounds. -/
theorem validatorHeaderBoundsBool_eq_true_of_haltsFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    {output : Tape Bool}
    (hhalts : Description.HaltsFromTape
      (validatorHeaderBoundsHandoffTape
        stateCount start halt transitionCount tokens)
      output) :
    validatorHeaderBoundsBool stateCount start halt = true := by
  cases hvalue : validatorHeaderBoundsBool stateCount start halt with
  | true => rfl
  | false =>
      rcases hhalts with ⟨steps, hstate, _htape⟩
      exact False.elim
        ((runConfig_state_ne_halt_of_bounds_false
          stateCount start halt transitionCount tokens hvalue steps) hstate)

/-- The header-bound machine halts on a canonical header exactly when all three
numeric bounds hold. -/
theorem exists_haltsFromTape_iff_headerBoundsBool
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (validatorHeaderBoundsHandoffTape
          stateCount start halt transitionCount tokens)
        output) <->
      validatorHeaderBoundsBool stateCount start halt = true := by
  constructor
  · rintro ⟨output, hhalts⟩
    exact validatorHeaderBoundsBool_eq_true_of_haltsFromTape
      stateCount start halt transitionCount tokens hhalts
  · intro hbounds
    rw [validatorHeaderBoundsBool_eq_true_iff] at hbounds
    exact ⟨validatorHeaderBoundsHandoffTape
      stateCount start halt transitionCount tokens,
      haltsFromTape_headerBoundsHandoff
        stateCount start halt transitionCount tokens
        hbounds.1 hbounds.2.1 hbounds.2.2⟩

/-- Every canonical header-bound source either restores and halts or reaches a
contiguous concrete missing generated row. -/
theorem haltsOrContiguousStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (validatorHeaderBoundsHandoffTape
          stateCount start halt transitionCount tokens) output) ∨
    (exists stuck : Tape Bool,
      Description.StuckFromTape
          (validatorHeaderBoundsHandoffTape
            stateCount start halt transitionCount tokens) stuck ∧
        ContiguousTape stuck) := by
  cases hvalue : validatorHeaderBoundsBool stateCount start halt with
  | true =>
      exact Or.inl
        ((exists_haltsFromTape_iff_headerBoundsBool
          stateCount start halt transitionCount tokens).2 hvalue)
  | false =>
      exact Or.inr (exists_contiguous_stuckFromTape_of_bounds_false
        stateCount start halt transitionCount tokens hvalue)

/-- Every canonical header-bound source either restores and halts or reaches a
concrete missing generated row. -/
theorem haltsOrStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (validatorHeaderBoundsHandoffTape
          stateCount start halt transitionCount tokens) output) ∨
    (exists stuck : Tape Bool,
      Description.StuckFromTape
        (validatorHeaderBoundsHandoffTape
          stateCount start halt transitionCount tokens) stuck) := by
  rcases haltsOrContiguousStuckFromTape
      stateCount start halt transitionCount tokens with hhalts | hstuck
  · exact Or.inl hhalts
  · rcases hstuck with ⟨stuck, hstuck, _hcontiguous⟩
    exact Or.inr ⟨stuck, hstuck⟩

end ValidatorHeaderBounds
end SelfHaltingRecognizer
end Computability
end FoC
