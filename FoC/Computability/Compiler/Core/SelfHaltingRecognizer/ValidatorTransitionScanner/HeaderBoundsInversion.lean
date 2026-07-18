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
  let witness := leafStuckWitness_of_bounds_false
    stateCount start halt transitionCount tokens hfalse
  have hcore := validatorBlockPhysical_ne_halt_of_leafStuckWitness
    (D := blockDescription) (M := Description)
    (fun _ hrow => compiledRow_mem_description hrow)
    description_subroutineReady.1.2.2.2.2
    description_subroutineReady.2
    blockDescription_sourceBound
    blockDescription_haltFree
    blockDescription_tailCompatible
    witness
  have hentry := runConfig_entry_to_logicalStart
    stateCount start halt transitionCount tokens
  intro steps
  exact
    CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_ne_halt_region
      (n := steps) description_subroutineReady.2 hentry hcore

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

end ValidatorHeaderBounds
end SelfHaltingRecognizer
end Computability
end FoC
