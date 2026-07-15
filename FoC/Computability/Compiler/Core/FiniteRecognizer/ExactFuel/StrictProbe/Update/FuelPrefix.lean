import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Selected-action fuel prefix

Transport the finite fuel-decrement run from the canonical protected frame to
any tape-equivalent representative produced by transition dispatch.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.FuelPrefix

open Languages
open SerializedFieldComposer

/-- Fuel decrement preserves the protected frame up to tape equivalence. -/
theorem run_from_equiv {stateCount : Nat}
    (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel (fuel + 1) L) callerData)) T) :
    exists endpoint,
      FuelDecrementMachine.machine.runConfigExact?
          (FuelDecrementMachine.runSteps fuel L callerData)
          { state := FuelDecrementMachine.machine.start, tape := T } =
        some endpoint ∧
      endpoint.state = FuelDecrementMachine.machine.halt ∧
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (FuelDecrementMachine.withFuel fuel L) callerData))
        endpoint.tape := by
  have hclean := FuelDecrementMachine.run_exact fuel L callerData
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  have hgate := FuelDecrementMachine.endpoint_tape_equiv_input
    fuel L callerData
  refine ⟨endpoint, ?_, ?_, Tape.Equiv.trans (Tape.Equiv.symm hgate) htape⟩
  · simpa [FuelDecrementMachine.startConfig,
      FuelDecrementMachine.config, FuelDecrementMachine.machine] using hrun
  · simpa [FuelDecrementMachine.updateConfig,
      FuelDecrementMachine.config, FuelDecrementMachine.machine,
      DeleteOneRestagedMachine.rewindConfig,
      RewindWord.gateConfig] using hstate

end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.FuelPrefix
