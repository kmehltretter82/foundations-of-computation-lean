import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorInputMaterializer

set_option doc.verso true

/-!
# Fuel-simulator structured-core shapes

Pure source and target decompositions used by the finite three-tape
constructor for sorry 13.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace FuelSimulatorCore

open EncRewriters.CanonicalLayouts.DovetailStagePrefix

/-- The stage-input code before the final fuel field. -/
def stageCode (i : FuelSimulatorStructuredIndex) :
    Word MachineCodeSymbol :=
  DovetailLayout.stageInputCode i.w i.limit

/-- Boolean expansion of the stage-input code. -/
def stageBits (i : FuelSimulatorStructuredIndex) : Word Bool :=
  encodeCodeWordAsInput (stageCode i)

/-- Boolean expansion of the final unary fuel field. -/
def fuelBits (i : FuelSimulatorStructuredIndex) : Word Bool :=
  encodeCodeWordAsInput (encodeNat i.fuel)

theorem inputCode_eq_stageCode_append_fuel
    (i : FuelSimulatorStructuredIndex) :
    fuelSimulatorStructuredInputCode i =
      List.append (stageCode i) (encodeNat i.fuel) := by
  cases i with | mk w limit fuel =>
  rw [fuelSimulatorStructuredInputCode,
    PairedRecognizerDovetailControllerStageAttemptFuelInputCode,
    stageInputCodeAppend_eq_append]
  simp [stageCode, encodeNatAppend]

theorem inputBits_eq_stageBits_append_fuel
    (i : FuelSimulatorStructuredIndex) :
    fuelSimulatorInputBits i =
      List.append (stageBits i) (fuelBits i) := by
  rw [fuelSimulatorInputBits, inputCode_eq_stageCode_append_fuel,
    encodeCodeWordAsInput_append]
  rfl

/-- Every stage-input expansion has a Boolean head cell. -/
theorem stageBits_cons
    (i : FuelSimulatorStructuredIndex) :
    exists b : Bool, exists rest : Word Bool,
      stageBits i = b :: rest := by
  cases i with | mk w limit fuel =>
  cases w with
  | nil =>
      simpa [stageBits, stageCode, DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend, encodeBoolWordAppend,
        encodeCellListAppend, encodeNatAppend, encodeNat,
        encodeCellsAppend] using
        (encodeCodeWordAsInput_cons_head
          MachineCodeSymbol.done (encodeNat limit))
  | cons b rest =>
      simpa [stageBits, stageCode, DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend, encodeBoolWordAppend,
        encodeCellListAppend, encodeNatAppend, encodeNat,
        encodeCellsAppend] using
        (encodeCodeWordAsInput_cons_head MachineCodeSymbol.tick
          (List.append (encodeNat rest.length)
            (encodeCellsAppend (some b :: rest.map some)
              (encodeNat limit))))

/-- Token-level expansion of an initial simulator layout with nonempty input. -/
theorem simulatorInitial_encode_cons
    (attempt : MachineDescription) (fuel : Nat)
    (b : Bool) (rest : Word Bool) :
    SimulatorLayout.encode
        (SimulatorLayout.initial attempt (b :: rest) fuel) =
      MachineCodeSymbol.header ::
        encodeCellListAppend ((b :: rest).map some)
          (encodeNatAppend fuel
            (encodeNatAppend attempt.start
              (encodeCellListAppend []
                (encodeCellAppend (some b)
                  (encodeCellListAppend (rest.map some)
                    (encodeBoolAppend false [])))))) := by
  rfl

/-- Exact token decomposition required on logical tape 2. -/
theorem outputCode_decomp
    (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex)
    (b : Bool) (rest : Word Bool)
    (hx : stageBits i = b :: rest) :
    SimulatorLayout.encode
        (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
          attempt i.w i.limit i.fuel) =
      MachineCodeSymbol.header ::
        encodeCellListAppend ((b :: rest).map some)
          (encodeNatAppend i.fuel
            (encodeNatAppend attempt.start
              (encodeCellListAppend []
                (encodeCellAppend (some b)
                  (encodeCellListAppend (rest.map some)
                    (encodeBoolAppend false [])))))) := by
  rw [PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout,
    show encodeCodeWordAsInput
        (PairedRecognizerDovetailStageInputCode i.w i.limit) =
      b :: rest by
        simpa [PairedRecognizerDovetailStageInputCode, stageBits, stageCode]
          using hx]
  exact simulatorInitial_encode_cons attempt i.fuel b rest

end FuelSimulatorCore
end StructuredConstructionTargets

end Computability
end FoC
