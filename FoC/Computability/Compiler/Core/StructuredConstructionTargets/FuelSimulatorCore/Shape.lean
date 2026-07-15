import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorInputMaterializer

set_option doc.verso true

/-!
# Fuel-simulator structured-core shapes

Pure source and target decompositions used by the finite three-tape
fuel-simulator constructor.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace FuelSimulatorCore

open EncRewriters.CanonicalLayouts.DovetailStagePrefix
open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

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

/-- Uniform Boolean decomposition of the stage prefix. -/
theorem stageBits_eq_length_cells_limit
    (i : FuelSimulatorStructuredIndex) :
    stageBits i =
      List.append (stageNatBits i.w.length)
        (List.append (cellsBits i.w) (stageNatBits i.limit)) := by
  cases i with | mk w limit fuel =>
  change stageInputBits w limit = _
  rw [stageInputBits_eq_false_false_tail,
    stageInputSecondBitTail_eq_prefix_stageNat]
  cases w with
  | nil =>
      simp [stageInputSecondBitTailPrefix]
  | cons bit rest =>
      simp [stageInputSecondBitTailPrefix, List.append_assoc]

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

private theorem encodeNatAppend_input
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput (encodeNatAppend n suffix) =
      List.append (stageNatBits n) (encodeCodeWordAsInput suffix) := by
  rw [show encodeNatAppend n suffix =
      List.append (encodeNatAppend n []) suffix by
    simpa using encodeNatAppend_append n [] suffix]
  rw [encodeCodeWordAsInput_append]
  simp [encodeNatAppend, stageNatBits]

private theorem encodeCellsAppend_input
    (bits : Word Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeCellsAppend (bits.map some) suffix) =
      List.append (cellsBits bits) (encodeCodeWordAsInput suffix) := by
  rw [show encodeCellsAppend (bits.map some) suffix =
      List.append (encodeCellsAppend (bits.map some) []) suffix by
    simpa using encodeCellsAppend_append (bits.map some) [] suffix]
  rw [encodeCodeWordAsInput_append]
  rfl

private theorem encodeCellAppend_input
    (bit : Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput (encodeCellAppend (some bit) suffix) =
      List.append (cellBits bit) (encodeCodeWordAsInput suffix) := by
  rw [show encodeCellAppend (some bit) suffix =
      List.append (encodeCellAppend (some bit) []) suffix by
    simpa using encodeCellAppend_append (some bit) [] suffix]
  rw [encodeCodeWordAsInput_append]
  cases bit <;>
    rfl

/-- Exact Boolean-field decomposition of the simulator-layout output. -/
theorem outputBits_decomp
    (attempt : MachineDescription) (i : FuelSimulatorStructuredIndex)
    (head : Bool) (tail : Word Bool)
    (hx : stageBits i = head :: tail) :
    encodeCodeWordAsInput
        (SimulatorLayout.encode
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt i.w i.limit i.fuel)) =
      List.append [false, false, false, false]
        (List.append (stageNatBits (head :: tail).length)
          (List.append (cellsBits (head :: tail))
            (List.append (stageNatBits i.fuel)
              (List.append (stageNatBits attempt.start)
                (List.append (stageNatBits 0)
                  (List.append (cellBits head)
                    (List.append (stageNatBits tail.length)
                      (List.append (cellsBits tail)
                        (cellBits false))))))))) := by
  rw [outputCode_decomp attempt i head tail hx]
  change List.append [false, false, false, false]
    (encodeCodeWordAsInput _) = _
  simp only [encodeCellListAppend, encodeBoolAppend, encodeCellsAppend,
    List.length_map, List.length_cons, List.length_nil,
    encodeNatAppend_input, encodeCellsAppend_input,
    encodeCellAppend_input]
  rfl

end FuelSimulatorCore
end StructuredConstructionTargets

end Computability
end FoC
