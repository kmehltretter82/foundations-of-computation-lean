import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ConcreteRefresh

set_option doc.verso true

/-!
# Structured construction target adapters

This module records target-specific bridges from three-logical-tape structured
descriptions to the public finite-scaffold construction targets.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists D : CommonGround.FiniteTransducers.Structured.Description,
      D.WellFormed ∧
        D.HaltTransitionFree ∧
          CommonGround.FiniteTransducers.Structured.MultiTapeLowering.SupportsReadWriteRows3
            D ∧
            EncRewriters.RightShiftedOutputCompiledSubroutineByDescription
              (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
                attempt)
              (CommonGround.FiniteTransducers.Structured.MultiTapeLowering.lowerStructured3Description
                D)

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction := by
  intro attempt
  rcases h attempt with ⟨D, _hDwf, _hDhaltFree, _hrows, hcompiled⟩
  exact
    ⟨CommonGround.FiniteTransducers.Structured.MultiTapeLowering.lowerStructured3Description
        D,
      hcompiled⟩

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction := by
  intro attempt
  -- Remaining structured finite-table obligation: give a three-logical-tape
  -- parser description whose lowered machine maps generated `(w, limit, fuel)`
  -- inputs to the canonical simulator-layout code word and halts one cell
  -- right of it.
  sorry

def PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists D : CommonGround.FiniteTransducers.Structured.Description,
        D.WellFormed ∧
          D.HaltTransitionFree ∧
            CommonGround.FiniteTransducers.Structured.MultiTapeLowering.SupportsReadWriteRows3
              D ∧
              CommonGround.ControllerInvocation.StageAttemptFramedRealizes
                attempt
                (CommonGround.FiniteTransducers.Structured.MultiTapeLowering.lowerStructured3Description
                  D)

theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_of_structured
    (h :
      PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData) :
    CommonGround.ControllerInvocation.StageAttemptFramedConstruction := by
  intro attempt hattempt
  rcases h attempt hattempt with
    ⟨D, _hDwf, _hDhaltFree, _hrows, hrealizes⟩
  exact
    ⟨CommonGround.FiniteTransducers.Structured.MultiTapeLowering.lowerStructured3Description
        D,
      hrealizes⟩

theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData_structuredLeaf :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData := by
  intro attempt hattempt
  -- Remaining structured finite-table obligation: give a three-logical-tape
  -- framed invoker whose lowered machine installs the simulated boolean-word
  -- result in the controller layout and is closed over framed outputs.
  sorry

def PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists D : CommonGround.FiniteTransducers.Structured.Description,
      D.WellFormed ∧
        D.HaltTransitionFree ∧
          CommonGround.FiniteTransducers.Structured.MultiTapeLowering.SupportsReadWriteRows3
            D ∧
            TapeCodePrimitiveOutputCompiledSubroutineByDescription
              (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
                attempt)
              (CommonGround.FiniteTransducers.Structured.MultiTapeLowering.lowerStructured3Description
                D)

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction := by
  intro attempt
  rcases h attempt with ⟨D, _hDwf, _hDhaltFree, _hrows, hcompiled⟩
  exact
    ⟨CommonGround.FiniteTransducers.Structured.MultiTapeLowering.lowerStructured3Description
        D,
      hcompiled⟩

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction := by
  intro attempt
  -- Remaining structured finite-table obligation: give a three-logical-tape
  -- extractor whose lowered machine emits the normalized boolean-word result
  -- code on halted simulator layouts and rejects all other inputs.
  sorry

def PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      exists D : CommonGround.FiniteTransducers.Structured.Description,
        D.WellFormed ∧
          D.HaltTransitionFree ∧
            CommonGround.FiniteTransducers.Structured.MultiTapeLowering.SupportsReadWriteRows3
              D ∧
              PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
                runner
                (CommonGround.FiniteTransducers.Structured.MultiTapeLowering.lowerStructured3Description
                  D)

theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction := by
  intro runner hrunner
  rcases h runner hrunner with
    ⟨D, _hDwf, _hDhaltFree, _hrows, hspec⟩
  exact
    ⟨CommonGround.FiniteTransducers.Structured.MultiTapeLowering.lowerStructured3Description
        D,
      hspec⟩

theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction := by
  intro runner hrunner
  -- Remaining structured finite-table obligation: enumerate bounded
  -- `(limit, fuel)` pairs, invoke the exact-fuel runner, preserve its encoded
  -- boolean-word output, and halt one cell right of that output for classifier
  -- handoff.
  sorry

end StructuredConstructionTargets

end Computability
end FoC
