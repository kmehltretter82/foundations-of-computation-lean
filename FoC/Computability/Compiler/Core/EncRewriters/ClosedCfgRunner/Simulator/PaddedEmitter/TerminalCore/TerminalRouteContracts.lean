import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.PhaseOutputAdapters
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter.TerminalCore.RunConfigEmitter

set_option doc.verso true

/-!
# Terminal padded-emitter route contracts

This module packages the terminal padded-emitter route around the remaining
run-config finite-machine leaf.  The exact post-scan construction still lives
in
{module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter.TerminalCore.RunConfigEmitter`;
the definitions here expose the weaker normalized-output and equivalence
surfaces that downstream simulator composition can use when exact physical tape
position is stronger than the semantic endpoint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

private theorem haltsFromTapeWithOutput_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape h

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

private theorem haltsFromTapeEquiv_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeEquiv Tin Tout :=
  MachineDescription.HaltsFromTape.toEquiv h

/-!
## Normalized-output endpoint facts
-/

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L := by
  rw [Tape.normalizedOutput,
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_cells_eq_outputBits_configRunner]
  simp [Function.comp_def]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_fieldOutputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_normalizedOutput_eq_outputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L := by
  rw [Tape.normalizedOutput,
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_cells_eq_outputBits_configRunner]
  simp [Function.comp_def]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_normalizedOutput_eq_fieldOutputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_normalizedOutput_eq_outputBits_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_normalizedOutput_eq_asBoolInput_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
      SimulatorLayout.asBoolInput L := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_normalizedOutput_eq_fieldSourceBits_configRunner]
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_normalizedOutput_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_normalizedOutput_eq_asBoolInput_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetTape_normalizedOutput_eq_outputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)) =
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L := by
  rw [CommonGround.FiniteTransducers.FSTTargetTape_normalizedOutput]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetTape_normalizedOutput_eq_fieldOutputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetTape_normalizedOutput_eq_outputBits_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner]

/-!
## Output-level terminal specs
-/

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputSpec_configRunner
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall L : SimulatorLayout,
      scanner.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (SimulatorLayout.asBoolInput L)

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_configRunner
    (D postScan : MachineDescription) : Prop :=
  postScan.SubroutineReady ∧
    forall L : SimulatorLayout,
      postScan.HaltsFromTapeWithOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeWithOutput
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1)
        (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeWithOutput
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceOutputSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceOutputSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceOutputSpec_configRunner
    (D afterRight : MachineDescription) : Prop :=
  afterRight.SubroutineReady ∧
    forall L : SimulatorLayout,
      afterRight.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterBodyOutputSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreOutputSpec_configRunner
    (D post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall explicitLeftBlank : Bool,
    forall L : SimulatorLayout,
      post.HaltsFromTapeWithOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
          explicitLeftBlank L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputConstruction_configRunner :
    Prop :=
  exists scanner : MachineDescription,
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputSpec_configRunner
      scanner

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists postScan : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_configRunner
        D postScan

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceOutputSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceOutputSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists afterRight : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceOutputSpec_configRunner
        D afterRight

def FixedDescriptionBoundedSimulatorPaddedEmitterBodyOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterBodyOutputSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreOutputConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists post : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreOutputSpec_configRunner
        D post

/-!
## Exact-to-output adapters
-/

theorem FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputSpec_of_exact_configRunner
    {scanner : MachineDescription}
    (hscanner :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftSpec_configRunner
        scanner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputSpec_configRunner
      scanner := by
  refine ⟨hscanner.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_normalizedOutput_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hscanner.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_of_exact_configRunner
    {D postScan : MachineDescription}
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchSpec_configRunner
        D postScan) :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_configRunner
      D postScan := by
  refine ⟨hpost.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hpost.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
    {D rightBody : MachineDescription}
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
      D rightBody := by
  refine ⟨hright.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hright.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_normalizedOutput_eq_fieldOutputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
    {D rightBody : MachineDescription}
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputSpec_configRunner
      D rightBody := by
  refine ⟨hright.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_normalizedOutput_eq_fieldOutputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hright.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_normalizedOutput_eq_fieldOutputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceOutputSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
    {D rightBody : MachineDescription}
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceOutputSpec_configRunner
      D rightBody := by
  refine ⟨hright.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hright.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
    {D afterRight : MachineDescription}
    (hafter :
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceSpec_configRunner
        D afterRight) :
    FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceOutputSpec_configRunner
      D afterRight := by
  refine ⟨hafter.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hafter.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterBodyOutputSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterBodySpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterBodyOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreOutputSpec_of_exact_configRunner
    {D post : MachineDescription}
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreSpec_configRunner
        D post) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreOutputSpec_configRunner
      D post := by
  refine ⟨hpost.left, ?_⟩
  intro explicitLeftBlank L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hpost.right explicitLeftBlank L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputConstruction_of_exact_configRunner
    (hscanner :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputConstruction_configRunner := by
  rcases hscanner with ⟨scanner, hspec⟩
  exact
    ⟨scanner,
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputConstruction_of_exact_configRunner
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputConstruction_configRunner := by
  intro D
  rcases hpost D with ⟨postScan, hspec⟩
  exact
    ⟨postScan,
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_of_exact_configRunner
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_configRunner := by
  intro D
  rcases hbody D with ⟨body, hspec⟩
  exact
    ⟨body,
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputConstruction_of_exact_configRunner
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputConstruction_configRunner := by
  intro D
  rcases hbody D with ⟨body, hspec⟩
  exact
    ⟨body,
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputConstruction_of_exact_configRunner
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputConstruction_configRunner := by
  intro D
  rcases hright D with ⟨rightBody, hspec⟩
  exact
    ⟨rightBody,
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_of_exact_configRunner
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_configRunner := by
  intro D
  rcases hbody D with ⟨body, hspec⟩
  exact
    ⟨body,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputConstruction_of_exact_configRunner
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputConstruction_configRunner := by
  intro D
  rcases hright D with ⟨rightBody, hspec⟩
  exact
    ⟨rightBody,
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputConstruction_of_exact_configRunner
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputConstruction_configRunner := by
  intro D
  rcases hbody D with ⟨body, hspec⟩
  exact
    ⟨body,
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputConstruction_of_exact_configRunner
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputConstruction_configRunner := by
  intro D
  rcases hbody D with ⟨body, hspec⟩
  exact
    ⟨body,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceOutputConstruction_of_exact_configRunner
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceOutputConstruction_configRunner := by
  intro D
  rcases hbody D with ⟨body, hspec⟩
  exact
    ⟨body,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceOutputConstruction_of_exact_configRunner
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceOutputConstruction_configRunner := by
  intro D
  rcases hright D with ⟨rightBody, hspec⟩
  exact
    ⟨rightBody,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceOutputConstruction_of_exact_configRunner
    (hafter :
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceOutputConstruction_configRunner := by
  intro D
  rcases hafter D with ⟨afterRight, hspec⟩
  exact
    ⟨afterRight,
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterBodyOutputConstruction_of_exact_configRunner
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterBodyOutputConstruction_configRunner := by
  intro D
  rcases hbody D with ⟨body, hspec⟩
  exact
    ⟨body,
      FixedDescriptionBoundedSimulatorPaddedEmitterBodyOutputSpec_of_exact_configRunner
        hspec⟩

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreOutputConstruction_of_exact_configRunner
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreOutputConstruction_configRunner := by
  intro D
  rcases hpost D with ⟨post, hspec⟩
  exact
    ⟨post,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreOutputSpec_of_exact_configRunner
        hspec⟩

/-!
## Output-level route composition
-/

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_of_rightEndLeftOutput_configRunner
    {D scanner postScan : MachineDescription}
    (hscanner :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftSpec_configRunner
        scanner)
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_configRunner
        D postScan) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_configRunner
      D (SeqViaCanonical scanner postScan) := by
  constructor
  · exact SeqViaCanonical_subroutineReady hscanner.left hpost.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        hscanner.left
        hpost.left
        (hscanner.right L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_move_left_move_right_configRunner
          L)
        (hpost.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_of_rightEndLeftOutput_configRunner
    (hscanner :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_configRunner)
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_configRunner := by
  rcases hscanner with ⟨scanner, hscannerSpec⟩
  intro D
  rcases hpost D with ⟨postScan, hpostSpec⟩
  exact
    ⟨SeqViaCanonical scanner postScan,
      fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_of_rightEndLeftOutput_configRunner
        hscannerSpec hpostSpec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_of_sourceOutput_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
      D
        (SeqViaCanonical
          CommonGround.FiniteTransducers.leftMoveOnceDescription
          body) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        CommonGround.FiniteTransducers.leftMoveOnceDescription_subroutineReady
        hbody.left
  · intro L
    have hleft :
        CommonGround.FiniteTransducers.leftMoveOnceDescription.HaltsFromTape
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
            L) := by
      simpa [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L] using
        CommonGround.FiniteTransducers.leftMoveOnceDescription_haltsFromTape
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        CommonGround.FiniteTransducers.leftMoveOnceDescription_subroutineReady
        hbody.left
        hleft
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L)
        (hbody.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputConstruction_of_sourceOutput_configRunner
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputConstruction_configRunner := by
  intro D
  rcases hbody D with ⟨body, hbodySpec⟩
  exact
    ⟨SeqViaCanonical
        CommonGround.FiniteTransducers.leftMoveOnceDescription
        body,
      fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_of_sourceOutput_configRunner
        hbodySpec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_of_rightShiftedFieldsOutput_configRunner
    {D rightBody : MachineDescription}
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputSpec_configRunner
        D rightBody) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_configRunner
      D
        (SeqViaCanonical
          FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
          rightBody) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hright.left
  · intro L
    have hreturn :
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltsFromTape
          (CommonGround.FiniteTransducers.FSTSourceTape
            (SimulatorLayout.asBoolInput L) 1)
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L) := by
      simpa [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_eq_FSTSourceTape_configRunner
          L] using
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFrom_terminalSource_configRunner
          L
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hright.left
        hreturn
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_move_left_move_right_configRunner
          L)
        (hright.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_of_rightShiftedFieldsOutput_configRunner
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceOutputConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_configRunner := by
  intro D
  rcases hright D with ⟨rightBody, hrightSpec⟩
  exact
    ⟨SeqViaCanonical
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
        rightBody,
      fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_of_rightShiftedFieldsOutput_configRunner
        hrightSpec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_of_fieldsOutput_configRunner
    {D body : MachineDescription}
    (hfields :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_configRunner
      D body := by
  refine ⟨hfields.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner]
    using hfields.right L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputConstruction_of_fieldsOutput_configRunner
    (hfields :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputConstruction_configRunner := by
  intro D
  rcases hfields D with ⟨body, hbody⟩
  exact
    ⟨body,
      fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_of_fieldsOutput_configRunner
        hbody⟩

/-!
## Equivalence endpoint specs
-/

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_configRunner
    (D postScan : MachineDescription) : Prop :=
  postScan.SubroutineReady ∧
    forall L : SimulatorLayout,
      postScan.HaltsFromTapeEquiv
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceEquivSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeEquiv
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceEquivSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeEquiv
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceEquivSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTapeEquiv
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetEquivSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeEquiv
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetEquivSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeEquiv
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists postScan : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_configRunner
        D postScan

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceEquivSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceEquivSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceEquivSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetEquivSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetEquivSpec_configRunner
        D body

theorem FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_of_exact_configRunner
    {D postScan : MachineDescription}
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchSpec_configRunner
        D postScan) :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_configRunner
      D postScan := by
  refine ⟨hpost.left, ?_⟩
  intro L
  exact haltsFromTapeEquiv_of_haltsFromTape_target (hpost.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceEquivSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceEquivSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  exact haltsFromTapeEquiv_of_haltsFromTape_target (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceEquivSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceEquivSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  exact haltsFromTapeEquiv_of_haltsFromTape_target (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceEquivSpec_of_exact_configRunner
    {D rightBody : MachineDescription}
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceEquivSpec_configRunner
      D rightBody := by
  refine ⟨hright.left, ?_⟩
  intro L
  exact haltsFromTapeEquiv_of_haltsFromTape_target (hright.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetEquivSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetEquivSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  exact haltsFromTapeEquiv_of_haltsFromTape_target (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetEquivSpec_of_exact_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetEquivSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  exact haltsFromTapeEquiv_of_haltsFromTape_target (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_of_equiv_configRunner
    {D postScan : MachineDescription}
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_configRunner
        D postScan) :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_configRunner
      D postScan := by
  refine ⟨hpost.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hpost.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_of_equiv_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceEquivSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_of_equiv_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceEquivSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputSpec_of_equiv_configRunner
    {D rightBody : MachineDescription}
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceEquivSpec_configRunner
        D rightBody) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceOutputSpec_configRunner
      D rightBody := by
  refine ⟨hright.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hright.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_of_equiv_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetEquivSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_normalizedOutput_eq_fieldOutputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hbody.right L)

theorem FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_of_equiv_configRunner
    {D body : MachineDescription}
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetEquivSpec_configRunner
        D body) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputSpec_configRunner
      D body := by
  refine ⟨hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetTape_normalizedOutput_eq_outputBits_configRunner]
    using
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hbody.right L)

/-!
## Endpoint shape bundle
-/

structure FixedDescriptionBoundedSimulatorPaddedEmitterTerminalEndpointShape_configRunner
    (D : MachineDescription) (L : SimulatorLayout) : Prop where
  terminalSourceEqFSTSource :
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L =
      CommonGround.FiniteTransducers.FSTSourceTape
        (SimulatorLayout.asBoolInput L) 1
  terminalSourceCells :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      none :: List.append ((SimulatorLayout.asBoolInput L).map some) [none]
  terminalSourceCellsEqFields :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend L.input
                (encodeNatAppend L.stage
                  (encodeConfigurationAppend L.config
                    (encodeBoolAppend L.hit []))))).map some)
          [none]
  terminalSourceNormalizedOutput :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      SimulatorLayout.asBoolInput L
  terminalSourceNormalizedOutputEqFields :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit []))))
  terminalSourceContextLength :
    Tape.contextLength
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      (SimulatorLayout.asBoolInput L).length + 1
  terminalSourceContextLengthEqScratchWidth :
    Tape.contextLength
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
        L + 2
  terminalRightShiftedCells :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L) =
      none :: List.append ((SimulatorLayout.asBoolInput L).map some) [none]
  terminalRightShiftedCellsEqFields :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend L.input
                (encodeNatAppend L.stage
                  (encodeConfigurationAppend L.config
                    (encodeBoolAppend L.hit []))))).map some)
          [none]
  terminalRightShiftedNormalizedOutput :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L) =
      SimulatorLayout.asBoolInput L
  terminalRightShiftedContextLength :
    Tape.contextLength
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L) =
      (SimulatorLayout.asBoolInput L).length + 1
  terminalRightShiftedExistsConsCons :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      SimulatorLayout.asBoolInput L = first :: second :: rest ∧
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L =
          DovetailInitialLayoutInitializer.tapeAtCells
            [some first, none]
            (some second :: List.append (rest.map some) [none])
  terminalRightEndLeftCells :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L) =
      none :: List.append ((SimulatorLayout.asBoolInput L).map some) [none]
  terminalRightEndLeftCellsEqFields :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend L.input
                (encodeNatAppend L.stage
                  (encodeConfigurationAppend L.config
                    (encodeBoolAppend L.hit []))))).map some)
          [none]
  terminalRightEndLeftNormalizedOutput :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
          L) =
      SimulatorLayout.asBoolInput L
  terminalRightEndLeftMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
            L)) =
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_configRunner
        L
  fstSourceCellsEqFieldSourceCells :
    Tape.cells
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTSourceCells_configRunner
        L
  fstSourceCellsEqFields :
    Tape.cells
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend L.input
                (encodeNatAppend L.stage
                  (encodeConfigurationAppend L.config
                    (encodeBoolAppend L.hit []))))).map some)
          [none]
  fstSourceNormalizedOutputEqSourceBits :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldSourceBits_configRunner
        L
  fstSourceNormalizedOutputEqFields :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit []))))
  fieldOutputBitsEqOutputBits :
    FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L
  fieldTargetCells :
    Tape.cells
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetCells_configRunner
        D L
  fieldTargetCellsEqFields :
    Tape.cells
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend L.input
              (encodeNatAppend L.stage
                (encodeConfigurationAppend
                  (D.runConfig L.stage L.config)
                  (encodeBoolAppend
                    (L.hit ||
                      SimulatorLayout.hitsFromConfigByBool
                        D L.config L.stage)
                    []))))).map some)
        (List.replicate
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)
          none)
  fieldTargetNormalizedOutput :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L
  rightScratchEqFSTTarget :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
        D L =
      CommonGround.FiniteTransducers.FSTTargetTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          L)
  rightScratchMoveLeft :
    Tape.move Direction.left
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
        D L
  rightScratchCellsEqOutputBits :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      List.append
        ((FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L).map some)
        (List.replicate
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none)
  rightScratchCellsEqFields :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend L.input
              (encodeNatAppend L.stage
                (encodeConfigurationAppend
                  (D.runConfig L.stage L.config)
                  (encodeBoolAppend
                    (L.hit ||
                      SimulatorLayout.hitsFromConfigByBool
                        D L.config L.stage)
                    []))))).map some)
        (List.replicate
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none)
  rightScratchNormalizedOutput :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L
  rightScratchNormalizedOutputEqFields :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L
  rightScratchExistsConsCons :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L =
        first :: second :: rest ∧
        FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
            D L =
          DovetailInitialLayoutInitializer.tapeAtCells [some first]
            (some second :: List.append (rest.map some)
              (List.replicate
                (Tape.contextLength
                  (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
                none))
  scratchCellsEqOutputBits :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      List.append
        ((FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L).map some)
        (List.replicate
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none)
  scratchCellsEqFields :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend L.input
              (encodeNatAppend L.stage
                (encodeConfigurationAppend
                  (D.runConfig L.stage L.config)
                  (encodeBoolAppend
                    (L.hit ||
                      SimulatorLayout.hitsFromConfigByBool
                        D L.config L.stage)
                    []))))).map some)
        (List.replicate
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none)
  scratchNormalizedOutput :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L
  scratchNormalizedOutputEqFields :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L
  scratchExistsCons :
    exists first : Bool,
    exists rest : Word Bool,
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L =
        first :: rest ∧
        FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
            D L =
          DovetailInitialLayoutInitializer.tapeAtCells []
            (some first :: List.append (rest.map some)
              (List.replicate
                (Tape.contextLength
                  (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
                none))
  outputBitsLengthGeTwo :
    2 <=
      (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L).length
  simulatorOutputLengthGeHeader :
    4 <= (FixedDescriptionBoundedSimulatorOutput D L).length

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalEndpointShape_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalEndpointShape_configRunner
      D L :=
  { terminalSourceEqFSTSource :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_eq_FSTSourceTape_configRunner
        L
    terminalSourceCells :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_configRunner
        L
    terminalSourceCellsEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_eq_fields_configRunner
        L
    terminalSourceNormalizedOutput :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_configRunner
        L
    terminalSourceNormalizedOutputEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_eq_fields_configRunner
        L
    terminalSourceContextLength :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_contextLength_configRunner
        L
    terminalSourceContextLengthEqScratchWidth :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_contextLength_eq_scratchWidth_configRunner
        L
    terminalRightShiftedCells :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_cells_configRunner
        L
    terminalRightShiftedCellsEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_cells_eq_fields_configRunner
        L
    terminalRightShiftedNormalizedOutput :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_normalizedOutput_configRunner
        L
    terminalRightShiftedContextLength :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_contextLength_configRunner
        L
    terminalRightShiftedExistsConsCons :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_exists_tapeAtCells_cons_cons_configRunner
        L
    terminalRightEndLeftCells :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_cells_configRunner
        L
    terminalRightEndLeftCellsEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_cells_eq_fields_configRunner
        L
    terminalRightEndLeftNormalizedOutput :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_normalizedOutput_configRunner
        L
    terminalRightEndLeftMoveLeftMoveRight :=
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_move_left_move_right_configRunner
        L
    fstSourceCellsEqFieldSourceCells :=
      fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_cells_eq_fieldSourceCells_configRunner
        L
    fstSourceCellsEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_cells_eq_fields_configRunner
        L
    fstSourceNormalizedOutputEqSourceBits :=
      fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_normalizedOutput_eq_fieldSourceBits_configRunner
        L
    fstSourceNormalizedOutputEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_normalizedOutput_eq_fields_configRunner
        L
    fieldOutputBitsEqOutputBits :=
      fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner
        D L
    fieldTargetCells :=
      fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_cells_eq_fieldTargetCells_configRunner
        D L
    fieldTargetCellsEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_cells_eq_fields_configRunner
        D L
    fieldTargetNormalizedOutput :=
      fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_normalizedOutput_eq_fieldOutputBits_configRunner
        D L
    rightScratchEqFSTTarget :=
      fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_eq_FSTTargetTape_configRunner
        D L
    rightScratchMoveLeft :=
      fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_move_left_configRunner
        D L
    rightScratchCellsEqOutputBits :=
      fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_cells_eq_outputBits_configRunner
        D L
    rightScratchCellsEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_cells_eq_fields_configRunner
        D L
    rightScratchNormalizedOutput :=
      fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_normalizedOutput_eq_outputBits_configRunner
        D L
    rightScratchNormalizedOutputEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_normalizedOutput_eq_fieldOutputBits_configRunner
        D L
    rightScratchExistsConsCons :=
      fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_eq_tapeAtCells_cons_cons_configRunner
        D L
    scratchCellsEqOutputBits :=
      fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_cells_eq_outputBits_configRunner
        D L
    scratchCellsEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_cells_eq_fields_configRunner
        D L
    scratchNormalizedOutput :=
      fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_outputBits_configRunner
        D L
    scratchNormalizedOutputEqFields :=
      fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_eq_fieldOutputBits_configRunner
        D L
    scratchExistsCons :=
      fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_tapeAtCells_cons_configRunner
        D L
    outputBitsLengthGeTwo :=
      fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
        D L
    simulatorOutputLengthGeHeader :=
      fixedDescriptionBoundedSimulatorOutput_length_ge_header_configRunner
        D L }

/-!
## Route bundles
-/

structure FixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteSpec_configRunner
    (D scanner postScan : MachineDescription) : Prop where
  scannerExact :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftSpec_configRunner
      scanner
  postExact :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchSpec_configRunner
      D postScan
  scannerOutput :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputSpec_configRunner
      scanner
  postOutput :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_configRunner
      D postScan
  postEquiv :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_configRunner
      D postScan
  sourceRouteOutput :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_configRunner
      D (SeqViaCanonical scanner postScan)
  sourceRouteEquiv :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceEquivSpec_configRunner
      D (SeqViaCanonical scanner postScan)
  endpointShape :
    forall L : SimulatorLayout,
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalEndpointShape_configRunner
        D L

def FixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists scanner : MachineDescription,
    exists postScan : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteSpec_configRunner
        D scanner postScan

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteSpec_of_exact_configRunner
    {D scanner postScan : MachineDescription}
    (hscanner :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftSpec_configRunner
        scanner)
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchSpec_configRunner
        D postScan) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteSpec_configRunner
      D scanner postScan := by
  let sourceBody := SeqViaCanonical scanner postScan
  have hsourceExact :
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceSpec_configRunner
        D sourceBody := by
    constructor
    · exact SeqViaCanonical_subroutineReady hscanner.left hpost.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          hscanner.left
          hpost.left
          (hscanner.right L)
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightEndLeftTape_move_left_move_right_configRunner
            L)
          (hpost.right L)
  exact
    { scannerExact := hscanner
      postExact := hpost
      scannerOutput :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftOutputSpec_of_exact_configRunner
          hscanner
      postOutput :=
        FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputSpec_of_exact_configRunner
          hpost
      postEquiv :=
        FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchEquivSpec_of_exact_configRunner
          hpost
      sourceRouteOutput :=
        FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputSpec_of_exact_configRunner
          hsourceExact
      sourceRouteEquiv :=
        FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceEquivSpec_of_exact_configRunner
          hsourceExact
      endpointShape :=
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalEndpointShape_configRunner
          D }

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteConstruction_of_exact_configRunner
    (hscanner :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_configRunner)
    (hpost :
      FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteConstruction_configRunner := by
  rcases hscanner with ⟨scanner, hscannerSpec⟩
  intro D
  rcases hpost D with ⟨postScan, hpostSpec⟩
  exact
    ⟨scanner, postScan,
      fixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteSpec_of_exact_configRunner
        hscannerSpec hpostSpec⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterRightEndLeftRouteConstruction_of_exact_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_core_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_core_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputConstruction_of_exact_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchConstruction_core_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_of_rightEndLeftOutput_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceToRightEndLeftConstruction_core_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterPostRightEndLeftToScratchOutputConstruction_core_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalRightShiftedSourceOutputConstruction_of_sourceOutput_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchFromTerminalSourceOutputConstruction_core_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_of_exact_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_core_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceOutputConstruction_of_exact_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetOutputConstruction_of_fieldsOutput_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetOutputConstruction_core_configRunner

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
