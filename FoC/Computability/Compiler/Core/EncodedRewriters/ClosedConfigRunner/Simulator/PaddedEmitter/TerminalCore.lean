import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.Shape
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedParser
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Padded simulator emitter terminal core

This module names the non-circular terminal/run-loop construction target for
the padded fixed-description simulator emitter.  The downstream terminal,
source-shape, run-loop, and public emitter modules consume this target as
adapter glue.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
    (explicitLeftBlank : Bool) (L : SimulatorLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append
      ((SimulatorLayout.asBoolInput L).reverse.map some)
      (if explicitLeftBlank then [none] else []))
    []

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
    (L : SimulatorLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells [none]
    (List.append ((SimulatorLayout.asBoolInput L).map some) [none])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_eq_FSTSourceTape_configRunner
    (L : SimulatorLayout) :
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner L =
    CommonGround.FiniteTransducers.FSTSourceTape
        (SimulatorLayout.asBoolInput L) 1 := by
  dsimp [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
    CommonGround.FiniteTransducers.FSTSourceTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    CommonGround.FiniteTransducers.tapeAtCells]
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      none :: List.append ((SimulatorLayout.asBoolInput L).map some) [none] := by
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells, hbits]
  | cons bit rest =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      SimulatorLayout.asBoolInput L := by
  rw [Tape.normalizedOutput,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_configRunner]
  simp [Function.comp_def]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_contextLength_configRunner
    (L : SimulatorLayout) :
    Tape.contextLength
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      (SimulatorLayout.asBoolInput L).length + 1 := by
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength,
        hbits]
  | cons bit rest =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength,
        hbits]
      omega

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_contextLength_eq_scratchWidth_configRunner
    (L : SimulatorLayout) :
    Tape.contextLength
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner L + 2 := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_contextLength_configRunner,
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
    FixedDescriptionBoundedSimulatorInput]
  have hlen : 1 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons bit rest =>
      simp [Tape.input, Tape.contextLength]

theorem fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner
    (L : SimulatorLayout) :
    SimulatorLayout.asBoolInput L =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  simp [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_eq_fields_configRunner
    (L : SimulatorLayout) :
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
          [none] := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.right
    (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
      D L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    2 <=
      (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L).length := by
  rw [FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner,
    FixedDescriptionBoundedSimulatorOutput]
  rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
  simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    encodeCodeSymbolAsInput]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_move_left_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.move Direction.left
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
        D L := by
  have hlen :=
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
      D L
  cases houtput :
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner,
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
              ScratchPaddedOutputTape, inputWithTrailingBlankPadding,
              houtput, Tape.move, Tape.moveLeft, Tape.moveRight]

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
    (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.right
    (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
      L)

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindSpec_configRunner
    (rewind : MachineDescription) : Prop :=
  rewind.SubroutineReady ∧
    forall explicitLeftBlank : Bool,
    forall L : SimulatorLayout,
      rewind.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
          explicitLeftBlank L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner :
    Prop :=
  exists rewind : MachineDescription,
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindSpec_configRunner
      rewind

def FixedDescriptionBoundedSimulatorPaddedEmitterBodySpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterBodySpec_configRunner D body

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceSpec_configRunner
    (D afterRight : MachineDescription) : Prop :=
  afterRight.SubroutineReady ∧
    forall L : SimulatorLayout,
      afterRight.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists afterRight : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceSpec_configRunner
        D afterRight

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreSpec_configRunner
    (D post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall explicitLeftBlank : Bool,
    forall L : SimulatorLayout,
      post.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
          explicitLeftBlank L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists post : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreSpec_configRunner
        D post

def FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 1
    , transition 1 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.right 2 ]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_wellFormed_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.transitions)
      (stateCount :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.transitions)
      (by decide)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltTransitionFree_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.transitions)
    (state :=
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.halt)
    (by decide)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner.SubroutineReady :=
  ⟨fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_wellFormed_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltTransitionFree_configRunner⟩

private abbrev FDBSPaddedEmitterTerminalRewind_configRunner :=
  FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_scan_configRunner
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig
        (leftBits.length + 1)
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftBits.map some)
              (some current :: rightCells) } =
      { state := 1
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells []
            (none ::
              List.append
                ((List.append leftBits.reverse [current]).map some)
                rightCells) } := by
  induction leftBits generalizing current rightCells with
  | nil =>
      cases current <;>
        simp [FDBSPaddedEmitterTerminalRewind_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
              { state := 1
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((next :: rest).map some)
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some)
                  (some next :: some current :: rightCells) } := by
        cases current <;>
          simp [FDBSPaddedEmitterTerminalRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_scan_explicitBlank_configRunner
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig
        (leftBits.length + 1)
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (leftBits.map some) [none])
              (some current :: rightCells) } =
      { state := 1
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells []
            (none ::
              List.append
                ((List.append leftBits.reverse [current]).map some)
                rightCells) } := by
  induction leftBits generalizing current rightCells with
  | nil =>
      cases current <;>
        simp [FDBSPaddedEmitterTerminalRewind_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
              { state := 1
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: rightCells) } := by
        cases current <;>
          simp [FDBSPaddedEmitterTerminalRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_step_finish_configRunner
    (bits : Word Bool) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (none :: List.append (bits.map some) [none]) } =
      { state := FDBSPaddedEmitterTerminalRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (bits.map some) [none]) } := by
  cases bits with
  | nil =>
      simp [FDBSPaddedEmitterTerminalRewind_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveRight, Tape.write]
  | cons bit rest =>
      cases bit <;>
        simp [FDBSPaddedEmitterTerminalRewind_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveRight, Tape.write]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_from_leftStack_configRunner
    (leftStack : Word Bool) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig
        (leftStack.length + 2)
        { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftStack.map some) [] } =
      { state := FDBSPaddedEmitterTerminalRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (leftStack.reverse.map some) [none]) } := by
  cases leftStack with
  | nil =>
      simp [FDBSPaddedEmitterTerminalRewind_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstart :
          FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
              { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((current :: rest).map some) [] } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some)
                  (some current :: none :: []) } := by
        cases current <;>
          simp [FDBSPaddedEmitterTerminalRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_scan_configRunner
          rest current [none]]
      simpa [List.map_append, List.append_assoc] using
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_step_finish_configRunner
          (List.append rest.reverse [current])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_from_leftStack_explicitBlank_configRunner
    (leftStack : Word Bool) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig
        (leftStack.length + 2)
        { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (leftStack.map some) [none]) [] } =
      { state := FDBSPaddedEmitterTerminalRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (leftStack.reverse.map some) [none]) } := by
  cases leftStack with
  | nil =>
      simp [FDBSPaddedEmitterTerminalRewind_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstart :
          FDBSPaddedEmitterTerminalRewind_configRunner.runConfig 1
              { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (List.append ((current :: rest).map some) [none]) [] } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (List.append (rest.map some) [none])
                  (some current :: none :: []) } := by
        cases current <;>
          simp [FDBSPaddedEmitterTerminalRewind_configRunner,
            FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_scan_explicitBlank_configRunner
          rest current [none]]
      simpa [List.map_append, List.append_assoc] using
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_step_finish_configRunner
          (List.append rest.reverse [current])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_configRunner
    (explicitLeftBlank : Bool) (bits : Word Bool) :
    FDBSPaddedEmitterTerminalRewind_configRunner.runConfig (bits.length + 2)
        { state := FDBSPaddedEmitterTerminalRewind_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (bits.reverse.map some)
                (if explicitLeftBlank then [none] else [])) [] } =
      { state := FDBSPaddedEmitterTerminalRewind_configRunner.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (bits.map some) [none]) } := by
  cases explicitLeftBlank
  · simpa [List.append_nil] using
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_from_leftStack_configRunner
        bits.reverse
  · simpa [List.map_append] using
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_from_leftStack_explicitBlank_configRunner
        bits.reverse

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltsFromTape_configRunner
    (explicitLeftBlank : Bool) (L : SimulatorLayout) :
    FDBSPaddedEmitterTerminalRewind_configRunner.HaltsFromTape
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
        explicitLeftBlank L)
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L) := by
  refine ⟨(SimulatorLayout.asBoolInput L).length + 2, ?_⟩
  constructor
  · simpa [
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner] using
      congrArg Configuration.state
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_configRunner
          explicitLeftBlank (SimulatorLayout.asBoolInput L))
  · simpa [
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner] using
      congrArg Configuration.tape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_run_configRunner
          explicitLeftBlank (SimulatorLayout.asBoolInput L))

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner :=
  ⟨FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_subroutineReady_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindDescription_haltsFromTape_configRunner⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
            L)) =
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L := by
  have hlen : 1 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          cases first <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFrom_terminalSource_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltsFromTape
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L)
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
        L) := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [hbits] at hlen
      | cons second tail =>
          refine ⟨3, ?_⟩
          constructor
          · cases tail <;> cases first <;> cases second <;>
              simp [
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
                transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight, hbits]
          · cases tail <;> cases first <;> cases second <;>
              simp [
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
                transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_move_left_move_right_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)) =
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
        L := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [hbits] at hlen
      | cons second tail =>
          cases tail <;> cases first <;> cases second <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_of_afterTerminalRightShiftedSource_configRunner
    (hafterRight :
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner := by
  intro D
  rcases hafterRight D with ⟨afterRight, hafterRightD⟩
  refine
    ⟨SeqViaCanonical
      FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
      afterRight, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hafterRightD.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hafterRightD.left
        (fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFrom_terminalSource_configRunner
          L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_move_left_move_right_configRunner
          L)
        (hafterRightD.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner := by
  intro D
  sorry

theorem fixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_of_afterTerminalRightShiftedSource_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_of_rewind_body_configRunner
    (hrewind :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner)
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner := by
  intro D
  rcases hrewind with ⟨rewind, hrewind⟩
  rcases hbody D with ⟨body, hbodyD⟩
  refine ⟨SeqViaCanonical rewind body, ?_⟩
  constructor
  · exact SeqViaCanonical_subroutineReady hrewind.left hbodyD.left
  · intro explicitLeftBlank L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hrewind.left
        hbodyD.left
        (hrewind.right explicitLeftBlank L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L)
        (hbodyD.right L)

/--
Finite-machine leaf for the exact terminal shapes of the padded
fixed-description simulator emitter.

For a fixed description {lean}`D`, this is the place where the restored
simulator layout is parsed, {lean}`D` is run for the encoded stage bound, the
hit bit is updated, and the exact padded scratch output is emitted.
-/
theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_of_rewind_body_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
