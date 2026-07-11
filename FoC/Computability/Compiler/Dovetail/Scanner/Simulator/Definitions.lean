import FoC.Computability.Compiler.Dovetail.Scanner.Composition.Definitions

set_option doc.verso true

/-!
# Composed simulator-layout scanner fields

The simulator-layout family
{lit}`header :: boolWord input :: nat stage :: configuration :: hit bool`
is a sub-shape of the dovetail layout with a different lead token.  This
module assembles the existing field scanners into a checked complete-layout
scanner for that family, mirroring the dovetail composition.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace CanonicalLayouts
namespace SimulatorLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.SeqComposition
open DovetailLayoutScanner

/-!
## Header-token remainder scanner

The checked scanner first marks the leading {lit}`false` bit.  The remaining
header-token bits are {lit}`false,false,false`, in contrast to the
transition-token remainder {lit}`false,false,true`.
-/

def headerPrefixBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.header

def headerRemainderBits : Word Bool :=
  [false, false, false]

def HeaderRemainderPrefixScannerDescription : MachineDescription where
  stateCount := 100
  start := 30
  halt := 99
  transitions :=
    [ keepMove 30 (some false) Direction.right 31
    , keepMove 31 (some false) Direction.right 32
    , keepMove 32 (some false) Direction.right 40
    , keepMove 40 (some false) Direction.left 99
    , keepMove 40 (some true) Direction.left 99
    ]

theorem headerRemainderPrefixScannerDescription_wellFormed :
    HeaderRemainderPrefixScannerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := HeaderRemainderPrefixScannerDescription.transitions)
      (stateCount :=
        HeaderRemainderPrefixScannerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := HeaderRemainderPrefixScannerDescription.transitions)
      (by decide)

theorem headerRemainderPrefixScannerDescription_haltTransitionFree :
    HeaderRemainderPrefixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := HeaderRemainderPrefixScannerDescription.transitions)
    (state := HeaderRemainderPrefixScannerDescription.halt)
    (by decide)

theorem headerRemainderPrefixScannerDescription_subroutineReady :
    HeaderRemainderPrefixScannerDescription.SubroutineReady :=
  ⟨headerRemainderPrefixScannerDescription_wellFormed,
    headerRemainderPrefixScannerDescription_haltTransitionFree⟩

def headerRemainderHandoffConfigWithBase
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  { state := HeaderRemainderPrefixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append (headerRemainderBits.reverse.map some)
            baseLeft)
          (suffixBits.map some)) }

def headerRemainderHandoffConfigWithBaseAndRight
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool)
    (rightPadding : List (Option Bool)) : Configuration :=
  { state := HeaderRemainderPrefixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append (headerRemainderBits.reverse.map some)
            baseLeft)
          (List.append (suffixBits.map some) rightPadding)) }

theorem run_headerRemainderPrefix_raw_to_handoff_withBase
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    exists steps : Nat,
      HeaderRemainderPrefixScannerDescription.runConfig steps
          (config 30 baseLeft
            (some false :: some false :: some false ::
              some b :: suffixTail.map some)) =
        headerRemainderHandoffConfigWithBase baseLeft
          (b :: suffixTail) := by
  refine ⟨4, ?_⟩
  cases b <;> cases suffixTail <;>
    simp [HeaderRemainderPrefixScannerDescription,
      headerRemainderHandoffConfigWithBase,
      headerRemainderBits, config, tapeAtCells, keepMove,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem run_headerRemainderPrefix_raw_to_handoff_withBaseAndRight
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    exists steps : Nat,
      HeaderRemainderPrefixScannerDescription.runConfig steps
          (config 30 baseLeft
            (some false :: some false :: some false ::
              some b :: List.append (suffixTail.map some) rightPadding)) =
        headerRemainderHandoffConfigWithBaseAndRight baseLeft
          (b :: suffixTail) rightPadding := by
  refine ⟨4, ?_⟩
  cases b <;>
    simp [HeaderRemainderPrefixScannerDescription,
      headerRemainderHandoffConfigWithBaseAndRight,
      headerRemainderBits, config, tapeAtCells, keepMove,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem headerRemainderHandoffConfigWithBase_move_right
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    Tape.move Direction.right
        (headerRemainderHandoffConfigWithBase baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (List.append (headerRemainderBits.reverse.map some)
          baseLeft)
        ((b :: suffixTail).map some) := by
  unfold headerRemainderHandoffConfigWithBase headerRemainderBits
  simpa [List.append_assoc] using!
    FoC.Computability.CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_cons
      (some false)
      (some false :: some false :: baseLeft)
      (some b) (suffixTail.map some)

theorem headerRemainderHandoffConfigWithBaseAndRight_move_right
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (headerRemainderHandoffConfigWithBaseAndRight baseLeft
          (b :: suffixTail) rightPadding).tape =
      tapeAtCells
        (List.append (headerRemainderBits.reverse.map some)
          baseLeft)
        (List.append ((b :: suffixTail).map some) rightPadding) := by
  unfold headerRemainderHandoffConfigWithBaseAndRight headerRemainderBits
  simpa [List.append_assoc] using!
    FoC.Computability.CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_cons
      (some false)
      (some false :: some false :: baseLeft)
      (some b) (List.append (suffixTail.map some) rightPadding)

/-!
## Composed simulator-layout scanners
-/

def ConfigurationAndFinalFlagScannerDescription : MachineDescription :=
  seqSubroutine
    ConfigurationSuffixScannerDescription
    BoolFinalScannerDescription
    Direction.right

theorem configurationAndFinalFlagScannerDescription_subroutineReady :
    ConfigurationAndFinalFlagScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    configurationSuffixScannerDescription_subroutineReady
    boolFinalScannerDescription_subroutineReady

def StageConfigurationAndFinalFlagScannerDescription :
    MachineDescription :=
  seqSubroutine
    DovetailStagePrefix.NonemptyNatSuffixScannerDescription
    ConfigurationAndFinalFlagScannerDescription
    Direction.right

theorem stageConfigurationAndFinalFlagScannerDescription_subroutineReady :
    StageConfigurationAndFinalFlagScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
    configurationAndFinalFlagScannerDescription_subroutineReady

def InputStageConfigurationAndFinalFlagScannerDescription :
    MachineDescription :=
  seqSubroutine
    BoolWordSuffixScannerDescription
    StageConfigurationAndFinalFlagScannerDescription
    Direction.right

theorem inputStageConfigurationAndFinalFlagScannerDescription_subroutineReady :
    InputStageConfigurationAndFinalFlagScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady
    stageConfigurationAndFinalFlagScannerDescription_subroutineReady

def MarkedSimulatorLayoutBodyScannerDescription : MachineDescription :=
  seqSubroutine
    HeaderRemainderPrefixScannerDescription
    InputStageConfigurationAndFinalFlagScannerDescription
    Direction.right

theorem markedSimulatorLayoutBodyScannerDescription_subroutineReady :
    MarkedSimulatorLayoutBodyScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    headerRemainderPrefixScannerDescription_subroutineReady
    inputStageConfigurationAndFinalFlagScannerDescription_subroutineReady

def CheckedSimulatorLayoutScannerDescription : MachineDescription :=
  seqSubroutine
    MarkFirstTransitionBitDescription
    (seqSubroutine
      MarkedSimulatorLayoutBodyScannerDescription
      ReturnToFirstMarkerDescription
      Direction.right)
    Direction.right

theorem checkedSimulatorLayoutScannerDescription_subroutineReady :
    CheckedSimulatorLayoutScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    markFirstTransitionBitDescription_subroutineReady
    (seqSubroutine_subroutineReady
      markedSimulatorLayoutBodyScannerDescription_subroutineReady
      returnToFirstMarkerDescription_subroutineReady)

/-!
## Simulator-layout field bits
-/

def simulatorLayoutFieldBits
    (L : SimulatorLayout)
    (suffixBits : Word Bool) : Word Bool :=
  List.append headerPrefixBits
    (boolWordFieldBits L.input
      (List.append (stageNatBits L.stage)
        (configurationFieldBits L.config
          (boolFieldBits L.hit suffixBits))))

theorem simulatorLayoutFieldBits_eq_encodeAppend
    (L : SimulatorLayout)
    (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (SimulatorLayout.encodeAppend L suffix) =
      simulatorLayoutFieldBits L
        (encodeCodeWordAsInput suffix) := by
  rw [SimulatorLayout.encodeAppend]
  change
    List.append headerPrefixBits
        (encodeCodeWordAsInput
          (encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit suffix))))) =
      simulatorLayoutFieldBits L
        (encodeCodeWordAsInput suffix)
  rw [boolWordBits_eq_encodeBoolWordAppend]
  rw [DovetailStagePrefix.natBits_eq_encodeNatAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [boolBits_eq_encodeBoolAppend]
  simp [simulatorLayoutFieldBits, boolWordFieldBits,
    cellListFieldBits, boolFieldBits, cellFieldBits]

def markedSimulatorLayoutBodyBits
    (L : SimulatorLayout) : Word Bool :=
  List.append headerRemainderBits
    (boolWordFieldBits L.input
      (List.append (stageNatBits L.stage)
        (configurationFieldBits L.config
          (boolFieldBits L.hit []))))

def markedSimulatorLayoutBodyRestoredBitsRev
    (L : SimulatorLayout) : Word Bool :=
  List.append (cellCodeBits (some L.hit)).reverse
    (List.append (configurationRestoredBitsRev L.config)
      (List.append (stageNatBits L.stage).reverse
        (List.append
          (cellListCanonicalRestoredBitsRev (L.input.map some))
          headerRemainderBits.reverse)))

theorem markedSimulatorLayoutBodyRestoredBitsRev_reverse
    (L : SimulatorLayout) :
    (markedSimulatorLayoutBodyRestoredBitsRev L).reverse =
      markedSimulatorLayoutBodyBits L := by
  simp [markedSimulatorLayoutBodyRestoredBitsRev,
    markedSimulatorLayoutBodyBits, boolWordFieldBits, boolFieldBits,
    cellFieldBits, cellListFieldBits,
    cellListCanonicalRestoredBitsRev_reverse,
    configurationRestoredBitsRev_reverse, List.reverse_append,
    List.append_assoc]
  simp [configurationFieldBits, tapeFieldBits, cellFieldBits,
    cellListFieldBits, List.append_assoc]

theorem markedSimulatorLayoutBodyRestoredBitsRev_map_some_withBase
    (L : SimulatorLayout) (base : List (Option Bool)) :
    List.append ((markedSimulatorLayoutBodyRestoredBitsRev L).map some)
        base =
      List.append ((cellCodeBits (some L.hit)).reverse.map some)
        (configurationRestoredLeftWithBase L.config
          (List.append ((stageNatBits L.stage).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase (L.input.map some)
              (List.append (headerRemainderBits.reverse.map some)
                base)))) := by
  let baseAfterHeader :=
    List.append (headerRemainderBits.reverse.map some) base
  let baseAfterInput :=
    cellListCanonicalRestoredLeftWithBase (L.input.map some)
      baseAfterHeader
  let baseAfterStage :=
    List.append ((stageNatBits L.stage).reverse.map some) baseAfterInput
  have hinput :
      List.append
          ((cellListCanonicalRestoredBitsRev (L.input.map some)).map some)
          baseAfterHeader =
        baseAfterInput := by
    simpa [baseAfterInput] using
      cellListCanonicalRestoredBitsRev_map_some_withBase
        (L.input.map some) baseAfterHeader
  have hconfig :
      List.append ((configurationRestoredBitsRev L.config).map some)
          baseAfterStage =
        configurationRestoredLeftWithBase L.config baseAfterStage :=
    configurationRestoredBitsRev_map_some_withBase
      L.config baseAfterStage
  calc
    List.append ((markedSimulatorLayoutBodyRestoredBitsRev L).map some)
        base =
      List.append ((cellCodeBits (some L.hit)).reverse.map some)
        (List.append
          ((configurationRestoredBitsRev L.config).map some)
          (List.append ((stageNatBits L.stage).reverse.map some)
            (List.append
              ((cellListCanonicalRestoredBitsRev
                (L.input.map some)).map some)
              baseAfterHeader))) := by
          simp [markedSimulatorLayoutBodyRestoredBitsRev,
            baseAfterHeader,
            List.map_append, List.map_reverse, List.append_assoc]
    _ =
      List.append ((cellCodeBits (some L.hit)).reverse.map some)
        (List.append
          ((configurationRestoredBitsRev L.config).map some)
          baseAfterStage) := by
          rw [hinput]
    _ =
      List.append ((cellCodeBits (some L.hit)).reverse.map some)
        (configurationRestoredLeftWithBase L.config baseAfterStage) := by
          rw [hconfig]
    _ =
      List.append ((cellCodeBits (some L.hit)).reverse.map some)
        (configurationRestoredLeftWithBase L.config
          (List.append ((stageNatBits L.stage).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase (L.input.map some)
              (List.append (headerRemainderBits.reverse.map some)
                base)))) := by
          simp [baseAfterStage, baseAfterInput, baseAfterHeader]

theorem simulatorLayoutFieldBits_nil_eq_first_body
    (L : SimulatorLayout) :
    simulatorLayoutFieldBits L [] =
      false :: markedSimulatorLayoutBodyBits L := by
  simp [simulatorLayoutFieldBits, markedSimulatorLayoutBodyBits,
    headerPrefixBits, headerRemainderBits,
    encodeCodeSymbolAsInput]

theorem markedSimulatorLayoutBodyBits_cons_false
    (L : SimulatorLayout) :
    exists tail : Word Bool,
      markedSimulatorLayoutBodyBits L = false :: tail := by
  refine ⟨List.cons false (List.cons false
    (boolWordFieldBits L.input
      (List.append (stageNatBits L.stage)
        (configurationFieldBits L.config
          (boolFieldBits L.hit []))))), ?_⟩
  simp [markedSimulatorLayoutBodyBits, headerRemainderBits]

end SimulatorLayoutScanner
end CanonicalLayouts
end EncRewriters

end Computability
end FoC
