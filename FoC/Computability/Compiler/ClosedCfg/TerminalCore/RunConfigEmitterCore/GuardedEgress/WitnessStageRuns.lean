import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessStage

set_option doc.verso true

/-!
# Other-branch execution of the guarded metadata-witness normalizer

This module proves the raw-state-preserving {lit}`other` branch of the
metadata-witness normalizer.  The small scan and fixed-step lemmas are also
available to the sibling known-witness execution proof.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessStage

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open MetadataWitnessBridge MetadataWitnessBridgeLocate MetadataTokenCopy

namespace Normalizer

theorem rawMetadataTokens_ne_nil (i : Index) :
    rawMetadataTokens i ≠ [] := by
  simp [rawMetadataTokens, MetadataWitnessBridge.boolWordTokens,
    natTokens_eq_ticks_done]

theorem physicalRawBits_ne_nil (i : Index) :
    physicalTokenBits (rawMetadataTokens i) ≠ [] := by
  intro hnil
  have hencoded :=
    encodedTokens_eq_map_physicalTokenBits (rawMetadataTokens i)
  rw [hnil] at hencoded
  have hlength :=
    MetadataTokenCopy.encodedTokens_length (rawMetadataTokens i)
  rw [hencoded] at hlength
  simp at hlength
  apply rawMetadataTokens_ne_nil i
  apply List.eq_nil_of_length_eq_zero
  lia

theorem exactTapeFieldBits_ne_nil (i : Index) :
    LengthAssembly.exactTapeFieldBits i.finalTape [] ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [LengthAssembly.exactTapeFieldBits,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length]
    at hlength

theorem step_otherSeekRaw_present
    (hit bit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := otherSeekRawState hit
          tape := tapeAtCells (cell :: left) (some bit :: right) } =
      { state := otherScanRawLeftState hit
        tape := tapeAtCells left (cell :: some bit :: right) } := by
  cases hit <;> cases bit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_otherScanRawLeft_none
    (hit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := otherScanRawLeftState hit
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := seekExactState false hit
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases hit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_seekExact_present
    (known hit bit : Bool) (cell next : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := seekExactState known hit
          tape := tapeAtCells (cell :: left) (some bit :: next :: right) } =
      { state := writeZeroState known hit
        tape := tapeAtCells (some bit :: cell :: left) (next :: right) } := by
  cases known <;> cases hit <;> cases bit <;> cases cell <;> cases next <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_seekExact_present_any
    (known hit bit : Bool) (left : List (Option Bool))
    (next : Option Bool) (right : List (Option Bool)) :
    description.runConfig 1
        { state := seekExactState known hit
          tape := tapeAtCells left (some bit :: next :: right) } =
      { state := writeZeroState known hit
        tape := tapeAtCells (some bit :: left) (next :: right) } := by
  cases known <;> cases hit <;> cases bit <;> cases next <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem run_writeHitField
    (known hit : Bool) (left : List (Option Bool))
    (boundary : Option Bool) (right : List (Option Bool)) :
    description.runConfig 4
        { state := writeZeroState known hit
          tape := tapeAtCells left
            (none :: none :: none :: none :: boundary :: right) } =
      { state := scanGapState known
        tape := tapeAtCells
          (some (!hit) :: some hit :: some true :: some false :: left)
          (boundary :: right) } := by
  cases known <;> cases hit <;> cases boundary <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem run_seekExact_writeHit
    (hit exactLast : Bool) (left : List (Option Bool))
    (boundary : Option Bool) (right : List (Option Bool)) :
    description.runConfig (1 + 4)
        { state := seekExactState false hit
          tape := tapeAtCells left
            (some exactLast ::
              none :: none :: none :: none :: boundary :: right) } =
      { state := scanGapState false
        tape := tapeAtCells
          (some (!hit) :: some hit :: some true :: some false ::
            some exactLast :: left)
          (boundary :: right) } := by
  rw [MachineDescription.runConfig_add]
  rw [step_seekExact_present_any]
  exact run_writeHitField false hit (some exactLast :: left)
    boundary right

theorem step_scanGap_marker
    (known : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := scanGapState known
          tape := tapeAtCells left (some false :: right) } =
      { state := scanRawRightState known
        tape := tapeAtCells (some false :: left) right } := by
  cases known <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

theorem run_scanGap_raw_other
    (gap : Nat) (bits : Word Bool)
    (left right : List (Option Bool)) :
    description.runConfig (gap + 1 + bits.length)
        { state := scanGapState false
          tape := tapeAtCells left
            (List.append (List.replicate gap none)
              (some false ::
                List.append (bits.map some) (none :: right))) } =
      { state := scanRawRightState false
        tape := tapeAtCells
          (List.append (bits.reverse.map some)
            (some false ::
              List.append (List.replicate gap none) left))
          (none :: right) } := by
  change List Bool at bits
  rw [show gap + 1 + bits.length = gap + (1 + bits.length) by lia]
  rw [MachineDescription.runConfig_add]
  rw [run_right_blanks description (scanGapState false)
    (step_scanGap_none false) gap (some false) left
    (List.append (bits.map some) (none :: right))]
  rw [MachineDescription.runConfig_add]
  rw [step_scanGap_marker]
  rw [run_right_present description (scanRawRightState false)
    (step_scanRawRight_present false) bits none
    (some false :: List.append (List.replicate gap none) left) right]

theorem run_scanGapRawWithPadding
    (gap : Nat) (bits : Word Bool)
    (left : List (Option Bool)) (rightPadding : Nat) :
    description.runConfig (gap + 1 + bits.length)
        { state := scanGapState false
          tape := tapeAtCells left
            (List.append (List.replicate gap none)
              (some false ::
                List.append (bits.map some)
                  (List.replicate (rightPadding + 3) none))) } =
      { state := scanRawRightState false
        tape := tapeAtCells
          (List.append (bits.reverse.map some)
            (some false ::
              List.append (List.replicate gap none) left))
          (none :: List.replicate (rightPadding + 2) none) } := by
  rw [show rightPadding + 3 = Nat.succ (rightPadding + 2) by lia]
  rw [List.replicate_succ]
  exact run_scanGap_raw_other gap bits left
    (List.replicate (rightPadding + 2) none)

theorem run_otherFinish
    (left : List (Option Bool)) (boundary : Option Bool)
    (right : List (Option Bool)) :
    description.runConfig 2
        { state := scanRawRightState false
          tape := tapeAtCells left (none :: none :: boundary :: right) } =
      { state := description.halt
        tape := tapeAtCells (none :: none :: left) (boundary :: right) } := by
  cases boundary <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

theorem run_otherFinishWithPadding
    (left : List (Option Bool)) (rightPadding : Nat) :
    description.runConfig 2
        { state := scanRawRightState false
          tape := tapeAtCells left
            (none :: List.replicate (rightPadding + 2) none) } =
      { state := description.halt
        tape := tapeAtCells (none :: none :: left)
          (none :: List.replicate rightPadding none) } := by
  rw [show rightPadding + 2 = Nat.succ (Nat.succ rightPadding) by lia]
  rw [List.replicate_succ, List.replicate_succ]
  exact run_otherFinish left none (List.replicate rightPadding none)

theorem run_otherRawBlock
    (hit rawLast : Bool) (rawRest : Word Bool)
    (base right : List (Option Bool)) :
    description.runConfig (1 + (List.append rawRest [false]).length)
        { state := otherSeekRawState hit
          tape := tapeAtCells
            (List.append (rawRest.map some)
              (some false :: none :: base))
            (some rawLast :: right) } =
      { state := otherScanRawLeftState hit
        tape := tapeAtCells base
          (none ::
            List.append
              ((List.append rawRest [false]).reverse.map some)
              (some rawLast :: right)) } := by
  change List Bool at rawRest
  rw [MachineDescription.runConfig_add]
  cases rawRest with
  | nil =>
      simp only [List.map, List.append]
      rw [step_otherSeekRaw_present]
      exact run_left_present description (otherScanRawLeftState hit)
        (step_otherScanRawLeft_present hit) [false] none base
        (some rawLast :: right)
  | cons bit rest =>
      simp only [List.map, List.append]
      rw [step_otherSeekRaw_present]
      simpa [leftPresentScanTape, List.map_append, List.append_assoc] using
        run_left_present description (otherScanRawLeftState hit)
          (step_otherScanRawLeft_present hit)
          (bit :: List.append rest [false]) none base
          (some rawLast :: right)

theorem otherRawBlock_right_eq
    (raw rawRest : Word Bool) (rawLast : Bool)
    (hraw : raw.reverse = rawLast :: rawRest)
    (right : List (Option Bool)) :
    List.append
        ((List.append rawRest [false]).reverse.map some)
        (some rawLast :: right) =
      some false :: List.append (raw.map some) right := by
  change List Bool at raw rawRest
  have hrawForward :
      raw = List.append rawRest.reverse [rawLast] := by
    simpa [List.reverse_cons] using congrArg List.reverse hraw
  simp [hrawForward, List.reverse_append, List.map_append,
    List.append_assoc]

theorem run_otherInitialBlanks
    (hit rawLast : Bool) (rawRest : Word Bool)
    (tail : List (Option Bool)) (rightPadding : Nat) :
    description.runConfig ((rightPadding + 2) + 1)
        { state := otherSeekRawState hit
          tape := tapeAtCells
            (List.append
              (List.replicate (rightPadding + 2) (none : Option Bool))
              (List.append ((rawLast :: rawRest).map some) tail))
            [none] } =
      { state := otherSeekRawState hit
        tape := tapeAtCells
          (List.append (rawRest.map some) tail)
          (some rawLast ::
            List.replicate ((rightPadding + 2) + 1) none) } := by
  change List Bool at rawRest
  simpa [List.append_assoc] using
    run_left_blanks description (otherSeekRawState hit)
      (step_otherSeekRaw_none hit) (rightPadding + 2)
      (some rawLast) (List.append (rawRest.map some) tail) []

theorem run_otherRawBlockWithGap
    (hit rawLast : Bool) (rawRest : Word Bool)
    (exactCells right : List (Option Bool)) (gapTail : Nat) :
    description.runConfig (1 + (List.append rawRest [false]).length)
        { state := otherSeekRawState hit
          tape := tapeAtCells
            (List.append (rawRest.map some)
              (some false ::
                List.append
                  (List.replicate ((gapTail + 1) + 4) none)
                  exactCells))
            (some rawLast :: right) } =
      { state := otherScanRawLeftState hit
        tape := tapeAtCells
          (List.append (List.replicate (gapTail + 4) none) exactCells)
          (none ::
            List.append
              ((List.append rawRest [false]).reverse.map some)
              (some rawLast :: right)) } := by
  rw [show (gapTail + 1) + 4 = Nat.succ (gapTail + 4) by lia]
  rw [List.replicate_succ]
  simpa [List.append_assoc] using
    run_otherRawBlock hit rawLast rawRest
      (List.append (List.replicate (gapTail + 4) none) exactCells) right

theorem step_otherRawBoundaryWithGap
    (hit : Bool) (exactCells right : List (Option Bool))
    (gapTail : Nat) :
    description.runConfig 1
        { state := otherScanRawLeftState hit
          tape := tapeAtCells
            (List.append (List.replicate (gapTail + 4) none) exactCells)
            (none :: right) } =
      { state := seekExactState false hit
        tape := tapeAtCells
          (List.append (List.replicate (gapTail + 3) none) exactCells)
          (none :: none :: right) } := by
  rw [show gapTail + 4 = Nat.succ (gapTail + 3) by lia]
  rw [List.replicate_succ]
  exact step_otherScanRawLeft_none hit none
    (List.append (List.replicate (gapTail + 3) none) exactCells) right

theorem run_otherSeekExact
    (hit exactLast : Bool) (exactRest : Word Bool)
    (gapTail : Nat) (right : List (Option Bool)) :
    description.runConfig ((gapTail + 3) + 1)
        { state := seekExactState false hit
          tape := tapeAtCells
            (List.append (List.replicate (gapTail + 3) none)
              ((exactLast :: exactRest).map some))
            (none :: right) } =
      { state := seekExactState false hit
        tape := tapeAtCells (exactRest.map some)
          (some exactLast ::
            List.append (List.replicate ((gapTail + 3) + 1) none)
              right) } := by
  change List Bool at exactRest
  simpa [List.append_assoc] using
    run_left_blanks description (seekExactState false hit)
      (step_seekExact_none false hit) (gapTail + 3)
      (some exactLast) (exactRest.map some) right

theorem run_otherWriteHitFromExactHead
    (hit exactLast : Bool) (gapTail : Nat)
    (exactRest : Word Bool) (tail : List (Option Bool)) :
    description.runConfig (1 + 4)
        { state := seekExactState false hit
          tape := tapeAtCells (exactRest.map some)
            (some exactLast ::
              List.append (List.replicate (gapTail + 3 + 1) none)
                (none :: tail)) } =
      { state := scanGapState false
        tape := tapeAtCells
          (some (!hit) :: some hit :: some true :: some false ::
            some exactLast :: exactRest.map some)
          (List.append (List.replicate (gapTail + 1) none) tail) } := by
  change List Bool at exactRest
  have hright :
      List.append (List.replicate (gapTail + 3) none) (none :: tail) =
        none :: none :: none :: none ::
          List.append (List.replicate gapTail none) tail := by
    calc
      List.append (List.replicate (gapTail + 3) none) (none :: tail) =
          List.append (List.replicate ((gapTail + 3) + 1) none)
            tail := by
          simpa using
            (FoC.Computability.list_replicate_add_append
              (none : Option Bool) (gapTail + 3) 1 tail).symm
      _ = List.append (List.replicate (4 + gapTail) none) tail := by
        rw [show (gapTail + 3) + 1 = 4 + gapTail by lia]
      _ = List.append (List.replicate 4 none)
          (List.append (List.replicate gapTail none) tail) := by
        exact FoC.Computability.list_replicate_add_append
          (none : Option Bool) 4 gapTail tail
      _ = none :: none :: none :: none ::
          List.append (List.replicate gapTail none) tail := by
        rfl
  rw [MachineDescription.runConfig_add]
  rw [show List.append (List.replicate (gapTail + 3 + 1) none)
      (none :: tail) =
        none ::
          List.append (List.replicate (gapTail + 3) none)
            (none :: tail) by
    rw [show gapTail + 3 + 1 = Nat.succ (gapTail + 3) by lia]
    rfl]
  rw [step_seekExact_present_any]
  rw [hright]
  rw [run_writeHitField]
  rw [show gapTail + 1 = Nat.succ gapTail by lia]
  rfl

def otherEntryTape (i : Index) (scratchCount : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (20 + 2 * scratchCount) (none : Option Bool))
      (List.append
        ((physicalTokenBits (rawMetadataTokens i)).reverse.map some)
        (some false ::
          List.append (List.replicate (readyGap i + 4) none)
            ((LengthAssembly.exactTapeFieldBits
              i.finalTape []).reverse.map some))))
    [none]

def otherCoreSourceTape
    (raw exact : Word Bool) (gapTail rightPadding : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (rightPadding + 2) (none : Option Bool))
      (List.append (raw.reverse.map some)
        (some false ::
          List.append
            (List.replicate ((gapTail + 1) + 4) none)
            (exact.reverse.map some))))
    [none]

def otherCoreTargetTape
    (hit : Bool) (raw exact : Word Bool)
    (gapTail rightPadding : Nat) : Tape Bool :=
  let left : List (Option Bool) :=
    none :: none ::
      List.append (raw.reverse.map some)
        (some false ::
          List.append (List.replicate (gapTail + 1) none)
            (List.append
              [some (!hit), some hit, some true, some false]
              (exact.reverse.map some)))
  tapeAtCells left (none :: List.replicate rightPadding none)

theorem description_run_otherCore
    (hit : Bool) (raw exact : Word Bool)
    (gapTail rightPadding : Nat)
    (hraw : raw ≠ []) (hexact : exact ≠ []) :
    exists steps : Nat,
      description.runConfig steps
          { state := otherSeekRawState hit
            tape := otherCoreSourceTape raw exact gapTail rightPadding } =
        { state := description.halt
          tape := otherCoreTargetTape hit raw exact gapTail rightPadding } := by
  change List Bool at raw exact
  cases hrawReverse : raw.reverse with
  | nil =>
      have h := congrArg List.reverse hrawReverse
      have hnil : raw = ([] : List Bool) := by
        simpa using h
      exact (hraw hnil).elim
  | cons rawLast rawRest =>
      cases hexactReverse : exact.reverse with
      | nil =>
          have h := congrArg List.reverse hexactReverse
          have hnil : exact = ([] : List Bool) := by
            simpa using h
          exact (hexact hnil).elim
      | cons exactLast exactRest =>
          refine ⟨
            ((rightPadding + 2) + 1) +
              ((1 + (List.append rawRest [false]).length) +
                (1 +
                  (((gapTail + 3) + 1) +
                    (1 +
                      (4 +
                        ((gapTail + 1) +
                          (1 + (raw.length + 2)))))))), ?_⟩
          unfold otherCoreSourceTape otherCoreTargetTape
          rw [hrawReverse, hexactReverse]
          rw [MachineDescription.runConfig_add]
          rw [run_otherInitialBlanks]
          rw [MachineDescription.runConfig_add]
          rw [run_otherRawBlockWithGap]
          rw [otherRawBlock_right_eq raw rawRest rawLast hrawReverse]
          rw [MachineDescription.runConfig_add]
          rw [step_otherRawBoundaryWithGap]
          rw [MachineDescription.runConfig_add]
          rw [run_otherSeekExact]
          rw [show
            1 + (4 +
              ((gapTail + 1) + (1 + (raw.length + 2)))) =
                (1 + 4) +
                  (((gapTail + 1) + 1 + raw.length) + 2) by lia]
          rw [MachineDescription.runConfig_add]
          rw [run_otherWriteHitFromExactHead]
          rw [MachineDescription.runConfig_add]
          rw [run_scanGapRawWithPadding]
          rw [run_otherFinishWithPadding]
          rw [hrawReverse]
          rfl

theorem otherEntryTape_eq_otherCoreSourceTape
    (i : Index) (scratchCount : Nat) :
    otherEntryTape i scratchCount =
      otherCoreSourceTape
        (physicalTokenBits (rawMetadataTokens i))
        (LengthAssembly.exactTapeFieldBits i.finalTape [])
        (readyGapTail i) (18 + 2 * scratchCount) := by
  unfold otherEntryTape otherCoreSourceTape
  rw [readyGap_eq_tail_add_one]
  congr 3 <;> lia

theorem otherCoreTargetTape_eq_preMarkerTape
    (i : Index) (rightPadding : Nat) :
    otherCoreTargetTape i.finalHit
        (physicalTokenBits (rawMetadataTokens i))
        (LengthAssembly.exactTapeFieldBits i.finalTape [])
        (readyGapTail i) rightPadding =
      preMarkerTape i (rawMetadataTokens i) rightPadding := by
  unfold otherCoreTargetTape preMarkerTape
    leadingBlankLeftShiftTargetTapeWithPadding stagedBase
  rw [readyGap_eq_tail_add_one, hitBits_eq_components]
  cases i.finalHit <;>
    simp

theorem description_run_other
    (i : Index) (scratchCount : Nat) :
    exists steps : Nat,
      description.runConfig steps
          { state := otherSeekRawState i.finalHit
            tape := otherEntryTape i scratchCount } =
        { state := description.halt
          tape := preMarkerTape i (rawMetadataTokens i)
            (18 + 2 * scratchCount) } := by
  rw [otherEntryTape_eq_otherCoreSourceTape,
    ← otherCoreTargetTape_eq_preMarkerTape]
  exact description_run_otherCore i.finalHit
    (physicalTokenBits (rawMetadataTokens i))
    (LengthAssembly.exactTapeFieldBits i.finalTape [])
    (readyGapTail i) (18 + 2 * scratchCount)
    (physicalRawBits_ne_nil i) (exactTapeFieldBits_ne_nil i)

theorem description_runsFrom_other
    (i : Index) (scratchCount : Nat) :
    RunsFromStateTapeEquiv description
      (otherSeekRawState i.finalHit) description.halt
      (otherEntryTape i scratchCount)
      (preMarkerTape i (rawMetadataTokens i)
        (18 + 2 * scratchCount)) := by
  rcases description_run_other i scratchCount with ⟨steps, hrun⟩
  exact ⟨steps,
    preMarkerTape i (rawMetadataTokens i) (18 + 2 * scratchCount),
    hrun, Tape.Equiv.refl _⟩

end Normalizer

end GuardedEgress.MetadataWitnessStage
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
