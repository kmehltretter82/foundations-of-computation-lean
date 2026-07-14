import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessStage
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.SuffixParser

set_option doc.verso true

/-!
# Known-witness execution for guarded metadata staging

This module closes the exact normalizer run selected by a
{lit}`LoopDispatcherDoneWitness.known` payload.  The parser has already
isolated the witnessed unary state from the raw metadata; the normalizer
installs the hit field, erases the raw unary-state suffix, and invokes the
checked sentinel-gap compactor to splice the witnessed state into place.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessStage

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open MetadataWitnessBridge MetadataWitnessBridgeLocate MetadataTokenCopy

namespace Normalizer

/-- Blank padding retained by the known branch after deleting the raw state
and closing the witness gap. -/
def knownRightPadding (scratchCount rawState : Nat) : Nat :=
  18 + 2 * scratchCount + 8 * (rawState + 1)

/-- Exact parser endpoint from which the known normalizer starts. -/
def knownEntryTape (i : Index) (scratchCount finalState : Nat) : Tape Bool :=
  GuardedEgress.MetadataWitnessSuffixParser.knownTargetTape
    (locatedLeft i) (rawMetadataTokens i) scratchCount finalState []

private theorem exactTapeFieldBits_reverse_two (i : Index) :
    exists first second : Bool, exists rest : List Bool,
      (LengthAssembly.exactTapeFieldBits i.finalTape []).reverse =
        first :: second :: rest := by
  cases hrev :
      (LengthAssembly.exactTapeFieldBits i.finalTape []).reverse with
  | nil =>
      have hlength := congrArg List.length hrev
      simp [LengthAssembly.exactTapeFieldBits,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length]
        at hlength
  | cons first tail =>
      cases tail with
      | nil =>
          have hlength := congrArg List.length hrev
          simp [LengthAssembly.exactTapeFieldBits,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length]
            at hlength
          lia
      | cons second rest =>
          exact ⟨first, second, rest, rfl⟩

private theorem knownEntryTape_eq (i : Index)
    (scratchCount finalState : Nat) :
    knownEntryTape i scratchCount finalState =
      tapeAtCells
        (List.append (List.replicate 4 none)
          (List.append
            ((physicalTokenBits
              (MetadataWitnessBridge.natTokens finalState)).reverse.map some)
            (none :: none ::
              List.append
                (List.replicate (14 + 2 * scratchCount) none)
                (List.append
                  ((physicalTokenBits (rawMetadataTokens i)).reverse.map some)
                  (some false :: none :: none ::
                    List.append
                      (List.replicate (readyGap i + 2) none)
                      ((LengthAssembly.exactTapeFieldBits
                        i.finalTape []).reverse.map some))))))
        [none] := by
  have hscratch :
      List.replicate (16 + 2 * scratchCount) (none : Option Bool) =
        none :: none ::
          List.replicate (14 + 2 * scratchCount) none := by
    rw [show 16 + 2 * scratchCount =
      Nat.succ (Nat.succ (14 + 2 * scratchCount)) by lia]
    rfl
  have hgap :
      List.replicate (readyGap i + 4) (none : Option Bool) =
        none :: none :: List.replicate (readyGap i + 2) none := by
    rw [show readyGap i + 4 =
      Nat.succ (Nat.succ (readyGap i + 2)) by lia]
    rfl
  have hmarker :
      some false :: none :: locatedLeft i =
        some false ::
          List.append (List.replicate (readyGap i + 4) none)
            ((LengthAssembly.exactTapeFieldBits
              i.finalTape []).reverse.map some) := by
    simpa only [List.append] using markerLocatedLeft_eq i
  have hfinalReverse :
      List.reverse
          (List.map some
            (show List Bool from
              physicalTokenBits
                (MetadataWitnessBridge.natTokens finalState))) =
        List.map some
          (List.reverse
            (show List Bool from
              physicalTokenBits
                (MetadataWitnessBridge.natTokens finalState))) := by
    exact List.map_reverse.symm
  have hrawReverse :
      List.reverse
          (List.map some
            (show List Bool from physicalTokenBits (rawMetadataTokens i))) =
        List.map some
          (List.reverse
            (show List Bool from physicalTokenBits (rawMetadataTokens i))) := by
    exact List.map_reverse.symm
  unfold knownEntryTape
    GuardedEgress.MetadataWitnessSuffixParser.knownTargetTape
  rw [encodedTokens_eq_map_physicalTokenBits,
    encodedTokens_eq_map_physicalTokenBits]
  rw [hfinalReverse, hrawReverse, hmarker, hscratch, hgap]
  simp

private theorem physicalNatBits_ne_nil (n : Nat) :
    physicalTokenBits (MetadataWitnessBridge.natTokens n) ≠ [] := by
  intro hnil
  have hencoded :=
    encodedTokens_eq_map_physicalTokenBits
      (MetadataWitnessBridge.natTokens n)
  rw [hnil] at hencoded
  have hlength :=
    MetadataTokenCopy.encodedTokens_length
      (MetadataWitnessBridge.natTokens n)
  rw [hencoded] at hlength
  simp [natTokens_eq_ticks_done] at hlength

private theorem step_knownSeekWitness_present
    (hit bit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := knownSeekWitnessState hit
          tape := tapeAtCells (cell :: left) (some bit :: right) } =
      { state := knownScanWitnessState hit
        tape := tapeAtCells left (cell :: some bit :: right) } := by
  cases hit <;> cases bit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

private theorem step_knownScanWitness_none
    (hit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := knownScanWitnessState hit
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := knownSeekRawState hit
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases hit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

private theorem step_knownSeekRaw_present
    (hit bit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := knownSeekRawState hit
          tape := tapeAtCells (cell :: left) (some bit :: right) } =
      { state := knownScanRawLeftState hit
        tape := tapeAtCells left (cell :: some bit :: right) } := by
  cases hit <;> cases bit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

private theorem step_knownScanRawLeft_none
    (hit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := knownScanRawLeftState hit
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := seekExactState true hit
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases hit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

private theorem run_seek_scan_left_block
    (seek scan next : Nat)
    (hblank : forall (cell : Option Bool)
        (left right : List (Option Bool)),
      description.runConfig 1
          { state := seek
            tape := tapeAtCells (cell :: left) (none :: right) } =
        { state := seek
          tape := tapeAtCells left (cell :: none :: right) })
    (hseek : forall (bit : Bool) (cell : Option Bool)
        (left right : List (Option Bool)),
      description.runConfig 1
          { state := seek
            tape := tapeAtCells (cell :: left) (some bit :: right) } =
        { state := scan
          tape := tapeAtCells left (cell :: some bit :: right) })
    (hscan : forall (bit : Bool) (cell : Option Bool)
        (left right : List (Option Bool)),
      description.runConfig 1
          { state := scan
            tape := tapeAtCells (cell :: left) (some bit :: right) } =
        { state := scan
          tape := tapeAtCells left (cell :: some bit :: right) })
    (hfinish : forall (cell : Option Bool)
        (left right : List (Option Bool)),
      description.runConfig 1
          { state := scan
            tape := tapeAtCells (cell :: left) (none :: right) } =
        { state := next
          tape := tapeAtCells left (cell :: none :: right) })
    (padding : Nat) (bits : Word Bool) (hbits : bits ≠ [])
    (cell : Option Bool) (left right : List (Option Bool)) :
    description.runConfig (padding + bits.length + 2)
        { state := seek
          tape := tapeAtCells
            (List.append (List.replicate padding none)
              (List.append (bits.reverse.map some)
                (none :: cell :: left)))
            (none :: right) } =
      { state := next
        tape := tapeAtCells left
          (cell :: none ::
            List.append (bits.map some)
              (List.append (List.replicate (padding + 1) none)
                right)) } := by
  have hbitsList : (show List Bool from bits) ≠ [] := by
    change bits ≠ []
    exact hbits
  change List Bool at bits
  cases hrev : bits.reverse with
  | nil =>
      apply False.elim
      apply hbitsList
      have := congrArg List.reverse hrev
      simpa using this
  | cons first rest =>
      have hbitsEq : bits = (first :: rest).reverse := by
        rw [← hrev]
        exact (List.reverse_reverse bits).symm
      have hlength : bits.length = rest.length + 1 := by
        rw [hbitsEq]
        simp
      have hsource :
          List.append (List.replicate padding none)
              (List.append (bits.reverse.map some)
                (none :: cell :: left)) =
            List.append (List.replicate padding none)
              (some first ::
                List.append (rest.map some) (none :: cell :: left)) := by
        rw [hrev]
        rfl
      have henter :
          description.runConfig 1
              { state := seek
                tape := tapeAtCells
                  (List.append (rest.map some) (none :: cell :: left))
                  (some first ::
                    List.append (List.replicate (padding + 1) none)
                      right) } =
            { state := scan
              tape := leftPresentScanTape rest none (cell :: left)
                (some first ::
                  List.append (List.replicate (padding + 1) none)
                    right) } := by
        cases rest with
        | nil =>
            simpa [leftPresentScanTape] using
              hseek first none (cell :: left)
                (List.append (List.replicate (padding + 1) none) right)
        | cons next tail =>
            simpa [leftPresentScanTape, List.append_assoc] using
              hseek first (some next)
                (List.append (tail.map some) (none :: cell :: left))
                (List.append (List.replicate (padding + 1) none) right)
      have hmap :
          bits.map some =
            List.append (rest.reverse.map some) [some first] := by
        rw [hbitsEq, List.reverse_cons, List.map_append]
        rfl
      rw [show padding + bits.length + 2 =
          (padding + 1) + (1 + (rest.length + 1)) by
        rw [hlength]
        lia]
      rw [MachineDescription.runConfig_add]
      simp only [List.map, List.append]
      rw [run_left_blanks description seek hblank padding (some first)
        (List.append (rest.map some) (none :: cell :: left)) right]
      rw [MachineDescription.runConfig_add]
      rw [henter]
      rw [MachineDescription.runConfig_add]
      rw [run_left_present description scan hscan rest none
        (cell :: left)
        (some first ::
          List.append (List.replicate (padding + 1) none) right)]
      rw [hfinish]
      simp [hmap, List.append_assoc]

private theorem step_seekExact_present
    (hit bit : Bool) (cell next : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := seekExactState true hit
          tape := tapeAtCells (cell :: left) (some bit :: next :: right) } =
      { state := writeZeroState true hit
        tape := tapeAtCells (some bit :: cell :: left) (next :: right) } := by
  cases hit <;> cases bit <;> cases cell <;> cases next <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

private theorem run_writeHitField
    (hit : Bool) (left : List (Option Bool))
    (boundary : Option Bool) (right : List (Option Bool)) :
    description.runConfig 4
        { state := writeZeroState true hit
          tape := tapeAtCells left
            (none :: none :: none :: none :: boundary :: right) } =
      { state := scanGapState true
        tape := tapeAtCells
          (some (!hit) :: some hit :: some true :: some false :: left)
          (boundary :: right) } := by
  cases hit <;> cases boundary <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

private theorem run_seekExact_writeHit
    (hit first second : Bool) (gapTail : Nat)
    (rest : List Bool) (tail : List (Option Bool)) :
    description.runConfig (gapTail + 9)
        { state := seekExactState true hit
          tape := tapeAtCells
            (List.append (List.replicate (gapTail + 3) none)
              (some first :: some second :: rest.map some))
            (none :: none :: tail) } =
      { state := scanGapState true
        tape := tapeAtCells
          (some (!hit) :: some hit :: some true :: some false ::
            some first :: some second :: rest.map some)
          (List.append (List.replicate (gapTail + 1) none) tail) } := by
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
  rw [show gapTail + 9 = (gapTail + 4) + (1 + 4) by lia]
  rw [MachineDescription.runConfig_add]
  rw [run_left_blanks description (seekExactState true hit)
    (step_seekExact_none true hit) (gapTail + 3) (some first)
    (some second :: rest.map some) (none :: tail)]
  rw [MachineDescription.runConfig_add]
  rw [show List.append (List.replicate (gapTail + 3 + 1) none)
      (none :: tail) =
        none ::
          List.append (List.replicate (gapTail + 3) none)
            (none :: tail) by
    rw [show gapTail + 3 + 1 = Nat.succ (gapTail + 3) by lia]
    rfl]
  rw [step_seekExact_present]
  rw [hright]
  rw [run_writeHitField]
  rw [show gapTail + 1 = Nat.succ gapTail by lia]
  rfl

private theorem step_scanGap_marker
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := scanGapState true
          tape := tapeAtCells left (some false :: right) } =
      { state := scanRawRightState true
        tape := tapeAtCells (some false :: left) right } := by
  cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

private theorem run_scanGap_raw
    (gap : Nat) (bits : Word Bool)
    (left right : List (Option Bool)) :
    description.runConfig (gap + 1 + bits.length)
        { state := scanGapState true
          tape := tapeAtCells left
            (List.append (List.replicate gap none)
              (some false ::
                List.append (bits.map some) (none :: right))) } =
      { state := scanRawRightState true
        tape := tapeAtCells
          (List.append (bits.reverse.map some)
            (some false ::
              List.append (List.replicate gap none) left))
          (none :: right) } := by
  change List Bool at bits
  rw [show gap + 1 + bits.length = gap + (1 + bits.length) by lia]
  rw [MachineDescription.runConfig_add]
  rw [run_right_blanks description (scanGapState true)
    (step_scanGap_none true) gap (some false) left
    (List.append (bits.map some) (none :: right))]
  rw [MachineDescription.runConfig_add]
  rw [step_scanGap_marker]
  rw [run_right_present description (scanRawRightState true)
    (step_scanRawRight_present true) bits none
    (some false :: List.append (List.replicate gap none) left) right]

private theorem step_scanRawRight_none_known
    (cell : Option Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := scanRawRightState true
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := eraseDoneStates.getD 0 38
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases cell <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

private theorem run_eraseDoneToken
    (cell : Option Bool) (left right : List (Option Bool)) :
    description.runConfig 9
        { state := scanRawRightState true
          tape := tapeAtCells
            (List.append
              (MetadataTokenCopy.encodedTokenCells .done).reverse
              (cell :: left))
            (none :: right) } =
      { state := inspectPrecedingTokenState
        tape := tapeAtCells left
          (cell :: List.append (List.replicate 9 none) right) } := by
  cases cell <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      MetadataTokenCopy.encodedTokenCells,
      MetadataTokenCopy.TokenKind.bits, logicalCellListBits,
      logicalCellBits, otherSeekRawState, otherScanRawLeftState,
      knownSeekWitnessState, knownScanWitnessState, knownSeekRawState,
      knownScanRawLeftState, seekExactState, writeZeroState,
      writeOneState, writeHitState, writeLastState, scanGapState,
      scanRawRightState, otherSecondBlankState, eraseDoneStates,
      inspectPrecedingTokenState, seekWitnessRightState,
      scanWitnessRightState, crossGuardTwoState, crossGuardThreeState,
      crossGuardFourState, compactorOffset]

private theorem run_eraseTickToken
    (cell : Option Bool) (left right : List (Option Bool)) :
    description.runConfig 8
        { state := inspectPrecedingTokenState
          tape := tapeAtCells
            (List.append
              (MetadataTokenCopy.encodedTokenCells .tick).reverse.tail
              (cell :: left))
            (some true :: right) } =
      { state := inspectPrecedingTokenState
        tape := tapeAtCells left
          (cell :: List.append (List.replicate 8 none) right) } := by
  cases cell <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      MetadataTokenCopy.encodedTokenCells,
      MetadataTokenCopy.TokenKind.bits, logicalCellListBits,
      logicalCellBits, otherSeekRawState, otherScanRawLeftState,
      knownSeekWitnessState, knownScanWitnessState, knownSeekRawState,
      knownScanRawLeftState, seekExactState, writeZeroState,
      writeOneState, writeHitState, writeLastState, scanGapState,
      scanRawRightState, otherSecondBlankState, eraseDoneStates,
      inspectPrecedingTokenState, seekWitnessRightState,
      scanWitnessRightState, crossGuardTwoState, crossGuardThreeState,
      crossGuardFourState, compactorOffset]

private theorem run_eraseNatSuffix
    (rawState : Nat) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig (9 + 8 * rawState)
        { state := scanRawRightState true
          tape := tapeAtCells
            (List.append
              (MetadataTokenCopy.encodedTokens
                (MetadataWitnessBridge.natTokens rawState)).reverse
              (cell :: left))
            (none :: right) } =
      { state := inspectPrecedingTokenState
        tape := tapeAtCells left
          (cell ::
            List.append (List.replicate (9 + 8 * rawState) none)
              right) } := by
  induction rawState generalizing cell left right with
  | zero =>
      simpa [MetadataWitnessBridge.natTokens,
        MetadataTokenCopy.encodedTokens] using
        run_eraseDoneToken cell left right
  | succ rawState ih =>
      let tickTail : List (Option Bool) :=
        (MetadataTokenCopy.encodedTokenCells .tick).reverse.tail
      have htick :
          (MetadataTokenCopy.encodedTokenCells .tick).reverse =
            some true :: tickTail := by
        rfl
      have hsource :
          List.append
              (MetadataTokenCopy.encodedTokens
                (MetadataWitnessBridge.natTokens (rawState + 1))).reverse
              (cell :: left) =
            List.append
              (MetadataTokenCopy.encodedTokens
                (MetadataWitnessBridge.natTokens rawState)).reverse
              (some true ::
                List.append tickTail (cell :: left)) := by
        rw [MetadataWitnessBridge.natTokens,
          MetadataTokenCopy.encodedTokens_cons, List.reverse_append,
          htick]
        exact List.append_assoc _ _ _
      have hpadding :
          List.append (List.replicate 8 none)
              (List.append
                (List.replicate (9 + 8 * rawState) none) right) =
            List.append
              (List.replicate (9 + 8 * (rawState + 1)) none) right := by
        calc
          List.append (List.replicate 8 none)
              (List.append
                (List.replicate (9 + 8 * rawState) none) right) =
            List.append
              (List.replicate (8 + (9 + 8 * rawState)) none)
              right := by
                exact
                  (FoC.Computability.list_replicate_add_append
                    (none : Option Bool) 8 (9 + 8 * rawState) right).symm
          _ = List.append
              (List.replicate (9 + 8 * (rawState + 1)) none)
              right := by
                rw [show 8 + (9 + 8 * rawState) =
                  9 + 8 * (rawState + 1) by lia]
      rw [show 9 + 8 * (rawState + 1) =
          (9 + 8 * rawState) + 8 by lia]
      rw [MachineDescription.runConfig_add]
      rw [hsource]
      rw [ih (some true)
        (List.append tickTail (cell :: left)) right]
      rw [run_eraseTickToken cell left
        (List.append (List.replicate (9 + 8 * rawState) none) right)]
      rw [hpadding]
      rw [show 9 + 8 * (rawState + 1) =
        9 + 8 * rawState + 8 by lia]

private theorem step_inspect_prefix_false
    (cell : Option Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := inspectPrecedingTokenState
          tape := tapeAtCells (cell :: left) (some false :: right) } =
      { state := seekWitnessRightState
        tape := tapeAtCells (some false :: cell :: left) right } := by
  cases cell <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

private theorem step_inspect_prefix_false_general
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := inspectPrecedingTokenState
          tape := tapeAtCells left (some false :: right) } =
      { state := seekWitnessRightState
        tape := tapeAtCells (some false :: left) right } := by
  cases left <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

private theorem run_eraseRawState
    (rawState : Nat) (prefixTail right : List (Option Bool)) :
    description.runConfig (10 + 8 * rawState)
        { state := scanRawRightState true
          tape := tapeAtCells
            (List.append
              (MetadataTokenCopy.encodedTokens
                (MetadataWitnessBridge.natTokens rawState)).reverse
              (some false :: prefixTail))
            (none :: right) } =
      { state := seekWitnessRightState
        tape := tapeAtCells (some false :: prefixTail)
          (none ::
            List.append
              (List.replicate (8 * (rawState + 1)) none) right) } := by
  rw [show 10 + 8 * rawState = (9 + 8 * rawState) + 1 by lia]
  rw [MachineDescription.runConfig_add]
  rw [run_eraseNatSuffix rawState (some false) prefixTail right]
  rw [step_inspect_prefix_false_general]
  have hpadding :
      List.append (List.replicate (9 + 8 * rawState) none) right =
        none ::
          List.append (List.replicate (8 * (rawState + 1)) none)
            right := by
    rw [show 9 + 8 * rawState = Nat.succ (8 * (rawState + 1)) by
      lia]
    rfl
  rw [hpadding]

private theorem step_seekWitnessRight_present
    (bit : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := seekWitnessRightState
          tape := tapeAtCells left (some bit :: right) } =
      { state := scanWitnessRightState
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

private theorem run_cross_witness_guard
    (left right : List (Option Bool)) :
    description.runConfig 4
        { state := scanWitnessRightState
          tape := tapeAtCells left
            (none :: none :: none :: none :: none :: right) } =
      { state := compactorOffset
        tape := tapeAtCells
          (List.append (List.replicate 4 none) left)
          (none :: right) } := by
  cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      compactorBranch, preservePresentLeft, preservePresentRight,
      erasePresentLeft, otherSeekRawState, otherScanRawLeftState,
      knownSeekWitnessState, knownScanWitnessState, knownSeekRawState,
      knownScanRawLeftState, seekExactState, writeZeroState,
      writeOneState, writeHitState, writeLastState, scanGapState,
      scanRawRightState, otherSecondBlankState, eraseDoneStates,
      inspectPrecedingTokenState, seekWitnessRightState,
      scanWitnessRightState, crossGuardTwoState, crossGuardThreeState,
      crossGuardFourState, compactorOffset]

private theorem run_seekWitness_to_compactor
    (bits : Word Bool) (hbits : bits ≠ [])
    (left right : List (Option Bool)) :
    description.runConfig (bits.length + 4)
        { state := seekWitnessRightState
          tape := tapeAtCells left
            (List.append (bits.map some)
              (List.append (List.replicate 5 none) right)) } =
      { state := compactorOffset
        tape := tapeAtCells
          (List.append (List.replicate 4 none)
            (List.append (bits.reverse.map some) left))
          (none :: right) } := by
  have hbitsList : (show List Bool from bits) ≠ [] := by
    change bits ≠ []
    exact hbits
  change List Bool at bits
  cases bits with
  | nil =>
      exact False.elim (hbitsList rfl)
  | cons first rest =>
      rw [show (first :: rest).length + 4 =
          1 + (rest.length + 4) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      simp only [List.map, List.append]
      rw [step_seekWitnessRight_present]
      rw [MachineDescription.runConfig_add]
      rw [show List.append (List.replicate 5 none) right =
          none :: List.append (List.replicate 4 none) right by
        rfl]
      rw [run_right_present description scanWitnessRightState
        step_scanWitnessRight_present rest none (some first :: left)
        (List.append (List.replicate 4 none) right)]
      rw [show none :: List.append (List.replicate 4 none) right =
          none :: none :: none :: none :: none :: right by
        rfl]
      rw [run_cross_witness_guard]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem description_run_compactor
    {source target : Tape Bool}
    (hrun :
      sentinelGapCompactorDescription.HaltsFromTape source target) :
    exists steps : Nat,
      description.runConfig steps
          { state := compactorOffset, tape := source } =
        { state := description.halt, tape := target } := by
  rcases hrun with ⟨steps, hstate, htape⟩
  have hlocal :
      sentinelGapCompactorDescription.runConfig steps
          { state := sentinelGapCompactorDescription.start
            tape := source } =
        { state := sentinelGapCompactorDescription.halt
          tape := target } := by
    cases hfinal :
        sentinelGapCompactorDescription.runConfig steps
          { state := sentinelGapCompactorDescription.start
            tape := source } with
    | mk finalState finalTape =>
        rw [hfinal] at hstate htape
        change finalState = sentinelGapCompactorDescription.halt at hstate
        change finalTape = target at htape
        simp [hstate, htape]
  have hbranch :=
    MachineDescription.offsetExitRetargetDescription_runConfig_eq
      (offset := compactorOffset)
      (localExit := sentinelGapCompactorDescription.halt)
      (target := 0) (by decide)
      sentinelGapCompactorDescription_haltTransitionFree hlocal
  have hbranchExact :
      compactorBranch.runConfig steps
          { state := compactorOffset, tape := source } =
        { state := 0, tape := target } := by
    have hstart :
        sentinelGapCompactorDescription.start ≠
          sentinelGapCompactorDescription.halt := by
      decide
    have hstartEq : sentinelGapCompactorDescription.start = 0 := by
      rfl
    have hhaltEq : sentinelGapCompactorDescription.halt = 13 := by
      rfl
    simpa [compactorBranch, compactorOffset,
      MachineDescription.sharedExitRetargetConfiguration, hstart,
      hstartEq, hhaltEq] using hbranch
  have hsubset :
      forall t : TransitionDescription,
        t ∈ compactorBranch.transitions -> t ∈ description.transitions := by
    intro t ht
    simp [description, ht]
  have hdet : description.Deterministic :=
    description_subroutineReady.left.right.right.right.right
  have hfree : compactorBranch.TransitionFreeAt 0 := by
    have hfree' :=
      MachineDescription.offsetExitRetargetDescription_haltTransitionFree
        (offset := compactorOffset)
        (localExit := sentinelGapCompactorDescription.halt)
        (D := sentinelGapCompactorDescription) (target := 0)
        (by unfold compactorOffset; decide)
    change compactorBranch.TransitionFreeAt compactorBranch.halt at hfree'
    change compactorBranch.TransitionFreeAt 0 at hfree'
    exact hfree'
  rcases
      StaticDispatcherReaderAssembly.firstReaches_transitionFreeAt_of_runConfig_eq
        hfree hbranchExact with
    ⟨firstSteps, _hfirstLe, hfirstRun, hfirst⟩
  refine ⟨firstSteps, ?_⟩
  rw [StaticDispatcherReaderAssembly.runConfig_eq_of_subset_deterministic_of_steps
    hsubset hdet
    (StaticDispatcherReaderAssembly.stepConfig_exists_before_firstReaches
      hfirstRun hfirst)]
  simpa [description] using hfirstRun

/-- Exact known-witness normalizer run from the suffix-parser endpoint to the
common marker-ready tape. -/
theorem description_runConfig_knownTargetTape
    (i : Index) (scratchCount finalState : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState) :
    exists steps : Nat,
      description.runConfig steps
          { state := knownSeekWitnessState i.finalHit
            tape := knownEntryTape i scratchCount finalState } =
        { state := description.halt
          tape := preMarkerTape i (sourceMetadataTokens i)
            (knownRightPadding scratchCount
              i.sourceLayout.config.state) } := by
  let qBits : Word Bool :=
    physicalTokenBits (MetadataWitnessBridge.natTokens finalState)
  let rawBits : Word Bool := physicalTokenBits (rawMetadataTokens i)
  let exactBits : Word Bool :=
    LengthAssembly.exactTapeFieldBits i.finalTape []
  let afterWitnessLeft : List (Option Bool) :=
    List.append (List.replicate (14 + 2 * scratchCount) none)
      (List.append (rawBits.reverse.map some)
        (some false :: none :: none ::
          List.append (List.replicate (readyGap i + 2) none)
            (exactBits.reverse.map some)))
  let afterWitnessRight : List (Option Bool) :=
    none :: none ::
      List.append (qBits.map some) (List.replicate 5 none)
  have hqBits : qBits ≠ [] := by
    simpa [qBits] using physicalNatBits_ne_nil finalState
  have hA :
      description.runConfig (4 + qBits.length + 2)
          { state := knownSeekWitnessState i.finalHit
            tape := knownEntryTape i scratchCount finalState } =
        { state := knownSeekRawState i.finalHit
          tape := tapeAtCells afterWitnessLeft afterWitnessRight } := by
    rw [knownEntryTape_eq]
    simpa [qBits, rawBits, exactBits, afterWitnessLeft,
      afterWitnessRight, List.append_assoc] using
      run_seek_scan_left_block
        (knownSeekWitnessState i.finalHit)
        (knownScanWitnessState i.finalHit)
        (knownSeekRawState i.finalHit)
        (step_knownSeekWitness_none i.finalHit)
        (step_knownSeekWitness_present i.finalHit)
        (step_knownScanWitness_present i.finalHit)
        (step_knownScanWitness_none i.finalHit)
        4 qBits hqBits none
        (List.append (List.replicate (14 + 2 * scratchCount) none)
          (List.append (rawBits.reverse.map some)
            (some false :: none :: none ::
              List.append (List.replicate (readyGap i + 2) none)
                (exactBits.reverse.map some)))) []
  let afterRawLeft : List (Option Bool) :=
    List.append (List.replicate (readyGap i + 2) none)
      (exactBits.reverse.map some)
  let afterRawRight : List (Option Bool) :=
    none :: none :: some false ::
      List.append (rawBits.map some)
        (List.append
          (List.replicate ((14 + 2 * scratchCount) + 1) none)
          (none :: List.append (qBits.map some) (List.replicate 5 none)))
  have hB :
      description.runConfig
          ((14 + 2 * scratchCount) + (false :: rawBits).length + 2)
          { state := knownSeekRawState i.finalHit
            tape := tapeAtCells afterWitnessLeft afterWitnessRight } =
        { state := seekExactState true i.finalHit
          tape := tapeAtCells afterRawLeft afterRawRight } := by
    have hnonempty : (false :: rawBits) ≠ [] := by simp
    simpa [afterWitnessLeft, afterWitnessRight, afterRawLeft,
      afterRawRight, List.append_assoc] using
      run_seek_scan_left_block
        (knownSeekRawState i.finalHit)
        (knownScanRawLeftState i.finalHit)
        (seekExactState true i.finalHit)
        (step_knownSeekRaw_none i.finalHit)
        (step_knownSeekRaw_present i.finalHit)
        (step_knownScanRawLeft_present i.finalHit)
        (step_knownScanRawLeft_none i.finalHit)
        (14 + 2 * scratchCount) (false :: rawBits) hnonempty none
        afterRawLeft
        (none :: List.append (qBits.map some) (List.replicate 5 none))
  rcases exactTapeFieldBits_reverse_two i with
    ⟨first, second, rest, hexact⟩
  have hexactBits : exactBits.reverse = first :: second :: rest := by
    simpa [exactBits] using hexact
  let afterExactTail : List (Option Bool) :=
    some false ::
      List.append (rawBits.map some)
        (List.append
          (List.replicate ((14 + 2 * scratchCount) + 1) none)
          (none :: List.append (qBits.map some) (List.replicate 5 none)))
  let afterHitLeft : List (Option Bool) :=
    some (!i.finalHit) :: some i.finalHit :: some true :: some false ::
      exactBits.reverse.map some
  let afterHitRight : List (Option Bool) :=
    List.append (List.replicate (readyGap i) none) afterExactTail
  have hC :
      description.runConfig (readyGapTail i + 9)
          { state := seekExactState true i.finalHit
            tape := tapeAtCells afterRawLeft afterRawRight } =
        { state := scanGapState true
          tape := tapeAtCells afterHitLeft afterHitRight } := by
    simpa [afterRawLeft, afterRawRight, afterExactTail, afterHitLeft,
      afterHitRight, hexactBits, readyGap_eq_tail_add_one,
      List.append_assoc] using
      run_seekExact_writeHit i.finalHit first second (readyGapTail i)
        rest afterExactTail
  have hstaged :
      some false ::
          List.append (List.replicate (readyGap i) none) afterHitLeft =
        stagedBase i := by
    unfold afterHitLeft stagedBase
    dsimp [exactBits]
    rw [hitBits_eq_components]
    simp
  let scanRightTail : List (Option Bool) :=
    List.append (List.replicate (14 + 2 * scratchCount) none)
      (none :: List.append (qBits.map some) (List.replicate 5 none))
  let afterScanRight : List (Option Bool) := none :: scanRightTail
  have hD :
      description.runConfig (readyGap i + 1 + rawBits.length)
          { state := scanGapState true
            tape := tapeAtCells afterHitLeft afterHitRight } =
        { state := scanRawRightState true
          tape := tapeAtCells
            (List.append (rawBits.reverse.map some) (stagedBase i))
            afterScanRight } := by
    have hsource :
        afterHitRight =
          List.append (List.replicate (readyGap i) none)
            (some false ::
              List.append (rawBits.map some) (none :: scanRightTail)) := by
      dsimp [afterHitRight, afterExactTail, scanRightTail]
      rw [show 14 + 2 * scratchCount + 1 =
        Nat.succ (14 + 2 * scratchCount) by lia]
      rfl
    have hleft :
        List.append (rawBits.reverse.map some)
            (some false ::
              List.append (List.replicate (readyGap i) none)
                afterHitLeft) =
          List.append (rawBits.reverse.map some) (stagedBase i) := by
      rw [hstaged]
    rw [hsource]
    rw [run_scanGap_raw (readyGap i) rawBits afterHitLeft scanRightTail]
    rw [hleft]
  let rawState : Nat := i.sourceLayout.config.state
  let prefixBits : Word Bool := physicalTokenBits (prefixMetadataTokens i)
  let rawStateBits : Word Bool :=
    physicalTokenBits (MetadataWitnessBridge.natTokens rawState)
  change List Bool at rawBits
  change List Bool at prefixBits
  change List Bool at rawStateBits
  have hrawBits :
      rawBits = List.append prefixBits rawStateBits := by
    dsimp [rawBits, prefixBits, rawStateBits, rawState]
    rw [rawMetadataTokens_eq_prefix_state, physicalTokenBits_append]
    rfl
  have hrawStateEncoded :
      MetadataTokenCopy.encodedTokens
          (MetadataWitnessBridge.natTokens rawState) =
        rawStateBits.map some := by
    simpa [rawStateBits] using
      encodedTokens_eq_map_physicalTokenBits
        (MetadataWitnessBridge.natTokens rawState)
  rcases prefixEncoded_reverse_exists i with
    ⟨prefixTail, hprefixEncoded⟩
  have hprefixBits :
      prefixBits.reverse.map some = some false :: prefixTail := by
    rw [List.map_reverse]
    simpa [prefixBits, encodedTokens_eq_map_physicalTokenBits] using
      hprefixEncoded
  let afterEraseLeft : List (Option Bool) :=
    some false :: List.append prefixTail (stagedBase i)
  let afterEraseRight : List (Option Bool) :=
    none ::
      List.append (List.replicate (8 * (rawState + 1)) none)
        scanRightTail
  have hE :
      description.runConfig (10 + 8 * rawState)
          { state := scanRawRightState true
            tape := tapeAtCells
              (List.append (rawBits.reverse.map some) (stagedBase i))
              afterScanRight } =
        { state := seekWitnessRightState
          tape := tapeAtCells afterEraseLeft afterEraseRight } := by
    have hreverseAppend :
        (List.append prefixBits rawStateBits).reverse =
          List.append rawStateBits.reverse prefixBits.reverse := by
      exact List.reverse_append
    have hmapAppend :
        List.map some
            (List.append rawStateBits.reverse prefixBits.reverse) =
          List.append (rawStateBits.reverse.map some)
            (prefixBits.reverse.map some) := by
      exact List.map_append
    have hrawStateReverse :
        rawStateBits.reverse.map some =
          (MetadataTokenCopy.encodedTokens
            (MetadataWitnessBridge.natTokens rawState)).reverse := by
      rw [List.map_reverse, ← hrawStateEncoded]
    have hrawLeft :
        List.append (rawBits.reverse.map some) (stagedBase i) =
          List.append
            (MetadataTokenCopy.encodedTokens
              (MetadataWitnessBridge.natTokens rawState)).reverse
            (some false :: List.append prefixTail (stagedBase i)) := by
      calc
        List.append (rawBits.reverse.map some) (stagedBase i) =
            List.append
              ((List.append prefixBits rawStateBits).reverse.map some)
              (stagedBase i) := by rw [hrawBits]
        _ = List.append (rawStateBits.reverse.map some)
              (List.append (prefixBits.reverse.map some) (stagedBase i)) := by
            rw [hreverseAppend, hmapAppend]
            exact List.append_assoc
              (as := rawStateBits.reverse.map some)
              (bs := prefixBits.reverse.map some)
              (cs := stagedBase i)
        _ = List.append
              (MetadataTokenCopy.encodedTokens
                (MetadataWitnessBridge.natTokens rawState)).reverse
              (List.append (some false :: prefixTail) (stagedBase i)) := by
            rw [hrawStateReverse, hprefixBits]
        _ = List.append
              (MetadataTokenCopy.encodedTokens
                (MetadataWitnessBridge.natTokens rawState)).reverse
              (some false :: List.append prefixTail (stagedBase i)) := by
            rfl
    rw [hrawLeft]
    simpa [afterScanRight, afterEraseLeft, afterEraseRight] using
      run_eraseRawState rawState
        (List.append prefixTail (stagedBase i)) scanRightTail
  change List Bool at qBits
  let seekGap : Nat :=
    16 + 2 * scratchCount + 8 * (rawState + 1)
  let qTail : List (Option Bool) :=
    List.append (qBits.map some) (List.replicate 5 none)
  have hseekSource :
      afterEraseRight =
        List.append (List.replicate seekGap none) qTail := by
    dsimp [afterEraseRight, scanRightTail, seekGap, qTail]
    rw [show 16 + 2 * scratchCount + 8 * (rawState + 1) =
      1 + (8 * (rawState + 1) + ((14 + 2 * scratchCount) + 1)) by
        lia]
    rw [FoC.Computability.list_replicate_add_append
      (none : Option Bool) 1
      (8 * (rawState + 1) + ((14 + 2 * scratchCount) + 1))]
    rw [FoC.Computability.list_replicate_add_append
      (none : Option Bool) (8 * (rawState + 1))
      ((14 + 2 * scratchCount) + 1)]
    rw [FoC.Computability.list_replicate_add_append
      (none : Option Bool) (14 + 2 * scratchCount) 1]
    rfl
  obtain ⟨qFirst, qRest, hqEq⟩ := List.exists_cons_of_ne_nil hqBits
  let afterSeekLeft : List (Option Bool) :=
    List.append (List.replicate seekGap none) afterEraseLeft
  have hFblank :
      description.runConfig seekGap
          { state := seekWitnessRightState
            tape := tapeAtCells afterEraseLeft afterEraseRight } =
        { state := seekWitnessRightState
          tape := tapeAtCells afterSeekLeft qTail } := by
    rw [hseekSource]
    dsimp [qTail]
    rw [hqEq]
    simpa [afterSeekLeft] using
      run_right_blanks description seekWitnessRightState
        step_seekWitnessRight_none seekGap (some qFirst) afterEraseLeft
        (List.append (qRest.map some) (List.replicate 5 none))
  let compactorSource : Tape Bool :=
    tapeAtCells
      (List.append (List.replicate 4 none)
        (List.append (qBits.reverse.map some) afterSeekLeft))
      [none]
  have hFguard :
      description.runConfig (qBits.length + 4)
          { state := seekWitnessRightState
            tape := tapeAtCells afterSeekLeft qTail } =
        { state := compactorOffset, tape := compactorSource } := by
    simpa [qTail, compactorSource] using
      run_seekWitness_to_compactor qBits hqBits afterSeekLeft []
  let compactorGap : Nat :=
    15 + 2 * scratchCount + 8 * (rawState + 1)
  have hseekGap : seekGap = compactorGap + 1 := by
    dsimp [seekGap, compactorGap]
    lia
  have hgapCells :
      List.replicate seekGap (none : Option Bool) =
        none :: List.replicate compactorGap none := by
    rw [hseekGap, show compactorGap + 1 = Nat.succ compactorGap by lia]
    rfl
  have hqRevNe : qBits.reverse ≠ [] := by
    rw [hqEq]
    simp
  obtain ⟨qRevFirst, qRevRest, hqRevEq⟩ :=
    List.exists_cons_of_ne_nil hqRevNe
  let checkedSource : Tape Bool :=
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
      (rightBlankLocalGapBaseLeft compactorGap afterEraseLeft)
      qRevFirst qRevRest 4 []
  let checkedTarget : Tape Bool :=
    leadingBlankLeftShiftTargetTapeWithPadding afterEraseLeft
      (qRevFirst :: qRevRest).reverse
      (sentinelGapCompactorFinalPadding compactorGap 4 [])
  have hcompactorSource : compactorSource = checkedSource := by
    unfold compactorSource checkedSource afterSeekLeft
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
      rightBlankLocalGapBaseLeft
    rw [hqRevEq, hgapCells]
    rfl
  have hcheckedHalts :
      sentinelGapCompactorDescription.HaltsFromTape
        compactorSource checkedTarget := by
    rw [hcompactorSource]
    simpa [checkedSource, checkedTarget, afterEraseLeft] using
      sentinelGapCompactorDescription_haltsFromTape_gapBase
        compactorGap (List.append prefixTail (stagedBase i)) false
        qRevFirst qRevRest 3 []
  rcases description_run_compactor hcheckedHalts with
    ⟨compactorSteps, hFcompactor⟩
  have hqTargetBits :
      (qRevFirst :: qRevRest).reverse = qBits := by
    rw [← hqRevEq, List.reverse_reverse]
  have hsourceTokens :
      sourceMetadataTokens i =
        List.append (prefixMetadataTokens i)
          (MetadataWitnessBridge.natTokens finalState) := by
    rw [sourceMetadataTokens_known i finalState hwitness]
    simp [prefixMetadataTokens, List.append_assoc]
  have hsourceBits :
      physicalTokenBits (sourceMetadataTokens i) =
        List.append prefixBits qBits := by
    rw [hsourceTokens, physicalTokenBits_append]
  have hfullReverse :
      (List.append prefixBits qBits).reverse.map some =
        List.append (qBits.reverse.map some)
          (prefixBits.reverse.map some) := by
    have hreverse :
        (List.append prefixBits qBits).reverse =
          List.append qBits.reverse prefixBits.reverse := by
      exact List.reverse_append
    have hmap :
        List.map some (List.append qBits.reverse prefixBits.reverse) =
          List.append (qBits.reverse.map some)
            (prefixBits.reverse.map some) := by
      exact List.map_append
    rw [hreverse, hmap]
  have hleftPayload :
      List.append (qBits.reverse.map some) afterEraseLeft =
        List.append
          ((List.append prefixBits qBits).reverse.map some)
          (stagedBase i) := by
    calc
      List.append (qBits.reverse.map some) afterEraseLeft =
          List.append (qBits.reverse.map some)
            (List.append (prefixBits.reverse.map some) (stagedBase i)) := by
        dsimp [afterEraseLeft]
        rw [hprefixBits]
        rfl
      _ = List.append
            (List.append (qBits.reverse.map some)
              (prefixBits.reverse.map some))
            (stagedBase i) := by
        exact (List.append_assoc
          (as := qBits.reverse.map some)
          (bs := prefixBits.reverse.map some)
          (cs := stagedBase i)).symm
      _ = List.append
            ((List.append prefixBits qBits).reverse.map some)
            (stagedBase i) := by
        rw [hfullReverse]
  have hpadding :
      sentinelGapCompactorFinalPadding compactorGap 4 [] =
        none ::
          List.replicate
            (knownRightPadding scratchCount rawState)
            (none : Option Bool) := by
    have hfinal :=
      sentinelGapCompactorFinalPadding_replicate compactorGap 3 0
    rw [show (List.replicate 0 (none : Option Bool)) = [] by rfl]
      at hfinal
    rw [hfinal]
    rw [show 4 + compactorGap + 0 =
      Nat.succ (knownRightPadding scratchCount rawState) by
        dsimp [compactorGap, knownRightPadding]
        lia]
    rfl
  have htarget :
      checkedTarget =
        preMarkerTape i (sourceMetadataTokens i)
          (knownRightPadding scratchCount rawState) := by
    unfold checkedTarget preMarkerTape
      leadingBlankLeftShiftTargetTapeWithPadding
    rw [hqTargetBits, hsourceBits, hleftPayload, hpadding]
  let totalSteps : Nat :=
    (4 + qBits.length + 2) +
      (((14 + 2 * scratchCount) + (false :: rawBits).length + 2) +
        ((readyGapTail i + 9) +
          ((readyGap i + 1 + rawBits.length) +
            ((10 + 8 * rawState) +
              (seekGap + ((qBits.length + 4) + compactorSteps))))))
  refine ⟨totalSteps, ?_⟩
  unfold totalSteps
  rw [MachineDescription.runConfig_add, hA]
  rw [MachineDescription.runConfig_add, hB]
  rw [MachineDescription.runConfig_add, hC]
  rw [MachineDescription.runConfig_add, hD]
  rw [MachineDescription.runConfig_add, hE]
  rw [MachineDescription.runConfig_add, hFblank]
  rw [MachineDescription.runConfig_add, hFguard]
  rw [hFcompactor, htarget]

/-- Tape-equivalence packaging of the exact known-witness normalizer run. -/
theorem description_runsFrom_known
    (i : Index) (scratchCount finalState : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState) :
    RunsFromStateTapeEquiv description
      (knownSeekWitnessState i.finalHit) description.halt
      (knownEntryTape i scratchCount finalState)
      (preMarkerTape i (sourceMetadataTokens i)
        (knownRightPadding scratchCount
          i.sourceLayout.config.state)) := by
  rcases description_runConfig_knownTargetTape
      i scratchCount finalState hwitness with
    ⟨steps, hrun⟩
  exact ⟨steps,
    preMarkerTape i (sourceMetadataTokens i)
      (knownRightPadding scratchCount i.sourceLayout.config.state),
    hrun, Tape.Equiv.refl _⟩

end Normalizer

end GuardedEgress.MetadataWitnessStage
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
