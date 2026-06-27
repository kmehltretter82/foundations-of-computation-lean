import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner.Basic

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace DovetailInitialLayoutInitializer
namespace StageInputMarkedScanner

/-!
**Closed proof split.**  The closed direction begins with the separate marker
subroutine, whose inversion theorem exposes an arbitrary second-bit tail.  The
scanner-specific closed obligation is therefore stated against such a tail; a
separate encoding lemma turns the accepted tail back into the canonical
stage-input code.
-/

def markedTailStartConfig (tail : Word Bool) :
    Configuration :=
  { state := StageInputMarkedScannerDescription.start
    tape :=
      Tape.move Direction.right
        (tapeAtCells [some false] (none :: tail.map some)) }

theorem no_halt_of_stepConfig_none
    {D : MachineDescription} {c : Configuration}
    {T : Tape Bool}
    (hstep : D.stepConfig c = none)
    (hstate : c.state ≠ D.halt)
    (hhalt :
      exists steps : Nat,
        D.runConfig steps c = { state := D.halt, tape := T }) :
    False := by
  rcases hhalt with ⟨steps, hsteps⟩
  have hstay := runConfig_of_stepConfig_none hstep steps
  rw [hstay] at hsteps
  have hstate' : c.state = D.halt := by
    simpa using congrArg Configuration.state hsteps
  exact hstate hstate'

theorem scanner_marked_tail_false_no_halt
    {rest : Word Bool} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig (false :: rest)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    False := by
  have hstep :
      StageInputMarkedScannerDescription.stepConfig
          (markedTailStartConfig (false :: rest)) = none := by
    cases rest <;>
    simp [markedTailStartConfig, StageInputMarkedScannerDescription,
      tapeAtCells, keep, keepMove, writeMove,
      scanLeftToSentinelRestart, scanLeftToSentinelHalt,
      stepConfig, lookupTransition,
      Matches, transition,
      Tape.move, Tape.moveRight, Tape.read]
  have hstate :
      (markedTailStartConfig (false :: rest)).state ≠
        StageInputMarkedScannerDescription.halt := by
    simp [markedTailStartConfig, StageInputMarkedScannerDescription]
  exact no_halt_of_stepConfig_none hstep hstate hscanner

theorem runConfig_halt_after_prefix
    {D : MachineDescription} {c mid : Configuration}
    {T : Tape Bool} {pref : Nat}
    (hD : D.HaltTransitionFree)
    (hprefix : D.runConfig pref c = mid)
    (hmid : mid.state ≠ D.halt)
    (hhalt :
      exists steps : Nat,
        D.runConfig steps c = { state := D.halt, tape := T }) :
    exists rem : Nat,
      D.runConfig rem mid = { state := D.halt, tape := T } := by
  rcases hhalt with ⟨steps, hsteps⟩
  by_cases hle : pref ≤ steps
  · refine ⟨steps - pref, ?_⟩
    have hsteps_eq : steps = pref + (steps - pref) := by
      omega
    rw [hsteps_eq, runConfig_add] at hsteps
    rw [hprefix] at hsteps
    exact hsteps
  · let rem := pref - steps
    have hprefix_eq : pref = steps + rem := by
      omega
    have hprefix_halt :
        D.runConfig pref c = { state := D.halt, tape := T } := by
      rw [hprefix_eq, runConfig_add, hsteps]
      exact runConfig_halt hD T rem
    rw [hprefix] at hprefix_halt
    have hstate : mid.state = D.halt := by
      simpa using
        congrArg Configuration.state hprefix_halt
    exact False.elim (hmid hstate)

theorem runConfig_halt_tape_functional_from_config
    {D : MachineDescription} {c : Configuration}
    {T₁ T₂ : Tape Bool} {n₁ n₂ : Nat}
    (hD : D.HaltTransitionFree)
    (h₁ :
      D.runConfig n₁ c =
        { state := D.halt, tape := T₁ })
    (h₂ :
      D.runConfig n₂ c =
        { state := D.halt, tape := T₂ }) :
    T₁ = T₂ :=
  MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
    hD h₁ h₂

theorem scanner_state_ne_halt_of_later_ne_halt
    {c : Configuration} {n k : Nat}
    (hle : n ≤ k)
    (hlater :
      (StageInputMarkedScannerDescription.runConfig k c).state ≠
        StageInputMarkedScannerDescription.halt) :
    (StageInputMarkedScannerDescription.runConfig n c).state ≠
      StageInputMarkedScannerDescription.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_later_ne_halt
    stageInputMarkedScannerDescription_haltTransitionFree hle hlater

theorem scanner_ne_halt_of_reaches_stuck
    {c stuck : Configuration} {k n : Nat}
    (hrun :
      StageInputMarkedScannerDescription.runConfig k c = stuck)
    (hstep :
      StageInputMarkedScannerDescription.stepConfig stuck = none)
    (hstuck :
      stuck.state ≠ StageInputMarkedScannerDescription.halt) :
    (StageInputMarkedScannerDescription.runConfig n c).state ≠
      StageInputMarkedScannerDescription.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
    stageInputMarkedScannerDescription_haltTransitionFree hrun hstep hstuck

theorem scanner_ne_halt_of_reaches_stepConfig_none
    {c : Configuration} {k n : Nat}
    (hstep :
      StageInputMarkedScannerDescription.stepConfig
        (StageInputMarkedScannerDescription.runConfig k c) = none)
    (hstate :
      (StageInputMarkedScannerDescription.runConfig k c).state ≠
        StageInputMarkedScannerDescription.halt) :
    (StageInputMarkedScannerDescription.runConfig n c).state ≠
      StageInputMarkedScannerDescription.halt := by
  exact
    scanner_ne_halt_of_reaches_stuck
      (k := k)
      (stuck := StageInputMarkedScannerDescription.runConfig k c)
      rfl hstep hstate

theorem scanner_ne_halt_of_reaches_ne_halt_region
    {c mid : Configuration} {k n : Nat}
    (hrun :
      StageInputMarkedScannerDescription.runConfig k c = mid)
    (hmid :
      forall m : Nat,
        (StageInputMarkedScannerDescription.runConfig m mid).state ≠
          StageInputMarkedScannerDescription.halt) :
    (StageInputMarkedScannerDescription.runConfig n c).state ≠
      StageInputMarkedScannerDescription.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_ne_halt_region
    stageInputMarkedScannerDescription_haltTransitionFree hrun hmid

/-!
**Closed-tail inversion.**  The scanner accepts some arbitrary bit tails that
cannot arise from an encoded code word.  The shape inversion is therefore stated
with the code-level origin of the marked tail, while the tape inversion remains
separate and only needs the recovered canonical tail equality.
-/

theorem scanner_marked_code_tail_first_symbol_inv
    {code : Word MachineCodeSymbol} {tail : Word Bool} {T : Tape Bool}
    (hbits :
      encodeCodeWordAsInput code =
        false :: false :: tail)
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    (exists rest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.tick :: rest ∧
        tail = true :: false ::
          encodeCodeWordAsInput rest) ∨
    (exists rest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.done :: rest ∧
        tail = true :: true ::
          encodeCodeWordAsInput rest) := by
  cases code with
  | nil =>
      simp [encodeCodeWordAsInput] at hbits
  | cons symbol rest =>
      cases symbol
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        have htail :
            tail = false :: false ::
              encodeCodeWordAsInput rest := by
          injection hbits with _ h1
          injection h1 with _ h2
          exact h2.symm
        subst tail
        exact False.elim (scanner_marked_tail_false_no_halt hscanner)
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        have htail :
            tail = false :: true ::
              encodeCodeWordAsInput rest := by
          injection hbits with _ h1
          injection h1 with _ h2
          exact h2.symm
        subst tail
        exact False.elim (scanner_marked_tail_false_no_halt hscanner)
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        have htail :
            tail = true :: false ::
              encodeCodeWordAsInput rest := by
          injection hbits with _ h1
          injection h1 with _ h2
          exact h2.symm
        exact Or.inl ⟨rest, rfl, htail⟩
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        have htail :
            tail = true :: true ::
              encodeCodeWordAsInput rest := by
          injection hbits with _ h1
          injection h1 with _ h2
          exact h2.symm
        exact Or.inr ⟨rest, rfl, htail⟩
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        injection hbits with _ htail
        injection htail with hbad
        cases hbad
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        injection hbits with _ htail
        injection htail with hbad
        cases hbad
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        injection hbits with _ htail
        injection htail with hbad
        cases hbad
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        injection hbits with _ htail
        injection htail with hbad
        cases hbad
      · simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hbits
        injection hbits with hhead
        cases hhead

theorem stageInputBits_tick_code_eq
    {rest : Word MachineCodeSymbol} {w : Word Bool}
    {stage : Nat}
    (hcode :
      MachineCodeSymbol.tick :: rest =
        PairedRecognizerDovetailStageInputCode w stage) :
    stageInputBits w stage =
      false :: false :: true :: false ::
        encodeCodeWordAsInput rest := by
  rw [stageInputBits, ← hcode]
  rfl

theorem run_marked_tail_tick_to_state120
    (bits : Word Bool) :
    StageInputMarkedScannerDescription.runConfig 6
        (markedTailStartConfig (true :: false :: bits)) =
      config 120 [none, some true, none, some false]
        (bits.map some) := by
  simp [markedTailStartConfig, StageInputMarkedScannerDescription,
    config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]
  generalize bits.map some = cells
  cases cells <;> rfl

theorem run_marked_tail_done_stageNat_to_state200
    (stage : Nat) (suffixBits : Word Bool) :
    StageInputMarkedScannerDescription.runConfig 18
        (markedTailStartConfig
          (true :: true ::
            List.append (stageNatBits stage) suffixBits)) =
      config 200 [some true, some true, none, some false]
        (List.append ((stageNatBits stage).map some)
          (suffixBits.map some)) := by
  cases stage <;>
  simp [markedTailStartConfig, StageInputMarkedScannerDescription,
    stageNatBits, encodeNat,
    encodeCodeWordAsInput,
    encodeCodeSymbolAsInput, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem run_marked_tail_done_false_false_to_state200
    (tail : Word Bool) :
    StageInputMarkedScannerDescription.runConfig 18
        (markedTailStartConfig
          (true :: true :: false :: false :: tail)) =
      config 200 [some true, some true, none, some false]
        (some false :: some false :: tail.map some) := by
  simp [markedTailStartConfig, StageInputMarkedScannerDescription,
    config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem state120_natPrefixFailure_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 120 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      StageInputMarkedScannerDescription.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        scanner_ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            rfl)
          (by
            change (120 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (122 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (122 : Nat) ≠ 999
                omega)
      | tick =>
          simp [decodeNat] at hdecode
          cases hrest : decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                scanner_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 120
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput] using
                  run_state120_tick leftRev
                    ((encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | one =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (120 : Nat) ≠ 999
                omega)

theorem run_state120_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 120 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      StageInputMarkedScannerDescription.halt :=
  state120_natPrefixFailure_ne_halt tokens leftRev hdecode n

theorem state130_cellPrefixFailure_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeCell tokens = none) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 130 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      StageInputMarkedScannerDescription.halt := by
  cases tokens with
  | nil =>
      exact
        scanner_ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            rfl)
          (by
            change (130 : Nat) ≠ 999
            omega)
  | cons symbol rest =>
      cases symbol with
      | header =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | done =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | blank =>
          simp [decodeCell] at hdecode
      | zero =>
          simp [decodeCell] at hdecode
      | one =>
          simp [decodeCell] at hdecode
      | moveLeft =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 5) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (145 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (135 : Nat) ≠ 999
                omega)

theorem run_state130_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeCell tokens = none) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 130 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      StageInputMarkedScannerDescription.halt :=
  state130_cellPrefixFailure_ne_halt tokens leftRev hdecode n

theorem run_state130_blank_cell_ne_halt
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 130 leftRev
        ((encodeCodeWordAsInput
          (encodeCellAppend none suffix)).map some))).state ≠
      StageInputMarkedScannerDescription.halt := by
  exact
    scanner_ne_halt_of_reaches_stepConfig_none
      (k := 5) (by
        cases suffix <;>
        simp [StageInputMarkedScannerDescription, config, tapeAtCells,
          keep, keepMove, writeMove, scanLeftToSentinelRestart,
          scanLeftToSentinelHalt,
          runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, encodeCellAppend,
          encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight])
      (by
        change (139 : Nat) ≠ 999
        omega)

def markingTailConfig
    (marked : Word Bool) (remainingCells : Nat)
    (tokens : Word MachineCodeSymbol) :
    Configuration :=
  config 120 (activeLengthPrefixRev marked.length)
    (List.append ((stageNatBits (remainingCells - 1)).map some)
      (List.append ((markedCellsBits marked).map some)
        ((encodeCodeWordAsInput tokens).map some)))

def markingTailPayloadLeftRev
    (marked : Word Bool) (remainingLengthTail : Nat) :
    List (Option Bool) :=
  List.append ((markedCellsBits marked).reverse.map some)
    (List.append ((stageNatBits remainingLengthTail).reverse.map some)
      (activeLengthPrefixRev marked.length))

def markingTailReturnScanRev
    (marked : Word Bool) (remainingLengthTail : Nat) :
    Word Bool :=
  List.append [true, true]
    (List.append (markedCellsBits marked).reverse
      (stageNatBits remainingLengthTail).reverse)

theorem run_marking_tail_to_first_payload
    (marked : Word Bool) (remainingLengthTail : Nat)
    (tokens : Word MachineCodeSymbol) :
    StageInputMarkedScannerDescription.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (markingTailConfig marked (remainingLengthTail + 1) tokens) =
      config 130
        (markingTailPayloadLeftRev marked remainingLengthTail)
        ((encodeCodeWordAsInput tokens).map some) := by
  unfold markingTailConfig markingTailPayloadLeftRev
  change
    StageInputMarkedScannerDescription.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (config 120 (activeLengthPrefixRev marked.length)
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append ((markedCellsBits marked).map some)
              ((encodeCodeWordAsInput tokens).map
                some)))) =
      config 130
        (List.append ((markedCellsBits marked).reverse.map some)
          (List.append ((stageNatBits remainingLengthTail).reverse.map some)
            (activeLengthPrefixRev marked.length)))
        ((encodeCodeWordAsInput tokens).map some)
  rw [runConfig_add]
  rw [run_state120_stageNat]
  rw [run_state130_markedCells]

theorem run_marking_tail_mark_one
    (marked : Word Bool) (remainingLengthTail : Nat)
    (b : Bool) (restAfterCell : Word MachineCodeSymbol) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markingTailConfig marked (remainingLengthTail + 2)
            (encodeCellAppend (some b) restAfterCell)) =
        markingTailConfig (List.append marked [b])
          (remainingLengthTail + 1) restAfterCell := by
  let scanRev := markingTailReturnScanRev marked (remainingLengthTail + 1)
  refine
    ⟨((4 * (remainingLengthTail + 1) + 4) +
        4 * marked.length) +
        ((6 + (scanRev.length + 4)) + 4), ?_⟩
  rw [runConfig_add]
  rw [run_marking_tail_to_first_payload]
  rw [show 6 + (scanRev.length + 4) + 4 =
      6 + ((scanRev.length + 4) + 4) by omega]
  rw [runConfig_add]
  have hcellBits :
      (encodeCodeWordAsInput
          (encodeCellAppend (some b) restAfterCell)).map
        some =
      List.append ((cellBits b).map some)
        ((encodeCodeWordAsInput restAfterCell).map
          some) := by
    cases b <;>
    simp [encodeCellAppend,
      encodeCell,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput, cellBits]
  rw [hcellBits]
  change
    StageInputMarkedScannerDescription.runConfig
        ((scanRev.length + 4) + 4)
        (StageInputMarkedScannerDescription.runConfig 6
          (config 130
            (markingTailPayloadLeftRev marked (remainingLengthTail + 1))
            (List.append ((cellBits b).map some)
              ((encodeCodeWordAsInput
                restAfterCell).map some)))) =
      markingTailConfig (List.append marked [b])
        (remainingLengthTail + 1) restAfterCell
  rw [run_state130_currentCell]
  rw [runConfig_add]
  have hleft :
      some true :: some true ::
          markingTailPayloadLeftRev marked (remainingLengthTail + 1) =
        List.append (scanRev.map some)
          (none :: some true :: activeLengthPrefixTail marked.length) := by
    simp [scanRev, markingTailReturnScanRev,
      markingTailPayloadLeftRev, activeLengthPrefixRev,
      List.map_append, List.append_assoc]
  rw [hleft]
  rw [run_state140_returnToLengthMarker]
  have hright :
      List.append (scanRev.reverse.map some)
          (some b :: some (!b) ::
            (encodeCodeWordAsInput restAfterCell).map
              some) =
        List.append (tickBits.map some)
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append
              ((markedCellsBits (List.append marked [b])).map some)
              ((encodeCodeWordAsInput restAfterCell).map
                some))) := by
    cases b
    · rw [markedCellsBits_append_single_map marked false]
      simp [scanRev, markingTailReturnScanRev,
        markedCellBits, stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
    · rw [markedCellsBits_append_single_map marked true]
      simp [scanRev, markingTailReturnScanRev,
        markedCellBits, stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
  rw [hright]
  rw [run_state100_tick]
  have hleftNext :
      List.append markedTickRev
          (some false :: some true ::
            activeLengthPrefixTail marked.length) =
        activeLengthPrefixRev (List.append marked [b]).length := by
    rw [show (List.append marked [b]).length =
        marked.length + 1 by simp]
    rw [activeLengthPrefixRev_succ]
    rw [activeLengthPrefixRestored]
  unfold markingTailConfig
  rw [hleftNext]
  simp

theorem markingTail_cellListFailure_ne_halt
    (marked : Word Bool) (remainingCells : Nat)
    (tokens : Word MachineCodeSymbol)
    (hdecode :
      decodeCells remainingCells tokens = none)
    (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (markingTailConfig marked remainingCells tokens)).state ≠
      StageInputMarkedScannerDescription.halt := by
  induction remainingCells generalizing marked tokens n with
  | zero =>
      simp [decodeCells] at hdecode
  | succ remainingTail ih =>
      cases hcell : decodeCell tokens with
      | none =>
          apply
            scanner_ne_halt_of_reaches_ne_halt_region
              (k := (4 * remainingTail + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (markingTailPayloadLeftRev marked remainingTail)
                  ((encodeCodeWordAsInput tokens).map
                    some))
          · exact
              run_marking_tail_to_first_payload
                marked remainingTail tokens
          · intro m
            exact
              run_state130_decodeCell_none_ne_halt
                tokens
                (markingTailPayloadLeftRev marked remainingTail)
                hcell m
      | some parsedCell =>
          rcases parsedCell with ⟨cell, restAfterCell⟩
          have htokens :
              tokens =
                encodeCellAppend cell restAfterCell :=
            decodeCell_eq_some_encodeCellAppend hcell
          cases cell with
          | none =>
              apply
                scanner_ne_halt_of_reaches_ne_halt_region
                  (k := (4 * remainingTail + 4) + 4 * marked.length)
                  (mid :=
                    config 130
                      (markingTailPayloadLeftRev marked remainingTail)
                      ((encodeCodeWordAsInput
                        (encodeCellAppend none
                          restAfterCell)).map some))
              · rw [htokens]
                exact
                  run_marking_tail_to_first_payload
                    marked remainingTail
                    (encodeCellAppend none restAfterCell)
              · intro m
                exact
                  run_state130_blank_cell_ne_halt
                    restAfterCell
                    (markingTailPayloadLeftRev marked remainingTail)
                    m
          | some b =>
              cases hrest :
                  decodeCells remainingTail
                    restAfterCell with
              | none =>
                  cases remainingTail with
                  | zero =>
                      simp [decodeCells, hcell]
                        at hdecode
                  | succ nextTail =>
                      rcases
                          run_marking_tail_mark_one
                            marked nextTail b restAfterCell with
                        ⟨steps, hsteps⟩
                      apply
                        scanner_ne_halt_of_reaches_ne_halt_region
                          (k := steps)
                          (mid :=
                            markingTailConfig (List.append marked [b])
                              (nextTail + 1) restAfterCell)
                      · rw [htokens]
                        exact hsteps
                      · intro m
                        exact
                          ih (List.append marked [b])
                            restAfterCell hrest m
              | some parsedRest =>
                  simp [decodeCells, hcell, hrest]
                    at hdecode

theorem run_marking_tail_decodeCells_none_ne_halt
    (marked : Word Bool) (remainingCells : Nat)
    (tokens : Word MachineCodeSymbol)
    (hdecode :
      decodeCells remainingCells tokens = none)
    (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (markingTailConfig marked remainingCells tokens)).state ≠
      StageInputMarkedScannerDescription.halt :=
  markingTail_cellListFailure_ne_halt marked remainingCells tokens hdecode n

theorem markingTail_boolWordFailure_ne_halt
    (marked : Word Bool) (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol)
    (hword : cellsToWord? cells = none)
    (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (markingTailConfig marked cells.length
        (encodeCellsAppend cells suffix))).state ≠
      StageInputMarkedScannerDescription.halt := by
  induction cells generalizing marked suffix n with
  | nil =>
      simp [cellsToWord?] at hword
  | cons cell rest ih =>
      cases cell with
      | none =>
          apply
            scanner_ne_halt_of_reaches_ne_halt_region
              (k := (4 * rest.length + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (markingTailPayloadLeftRev marked rest.length)
                  ((encodeCodeWordAsInput
                    (encodeCellAppend none
                      (encodeCellsAppend rest
                        suffix))).map some))
          · change
              StageInputMarkedScannerDescription.runConfig
                  ((4 * rest.length + 4) + 4 * marked.length)
                  (markingTailConfig marked (rest.length + 1)
                    (encodeCellAppend none
                      (encodeCellsAppend rest suffix))) =
                config 130
                  (markingTailPayloadLeftRev marked rest.length)
                  ((encodeCodeWordAsInput
                    (encodeCellAppend none
                      (encodeCellsAppend rest
                        suffix))).map some)
            exact
              run_marking_tail_to_first_payload
                marked rest.length
                (encodeCellAppend none
                  (encodeCellsAppend rest suffix))
          · intro m
            exact
              run_state130_blank_cell_ne_halt
                (encodeCellsAppend rest suffix)
                (markingTailPayloadLeftRev marked rest.length)
                m
      | some b =>
          cases hrest : cellsToWord? rest with
          | none =>
              cases rest with
              | nil =>
                  simp [cellsToWord?] at hrest
              | cons nextCell restTail =>
                  rcases
                      run_marking_tail_mark_one
                        marked restTail.length b
                        (encodeCellsAppend
                          (nextCell :: restTail) suffix) with
                    ⟨steps, hsteps⟩
                  apply
                    scanner_ne_halt_of_reaches_ne_halt_region
                      (k := steps)
                      (mid :=
                        markingTailConfig (List.append marked [b])
                          (restTail.length + 1)
                          (encodeCellsAppend
                            (nextCell :: restTail) suffix))
                  · change
                      StageInputMarkedScannerDescription.runConfig steps
                        (markingTailConfig marked (restTail.length + 2)
                          (encodeCellAppend (some b)
                            (encodeCellsAppend
                              (nextCell :: restTail) suffix))) =
                        markingTailConfig (List.append marked [b])
                          (restTail.length + 1)
                          (encodeCellsAppend
                            (nextCell :: restTail) suffix)
                    exact hsteps
                  · intro m
                    exact
                      ih (List.append marked [b]) suffix hrest m
          | some decoded =>
              simp [cellsToWord?, hrest] at hword

theorem run_marking_tail_cellsToWord_none_ne_halt
    (marked : Word Bool) (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol)
    (hword : cellsToWord? cells = none)
    (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (markingTailConfig marked cells.length
        (encodeCellsAppend cells suffix))).state ≠
      StageInputMarkedScannerDescription.halt :=
  markingTail_boolWordFailure_ne_halt marked cells suffix hword n

theorem state120_boolWordFailure_ne_halt
    (rest : Word MachineCodeSymbol)
    (hdecode :
      decodeBoolWord
        (MachineCodeSymbol.tick :: rest) = none)
    (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 120 [none, some true, none, some false]
        ((encodeCodeWordAsInput rest).map some))).state ≠
      StageInputMarkedScannerDescription.halt := by
  cases hnat : decodeNat rest with
  | none =>
      exact
        run_state120_decodeNat_none_ne_halt
          rest [none, some true, none, some false] hnat n
  | some parsedNat =>
      rcases parsedNat with ⟨remainingTail, tokensAfterLen⟩
      have hrest :
          rest =
            encodeNatAppend
              remainingTail tokensAfterLen :=
        decodeNat_eq_some_encodeNatAppend hnat
      rw [hrest]
      change
        (StageInputMarkedScannerDescription.runConfig n
          (config 120 [none, some true, none, some false]
            (List.map some
              (encodeCodeWordAsInput
                (encodeNatAppend remainingTail
                  tokensAfterLen))))).state ≠
          StageInputMarkedScannerDescription.halt
      unfold encodeNatAppend
      rw [encodeCodeWordAsInput_append]
      have hbits :
          List.map some
              (List.append
                (encodeCodeWordAsInput
                  (encodeNat remainingTail))
                (encodeCodeWordAsInput tokensAfterLen)) =
            List.append ((stageNatBits remainingTail).map some)
              ((encodeCodeWordAsInput tokensAfterLen).map
                some) := by
        simp [stageNatBits, List.map_append]
      rw [hbits]
      change
        (StageInputMarkedScannerDescription.runConfig n
          (markingTailConfig ([] : Word Bool)
            (remainingTail + 1) tokensAfterLen)).state ≠
          StageInputMarkedScannerDescription.halt
      cases hcells :
          decodeCells (remainingTail + 1)
            tokensAfterLen with
      | none =>
          exact
            run_marking_tail_decodeCells_none_ne_halt
              ([] : Word Bool) (remainingTail + 1)
              tokensAfterLen hcells n
      | some parsedCells =>
          rcases parsedCells with ⟨cells, suffix⟩
          cases hword : cellsToWord? cells with
          | none =>
              have hcellsShape :
                  remainingTail + 1 = cells.length ∧
                    tokensAfterLen =
                      encodeCellsAppend cells suffix :=
                decodeCells_eq_some_encodeCellsAppend
                  hcells
              rw [hcellsShape.left, hcellsShape.right]
              exact
                run_marking_tail_cellsToWord_none_ne_halt
                  ([] : Word Bool) cells suffix hword n
          | some decoded =>
              simp [decodeBoolWord,
                decodeCellList,
                decodeNat, hnat, hcells, hword]
                at hdecode

theorem run_state120_decodeBoolWord_none_ne_halt
    (rest : Word MachineCodeSymbol)
    (hdecode :
      decodeBoolWord
        (MachineCodeSymbol.tick :: rest) = none)
    (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 120 [none, some true, none, some false]
        ((encodeCodeWordAsInput rest).map some))).state ≠
      StageInputMarkedScannerDescription.halt :=
  state120_boolWordFailure_ne_halt rest hdecode n

theorem run_state200_done_to_state210
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 4
        (config 200 left
          (List.append (doneBits.map some) right)) =
      config 210 (List.append (doneBits.reverse.map some) left)
        right := by
  cases right <;>
  simp [StageInputMarkedScannerDescription, doneBits, config,
    tapeAtCells, keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig (4 * stage + 4)
        (config 200 left
          (List.append ((stageNatBits stage).map some) right)) =
      config 210
        (List.append ((stageNatBits stage).reverse.map some) left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using
        run_state200_done_to_state210 left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 =
          4 + (4 * stage + 4) by omega]
      rw [runConfig_add]
      rw [show
          (stageNatBits (stage + 1)).map some =
            List.append (tickBits.map some)
              ((stageNatBits stage).map some) by
          simp [stageNatBits_succ, tickBits,
            encodeCodeSymbolAsInput]]
      change
        StageInputMarkedScannerDescription.runConfig
            (4 * stage + 4)
            (StageInputMarkedScannerDescription.runConfig 4
              (config 200 left
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits stage).map some) right)))) =
          config 210
            (List.append ((stageNatBits (stage + 1)).reverse.map some)
              left)
            right
      rw [run_state200_tick]
      have h := ih
        (List.append (tickBits.reverse.map some) left)
      simpa [stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc] using h

theorem run_state210_encoded_cons_ne_halt
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 210 leftRev
        ((encodeCodeWordAsInput
          (symbol :: rest)).map some))).state ≠
      StageInputMarkedScannerDescription.halt := by
  exact
    scanner_ne_halt_of_reaches_stepConfig_none
      (k := 0) (by
        cases symbol <;>
        simp [StageInputMarkedScannerDescription, config, tapeAtCells,
          keep, keepMove, writeMove, scanLeftToSentinelRestart,
          scanLeftToSentinelHalt,
          runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read])
      (by
        change (210 : Nat) ≠ 999
        omega)

theorem run_state200_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 200 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      StageInputMarkedScannerDescription.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        scanner_ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            rfl)
          (by
            change (200 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                omega)
      | tick =>
          simp [decodeNat] at hdecode
          cases hrest : decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                scanner_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 200
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput] using
                  run_state200_tick leftRev
                    ((encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | one =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                cases rest <;>
                simp [StageInputMarkedScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (200 : Nat) ≠ 999
                omega)

theorem state200_nonemptySuffixFailure_ne_halt
    (stage : Nat) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 200 leftRev
        ((encodeCodeWordAsInput
          (encodeNatAppend stage
            (symbol :: suffix))).map some))).state ≠
      StageInputMarkedScannerDescription.halt := by
  apply
    scanner_ne_halt_of_reaches_ne_halt_region
      (k := 4 * stage + 4)
      (mid :=
        config 210
          (List.append ((stageNatBits stage).reverse.map some) leftRev)
          ((encodeCodeWordAsInput
            (symbol :: suffix)).map some))
  · have hbits :
        (encodeCodeWordAsInput
            (encodeNatAppend stage
              (symbol :: suffix))).map some =
          List.append ((stageNatBits stage).map some)
            ((encodeCodeWordAsInput
              (symbol :: suffix)).map some) := by
        change
          List.map some
              (encodeCodeWordAsInput
                (List.append (encodeNat stage)
                  (symbol :: suffix))) =
            List.append
              (List.map some
                (encodeCodeWordAsInput
                  (encodeNat stage)))
              (List.map some
                (encodeCodeWordAsInput
                  (symbol :: suffix)))
        rw [encodeCodeWordAsInput_append]
        simp [List.map_append]
    rw [hbits]
    exact
      run_state200_stageNat_to_state210 stage leftRev
        ((encodeCodeWordAsInput
          (symbol :: suffix)).map some)
  · intro m
    exact run_state210_encoded_cons_ne_halt symbol suffix
      (List.append ((stageNatBits stage).reverse.map some) leftRev) m

theorem run_state200_stageNat_suffix_ne_halt
    (stage : Nat) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (config 200 leftRev
        ((encodeCodeWordAsInput
          (encodeNatAppend stage
            (symbol :: suffix))).map some))).state ≠
      StageInputMarkedScannerDescription.halt :=
  state200_nonemptySuffixFailure_ne_halt stage symbol suffix leftRev n

theorem state200_code_tail_nat_inv
    {rest : Word MachineCodeSymbol} {leftRev : List (Option Bool)}
    {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (config 200 leftRev
              ((encodeCodeWordAsInput rest).map some)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists stage : Nat,
      rest = encodeNat stage := by
  rcases hscanner with ⟨steps, hsteps⟩
  cases hdecode : decodeNat rest with
  | none =>
      have hne :=
        run_state200_decodeNat_none_ne_halt rest leftRev hdecode steps
      have hstate :
          (StageInputMarkedScannerDescription.runConfig steps
            (config 200 leftRev
              ((encodeCodeWordAsInput rest).map some))).state =
            StageInputMarkedScannerDescription.halt := by
        simpa using
          congrArg Configuration.state hsteps
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨stage, suffix⟩
      have hrest :
          rest = encodeNatAppend stage suffix :=
        decodeNat_eq_some_encodeNatAppend hdecode
      cases suffix with
      | nil =>
          exact ⟨stage, by
            simpa [encodeNatAppend] using hrest⟩
      | cons symbol suffixTail =>
          rw [hrest] at hsteps
          have hne :=
            state200_nonemptySuffixFailure_ne_halt
              stage symbol suffixTail leftRev steps
          have hstate :
              (StageInputMarkedScannerDescription.runConfig steps
                (config 200 leftRev
                  ((encodeCodeWordAsInput
                    (encodeNatAppend stage
                      (symbol :: suffixTail))).map some))).state =
                StageInputMarkedScannerDescription.halt := by
            simpa using
              congrArg Configuration.state hsteps
          exact False.elim (hne hstate)

theorem state120_tick_tail_decodeBoolWord_inv
    {rest : Word MachineCodeSymbol} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (config 120 [none, some true, none, some false]
              ((encodeCodeWordAsInput rest).map some)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists suffix : Word MachineCodeSymbol,
      decodeBoolWord
          (MachineCodeSymbol.tick :: rest) =
        some (w, suffix) := by
  rcases hscanner with ⟨steps, hsteps⟩
  cases hdecode :
      decodeBoolWord
        (MachineCodeSymbol.tick :: rest) with
  | none =>
      have hne :=
        run_state120_decodeBoolWord_none_ne_halt
          rest hdecode steps
      have hstate :
          (StageInputMarkedScannerDescription.runConfig steps
            (config 120 [none, some true, none, some false]
              ((encodeCodeWordAsInput rest).map
                some))).state =
            StageInputMarkedScannerDescription.halt := by
        simpa using
          congrArg Configuration.state hsteps
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨w, suffix⟩
      exact ⟨w, suffix, rfl⟩


end StageInputMarkedScanner
end DovetailInitialLayoutInitializer
end Computability
end FoC
