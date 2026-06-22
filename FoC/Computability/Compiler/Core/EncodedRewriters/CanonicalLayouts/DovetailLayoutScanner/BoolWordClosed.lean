import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWord

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open DovetailInitialLayoutInitializer

namespace EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner

/-!
**Closed proof split.**  The closed direction begins with the separate marker
subroutine, whose inversion theorem exposes an arbitrary second-bit tail.  The
scanner-specific closed obligation is therefore stated against such a tail; a
separate encoding lemma turns the accepted tail back into the canonical
stage-input code.
-/

def markedTailStartConfig (tail : Word Bool) :
    MachineDescription.Configuration :=
  { state := BoolWordSuffixScannerDescription.start
    tape :=
      Tape.move Direction.right
        (tapeAtCells [some false] (none :: tail.map some)) }

theorem no_halt_of_stepConfig_none
    {D : MachineDescription} {c : MachineDescription.Configuration}
    {T : Tape Bool}
    (hstep : D.stepConfig c = none)
    (hstate : c.state ≠ D.halt)
    (hhalt :
      exists steps : Nat,
        D.runConfig steps c = { state := D.halt, tape := T }) :
    False := by
  rcases hhalt with ⟨steps, hsteps⟩
  have hstay := MachineDescription.runConfig_of_stepConfig_none hstep steps
  rw [hstay] at hsteps
  have hstate' : c.state = D.halt := by
    simpa using congrArg MachineDescription.Configuration.state hsteps
  exact hstate hstate'

theorem scanner_marked_tail_false_no_halt
    {rest : Word Bool} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        BoolWordSuffixScannerDescription.runConfig steps
            (markedTailStartConfig (false :: rest)) =
          { state := BoolWordSuffixScannerDescription.halt
            tape := T }) :
    False := by
  have hstep :
      BoolWordSuffixScannerDescription.stepConfig
          (markedTailStartConfig (false :: rest)) = none := by
    cases rest <;>
    simp [markedTailStartConfig, BoolWordSuffixScannerDescription,
      tapeAtCells, keep, keepMove, writeMove,
      scanLeftToSentinelRestart, scanLeftToSentinelHalt,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition,
      Tape.move, Tape.moveRight, Tape.read]
  have hstate :
      (markedTailStartConfig (false :: rest)).state ≠
        BoolWordSuffixScannerDescription.halt := by
    simp [markedTailStartConfig, BoolWordSuffixScannerDescription]
  exact no_halt_of_stepConfig_none hstep hstate hscanner

theorem runConfig_halt_after_prefix
    {D : MachineDescription} {c mid : MachineDescription.Configuration}
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
    rw [hsteps_eq, MachineDescription.runConfig_add] at hsteps
    rw [hprefix] at hsteps
    exact hsteps
  · let rem := pref - steps
    have hprefix_eq : pref = steps + rem := by
      omega
    have hprefix_halt :
        D.runConfig pref c = { state := D.halt, tape := T } := by
      rw [hprefix_eq, MachineDescription.runConfig_add, hsteps]
      exact MachineDescription.runConfig_halt hD T rem
    rw [hprefix] at hprefix_halt
    have hstate : mid.state = D.halt := by
      simpa using
        congrArg MachineDescription.Configuration.state hprefix_halt
    exact False.elim (hmid hstate)

theorem runConfig_halt_tape_functional_from_config
    {D : MachineDescription} {c : MachineDescription.Configuration}
    {T₁ T₂ : Tape Bool} {n₁ n₂ : Nat}
    (hD : D.HaltTransitionFree)
    (h₁ :
      D.runConfig n₁ c =
        { state := D.halt, tape := T₁ })
    (h₂ :
      D.runConfig n₂ c =
        { state := D.halt, tape := T₂ }) :
    T₁ = T₂ := by
  have hordered :
      forall {n m : Nat} {Tn Tm : Tape Bool},
        n ≤ m ->
        D.runConfig n c = { state := D.halt, tape := Tn } ->
        D.runConfig m c = { state := D.halt, tape := Tm } ->
          Tn = Tm := by
    intro n m Tn Tm hle hn hm
    let d := m - n
    have hm_eq : m = n + d := by
      omega
    have hrunm :
        D.runConfig m c =
          D.runConfig d (D.runConfig n c) := by
      rw [hm_eq, MachineDescription.runConfig_add]
    have hstay :
        D.runConfig d (D.runConfig n c) =
          D.runConfig n c := by
      rw [hn]
      exact MachineDescription.runConfig_halt hD Tn d
    have htape_m :
        (D.runConfig m c).tape = Tn := by
      rw [hrunm, hstay, hn]
    have htm : (D.runConfig m c).tape = Tm := by
      rw [hm]
    rw [htm] at htape_m
    exact htape_m.symm
  by_cases hle : n₁ ≤ n₂
  · exact hordered hle h₁ h₂
  · have hle' : n₂ ≤ n₁ := by omega
    exact (hordered hle' h₂ h₁).symm

theorem scanner_state_ne_halt_of_later_ne_halt
    {c : MachineDescription.Configuration} {n k : Nat}
    (hle : n ≤ k)
    (hlater :
      (BoolWordSuffixScannerDescription.runConfig k c).state ≠
        BoolWordSuffixScannerDescription.halt) :
    (BoolWordSuffixScannerDescription.runConfig n c).state ≠
      BoolWordSuffixScannerDescription.halt := by
  intro hhalt
  have hk : k = n + (k - n) := by omega
  have hcfg :
      BoolWordSuffixScannerDescription.runConfig n c =
        { state := BoolWordSuffixScannerDescription.halt
          tape :=
            (BoolWordSuffixScannerDescription.runConfig n c).tape } := by
    cases hrunN :
        BoolWordSuffixScannerDescription.runConfig n c with
    | mk state tape =>
        simp [hrunN] at hhalt
        simp [hhalt]
  have hfinal :
      (BoolWordSuffixScannerDescription.runConfig k c).state =
        BoolWordSuffixScannerDescription.halt := by
    rw [hk, MachineDescription.runConfig_add, hcfg,
      MachineDescription.runConfig_halt
        boolWordSuffixScannerDescription_haltTransitionFree]
  exact hlater hfinal

theorem scanner_ne_halt_of_reaches_stuck
    {c stuck : MachineDescription.Configuration} {k n : Nat}
    (hrun :
      BoolWordSuffixScannerDescription.runConfig k c = stuck)
    (hstep :
      BoolWordSuffixScannerDescription.stepConfig stuck = none)
    (hstuck :
      stuck.state ≠ BoolWordSuffixScannerDescription.halt) :
    (BoolWordSuffixScannerDescription.runConfig n c).state ≠
      BoolWordSuffixScannerDescription.halt := by
  by_cases hle : n ≤ k
  · apply scanner_state_ne_halt_of_later_ne_halt hle
    rw [hrun]
    exact hstuck
  · have hn : n = k + (n - k) := by omega
    rw [hn, MachineDescription.runConfig_add, hrun,
      MachineDescription.runConfig_of_stepConfig_none hstep]
    exact hstuck

theorem scanner_ne_halt_of_reaches_stepConfig_none
    {c : MachineDescription.Configuration} {k n : Nat}
    (hstep :
      BoolWordSuffixScannerDescription.stepConfig
        (BoolWordSuffixScannerDescription.runConfig k c) = none)
    (hstate :
      (BoolWordSuffixScannerDescription.runConfig k c).state ≠
        BoolWordSuffixScannerDescription.halt) :
    (BoolWordSuffixScannerDescription.runConfig n c).state ≠
      BoolWordSuffixScannerDescription.halt := by
  exact
    scanner_ne_halt_of_reaches_stuck
      (k := k)
      (stuck := BoolWordSuffixScannerDescription.runConfig k c)
      rfl hstep hstate

theorem scanner_ne_halt_of_reaches_ne_halt_region
    {c mid : MachineDescription.Configuration} {k n : Nat}
    (hrun :
      BoolWordSuffixScannerDescription.runConfig k c = mid)
    (hmid :
      forall m : Nat,
        (BoolWordSuffixScannerDescription.runConfig m mid).state ≠
          BoolWordSuffixScannerDescription.halt) :
    (BoolWordSuffixScannerDescription.runConfig n c).state ≠
      BoolWordSuffixScannerDescription.halt := by
  by_cases hle : n ≤ k
  · apply scanner_state_ne_halt_of_later_ne_halt hle
    rw [hrun]
    exact hmid 0
  · have hn : n = k + (n - k) := by omega
    rw [hn, MachineDescription.runConfig_add, hrun]
    exact hmid (n - k)

/-!
**Closed-tail inversion.**  The scanner accepts some arbitrary bit tails that
cannot arise from an encoded code word.  The shape inversion is therefore stated
with the code-level origin of the marked tail, while the tape inversion remains
separate and only needs the recovered canonical tail equality.
-/

theorem scanner_marked_code_tail_first_symbol_inv
    {code : Word MachineCodeSymbol} {tail : Word Bool} {T : Tape Bool}
    (hbits :
      MachineDescription.encodeCodeWordAsInput code =
        false :: false :: tail)
    (hscanner :
      exists steps : Nat,
        BoolWordSuffixScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := BoolWordSuffixScannerDescription.halt
            tape := T }) :
    (exists rest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.tick :: rest ∧
        tail = true :: false ::
          MachineDescription.encodeCodeWordAsInput rest) ∨
    (exists rest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.done :: rest ∧
        tail = true :: true ::
          MachineDescription.encodeCodeWordAsInput rest) := by
  cases code with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput] at hbits
  | cons symbol rest =>
      cases symbol
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
        have htail :
            tail = false :: false ::
              MachineDescription.encodeCodeWordAsInput rest := by
          injection hbits with _ h1
          injection h1 with _ h2
          exact h2.symm
        subst tail
        exact False.elim (scanner_marked_tail_false_no_halt hscanner)
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
        have htail :
            tail = false :: true ::
              MachineDescription.encodeCodeWordAsInput rest := by
          injection hbits with _ h1
          injection h1 with _ h2
          exact h2.symm
        subst tail
        exact False.elim (scanner_marked_tail_false_no_halt hscanner)
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
        have htail :
            tail = true :: false ::
              MachineDescription.encodeCodeWordAsInput rest := by
          injection hbits with _ h1
          injection h1 with _ h2
          exact h2.symm
        exact Or.inl ⟨rest, rfl, htail⟩
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
        have htail :
            tail = true :: true ::
              MachineDescription.encodeCodeWordAsInput rest := by
          injection hbits with _ h1
          injection h1 with _ h2
          exact h2.symm
        exact Or.inr ⟨rest, rfl, htail⟩
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
        injection hbits with _ htail
        injection htail with hbad
        cases hbad
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
        injection hbits with _ htail
        injection htail with hbad
        cases hbad
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
        injection hbits with _ htail
        injection htail with hbad
        cases hbad
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
        injection hbits with _ htail
        injection htail with hbad
        cases hbad
      · simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hbits
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
        MachineDescription.encodeCodeWordAsInput rest := by
  rw [stageInputBits, ← hcode]
  rfl

theorem run_marked_tail_tick_to_boolWordSuffix_state120
    (bits : Word Bool) :
    BoolWordSuffixScannerDescription.runConfig 6
        (markedTailStartConfig (true :: false :: bits)) =
      config 120 (none :: some true :: some false :: some false :: baseLeft)
        (bits.map some) := by
  simp [markedTailStartConfig, BoolWordSuffixScannerDescription,
    config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]
  generalize bits.map some = cells
  cases cells <;> rfl

theorem run_marked_tail_done_stageNat_to_state200
    (stage : Nat) (suffixBits : Word Bool) :
    BoolWordSuffixScannerDescription.runConfig 18
        (markedTailStartConfig
          (true :: true ::
            List.append (stageNatBits stage) suffixBits)) =
      config 200 [some true, some true, none, some false]
        (List.append ((stageNatBits stage).map some)
          (suffixBits.map some)) := by
  cases stage <;>
  simp [markedTailStartConfig, BoolWordSuffixScannerDescription,
    stageNatBits, MachineDescription.encodeNat,
    MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem run_marked_tail_done_false_false_to_state200
    (tail : Word Bool) :
    BoolWordSuffixScannerDescription.runConfig 18
        (markedTailStartConfig
          (true :: true :: false :: false :: tail)) =
      config 200 [some true, some true, none, some false]
        (some false :: some false :: tail.map some) := by
  simp [markedTailStartConfig, BoolWordSuffixScannerDescription,
    config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem run_boolWordSuffix_boolWordSuffix_state120_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 120 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
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
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (122 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (122 : Nat) ≠ 999
                omega)
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases hrest : MachineDescription.decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                scanner_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 120
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((MachineDescription.encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput] using
                  run_boolWordSuffix_boolWordSuffix_state120_tick leftRev
                    ((MachineDescription.encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | one =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (120 : Nat) ≠ 999
                omega)

theorem run_boolWordSuffix_state130_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeCell tokens = none) (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 130 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
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
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | done =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | blank =>
          simp [MachineDescription.decodeCell] at hdecode
      | zero =>
          simp [MachineDescription.decodeCell] at hdecode
      | one =>
          simp [MachineDescription.decodeCell] at hdecode
      | moveLeft =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 5) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
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
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (135 : Nat) ≠ 999
                omega)

theorem run_boolWordSuffix_state130_blank_cell_ne_halt
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 130 leftRev
        ((MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellAppend none suffix)).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  exact
    scanner_ne_halt_of_reaches_stepConfig_none
      (k := 5) (by
        cases suffix <;>
        simp [BoolWordSuffixScannerDescription, config, tapeAtCells,
          keep, keepMove, writeMove, scanLeftToSentinelRestart,
          scanLeftToSentinelHalt,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight])
      (by
        change (139 : Nat) ≠ 999
        omega)

def markingTailConfig
    (marked : Word Bool) (remainingCells : Nat)
    (tokens : Word MachineCodeSymbol) :
    MachineDescription.Configuration :=
  config 120 (activeLengthPrefixRev marked.length)
    (List.append ((stageNatBits (remainingCells - 1)).map some)
      (List.append ((markedCellsBits marked).map some)
        ((MachineDescription.encodeCodeWordAsInput tokens).map some)))

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
    BoolWordSuffixScannerDescription.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (markingTailConfig marked (remainingLengthTail + 1) tokens) =
      config 130
        (markingTailPayloadLeftRev marked remainingLengthTail)
        ((MachineDescription.encodeCodeWordAsInput tokens).map some) := by
  unfold markingTailConfig markingTailPayloadLeftRev
  change
    BoolWordSuffixScannerDescription.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (config 120 (activeLengthPrefixRev marked.length)
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append ((markedCellsBits marked).map some)
              ((MachineDescription.encodeCodeWordAsInput tokens).map
                some)))) =
      config 130
        (List.append ((markedCellsBits marked).reverse.map some)
          (List.append ((stageNatBits remainingLengthTail).reverse.map some)
            (activeLengthPrefixRev marked.length)))
        ((MachineDescription.encodeCodeWordAsInput tokens).map some)
  rw [MachineDescription.runConfig_add]
  rw [run_boolWordSuffix_boolWordSuffix_state120_stageNat]
  rw [run_boolWordSuffix_state130_markedCells]

theorem run_marking_tail_mark_one
    (marked : Word Bool) (remainingLengthTail : Nat)
    (b : Bool) (restAfterCell : Word MachineCodeSymbol) :
    exists steps : Nat,
      BoolWordSuffixScannerDescription.runConfig steps
          (markingTailConfig marked (remainingLengthTail + 2)
            (MachineDescription.encodeCellAppend (some b) restAfterCell)) =
        markingTailConfig (List.append marked [b])
          (remainingLengthTail + 1) restAfterCell := by
  let scanRev := markingTailReturnScanRev marked (remainingLengthTail + 1)
  refine
    ⟨((4 * (remainingLengthTail + 1) + 4) +
        4 * marked.length) +
        ((6 + (scanRev.length + 4)) + 4), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [run_marking_tail_to_first_payload]
  rw [show 6 + (scanRev.length + 4) + 4 =
      6 + ((scanRev.length + 4) + 4) by omega]
  rw [MachineDescription.runConfig_add]
  have hcellBits :
      (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellAppend (some b) restAfterCell)).map
        some =
      List.append ((cellBits b).map some)
        ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
          some) := by
    cases b <;>
    simp [MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput, cellBits]
  rw [hcellBits]
  change
    BoolWordSuffixScannerDescription.runConfig
        ((scanRev.length + 4) + 4)
        (BoolWordSuffixScannerDescription.runConfig 6
          (config 130
            (markingTailPayloadLeftRev marked (remainingLengthTail + 1))
            (List.append ((cellBits b).map some)
              ((MachineDescription.encodeCodeWordAsInput
                restAfterCell).map some)))) =
      markingTailConfig (List.append marked [b])
        (remainingLengthTail + 1) restAfterCell
  rw [run_boolWordSuffix_state130_currentCell]
  rw [MachineDescription.runConfig_add]
  have hleft :
      some true :: some true ::
          markingTailPayloadLeftRev marked (remainingLengthTail + 1) =
        List.append (scanRev.map some)
          (none :: some true :: activeLengthPrefixTail marked.length) := by
    simp [scanRev, markingTailReturnScanRev,
      markingTailPayloadLeftRev, activeLengthPrefixRev,
      List.map_append, List.append_assoc]
  rw [hleft]
  rw [run_boolWordSuffix_state140_returnToLengthMarker]
  have hright :
      List.append (scanRev.reverse.map some)
          (some b :: some (!b) ::
            (MachineDescription.encodeCodeWordAsInput restAfterCell).map
              some) =
        List.append (tickBits.map some)
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append
              ((markedCellsBits (List.append marked [b])).map some)
              ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
                some))) := by
    cases b
    · rw [markedCellsBits_append_single_map marked false]
      simp [scanRev, markingTailReturnScanRev,
        markedCellBits, stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
    · rw [markedCellsBits_append_single_map marked true]
      simp [scanRev, markingTailReturnScanRev,
        markedCellBits, stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
  rw [hright]
  rw [run_boolWordSuffix_state100_tick]
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

theorem run_marking_tail_decodeCells_none_ne_halt
    (marked : Word Bool) (remainingCells : Nat)
    (tokens : Word MachineCodeSymbol)
    (hdecode :
      MachineDescription.decodeCells remainingCells tokens = none)
    (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (markingTailConfig marked remainingCells tokens)).state ≠
      BoolWordSuffixScannerDescription.halt := by
  induction remainingCells generalizing marked tokens n with
  | zero =>
      simp [MachineDescription.decodeCells] at hdecode
  | succ remainingTail ih =>
      cases hcell : MachineDescription.decodeCell tokens with
      | none =>
          apply
            scanner_ne_halt_of_reaches_ne_halt_region
              (k := (4 * remainingTail + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (markingTailPayloadLeftRev marked remainingTail)
                  ((MachineDescription.encodeCodeWordAsInput tokens).map
                    some))
          · exact
              run_marking_tail_to_first_payload
                marked remainingTail tokens
          · intro m
            exact
              run_boolWordSuffix_state130_decodeCell_none_ne_halt
                tokens
                (markingTailPayloadLeftRev marked remainingTail)
                hcell m
      | some parsedCell =>
          rcases parsedCell with ⟨cell, restAfterCell⟩
          have htokens :
              tokens =
                MachineDescription.encodeCellAppend cell restAfterCell :=
            MachineDescription.decodeCell_eq_some_encodeCellAppend hcell
          cases cell with
          | none =>
              apply
                scanner_ne_halt_of_reaches_ne_halt_region
                  (k := (4 * remainingTail + 4) + 4 * marked.length)
                  (mid :=
                    config 130
                      (markingTailPayloadLeftRev marked remainingTail)
                      ((MachineDescription.encodeCodeWordAsInput
                        (MachineDescription.encodeCellAppend none
                          restAfterCell)).map some))
              · rw [htokens]
                exact
                  run_marking_tail_to_first_payload
                    marked remainingTail
                    (MachineDescription.encodeCellAppend none restAfterCell)
              · intro m
                exact
                  run_boolWordSuffix_state130_blank_cell_ne_halt
                    restAfterCell
                    (markingTailPayloadLeftRev marked remainingTail)
                    m
          | some b =>
              cases hrest :
                  MachineDescription.decodeCells remainingTail
                    restAfterCell with
              | none =>
                  cases remainingTail with
                  | zero =>
                      simp [MachineDescription.decodeCells, hcell]
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
                  simp [MachineDescription.decodeCells, hcell, hrest]
                    at hdecode

theorem run_marking_tail_cellsToWord_none_ne_halt
    (marked : Word Bool) (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol)
    (hword : MachineDescription.cellsToWord? cells = none)
    (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (markingTailConfig marked cells.length
        (MachineDescription.encodeCellsAppend cells suffix))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  induction cells generalizing marked suffix n with
  | nil =>
      simp [MachineDescription.cellsToWord?] at hword
  | cons cell rest ih =>
      cases cell with
      | none =>
          apply
            scanner_ne_halt_of_reaches_ne_halt_region
              (k := (4 * rest.length + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (markingTailPayloadLeftRev marked rest.length)
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest
                        suffix))).map some))
          · change
              BoolWordSuffixScannerDescription.runConfig
                  ((4 * rest.length + 4) + 4 * marked.length)
                  (markingTailConfig marked (rest.length + 1)
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest suffix))) =
                config 130
                  (markingTailPayloadLeftRev marked rest.length)
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest
                        suffix))).map some)
            exact
              run_marking_tail_to_first_payload
                marked rest.length
                (MachineDescription.encodeCellAppend none
                  (MachineDescription.encodeCellsAppend rest suffix))
          · intro m
            exact
              run_boolWordSuffix_state130_blank_cell_ne_halt
                (MachineDescription.encodeCellsAppend rest suffix)
                (markingTailPayloadLeftRev marked rest.length)
                m
      | some b =>
          cases hrest : MachineDescription.cellsToWord? rest with
          | none =>
              cases rest with
              | nil =>
                  simp [MachineDescription.cellsToWord?] at hrest
              | cons nextCell restTail =>
                  rcases
                      run_marking_tail_mark_one
                        marked restTail.length b
                        (MachineDescription.encodeCellsAppend
                          (nextCell :: restTail) suffix) with
                    ⟨steps, hsteps⟩
                  apply
                    scanner_ne_halt_of_reaches_ne_halt_region
                      (k := steps)
                      (mid :=
                        markingTailConfig (List.append marked [b])
                          (restTail.length + 1)
                          (MachineDescription.encodeCellsAppend
                            (nextCell :: restTail) suffix))
                  · change
                      BoolWordSuffixScannerDescription.runConfig steps
                        (markingTailConfig marked (restTail.length + 2)
                          (MachineDescription.encodeCellAppend (some b)
                            (MachineDescription.encodeCellsAppend
                              (nextCell :: restTail) suffix))) =
                        markingTailConfig (List.append marked [b])
                          (restTail.length + 1)
                          (MachineDescription.encodeCellsAppend
                            (nextCell :: restTail) suffix)
                    exact hsteps
                  · intro m
                    exact
                      ih (List.append marked [b]) suffix hrest m
          | some decoded =>
              simp [MachineDescription.cellsToWord?, hrest] at hword

theorem run_boolWordSuffix_boolWordSuffix_state120_decodeBoolWord_none_ne_halt
    (baseLeft : List (Option Bool))
    (rest : Word MachineCodeSymbol)
    (hdecode :
      MachineDescription.decodeBoolWord
        (MachineCodeSymbol.tick :: rest) = none)
    (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 120 (none :: some true :: some false :: some false :: baseLeft)
        ((MachineDescription.encodeCodeWordAsInput rest).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  cases hnat : MachineDescription.decodeNat rest with
  | none =>
      exact
        run_boolWordSuffix_boolWordSuffix_state120_decodeNat_none_ne_halt
          rest (none :: some true :: some false :: some false :: baseLeft) hnat n
  | some parsedNat =>
      rcases parsedNat with ⟨remainingTail, tokensAfterLen⟩
      have hrest :
          rest =
            MachineDescription.encodeNatAppend
              remainingTail tokensAfterLen :=
        MachineDescription.decodeNat_eq_some_encodeNatAppend hnat
      rw [hrest]
      change
        (BoolWordSuffixScannerDescription.runConfig n
          (config 120 (none :: some true :: some false :: some false :: baseLeft)
            (List.map some
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeNatAppend remainingTail
                  tokensAfterLen))))).state ≠
          BoolWordSuffixScannerDescription.halt
      unfold MachineDescription.encodeNatAppend
      rw [MachineDescription.encodeCodeWordAsInput_append]
      have hbits :
          List.map some
              (List.append
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.encodeNat remainingTail))
                (MachineDescription.encodeCodeWordAsInput tokensAfterLen)) =
            List.append ((stageNatBits remainingTail).map some)
              ((MachineDescription.encodeCodeWordAsInput tokensAfterLen).map
                some) := by
        simp [stageNatBits, List.map_append]
      rw [hbits]
      change
        (BoolWordSuffixScannerDescription.runConfig n
          (markingTailConfig ([] : Word Bool)
            (remainingTail + 1) tokensAfterLen)).state ≠
          BoolWordSuffixScannerDescription.halt
      cases hcells :
          MachineDescription.decodeCells (remainingTail + 1)
            tokensAfterLen with
      | none =>
          exact
            run_marking_tail_decodeCells_none_ne_halt
              ([] : Word Bool) (remainingTail + 1)
              tokensAfterLen hcells n
      | some parsedCells =>
          rcases parsedCells with ⟨cells, suffix⟩
          cases hword : MachineDescription.cellsToWord? cells with
          | none =>
              have hcellsShape :
                  remainingTail + 1 = cells.length ∧
                    tokensAfterLen =
                      MachineDescription.encodeCellsAppend cells suffix :=
                MachineDescription.decodeCells_eq_some_encodeCellsAppend
                  hcells
              rw [hcellsShape.left, hcellsShape.right]
              exact
                run_marking_tail_cellsToWord_none_ne_halt
                  ([] : Word Bool) cells suffix hword n
          | some decoded =>
              simp [MachineDescription.decodeBoolWord,
                MachineDescription.decodeCellList,
                MachineDescription.decodeNat, hnat, hcells, hword]
                at hdecode

theorem run_boolWordSuffix_state200_done_to_state210
    (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 4
        (config 200 left
          (List.append (doneBits.map some) right)) =
      config 210 (List.append (doneBits.reverse.map some) left)
        right := by
  cases right <;>
  simp [BoolWordSuffixScannerDescription, doneBits, config,
    tapeAtCells, keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_boolWordSuffix_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig (4 * stage + 4)
        (config 200 left
          (List.append ((stageNatBits stage).map some) right)) =
      config 210
        (List.append ((stageNatBits stage).reverse.map some) left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using
        run_boolWordSuffix_state200_done_to_state210 left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 =
          4 + (4 * stage + 4) by omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          (stageNatBits (stage + 1)).map some =
            List.append (tickBits.map some)
              ((stageNatBits stage).map some) by
          simp [stageNatBits_succ, tickBits,
            MachineDescription.encodeCodeSymbolAsInput]]
      change
        BoolWordSuffixScannerDescription.runConfig
            (4 * stage + 4)
            (BoolWordSuffixScannerDescription.runConfig 4
              (config 200 left
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits stage).map some) right)))) =
          config 210
            (List.append ((stageNatBits (stage + 1)).reverse.map some)
              left)
            right
      rw [run_boolWordSuffix_state200_tick]
      have h := ih
        (List.append (tickBits.reverse.map some) left)
      simpa [stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc] using h

theorem run_boolWordSuffix_state210_encoded_cons_ne_halt
    (symbol : MachineCodeSymbol) (baseLeft : List (Option Bool))
    (rest : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 210 leftRev
        ((MachineDescription.encodeCodeWordAsInput
          (symbol :: rest)).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  exact
    scanner_ne_halt_of_reaches_stepConfig_none
      (k := 0) (by
        cases symbol <;>
        simp [BoolWordSuffixScannerDescription, config, tapeAtCells,
          keep, keepMove, writeMove, scanLeftToSentinelRestart,
          scanLeftToSentinelHalt,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.read])
      (by
        change (210 : Nat) ≠ 999
        omega)

theorem run_boolWordSuffix_state200_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 200 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
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
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                omega)
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases hrest : MachineDescription.decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                scanner_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 200
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((MachineDescription.encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput] using
                  run_boolWordSuffix_state200_tick leftRev
                    ((MachineDescription.encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | one =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (200 : Nat) ≠ 999
                omega)

theorem run_boolWordSuffix_state200_stageNat_suffix_ne_halt
    (stage : Nat) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 200 leftRev
        ((MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeNatAppend stage
            (symbol :: suffix))).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  apply
    scanner_ne_halt_of_reaches_ne_halt_region
      (k := 4 * stage + 4)
      (mid :=
        config 210
          (List.append ((stageNatBits stage).reverse.map some) leftRev)
          ((MachineDescription.encodeCodeWordAsInput
            (symbol :: suffix)).map some))
  · have hbits :
        (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeNatAppend stage
              (symbol :: suffix))).map some =
          List.append ((stageNatBits stage).map some)
            ((MachineDescription.encodeCodeWordAsInput
              (symbol :: suffix)).map some) := by
        change
          List.map some
              (MachineDescription.encodeCodeWordAsInput
                (List.append (MachineDescription.encodeNat stage)
                  (symbol :: suffix))) =
            List.append
              (List.map some
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.encodeNat stage)))
              (List.map some
                (MachineDescription.encodeCodeWordAsInput
                  (symbol :: suffix)))
        rw [MachineDescription.encodeCodeWordAsInput_append]
        simp [List.map_append]
    rw [hbits]
    exact
      run_boolWordSuffix_state200_stageNat_to_state210 stage leftRev
        ((MachineDescription.encodeCodeWordAsInput
          (symbol :: suffix)).map some)
  · intro m
    exact run_boolWordSuffix_state210_encoded_cons_ne_halt symbol suffix
      (List.append ((stageNatBits stage).reverse.map some) leftRev) m

theorem state200_code_tail_nat_inv
    {rest : Word MachineCodeSymbol} {leftRev : List (Option Bool)}
    {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        BoolWordSuffixScannerDescription.runConfig steps
            (config 200 leftRev
              ((MachineDescription.encodeCodeWordAsInput rest).map some)) =
          { state := BoolWordSuffixScannerDescription.halt
            tape := T }) :
    exists stage : Nat,
      rest = MachineDescription.encodeNat stage := by
  rcases hscanner with ⟨steps, hsteps⟩
  cases hdecode : MachineDescription.decodeNat rest with
  | none =>
      have hne :=
        run_boolWordSuffix_state200_decodeNat_none_ne_halt rest leftRev hdecode steps
      have hstate :
          (BoolWordSuffixScannerDescription.runConfig steps
            (config 200 leftRev
              ((MachineDescription.encodeCodeWordAsInput rest).map some))).state =
            BoolWordSuffixScannerDescription.halt := by
        simpa using
          congrArg MachineDescription.Configuration.state hsteps
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨stage, suffix⟩
      have hrest :
          rest = MachineDescription.encodeNatAppend stage suffix :=
        MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode
      cases suffix with
      | nil =>
          exact ⟨stage, by
            simpa [MachineDescription.encodeNatAppend] using hrest⟩
      | cons symbol suffixTail =>
          rw [hrest] at hsteps
          have hne :=
            run_boolWordSuffix_state200_stageNat_suffix_ne_halt
              stage symbol suffixTail leftRev steps
          have hstate :
              (BoolWordSuffixScannerDescription.runConfig steps
                (config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNatAppend stage
                      (symbol :: suffixTail))).map some))).state =
                BoolWordSuffixScannerDescription.halt := by
            simpa using
              congrArg MachineDescription.Configuration.state hsteps
          exact False.elim (hne hstate)

theorem boolWordSuffix_state120_tick_tail_decodeBoolWord_inv
    {rest : Word MachineCodeSymbol} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        BoolWordSuffixScannerDescription.runConfig steps
            (config 120 (none :: some true :: some false :: some false :: baseLeft)
              ((MachineDescription.encodeCodeWordAsInput rest).map some)) =
          { state := BoolWordSuffixScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists suffix : Word MachineCodeSymbol,
      MachineDescription.decodeBoolWord
          (MachineCodeSymbol.tick :: rest) =
        some (w, suffix) := by
  rcases hscanner with ⟨steps, hsteps⟩
  cases hdecode :
      MachineDescription.decodeBoolWord
        (MachineCodeSymbol.tick :: rest) with
  | none =>
      have hne :=
        run_boolWordSuffix_boolWordSuffix_state120_decodeBoolWord_none_ne_halt
          rest hdecode steps
      have hstate :
          (BoolWordSuffixScannerDescription.runConfig steps
            (config 120 (none :: some true :: some false :: some false :: baseLeft)
              ((MachineDescription.encodeCodeWordAsInput rest).map
                some))).state =
            BoolWordSuffixScannerDescription.halt := by
        simpa using
          congrArg MachineDescription.Configuration.state hsteps
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨w, suffix⟩
      exact ⟨w, suffix, rfl⟩


end EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner
end Computability
end FoC
