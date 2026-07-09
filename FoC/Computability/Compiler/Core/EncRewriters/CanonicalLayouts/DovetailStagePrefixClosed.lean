import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.DovetailStagePrefix
import FoC.Computability.Compiler.Core.DovetailInitLayout.StageInputMarkedScanner.TailBits
import FoC.Computability.Compiler.Core.EncodingLemmas

/-
# Closed inversion for the dovetail stage-prefix scanner

MarkedPrefixScannerDescription (MP) differs from the base
StageInputMarkedScannerDescription (SIMS) only by two extra transitions at
state 210 that let it accept a nonblank suffix.  Every other lookup is shared,
so an MP run agrees with the corresponding SIMS run until (and unless) it sits at
state 210 with a bit under the head.  This module records that cross-machine
agreement and uses it to transfer the base marking-loop non-halting facts to MP.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace CanonicalLayouts
namespace DovetailStagePrefix

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

private abbrev SIMS := StageInputMarkedScannerDescription
private abbrev MP := MarkedPrefixScannerDescription

/-- MP's transition table is SIMS's table with two extra state-`210` rows. -/
theorem markedPrefix_transitions_eq :
    MP.transitions =
      SIMS.transitions ++
        [ keepMove 210 (some false) Direction.left SIMS.halt
        , keepMove 210 (some true) Direction.left SIMS.halt ] := rfl

/--
Whenever SIMS can take a step, MP takes the identical step: a successful SIMS
lookup is the first match in MP's longer table.
-/
theorem markedPrefix_stepConfig_eq_of_sims_some
    {c c' : MachineDescription.Configuration}
    (h : SIMS.stepConfig c = some c') :
    MP.stepConfig c = some c' := by
  unfold MachineDescription.stepConfig at h ⊢
  unfold MachineDescription.lookupTransition at h ⊢
  cases hfind :
      SIMS.transitions.find? (Matches c.state (Tape.read c.tape)) with
  | none =>
      rw [hfind] at h
      simp at h
  | some t =>
      rw [hfind] at h
      have hMP :
          MP.transitions.find?
              (Matches c.state (Tape.read c.tape)) = some t := by
        rw [markedPrefix_transitions_eq, List.find?_append, hfind, Option.some_or]
      rw [hMP]
      exact h

private theorem matches_extra210_false_of_ne
    {c : MachineDescription.Configuration} (b : Bool)
    (hne : c.state ≠ 210) :
    Matches c.state (Tape.read c.tape)
        (keepMove 210 (some b) Direction.left SIMS.halt) = false := by
  have hs : (210 == c.state) = false := by
    cases hb : 210 == c.state with
    | false => rfl
    | true => exact absurd (eq_of_beq hb).symm hne
  simp [Matches, keepMove, transition, hs]

/--
When SIMS is stuck at a non-`210` state, MP is stuck there too: the extra rows
only fire at state `210`.
-/
theorem markedPrefix_stepConfig_none_of_sims_none_ne_210
    {c : MachineDescription.Configuration}
    (hne : c.state ≠ 210)
    (h : SIMS.stepConfig c = none) :
    MP.stepConfig c = none := by
  unfold MachineDescription.stepConfig at h ⊢
  unfold MachineDescription.lookupTransition at h ⊢
  cases hfind :
      SIMS.transitions.find? (Matches c.state (Tape.read c.tape)) with
  | some t =>
      rw [hfind] at h
      simp at h
  | none =>
      have hextra :
          ([ keepMove 210 (some false) Direction.left SIMS.halt
           , keepMove 210 (some true) Direction.left SIMS.halt ]).find?
              (Matches c.state (Tape.read c.tape)) = none := by
        simp only [List.find?,
          matches_extra210_false_of_ne false hne,
          matches_extra210_false_of_ne true hne]
      have hMP :
          MP.transitions.find?
              (Matches c.state (Tape.read c.tape)) = none := by
        rw [markedPrefix_transitions_eq, List.find?_append, hfind,
          Option.none_or, hextra]
      rw [hMP]

/-- At state `210` a stuck SIMS step forces a bit under the head. -/
theorem markedPrefix_sims_stepNone_state210_read_isSome
    {c : MachineDescription.Configuration}
    (h210 : c.state = 210)
    (hstep : SIMS.stepConfig c = none) :
    (Tape.read c.tape).isSome = true := by
  cases hread : Tape.read c.tape with
  | some b => rfl
  | none =>
      exfalso
      have hlook : SIMS.lookupTransition 210 none =
          some (keepMove 210 none Direction.left 220) := by decide
      have hne : SIMS.stepConfig c ≠ none := by
        unfold MachineDescription.stepConfig
        rw [h210, hread, hlook]
        simp
      exact hne hstep

/--
An MP run either coincides with the SIMS run of the same length, or the SIMS run
has already visited a state-`210` configuration with a bit under the head — the
sole place the two machines diverge.
-/
theorem markedPrefix_runConfig_eq_sims_or_reaches_state210_bit
    (n : Nat) (c : MachineDescription.Configuration) :
    MP.runConfig n c = SIMS.runConfig n c ∨
      exists m : Nat,
        m < n ∧ (SIMS.runConfig m c).state = 210 ∧
          (Tape.read (SIMS.runConfig m c).tape).isSome := by
  induction n generalizing c with
  | zero => exact Or.inl rfl
  | succ n ih =>
      cases hstep : SIMS.stepConfig c with
      | some c' =>
          have hMPstep : MP.stepConfig c = some c' :=
            markedPrefix_stepConfig_eq_of_sims_some hstep
          have hMP : MP.runConfig (n + 1) c = MP.runConfig n c' := by
            simp [MachineDescription.runConfig, hMPstep]
          have hSIMS : SIMS.runConfig (n + 1) c = SIMS.runConfig n c' := by
            simp [MachineDescription.runConfig, hstep]
          have hstepC : forall k : Nat,
              SIMS.runConfig (k + 1) c = SIMS.runConfig k c' := by
            intro k
            simp [MachineDescription.runConfig, hstep]
          rcases ih c' with heq | ⟨m, hmlt, hm210, hmread⟩
          · exact Or.inl (by rw [hMP, hSIMS, heq])
          · refine Or.inr ⟨m + 1, by lia, ?_, ?_⟩
            · rw [hstepC m]; exact hm210
            · rw [hstepC m]; exact hmread
      | none =>
          have hSIMS : SIMS.runConfig (n + 1) c = c := by
            simp [MachineDescription.runConfig, hstep]
          by_cases h210 : c.state = 210
          · refine Or.inr ⟨0, by lia, ?_, ?_⟩
            · simpa [MachineDescription.runConfig] using h210
            · have := markedPrefix_sims_stepNone_state210_read_isSome h210 hstep
              simpa [MachineDescription.runConfig] using this
          · have hMPstep : MP.stepConfig c = none :=
              markedPrefix_stepConfig_none_of_sims_none_ne_210 h210 hstep
            have hMP : MP.runConfig (n + 1) c = c := by
              simp [MachineDescription.runConfig, hMPstep]
            exact Or.inl (by rw [hMP, hSIMS])

/-- Appending a code suffix to a stage-input code is a plain list append. -/
theorem stageInputCodeAppend_eq_append
    (w : Word Bool) (stage : Nat) (suffix : Word MachineCodeSymbol) :
    DovetailLayout.stageInputCodeAppend w stage suffix =
      List.append (DovetailLayout.stageInputCode w stage) suffix := by
  unfold DovetailLayout.stageInputCode DovetailLayout.stageInputCodeAppend
  rw [show encodeNatAppend stage suffix =
        List.append (encodeNatAppend stage []) suffix by
      simp [encodeNatAppend]]
  exact encodeBoolWordAppend_append w (encodeNatAppend stage []) suffix

/-- The encoding of a nonempty code word starts with an explicit bit. -/
theorem encodeCodeWordAsInput_cons_head
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    exists b : Bool,
    exists bits : Word Bool,
      encodeCodeWordAsInput (symbol :: rest) = b :: bits := by
  cases symbol <;> exact ⟨_, _, rfl⟩

/--
The closed fuel-suffix scanner rejects a checked stage-input handoff tape: the
cell one step to the right of the restored mark is a marked prefix bit, not the
start of a stage nat, so the scanner is stuck within two steps.
-/
theorem sims_state200_checked_handoff_ne_halt
    (w : Word Bool) (stage : Nat) (n : Nat) :
    (SIMS.runConfig n
        { state := 200
          tape :=
            Tape.move Direction.right
              (stageInputSecondBitMarkedCheckedHandoffTape w stage) }).state ≠
      SIMS.halt := by
  cases w with
  | nil =>
      refine scanner_ne_halt_of_reaches_stepConfig_none (k := 0) ?_ ?_
      · simp [stageInputSecondBitMarkedCheckedHandoffTape,
          stageInputSecondBitMarkedCheckedTape,
          stageInputSecondBitTail_eq_prefix_stageNat,
          stageInputSecondBitTailPrefix,
          StageInputMarkedScannerDescription,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, scanLeftToSentinelHalt,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, Matches, transition,
          Tape.move, Tape.moveRight, Tape.read]
      · simp [MachineDescription.runConfig,
          StageInputMarkedScannerDescription]
  | cons b rest =>
      rcases stageNatBits_false_false_tail rest.length with ⟨t, ht⟩
      refine scanner_ne_halt_of_reaches_stepConfig_none (k := 2) ?_ ?_
      · simp [stageInputSecondBitMarkedCheckedHandoffTape,
          stageInputSecondBitMarkedCheckedTape,
          stageInputSecondBitTail_eq_prefix_stageNat,
          stageInputSecondBitTailPrefix, ht,
          StageInputMarkedScannerDescription,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, scanLeftToSentinelHalt,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, Matches, transition,
          Tape.move, Tape.moveRight, Tape.read, Tape.write,
          List.append_assoc]
      · simp [stageInputSecondBitMarkedCheckedHandoffTape,
          stageInputSecondBitMarkedCheckedTape,
          stageInputSecondBitTail_eq_prefix_stageNat,
          stageInputSecondBitTailPrefix, ht,
          StageInputMarkedScannerDescription,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, scanLeftToSentinelHalt,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, Matches, transition,
          Tape.move, Tape.moveRight, Tape.read, Tape.write,
          List.append_assoc]

private theorem markedPrefix_lookup_210_bit (b : Bool) :
    MP.lookupTransition 210 (some b) =
      some (keepMove 210 (some b) Direction.left SIMS.halt) := by
  cases b <;> decide

/--
A base-scanner visit to the suffix gate makes the marked-prefix scanner halt
one step later: the runs agree up to the visit, and MP's extra rows fire there.
-/
theorem markedPrefix_halts_of_sims_reach210_bit
    (m : Nat) (c : MachineDescription.Configuration)
    (hstate : (SIMS.runConfig m c).state = 210)
    (hread : (Tape.read (SIMS.runConfig m c).tape).isSome = true) :
    exists j : Nat,
      j ≤ m + 1 ∧
        exists T : Tape Bool,
          MP.runConfig j c = { state := MP.halt, tape := T } := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      rcases markedPrefix_runConfig_eq_sims_or_reaches_state210_bit m c with
        heq | ⟨m', hm'm, h210', hread'⟩
      · rcases Option.isSome_iff_exists.mp hread with ⟨b, hb⟩
        have hstep :
            MP.stepConfig (SIMS.runConfig m c) =
              some { state := SIMS.halt
                     tape :=
                       Tape.move Direction.left
                         (Tape.write (some b)
                           (SIMS.runConfig m c).tape) } := by
          unfold MachineDescription.stepConfig
          rw [hstate, hb, markedPrefix_lookup_210_bit b]
          rfl
        refine
          ⟨m + 1, Nat.le_refl _,
            Tape.move Direction.left
              (Tape.write (some b) (SIMS.runConfig m c).tape), ?_⟩
        rw [runConfig_add MP m 1 c, heq]
        simp [MachineDescription.runConfig, hstep]
        rfl
      · rcases ih m' hm'm h210' hread' with ⟨j, hj, T, hT⟩
        exact ⟨j, by lia, T, hT⟩

/--
A marked-prefix forward run whose target has not halted is also a base-scanner
run: the two machines only diverge at the suffix gate, and passing through it
would freeze MP at the halt state.
-/
theorem sims_runConfig_eq_of_markedPrefix_ne_halt
    {k : Nat} {c target : MachineDescription.Configuration}
    (hMP : MP.runConfig k c = target)
    (hne : target.state ≠ MP.halt) :
    SIMS.runConfig k c = target := by
  rcases markedPrefix_runConfig_eq_sims_or_reaches_state210_bit k c with
    heq | ⟨m, hmk, h210, hread⟩
  · rw [← heq]
    exact hMP
  · exfalso
    rcases markedPrefix_halts_of_sims_reach210_bit m c h210 hread with
      ⟨j, hjm, T, hT⟩
    have hhalt : MP.runConfig k c = { state := MP.halt, tape := T } := by
      have hsplit :
          MP.runConfig k c = MP.runConfig (j + (k - j)) c := by
        have hjk : j + (k - j) = k := by lia
        rw [hjk]
      rw [hsplit, runConfig_add, hT]
      exact
        runConfig_halt markedPrefixScannerDescription_haltTransitionFree
          T (k - j)
    rw [hMP] at hhalt
    exact hne (by simpa using congrArg MachineDescription.Configuration.state hhalt)

/--
Dead configurations for a marked done tail whose stage nat fails to parse:
the mirror of the halting refutation, concluding that the run also avoids the
suffix gate.
-/
private theorem scanner_marked_done_tail_decodeNat_none_dead
    (rest : Word MachineCodeSymbol)
    (hdecode : decodeNat rest = none)
    (n : Nat) :
    ScannerDeadAt
      (markedTailStartConfig
        (true :: true :: encodeCodeWordAsInput rest)) n := by
  cases rest with
  | nil =>
      exact
        scannerDeadAt_of_reaches_stepConfig_none
          (k := 6) (by
            rfl)
          (by
            change (150 : Nat) ≠ 999
            lia)
          (by
            change (150 : Nat) ≠ 210
            lia)
  | cons symbol suffix =>
      cases symbol with
      | header =>
          apply
            scannerDeadAt_of_reaches_dead_region
              (k := 18)
              (mid :=
                config 200 [some true, some true, none, some false]
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: suffix)).map some))
          · simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              run_marked_tail_done_false_false_to_state200
                (false :: false ::
                  encodeCodeWordAsInput suffix)
          · intro m
            exact
              run_state200_decodeNat_none_dead
                (MachineCodeSymbol.header :: suffix)
                [some true, some true, none, some false]
                hdecode m
      | transition =>
          apply
            scannerDeadAt_of_reaches_dead_region
              (k := 18)
              (mid :=
                config 200 [some true, some true, none, some false]
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: suffix)).map some))
          · simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              run_marked_tail_done_false_false_to_state200
                (false :: true ::
                  encodeCodeWordAsInput suffix)
          · intro m
            exact
              run_state200_decodeNat_none_dead
                (MachineCodeSymbol.transition :: suffix)
                [some true, some true, none, some false]
                hdecode m
      | tick =>
          apply
            scannerDeadAt_of_reaches_dead_region
              (k := 18)
              (mid :=
                config 200 [some true, some true, none, some false]
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.tick :: suffix)).map some))
          · simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              run_marked_tail_done_false_false_to_state200
                (true :: false ::
                  encodeCodeWordAsInput suffix)
          · intro m
            exact
              run_state200_decodeNat_none_dead
                (MachineCodeSymbol.tick :: suffix)
                [some true, some true, none, some false]
                hdecode m
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            scannerDeadAt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (151 : Nat) ≠ 999
                lia)
              (by
                change (151 : Nat) ≠ 210
                lia)
      | zero =>
          exact
            scannerDeadAt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (151 : Nat) ≠ 999
                lia)
              (by
                change (151 : Nat) ≠ 210
                lia)
      | one =>
          exact
            scannerDeadAt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (151 : Nat) ≠ 999
                lia)
              (by
                change (151 : Nat) ≠ 210
                lia)
      | moveLeft =>
          exact
            scannerDeadAt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (151 : Nat) ≠ 999
                lia)
              (by
                change (151 : Nat) ≠ 210
                lia)
      | moveRight =>
          exact
            scannerDeadAt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (152 : Nat) ≠ 999
                lia)
              (by
                change (152 : Nat) ≠ 210
                lia)

/--
Marking-loop inversion: if the base scanner, started on the marked tail of an
encoded code word, reaches state `210` with a bit under the head, then the
code word parses as a stage-input prefix followed by a nonempty code suffix.
State `210` is entered exactly after the post-prefix stage nat scans to its
done block, and the bit under the head is the first suffix bit.
-/
theorem sims_marked_code_tail_reach210_decodeStageInput
    (code : Word MachineCodeSymbol) (tail : Word Bool) (m : Nat)
    (hbits : encodeCodeWordAsInput code = false :: false :: tail)
    (h210 :
      (SIMS.runConfig m (markedTailStartConfig tail)).state = 210)
    (hread :
      (Tape.read
        (SIMS.runConfig m (markedTailStartConfig tail)).tape).isSome = true) :
    exists w : Word Bool,
    exists limit : Nat,
    exists symbol : MachineCodeSymbol,
    exists rest : Word MachineCodeSymbol,
      DovetailLayout.decodeStageInput code =
        some ((w, limit), symbol :: rest) := by
  cases hdec : DovetailLayout.decodeStageInput code with
  | some parsed =>
      rcases parsed with ⟨⟨w, limit⟩, suffix⟩
      cases suffix with
      | cons symbol rest =>
          exact ⟨w, limit, symbol, rest, rfl⟩
      | nil =>
          -- An exact stage-input code halts the scanner, and a halting run
          -- never rests at the suffix gate.
          exfalso
          have hcodeEq :
              code = DovetailLayout.stageInputCodeAppend w limit [] :=
            DovetailLayout.decodeStageInput_eq_some_stageInputCodeAppend hdec
          have hbits' :
              encodeCodeWordAsInput code =
                false :: false :: stageInputSecondBitTail w limit := by
            rw [hcodeEq]
            exact stageInputBits_eq_false_false_tail w limit
          rw [hbits] at hbits'
          have htail : tail = stageInputSecondBitTail w limit := by
            injection hbits' with _ h1
            injection h1 with _ h2
          subst htail
          rcases run_start_forward w limit with ⟨steps, hforward⟩
          have hforward' :
              SIMS.runConfig steps
                  (markedTailStartConfig
                    (stageInputSecondBitTail w limit)) =
                { state := SIMS.halt
                  tape :=
                    stageInputSecondBitMarkedCheckedHandoffTape w limit } := by
            simpa [markedTailStartConfig, markedStartConfig,
              checkedHaltConfig] using hforward
          exact scanner_halt_no_reach210_bit hforward' h210 hread
  | none =>
      exfalso
      cases code with
      | nil =>
          simp [encodeCodeWordAsInput] at hbits
      | cons symbol rest =>
          cases symbol
          · -- header: the tail starts with a cleared bit
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            have htail :
                tail = false :: false ::
                  encodeCodeWordAsInput rest := by
              injection hbits with _ h1
              injection h1 with _ h2
              exact h2.symm
            subst htail
            exact
              (scanner_marked_tail_false_dead
                (false :: encodeCodeWordAsInput rest) m).2 ⟨h210, hread⟩
          · -- transition: the tail starts with a cleared bit
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            have htail :
                tail = false :: true ::
                  encodeCodeWordAsInput rest := by
              injection hbits with _ h1
              injection h1 with _ h2
              exact h2.symm
            subst htail
            exact
              (scanner_marked_tail_false_dead
                (true :: encodeCodeWordAsInput rest) m).2 ⟨h210, hread⟩
          · -- tick: enter the marking loop and split on the boolword parse
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            have htail :
                tail = true :: false ::
                  encodeCodeWordAsInput rest := by
              injection hbits with _ h1
              injection h1 with _ h2
              exact h2.symm
            subst htail
            obtain ⟨m', h210', hread'⟩ :=
              scanner_reach210_bit_after_prefix
                (run_marked_tail_tick_to_state120
                  (encodeCodeWordAsInput rest)) h210 hread
            cases hbw :
                decodeBoolWord (MachineCodeSymbol.tick :: rest) with
            | none =>
                exact
                  (run_state120_decodeBoolWord_none_dead rest hbw m').2
                    ⟨h210', hread'⟩
            | some parsedW =>
                rcases parsedW with ⟨w, rest₁⟩
                cases hnat : decodeNat rest₁ with
                | some parsedNat =>
                    rcases parsedNat with ⟨limit, suffix⟩
                    have hsome :
                        DovetailLayout.decodeStageInput
                            (MachineCodeSymbol.tick :: rest) =
                          some ((w, limit), suffix) := by
                      simp [DovetailLayout.decodeStageInput, hbw, hnat]
                    rw [hdec] at hsome
                    simp at hsome
                | none =>
                    exact
                      (run_state120_boolWord_suffix_decodeNat_none_dead
                        rest rest₁ w hbw hnat m').2 ⟨h210', hread'⟩
          · -- done: the boolword is empty and the stage nat must fail
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            have htail :
                tail = true :: true ::
                  encodeCodeWordAsInput rest := by
              injection hbits with _ h1
              injection h1 with _ h2
              exact h2.symm
            subst htail
            cases hnat : decodeNat rest with
            | some parsedNat =>
                rcases parsedNat with ⟨limit, suffix⟩
                have hsome :
                    DovetailLayout.decodeStageInput
                        (MachineCodeSymbol.done :: rest) =
                      some ((([] : Word Bool), limit), suffix) := by
                  simp [DovetailLayout.decodeStageInput, decodeBoolWord,
                    decodeCellList, decodeNat, decodeCells, cellsToWord?,
                    hnat]
                  rfl
                rw [hdec] at hsome
                simp at hsome
            | none =>
                exact
                  (scanner_marked_done_tail_decodeNat_none_dead
                    rest hnat m).2 ⟨h210, hread⟩
          · -- blank: rejected by the encoding shape
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            injection hbits with _ htail
            injection htail with hbad
            cases hbad
          · -- zero
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            injection hbits with _ htail
            injection htail with hbad
            cases hbad
          · -- one
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            injection hbits with _ htail
            injection htail with hbad
            cases hbad
          · -- moveLeft
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            injection hbits with _ htail
            injection htail with hbad
            cases hbad
          · -- moveRight
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at hbits
            injection hbits with hhead
            cases hhead

end DovetailStagePrefix
end CanonicalLayouts
end EncRewriters
end Computability
end FoC
