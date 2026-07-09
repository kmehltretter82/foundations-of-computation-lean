import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.DovetailStagePrefix
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

/--
Remaining marking-loop leaf (temporary named sorry, tracked in
FUELSIMULATOR_RECOGNIZER_SORRIES_PLAN.md): if the base scanner, started on the
marked tail of an encoded code word, reaches state `210` with a bit under the
head, then the code word parses as a stage-input prefix followed by a nonempty
code suffix.  State `210` is entered exactly after the post-prefix stage nat
scans to its done block, and the bit under the head is the first suffix bit.
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
  sorry

end DovetailStagePrefix
end CanonicalLayouts
end EncRewriters
end Computability
end FoC
