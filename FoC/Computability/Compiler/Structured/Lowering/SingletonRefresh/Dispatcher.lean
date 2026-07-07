import FoC.Computability.Compiler.Structured.Lowering.SingletonRefresh.TerminalPairProbe

set_option doc.verso true

/-!
# Singleton refresh dispatcher

Fixed singleton-shape dispatcher layout and branch composition.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Fixed singleton-shape dispatcher layout
-/

def singletonShapeRefreshFinalHalt : Nat :=
  2

def singletonShapeLeftRepairOffset : Nat :=
  3

def singletonShapeLeftRepairDescription : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    singletonShapeLeftRepairOffset
    singletonShapeRefreshFinalHalt
    leftBoundaryGuardSlackRefreshDescription

def singletonShapeLeftRepairStart : Nat :=
  singletonShapeLeftRepairDescription.start

def singletonShapeLeftRepairLimit : Nat :=
  singletonShapeLeftRepairDescription.stateCount

def singletonShapeRightRepairOffset : Nat :=
  singletonShapeLeftRepairLimit

def singletonShapeRightRepairDescription : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    singletonShapeRightRepairOffset
    singletonShapeRefreshFinalHalt
    rightBoundaryGuardSlackRefreshDescription

def singletonShapeRightRepairStart : Nat :=
  singletonShapeRightRepairDescription.start

def singletonShapeRightRepairLimit : Nat :=
  singletonShapeRightRepairDescription.stateCount

def singletonShapeTerminalProbeOffset : Nat :=
  singletonShapeRightRepairLimit

def singletonShapeTerminalLocalCanonicalExit : Nat :=
  11

def singletonShapeTerminalLocalRightBoundaryExit : Nat :=
  12

def singletonShapeTerminalLocalUnusedExit : Nat :=
  13

def singletonShapeTerminalLocalTarget : Option Bool -> Nat
  | none => singletonShapeTerminalLocalCanonicalExit
  | some false => singletonShapeTerminalLocalRightBoundaryExit
  | some true => singletonShapeTerminalLocalUnusedExit

def singletonShapeTerminalTarget : Option Bool -> Nat
  | none => singletonShapeRefreshFinalHalt
  | some false => singletonShapeRightRepairStart
  | some true => singletonShapeRefreshFinalHalt

def singletonShapeTerminalLocalDescription : MachineDescription :=
  singletonTerminalPairProbeDescription
    singletonShapeTerminalLocalCanonicalExit
    singletonShapeTerminalLocalRightBoundaryExit

def singletonShapeTerminalProbeDescription : MachineDescription :=
  MachineDescription.offsetReadExitRetargetDescription
    singletonShapeTerminalProbeOffset
    singletonShapeTerminalLocalTarget
    singletonShapeTerminalTarget
    singletonShapeTerminalLocalDescription

def singletonShapeTerminalProbeStart : Nat :=
  singletonShapeTerminalProbeDescription.start

def singletonShapeRefreshOpeningDescription : MachineDescription :=
  singletonOpeningProbeDescription
    singletonShapeTerminalProbeStart
    singletonShapeLeftRepairStart

def singletonShapeRefreshDescription : MachineDescription where
  stateCount := singletonShapeTerminalProbeDescription.stateCount
  start := singletonShapeRefreshOpeningDescription.start
  halt := singletonShapeRefreshFinalHalt
  transitions :=
    singletonShapeRefreshOpeningDescription.transitions ++
      singletonShapeLeftRepairDescription.transitions ++
      singletonShapeRightRepairDescription.transitions ++
      singletonShapeTerminalProbeDescription.transitions

theorem singletonShapeRefreshFinalHalt_lt_leftRepairOffset :
    singletonShapeRefreshFinalHalt < singletonShapeLeftRepairOffset := by
  decide

theorem singletonShapeRefreshFinalHalt_lt_rightRepairOffset :
    singletonShapeRefreshFinalHalt < singletonShapeRightRepairOffset := by
  unfold singletonShapeRightRepairOffset singletonShapeLeftRepairLimit
    singletonShapeLeftRepairDescription
  simp [MachineDescription.offsetRetargetDescription,
    singletonShapeLeftRepairOffset, singletonShapeRefreshFinalHalt]
  lia

theorem singletonShapeLeftRepairDescription_subroutineReady :
    singletonShapeLeftRepairDescription.SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    singletonShapeRefreshFinalHalt_lt_leftRepairOffset
    leftBoundaryGuardSlackRefreshDescription_subroutineReady.left

theorem singletonShapeRightRepairDescription_subroutineReady :
    singletonShapeRightRepairDescription.SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    singletonShapeRefreshFinalHalt_lt_rightRepairOffset
    rightBoundaryGuardSlackRefreshDescription_subroutineReady.left

theorem singletonShapeTerminalLocalDescription_subroutineReady :
    singletonShapeTerminalLocalDescription.SubroutineReady :=
  singletonTerminalPairProbeDescription_subroutineReady
    singletonShapeTerminalLocalCanonicalExit
    singletonShapeTerminalLocalRightBoundaryExit

theorem singletonShapeTerminalLocalDescription_transitionFreeAt
    (cell : Option Bool) :
    singletonShapeTerminalLocalDescription.TransitionFreeAt
      (singletonShapeTerminalLocalTarget cell) := by
  cases cell with
  | none =>
      exact
        transition_notFrom_of_all
          (l := singletonShapeTerminalLocalDescription.transitions)
          (state := singletonShapeTerminalLocalTarget none)
          (by decide)
  | some bit =>
      cases bit with
      | false =>
          exact
            transition_notFrom_of_all
              (l := singletonShapeTerminalLocalDescription.transitions)
              (state := singletonShapeTerminalLocalTarget (some false))
              (by decide)
      | true =>
          exact
            transition_notFrom_of_all
              (l := singletonShapeTerminalLocalDescription.transitions)
              (state := singletonShapeTerminalLocalTarget (some true))
              (by decide)

theorem singletonShapeTerminalTarget_lt_probeOffset :
    forall cell : Option Bool,
      singletonShapeTerminalTarget cell <
        singletonShapeTerminalProbeOffset := by
  intro cell
  cases cell with
  | none =>
      have hhalt :=
        singletonShapeRightRepairDescription_subroutineReady.left.right.right.left
      simpa [singletonShapeTerminalTarget,
        singletonShapeTerminalProbeOffset,
        singletonShapeRightRepairLimit,
        singletonShapeRightRepairDescription] using hhalt
  | some bit =>
      cases bit with
      | false =>
          have hstart :=
            singletonShapeRightRepairDescription_subroutineReady.left.right.left
          simpa [singletonShapeTerminalTarget,
            singletonShapeTerminalProbeOffset,
            singletonShapeRightRepairLimit,
            singletonShapeRightRepairStart] using hstart
      | true =>
          have hhalt :=
            singletonShapeRightRepairDescription_subroutineReady.left.right.right.left
          simpa [singletonShapeTerminalTarget,
            singletonShapeTerminalProbeOffset,
            singletonShapeRightRepairLimit,
            singletonShapeRightRepairDescription] using hhalt

theorem singletonShapeTerminalProbeDescription_subroutineReady :
    singletonShapeTerminalProbeDescription.SubroutineReady :=
  MachineDescription.offsetReadExitRetargetDescription_subroutineReady
    singletonShapeTerminalTarget_lt_probeOffset
    singletonShapeTerminalLocalDescription_subroutineReady.left

theorem singletonShapeRefreshOpeningDescription_subroutineReady :
    singletonShapeRefreshOpeningDescription.SubroutineReady :=
  singletonOpeningProbeDescription_subroutineReady
    singletonShapeTerminalProbeStart
    singletonShapeLeftRepairStart

theorem singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset :
    forall t : TransitionDescription,
      t ∈ singletonShapeRefreshOpeningDescription.transitions ->
        t.source < singletonShapeLeftRepairOffset := by
  intro t ht
  simp [singletonShapeRefreshOpeningDescription,
    singletonOpeningProbeDescription] at ht
  rcases ht with rfl | rfl | rfl <;>
    decide

theorem singletonShapeLeftRepairDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ singletonShapeLeftRepairDescription.transitions ->
        singletonShapeLeftRepairOffset ≤ t.source ∧
          t.source < singletonShapeLeftRepairLimit := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonShapeLeftRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (leftBoundaryGuardSlackRefreshDescription_subroutineReady.left.right.right.right.left
      base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      singletonShapeLeftRepairLimit, singletonShapeLeftRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource singletonShapeLeftRepairOffset
    · exact Nat.le_max_left _ _

theorem singletonShapeRightRepairDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ singletonShapeRightRepairDescription.transitions ->
        singletonShapeRightRepairOffset ≤ t.source ∧
          t.source < singletonShapeRightRepairLimit := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonShapeRightRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (rightBoundaryGuardSlackRefreshDescription_subroutineReady.left.right.right.right.left
      base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      singletonShapeRightRepairLimit, singletonShapeRightRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource singletonShapeRightRepairOffset
    · exact Nat.le_max_left _ _

theorem singletonShapeTerminalProbeDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ singletonShapeTerminalProbeDescription.transitions ->
        singletonShapeTerminalProbeOffset ≤ t.source ∧
          t.source < singletonShapeTerminalProbeDescription.stateCount := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonShapeTerminalProbeDescription,
        MachineDescription.offsetReadExitRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (singletonShapeTerminalLocalDescription_subroutineReady.left.right.right.right.left
      base hbase).left
  constructor
  · simp [MachineDescription.readExitRetargetStates]
  · simp [MachineDescription.readExitRetargetStates,
      singletonShapeTerminalProbeDescription,
      MachineDescription.offsetReadExitRetargetDescription]
    simpa [singletonShapeTerminalLocalDescription] using
      Nat.add_lt_add_left hsource singletonShapeTerminalProbeOffset

theorem singletonShapeLeftRepairOffset_lt_rightRepairOffset :
    singletonShapeLeftRepairOffset < singletonShapeRightRepairOffset := by
  have hstart :=
    singletonShapeLeftRepairDescription_subroutineReady.left.right.left
  simpa [singletonShapeRightRepairOffset, singletonShapeLeftRepairLimit,
    singletonShapeLeftRepairDescription,
    MachineDescription.offsetRetargetDescription] using hstart

theorem singletonShapeLeftRepairOffset_le_rightRepairOffset :
    singletonShapeLeftRepairOffset ≤ singletonShapeRightRepairOffset :=
  Nat.le_of_lt singletonShapeLeftRepairOffset_lt_rightRepairOffset

theorem singletonShapeRightRepairOffset_lt_terminalProbeOffset :
    singletonShapeRightRepairOffset < singletonShapeTerminalProbeOffset := by
  have hstart :=
    singletonShapeRightRepairDescription_subroutineReady.left.right.left
  simpa [singletonShapeTerminalProbeOffset, singletonShapeRightRepairLimit,
    singletonShapeRightRepairDescription,
    MachineDescription.offsetRetargetDescription] using hstart

theorem singletonShapeRightRepairOffset_le_terminalProbeOffset :
    singletonShapeRightRepairOffset ≤ singletonShapeTerminalProbeOffset :=
  Nat.le_of_lt singletonShapeRightRepairOffset_lt_terminalProbeOffset

theorem singletonShapeLeftRepairLimit_le_terminalProbeOffset :
    singletonShapeLeftRepairLimit ≤ singletonShapeTerminalProbeOffset := by
  simpa [singletonShapeRightRepairOffset] using
    singletonShapeRightRepairOffset_le_terminalProbeOffset

theorem singletonShapeLeftRepairOffset_le_terminalProbeOffset :
    singletonShapeLeftRepairOffset ≤ singletonShapeTerminalProbeOffset :=
  Nat.le_trans singletonShapeLeftRepairOffset_le_rightRepairOffset
    singletonShapeRightRepairOffset_le_terminalProbeOffset

theorem singletonShapeRefreshFinalHalt_lt_stateCount :
    singletonShapeRefreshFinalHalt <
      singletonShapeRefreshDescription.stateCount := by
  have hhalt :=
    singletonShapeTerminalProbeDescription_subroutineReady.left.right.right.left
  simpa [singletonShapeRefreshDescription,
    singletonShapeTerminalProbeDescription,
    singletonShapeTerminalTarget] using hhalt

theorem singletonShapeTerminalProbeOffset_lt_stateCount :
    singletonShapeTerminalProbeOffset <
      singletonShapeRefreshDescription.stateCount := by
  have hpos := singletonShapeTerminalLocalDescription_subroutineReady.left.left
  simpa [singletonShapeRefreshDescription,
    singletonShapeTerminalProbeDescription,
    MachineDescription.offsetReadExitRetargetDescription] using
    Nat.lt_add_of_pos_right (n := singletonShapeTerminalProbeOffset) hpos

theorem singletonShapeLeftRepairLimit_le_stateCount :
    singletonShapeLeftRepairLimit ≤
      singletonShapeRefreshDescription.stateCount :=
  Nat.le_trans singletonShapeLeftRepairLimit_le_terminalProbeOffset
    (Nat.le_of_lt singletonShapeTerminalProbeOffset_lt_stateCount)

theorem singletonShapeRightRepairLimit_le_stateCount :
    singletonShapeRightRepairLimit ≤
      singletonShapeRefreshDescription.stateCount := by
  simpa [singletonShapeTerminalProbeOffset] using
    Nat.le_of_lt singletonShapeTerminalProbeOffset_lt_stateCount

theorem singletonShapeRefreshDescription_transitions_wellFormed :
    forall t : TransitionDescription,
      t ∈ singletonShapeRefreshDescription.transitions ->
        TransitionDescription.WellFormed
          singletonShapeRefreshDescription.stateCount t := by
  intro t ht
  simp [singletonShapeRefreshDescription] at ht
  rcases ht with hopen | hleft | hright | hterminal
  · simp [singletonShapeRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopen
    rcases hopen with rfl | rfl | rfl
    · constructor
      · exact Nat.lt_trans (by decide)
          singletonShapeRefreshFinalHalt_lt_stateCount
      · exact Nat.lt_trans (by decide)
          singletonShapeRefreshFinalHalt_lt_stateCount
    · constructor
      · exact Nat.lt_trans (by decide)
          singletonShapeRefreshFinalHalt_lt_stateCount
      · exact
          singletonShapeTerminalProbeDescription_subroutineReady.left.right.left
    · constructor
      · exact Nat.lt_trans (by decide)
          singletonShapeRefreshFinalHalt_lt_stateCount
      · exact
          Nat.lt_of_lt_of_le
            singletonShapeLeftRepairDescription_subroutineReady.left.right.left
            singletonShapeLeftRepairLimit_le_stateCount
  · have hformed :=
      singletonShapeLeftRepairDescription_subroutineReady.left.right.right.right.left
        t hleft
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        singletonShapeLeftRepairLimit_le_stateCount,
      Nat.lt_of_lt_of_le hformed.right
        singletonShapeLeftRepairLimit_le_stateCount⟩
  · have hformed :=
      singletonShapeRightRepairDescription_subroutineReady.left.right.right.right.left
        t hright
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        singletonShapeRightRepairLimit_le_stateCount,
      Nat.lt_of_lt_of_le hformed.right
        singletonShapeRightRepairLimit_le_stateCount⟩
  · exact
      singletonShapeTerminalProbeDescription_subroutineReady.left.right.right.right.left
        t hterminal

theorem singletonShapeRefreshDescription_deterministic :
    singletonShapeRefreshDescription.Deterministic := by
  intro t u ht hu hkey
  simp [singletonShapeRefreshDescription] at ht hu
  rcases ht with hopenT | hleftT | hrightT | hterminalT <;>
    rcases hu with hopenU | hleftU | hrightU | hterminalU
  · exact
      singletonShapeRefreshOpeningDescription_subroutineReady.left.right.right.right.right
        t u hopenT hopenU hkey
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (singletonShapeLeftRepairDescription_sources_in_block u hleftU).left
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (singletonShapeRightRepairDescription_sources_in_block u hrightU).left
    have horder := singletonShapeLeftRepairOffset_le_rightRepairOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have horder := singletonShapeLeftRepairOffset_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (singletonShapeLeftRepairDescription_sources_in_block t hleftT).left
    exact False.elim (by
      have hs := hkey.left
      lia)
  · exact
      singletonShapeLeftRepairDescription_subroutineReady.left.right.right.right.right
        t u hleftT hleftU hkey
  · have htBound :=
      (singletonShapeLeftRepairDescription_sources_in_block t hleftT).right
    have huBound :=
      (singletonShapeRightRepairDescription_sources_in_block u hrightU).left
    exact False.elim (by
      have hs := hkey.left
      simp [singletonShapeRightRepairOffset] at huBound
      lia)
  · have htBound :=
      (singletonShapeLeftRepairDescription_sources_in_block t hleftT).right
    have huBound :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have horder := singletonShapeLeftRepairLimit_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (singletonShapeRightRepairDescription_sources_in_block t hrightT).left
    have horder := singletonShapeLeftRepairOffset_le_rightRepairOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (singletonShapeLeftRepairDescription_sources_in_block u hleftU).right
    have huBound :=
      (singletonShapeRightRepairDescription_sources_in_block t hrightT).left
    exact False.elim (by
      have hs := hkey.left
      simp [singletonShapeRightRepairOffset] at huBound
      lia)
  · exact
      singletonShapeRightRepairDescription_subroutineReady.left.right.right.right.right
        t u hrightT hrightU hkey
  · have htBound :=
      (singletonShapeRightRepairDescription_sources_in_block t hrightT).right
    have huLower :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have huBound : singletonShapeRightRepairLimit ≤ u.source := by
      simpa [singletonShapeTerminalProbeOffset] using huLower
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have horder := singletonShapeLeftRepairOffset_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (singletonShapeLeftRepairDescription_sources_in_block u hleftU).right
    have huBound :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have horder := singletonShapeLeftRepairLimit_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (singletonShapeRightRepairDescription_sources_in_block u hrightU).right
    have huLower :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have huBound : singletonShapeRightRepairLimit ≤ t.source := by
      simpa [singletonShapeTerminalProbeOffset] using huLower
    exact False.elim (by
      have hs := hkey.left
      lia)
  · exact
      singletonShapeTerminalProbeDescription_subroutineReady.left.right.right.right.right
        t u hterminalT hterminalU hkey

theorem singletonShapeRefreshDescription_wellFormed :
    singletonShapeRefreshDescription.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      Nat.lt_of_lt_of_le (by decide : 0 < singletonShapeRefreshFinalHalt)
        (Nat.le_of_lt singletonShapeRefreshFinalHalt_lt_stateCount)
  · exact
      Nat.lt_of_lt_of_le (by decide : 0 < singletonShapeRefreshFinalHalt)
        (Nat.le_of_lt singletonShapeRefreshFinalHalt_lt_stateCount)
  · exact singletonShapeRefreshFinalHalt_lt_stateCount
  · exact singletonShapeRefreshDescription_transitions_wellFormed
  · exact singletonShapeRefreshDescription_deterministic

theorem singletonShapeRefreshDescription_haltTransitionFree :
    singletonShapeRefreshDescription.HaltTransitionFree := by
  intro t ht
  simp [singletonShapeRefreshDescription] at ht
  rcases ht with hopening | hleft | hright | hterminal
  · simp [singletonShapeRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopening
    rcases hopening with rfl | rfl | rfl <;>
      decide
  · exact singletonShapeLeftRepairDescription_subroutineReady.right t hleft
  · exact singletonShapeRightRepairDescription_subroutineReady.right t hright
  · exact singletonShapeTerminalProbeDescription_subroutineReady.right
      t hterminal

theorem singletonShapeRefreshDescription_subroutineReady :
    singletonShapeRefreshDescription.SubroutineReady :=
  ⟨singletonShapeRefreshDescription_wellFormed,
    singletonShapeRefreshDescription_haltTransitionFree⟩

theorem singletonShapeTerminalProbeDescription_reaches_canonical
    (target : Tape Bool) :
    exists steps : Nat,
      singletonShapeTerminalProbeDescription.runConfig steps
        { state := singletonShapeTerminalProbeStart
          tape := encodedGuardedStructuredTapes [target] } =
      { state := singletonShapeRefreshFinalHalt
        tape := encodedGuardedStructuredTapes [target] } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_canonical
        singletonShapeTerminalLocalCanonicalExit
        singletonShapeTerminalLocalRightBoundaryExit
        target with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonShapeTerminalProbeOffset)
      (localTarget := singletonShapeTerminalLocalTarget)
      (target := singletonShapeTerminalTarget)
      singletonShapeTerminalTarget_lt_probeOffset
      singletonShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [singletonShapeTerminalProbeDescription,
    singletonShapeTerminalProbeStart, singletonShapeTerminalLocalDescription,
    singletonShapeTerminalLocalTarget, singletonShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using hcopy

theorem singletonShapeTerminalProbeDescription_reaches_canonical_cons
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      singletonShapeTerminalProbeDescription.runConfig steps
        { state := singletonShapeTerminalProbeStart
          tape := encodedStructuredTapes (guardLogicalTape target :: rest) } =
      { state := singletonShapeRefreshFinalHalt
        tape := encodedStructuredTapes (guardLogicalTape target :: rest) } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_canonical_cons
        singletonShapeTerminalLocalCanonicalExit
        singletonShapeTerminalLocalRightBoundaryExit
        target rest with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonShapeTerminalProbeOffset)
      (localTarget := singletonShapeTerminalLocalTarget)
      (target := singletonShapeTerminalTarget)
      singletonShapeTerminalTarget_lt_probeOffset
      singletonShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [singletonShapeTerminalProbeDescription,
    singletonShapeTerminalProbeStart, singletonShapeTerminalLocalDescription,
    singletonShapeTerminalLocalTarget, singletonShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using hcopy

theorem singletonShapeTerminalProbeDescription_reaches_rightBoundary
    (left : List (Option Bool)) (head : Option Bool) :
    exists steps : Nat,
      singletonShapeTerminalProbeDescription.runConfig steps
        { state := singletonShapeTerminalProbeStart
          tape :=
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] } =
      { state := singletonShapeRightRepairStart
        tape :=
          encodedStructuredTapes
            [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_rightBoundary
        singletonShapeTerminalLocalCanonicalExit
        singletonShapeTerminalLocalRightBoundaryExit
        left head with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonShapeTerminalProbeOffset)
      (localTarget := singletonShapeTerminalLocalTarget)
      (target := singletonShapeTerminalTarget)
      singletonShapeTerminalTarget_lt_probeOffset
      singletonShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [singletonShapeTerminalProbeDescription,
    singletonShapeTerminalProbeStart, singletonShapeTerminalLocalDescription,
    singletonShapeTerminalLocalTarget, singletonShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using hcopy

theorem singletonShapeTerminalProbeDescription_reaches_rightBoundary_cons
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      singletonShapeTerminalProbeDescription.runConfig steps
        { state := singletonShapeTerminalProbeStart
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) } =
      { state := singletonShapeRightRepairStart
        tape :=
          encodedStructuredTapes
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest) } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_rightBoundary_cons
        singletonShapeTerminalLocalCanonicalExit
        singletonShapeTerminalLocalRightBoundaryExit
        left head rest with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonShapeTerminalProbeOffset)
      (localTarget := singletonShapeTerminalLocalTarget)
      (target := singletonShapeTerminalTarget)
      singletonShapeTerminalTarget_lt_probeOffset
      singletonShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [singletonShapeTerminalProbeDescription,
    singletonShapeTerminalProbeStart, singletonShapeTerminalLocalDescription,
    singletonShapeTerminalLocalTarget, singletonShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using hcopy

theorem singletonShapeLeftRepairDescription_haltsFrom_leftBoundary
    (head : Option Bool) (right : List (Option Bool)) :
    singletonShapeLeftRepairDescription.HaltsFromTapeEquiv
      (encodedStructuredTapes
        [({ left := [], head := head, right := right ++ [none] } :
          Tape Bool)])
      (encodedGuardedStructuredTapes
        [({ left := [], head := head, right := right } : Tape Bool)]) := by
  rcases
      leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundarySlackSingleton
        head (right ++ [none]) with
    ⟨actual, hhalts, hequiv⟩
  refine ⟨actual, ?_, ?_⟩
  · simpa [singletonShapeLeftRepairDescription] using
    MachineDescription.offsetRetargetDescription_haltsFromTape
      singletonShapeRefreshFinalHalt_lt_leftRepairOffset
      leftBoundaryGuardSlackRefreshDescription_subroutineReady.right
      hhalts
  · simpa [encodedGuardedStructuredTapes, guardLogicalTapes,
      guardLogicalTape] using hequiv

theorem singletonShapeRightRepairDescription_haltsFrom_rightBoundary
    (left : List (Option Bool)) (head : Option Bool) :
    singletonShapeRightRepairDescription.HaltsFromTapeEquiv
      (encodedStructuredTapes
        [({ left := left ++ [none], head := head, right := [] } :
          Tape Bool)])
      (encodedGuardedStructuredTapes
        [({ left := left, head := head, right := [] } : Tape Bool)]) := by
  refine
    ⟨encodedStructuredTapes
        [({ left := left ++ [none], head := head, right := [none] } :
          Tape Bool)],
      ?_, ?_⟩
  · simpa [singletonShapeRightRepairDescription] using
      MachineDescription.offsetRetargetDescription_haltsFromTape
        singletonShapeRefreshFinalHalt_lt_rightRepairOffset
        rightBoundaryGuardSlackRefreshDescription_subroutineReady.right
        (rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundarySlackSingleton
          (left ++ [none]) head)
  · exact Tape.Equiv.refl _


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
