import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.CursorBoundaryGap.Contracts

set_option doc.verso true

/-!
# Boundary-gap refresh assembly

This module keeps the public wrapper for boundary-gap refresh handoffs and
assembles the singleton-head guard refresh machine from the contract layer.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

private def TransitionListDeterministic
    (transitions : List TransitionDescription) : Prop :=
  forall t u : TransitionDescription,
    t ∈ transitions -> u ∈ transitions ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u

private def TransitionSourceDisjoint
    (left right : List TransitionDescription) : Prop :=
  forall t u : TransitionDescription,
    t ∈ left -> u ∈ right -> t.source ≠ u.source

private def TransitionSourcesBelow
    (bound : Nat) (transitions : List TransitionDescription) : Prop :=
  forall t : TransitionDescription, t ∈ transitions -> t.source < bound

private def TransitionSourcesAtLeast
    (bound : Nat) (transitions : List TransitionDescription) : Prop :=
  forall t : TransitionDescription, t ∈ transitions -> bound ≤ t.source

private theorem transitionListDeterministic_append_of_sourceDisjoint
    {left right : List TransitionDescription}
    (hleft : TransitionListDeterministic left)
    (hright : TransitionListDeterministic right)
    (hdisjoint : TransitionSourceDisjoint left right) :
    TransitionListDeterministic (left ++ right) := by
  intro t u ht hu hkey
  simp at ht hu
  rcases ht with ht | ht <;> rcases hu with hu | hu
  · exact hleft t u ht hu hkey
  · exact False.elim ((hdisjoint t u ht hu) hkey.left)
  · exact False.elim ((hdisjoint u t hu ht) hkey.left.symm)
  · exact hright t u ht hu hkey

private theorem transitionSourceDisjoint_of_below_atLeast
    {bound : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesBelow bound left)
    (hright : TransitionSourcesAtLeast bound right) :
    TransitionSourceDisjoint left right := by
  intro t u ht hu hsource
  have htBound := hleft t ht
  have huBound := hright u hu
  lia

private theorem transitionSourcesBelow_append
    {bound : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesBelow bound left)
    (hright : TransitionSourcesBelow bound right) :
    TransitionSourcesBelow bound (left ++ right) := by
  intro t ht
  simp at ht
  rcases ht with ht | ht
  · exact hleft t ht
  · exact hright t ht

private theorem transitionSourcesAtLeast_append
    {bound : Nat} {left right : List TransitionDescription}
    (hleft : TransitionSourcesAtLeast bound left)
    (hright : TransitionSourcesAtLeast bound right) :
    TransitionSourcesAtLeast bound (left ++ right) := by
  intro t ht
  simp at ht
  rcases ht with ht | ht
  · exact hleft t ht
  · exact hright t ht

/-
Retargeted branch blocks for the future suffix-preserving singleton head
dispatcher.  They mirror the edge-only `singletonShape...RepairDescription`
blocks, but their local bodies first create the suffix gap and then run the
existing boundary repair leaf.
-/
def singletonHeadRefreshFinalHalt : Nat :=
  2

def singletonHeadLeftRepairOffset : Nat :=
  3

def singletonHeadLeftRepairDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    singletonHeadLeftRepairOffset
    singletonHeadRefreshFinalHalt
    (singletonLeftBoundaryHeadRefreshDescription gapCreator)

def singletonHeadLeftRepairStart
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadLeftRepairDescription gapCreator).start

def singletonHeadLeftRepairLimit
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadLeftRepairDescription gapCreator).stateCount

def singletonHeadRightRepairOffset
    (gapCreator : MachineDescription) : Nat :=
  singletonHeadLeftRepairLimit gapCreator

def singletonHeadRightRepairDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    (singletonHeadRightRepairOffset gapCreator)
    singletonHeadRefreshFinalHalt
    (singletonRightBoundaryHeadRefreshDescription gapCreator)

def singletonHeadRightRepairStart
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadRightRepairDescription gapCreator).start

def singletonHeadRightRepairLimit
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadRightRepairDescription gapCreator).stateCount

theorem singletonHeadRefreshFinalHalt_lt_leftRepairOffset :
    singletonHeadRefreshFinalHalt < singletonHeadLeftRepairOffset := by
  decide

theorem singletonHeadLeftRepairDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadLeftRepairDescription gapCreator).SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    singletonHeadRefreshFinalHalt_lt_leftRepairOffset
    (singletonLeftBoundaryHeadRefreshDescription_subroutineReady hgap).left

theorem singletonHeadRefreshFinalHalt_lt_rightRepairOffset
    (gapCreator : MachineDescription) :
    singletonHeadRefreshFinalHalt <
      singletonHeadRightRepairOffset gapCreator := by
  simp [singletonHeadRightRepairOffset, singletonHeadLeftRepairLimit,
    singletonHeadLeftRepairDescription,
    MachineDescription.offsetRetargetDescription]
  exact
    Nat.lt_of_lt_of_le
      (Nat.lt_succ_self singletonHeadRefreshFinalHalt)
      (Nat.le_max_right
        (singletonHeadLeftRepairOffset +
          (singletonLeftBoundaryHeadRefreshDescription gapCreator).stateCount)
        (singletonHeadRefreshFinalHalt + 1))

theorem singletonHeadRightRepairDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRightRepairDescription gapCreator).SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    (singletonHeadRefreshFinalHalt_lt_rightRepairOffset gapCreator)
    (singletonRightBoundaryHeadRefreshDescription_subroutineReady hgap).left

def singletonHeadTerminalProbeOffset
    (gapCreator : MachineDescription) : Nat :=
  singletonHeadRightRepairLimit gapCreator

def singletonHeadTerminalLocalCanonicalExit : Nat :=
  11

def singletonHeadTerminalLocalRightBoundaryExit : Nat :=
  12

def singletonHeadTerminalLocalUnusedExit : Nat :=
  13

def singletonHeadTerminalLocalTarget
    (cell : Option Bool) : Nat :=
  match cell with
  | none => singletonHeadTerminalLocalCanonicalExit
  | some false => singletonHeadTerminalLocalRightBoundaryExit
  | some true => singletonHeadTerminalLocalUnusedExit

def singletonHeadTerminalTarget
    (gapCreator : MachineDescription) (cell : Option Bool) : Nat :=
  match cell with
  | none => singletonHeadRefreshFinalHalt
  | some false => singletonHeadRightRepairStart gapCreator
  | some true => singletonHeadRefreshFinalHalt

def singletonHeadTerminalLocalDescription : MachineDescription :=
  singletonTerminalPairProbeDescription
    singletonHeadTerminalLocalCanonicalExit
    singletonHeadTerminalLocalRightBoundaryExit

def singletonHeadTerminalProbeDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  MachineDescription.offsetReadExitRetargetDescription
    (singletonHeadTerminalProbeOffset gapCreator)
    singletonHeadTerminalLocalTarget
    (singletonHeadTerminalTarget gapCreator)
    singletonHeadTerminalLocalDescription

def singletonHeadTerminalProbeStart
    (gapCreator : MachineDescription) : Nat :=
  (singletonHeadTerminalProbeDescription gapCreator).start

def singletonHeadRefreshOpeningDescription
    (gapCreator : MachineDescription) : MachineDescription :=
  singletonOpeningProbeDescription
    (singletonHeadTerminalProbeStart gapCreator)
    (singletonHeadLeftRepairStart gapCreator)

def singletonHeadRefreshDescription
    (gapCreator : MachineDescription) : MachineDescription where
  stateCount := (singletonHeadTerminalProbeDescription gapCreator).stateCount
  start := (singletonHeadRefreshOpeningDescription gapCreator).start
  halt := singletonHeadRefreshFinalHalt
  transitions :=
    (singletonHeadRefreshOpeningDescription gapCreator).transitions ++
      ((singletonHeadLeftRepairDescription gapCreator).transitions ++
        ((singletonHeadRightRepairDescription gapCreator).transitions ++
          (singletonHeadTerminalProbeDescription gapCreator).transitions))

theorem singletonHeadTerminalLocalDescription_subroutineReady :
    singletonHeadTerminalLocalDescription.SubroutineReady :=
  singletonTerminalPairProbeDescription_subroutineReady
    singletonHeadTerminalLocalCanonicalExit
    singletonHeadTerminalLocalRightBoundaryExit

theorem singletonHeadTerminalLocalDescription_transitionFreeAt
    (cell : Option Bool) :
    singletonHeadTerminalLocalDescription.TransitionFreeAt
      (singletonHeadTerminalLocalTarget cell) := by
  cases cell with
  | none =>
      exact
        transition_notFrom_of_all
          (l := singletonHeadTerminalLocalDescription.transitions)
          (state := singletonHeadTerminalLocalTarget none)
          (by decide)
  | some bit =>
      cases bit with
      | false =>
          exact
            transition_notFrom_of_all
              (l := singletonHeadTerminalLocalDescription.transitions)
              (state := singletonHeadTerminalLocalTarget (some false))
              (by decide)
      | true =>
          exact
            transition_notFrom_of_all
              (l := singletonHeadTerminalLocalDescription.transitions)
              (state := singletonHeadTerminalLocalTarget (some true))
              (by decide)

theorem singletonHeadTerminalTarget_lt_probeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    forall cell : Option Bool,
      singletonHeadTerminalTarget gapCreator cell <
        singletonHeadTerminalProbeOffset gapCreator := by
  intro cell
  cases cell with
  | none =>
      have hhalt :=
        (singletonHeadRightRepairDescription_subroutineReady
          hgap).left.right.right.left
      simpa [singletonHeadTerminalTarget,
        singletonHeadTerminalProbeOffset,
        singletonHeadRightRepairLimit,
        singletonHeadRightRepairDescription] using hhalt
  | some bit =>
      cases bit with
      | false =>
          have hstart :=
            (singletonHeadRightRepairDescription_subroutineReady
              hgap).left.right.left
          simpa [singletonHeadTerminalTarget,
            singletonHeadTerminalProbeOffset,
            singletonHeadRightRepairLimit,
            singletonHeadRightRepairStart] using hstart
      | true =>
          have hhalt :=
            (singletonHeadRightRepairDescription_subroutineReady
              hgap).left.right.right.left
          simpa [singletonHeadTerminalTarget,
            singletonHeadTerminalProbeOffset,
            singletonHeadRightRepairLimit,
            singletonHeadRightRepairDescription] using hhalt

theorem singletonHeadTerminalProbeDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadTerminalProbeDescription gapCreator).SubroutineReady :=
  MachineDescription.offsetReadExitRetargetDescription_subroutineReady
    (singletonHeadTerminalTarget_lt_probeOffset hgap)
    singletonHeadTerminalLocalDescription_subroutineReady.left

theorem singletonHeadRefreshOpeningDescription_subroutineReady
    (gapCreator : MachineDescription) :
    (singletonHeadRefreshOpeningDescription gapCreator).SubroutineReady :=
  singletonOpeningProbeDescription_subroutineReady
    (singletonHeadTerminalProbeStart gapCreator)
    (singletonHeadLeftRepairStart gapCreator)

theorem singletonHeadRefreshOpeningDescription_sources_below_leftRepairOffset
    (gapCreator : MachineDescription) :
    TransitionSourcesBelow singletonHeadLeftRepairOffset
      (singletonHeadRefreshOpeningDescription gapCreator).transitions := by
  intro t ht
  simp [singletonHeadRefreshOpeningDescription,
    singletonOpeningProbeDescription] at ht
  rcases ht with rfl | rfl | rfl
  · simpa using (by decide : 0 < singletonHeadLeftRepairOffset)
  · simpa using (by decide : 1 < singletonHeadLeftRepairOffset)
  · simpa using (by decide : 1 < singletonHeadLeftRepairOffset)

theorem singletonHeadLeftRepairDescription_sources_in_block
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    forall t : TransitionDescription,
      t ∈ (singletonHeadLeftRepairDescription gapCreator).transitions ->
        singletonHeadLeftRepairOffset ≤ t.source ∧
          t.source < singletonHeadLeftRepairLimit gapCreator := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonHeadLeftRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    ((singletonLeftBoundaryHeadRefreshDescription_subroutineReady
      hgap).left.right.right.right.left base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      singletonHeadLeftRepairLimit, singletonHeadLeftRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource singletonHeadLeftRepairOffset
    · exact Nat.le_max_left _ _

theorem singletonHeadRightRepairDescription_sources_in_block
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    forall t : TransitionDescription,
      t ∈ (singletonHeadRightRepairDescription gapCreator).transitions ->
        singletonHeadRightRepairOffset gapCreator ≤ t.source ∧
          t.source < singletonHeadRightRepairLimit gapCreator := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonHeadRightRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    ((singletonRightBoundaryHeadRefreshDescription_subroutineReady
      hgap).left.right.right.right.left base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      singletonHeadRightRepairLimit, singletonHeadRightRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource
        (singletonHeadRightRepairOffset gapCreator)
    · exact Nat.le_max_left _ _

theorem singletonHeadTerminalProbeDescription_sources_in_block
    (gapCreator : MachineDescription) :
    forall t : TransitionDescription,
      t ∈ (singletonHeadTerminalProbeDescription gapCreator).transitions ->
        singletonHeadTerminalProbeOffset gapCreator ≤ t.source ∧
          t.source <
            (singletonHeadTerminalProbeDescription gapCreator).stateCount := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonHeadTerminalProbeDescription,
        MachineDescription.offsetReadExitRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (singletonHeadTerminalLocalDescription_subroutineReady.left.right.right.right.left
      base hbase).left
  constructor
  · simp [MachineDescription.readExitRetargetStates]
  · simp [MachineDescription.readExitRetargetStates,
      singletonHeadTerminalProbeDescription,
      MachineDescription.offsetReadExitRetargetDescription]
    simpa [singletonHeadTerminalLocalDescription] using
      Nat.add_lt_add_left hsource
        (singletonHeadTerminalProbeOffset gapCreator)

theorem singletonHeadLeftRepairOffset_lt_rightRepairOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairOffset <
      singletonHeadRightRepairOffset gapCreator := by
  have hpos :=
    (singletonLeftBoundaryHeadRefreshDescription_subroutineReady
      hgap).left.left
  simp [singletonHeadRightRepairOffset, singletonHeadLeftRepairLimit,
    singletonHeadLeftRepairDescription,
    MachineDescription.offsetRetargetDescription]
  exact
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hpos singletonHeadLeftRepairOffset)
      (Nat.le_max_left _ _)

theorem singletonHeadLeftRepairOffset_le_rightRepairOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairOffset ≤
      singletonHeadRightRepairOffset gapCreator :=
  Nat.le_of_lt (singletonHeadLeftRepairOffset_lt_rightRepairOffset hgap)

theorem singletonHeadRightRepairOffset_lt_terminalProbeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadRightRepairOffset gapCreator <
      singletonHeadTerminalProbeOffset gapCreator := by
  have hpos :=
    (singletonRightBoundaryHeadRefreshDescription_subroutineReady
      hgap).left.left
  simp [singletonHeadTerminalProbeOffset, singletonHeadRightRepairLimit,
    singletonHeadRightRepairDescription,
    MachineDescription.offsetRetargetDescription]
  exact
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hpos
        (singletonHeadRightRepairOffset gapCreator))
      (Nat.le_max_left _ _)

theorem singletonHeadRightRepairOffset_le_terminalProbeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadRightRepairOffset gapCreator ≤
      singletonHeadTerminalProbeOffset gapCreator :=
  Nat.le_of_lt
    (singletonHeadRightRepairOffset_lt_terminalProbeOffset hgap)

theorem singletonHeadLeftRepairLimit_le_terminalProbeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairLimit gapCreator ≤
      singletonHeadTerminalProbeOffset gapCreator := by
  simpa [singletonHeadTerminalProbeOffset,
    singletonHeadRightRepairOffset] using
    singletonHeadRightRepairOffset_le_terminalProbeOffset hgap

theorem singletonHeadLeftRepairOffset_le_terminalProbeOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairOffset ≤
      singletonHeadTerminalProbeOffset gapCreator :=
  Nat.le_trans
    (singletonHeadLeftRepairOffset_le_rightRepairOffset hgap)
    (singletonHeadRightRepairOffset_le_terminalProbeOffset hgap)

theorem singletonHeadRefreshFinalHalt_lt_stateCount
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadRefreshFinalHalt <
      (singletonHeadRefreshDescription gapCreator).stateCount := by
  have hhalt :=
    (singletonHeadTerminalProbeDescription_subroutineReady
      hgap).left.right.right.left
  simpa [singletonHeadRefreshDescription,
    singletonHeadTerminalProbeDescription,
    singletonHeadTerminalTarget] using hhalt

theorem singletonHeadTerminalProbeOffset_lt_stateCount
    (gapCreator : MachineDescription) :
    singletonHeadTerminalProbeOffset gapCreator <
      (singletonHeadRefreshDescription gapCreator).stateCount := by
  have hpos := singletonHeadTerminalLocalDescription_subroutineReady.left.left
  simpa [singletonHeadRefreshDescription,
    singletonHeadTerminalProbeDescription,
    MachineDescription.offsetReadExitRetargetDescription] using
    Nat.lt_add_of_pos_right
      (n := singletonHeadTerminalProbeOffset gapCreator) hpos

theorem singletonHeadLeftRepairLimit_le_stateCount
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    singletonHeadLeftRepairLimit gapCreator ≤
      (singletonHeadRefreshDescription gapCreator).stateCount :=
  Nat.le_trans
    (singletonHeadLeftRepairLimit_le_terminalProbeOffset hgap)
    (Nat.le_of_lt
      (singletonHeadTerminalProbeOffset_lt_stateCount gapCreator))

theorem singletonHeadRightRepairLimit_le_stateCount
    (gapCreator : MachineDescription) :
    singletonHeadRightRepairLimit gapCreator ≤
      (singletonHeadRefreshDescription gapCreator).stateCount := by
  simpa [singletonHeadTerminalProbeOffset] using
    Nat.le_of_lt
      (singletonHeadTerminalProbeOffset_lt_stateCount gapCreator)

theorem singletonHeadLeftRepairDescription_sources_atLeast
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast singletonHeadLeftRepairOffset
      (singletonHeadLeftRepairDescription gapCreator).transitions := by
  intro t ht
  exact
    (singletonHeadLeftRepairDescription_sources_in_block hgap t ht).left

theorem singletonHeadRightRepairDescription_sources_atLeast_leftOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast singletonHeadLeftRepairOffset
      (singletonHeadRightRepairDescription gapCreator).transitions := by
  intro t ht
  have hsource :=
    (singletonHeadRightRepairDescription_sources_in_block hgap t ht).left
  exact Nat.le_trans
    (singletonHeadLeftRepairOffset_le_rightRepairOffset hgap) hsource

theorem singletonHeadTerminalProbeDescription_sources_atLeast_leftOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast singletonHeadLeftRepairOffset
      (singletonHeadTerminalProbeDescription gapCreator).transitions := by
  intro t ht
  have hsource :=
    (singletonHeadTerminalProbeDescription_sources_in_block
      gapCreator t ht).left
  exact Nat.le_trans
    (singletonHeadLeftRepairOffset_le_terminalProbeOffset hgap) hsource

theorem singletonHeadRightRepairDescription_sources_atLeast_rightOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast (singletonHeadRightRepairOffset gapCreator)
      (singletonHeadRightRepairDescription gapCreator).transitions := by
  intro t ht
  exact
    (singletonHeadRightRepairDescription_sources_in_block hgap t ht).left

theorem singletonHeadTerminalProbeDescription_sources_atLeast_rightOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesAtLeast (singletonHeadRightRepairOffset gapCreator)
      (singletonHeadTerminalProbeDescription gapCreator).transitions := by
  intro t ht
  have hsource :=
    (singletonHeadTerminalProbeDescription_sources_in_block
      gapCreator t ht).left
  exact Nat.le_trans
    (singletonHeadRightRepairOffset_le_terminalProbeOffset hgap) hsource

theorem singletonHeadTerminalProbeDescription_sources_atLeast_terminalOffset
    (gapCreator : MachineDescription) :
    TransitionSourcesAtLeast (singletonHeadTerminalProbeOffset gapCreator)
      (singletonHeadTerminalProbeDescription gapCreator).transitions := by
  intro t ht
  exact
    (singletonHeadTerminalProbeDescription_sources_in_block
      gapCreator t ht).left

theorem singletonHeadLeftRepairDescription_sources_below_rightOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesBelow (singletonHeadRightRepairOffset gapCreator)
      (singletonHeadLeftRepairDescription gapCreator).transitions := by
  intro t ht
  simpa [singletonHeadRightRepairOffset] using
    (singletonHeadLeftRepairDescription_sources_in_block hgap t ht).right

theorem singletonHeadRightRepairDescription_sources_below_terminalOffset
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionSourcesBelow (singletonHeadTerminalProbeOffset gapCreator)
      (singletonHeadRightRepairDescription gapCreator).transitions := by
  intro t ht
  simpa [singletonHeadTerminalProbeOffset] using
    (singletonHeadRightRepairDescription_sources_in_block hgap t ht).right

theorem singletonHeadRefreshDescription_transitions_wellFormed
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    forall t : TransitionDescription,
      t ∈ (singletonHeadRefreshDescription gapCreator).transitions ->
        TransitionDescription.WellFormed
          (singletonHeadRefreshDescription gapCreator).stateCount t := by
  intro t ht
  simp [singletonHeadRefreshDescription] at ht
  rcases ht with hopen | hleft | hright | hterminal
  · simp [singletonHeadRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopen
    rcases hopen with rfl | rfl | rfl
    · constructor
      · exact Nat.lt_trans
          (by
            simpa using
              (by decide : 0 < singletonHeadRefreshFinalHalt))
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap)
      · exact Nat.lt_trans
          (by
            simpa using
              (by decide : 1 < singletonHeadRefreshFinalHalt))
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap)
    · constructor
      · exact Nat.lt_trans
          (by
            simpa using
              (by decide : 1 < singletonHeadRefreshFinalHalt))
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap)
      · exact
          (singletonHeadTerminalProbeDescription_subroutineReady
            hgap).left.right.left
    · constructor
      · exact Nat.lt_trans
          (by
            simpa using
              (by decide : 1 < singletonHeadRefreshFinalHalt))
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap)
      · exact
          Nat.lt_of_lt_of_le
            (singletonHeadLeftRepairDescription_subroutineReady
              hgap).left.right.left
            (singletonHeadLeftRepairLimit_le_stateCount hgap)
  · have hformed :=
      (singletonHeadLeftRepairDescription_subroutineReady
        hgap).left.right.right.right.left t hleft
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        (singletonHeadLeftRepairLimit_le_stateCount hgap),
      Nat.lt_of_lt_of_le hformed.right
        (singletonHeadLeftRepairLimit_le_stateCount hgap)⟩
  · have hformed :=
      (singletonHeadRightRepairDescription_subroutineReady
        hgap).left.right.right.right.left t hright
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        (singletonHeadRightRepairLimit_le_stateCount gapCreator),
      Nat.lt_of_lt_of_le hformed.right
        (singletonHeadRightRepairLimit_le_stateCount gapCreator)⟩
  · exact
      (singletonHeadTerminalProbeDescription_subroutineReady
        hgap).left.right.right.right.left t hterminal

theorem singletonHeadRefreshDescription_transitionListDeterministic
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    TransitionListDeterministic
      (singletonHeadRefreshDescription gapCreator).transitions := by
  unfold singletonHeadRefreshDescription
  apply transitionListDeterministic_append_of_sourceDisjoint
  · exact
      (singletonHeadRefreshOpeningDescription_subroutineReady
        gapCreator).left.right.right.right.right
  · apply transitionListDeterministic_append_of_sourceDisjoint
    · exact
        (singletonHeadLeftRepairDescription_subroutineReady
          hgap).left.right.right.right.right
    · apply transitionListDeterministic_append_of_sourceDisjoint
      · exact
          (singletonHeadRightRepairDescription_subroutineReady
            hgap).left.right.right.right.right
      · exact
          (singletonHeadTerminalProbeDescription_subroutineReady
            hgap).left.right.right.right.right
      · apply transitionSourceDisjoint_of_below_atLeast
        · exact
            singletonHeadRightRepairDescription_sources_below_terminalOffset
              hgap
        · exact
            singletonHeadTerminalProbeDescription_sources_atLeast_terminalOffset
              gapCreator
    · apply transitionSourceDisjoint_of_below_atLeast
      · exact
          singletonHeadLeftRepairDescription_sources_below_rightOffset
            hgap
      · apply transitionSourcesAtLeast_append
        · exact
            singletonHeadRightRepairDescription_sources_atLeast_rightOffset
              hgap
        · exact
            singletonHeadTerminalProbeDescription_sources_atLeast_rightOffset
              hgap
  · apply transitionSourceDisjoint_of_below_atLeast
    · exact
        singletonHeadRefreshOpeningDescription_sources_below_leftRepairOffset
          gapCreator
    · apply transitionSourcesAtLeast_append
      · exact singletonHeadLeftRepairDescription_sources_atLeast hgap
      · apply transitionSourcesAtLeast_append
        · exact
            singletonHeadRightRepairDescription_sources_atLeast_leftOffset
              hgap
        · exact
            singletonHeadTerminalProbeDescription_sources_atLeast_leftOffset
              hgap

theorem singletonHeadRefreshDescription_deterministic
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRefreshDescription gapCreator).Deterministic :=
  singletonHeadRefreshDescription_transitionListDeterministic hgap

theorem singletonHeadRefreshDescription_wellFormed
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRefreshDescription gapCreator).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      Nat.lt_of_lt_of_le
        (by decide : 0 < singletonHeadRefreshFinalHalt)
        (Nat.le_of_lt
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap))
  · exact
      Nat.lt_of_lt_of_le
        (by decide : 0 < singletonHeadRefreshFinalHalt)
        (Nat.le_of_lt
          (singletonHeadRefreshFinalHalt_lt_stateCount hgap))
  · exact singletonHeadRefreshFinalHalt_lt_stateCount hgap
  · exact singletonHeadRefreshDescription_transitions_wellFormed hgap
  · exact singletonHeadRefreshDescription_deterministic hgap

theorem singletonHeadRefreshDescription_haltTransitionFree
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRefreshDescription gapCreator).HaltTransitionFree := by
  intro t ht
  simp [singletonHeadRefreshDescription] at ht
  rcases ht with hopening | hleft | hright | hterminal
  · simp [singletonHeadRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopening
    rcases hopening with rfl | rfl | rfl
    · simpa [singletonHeadRefreshDescription] using
        (by decide : 0 ≠ singletonHeadRefreshFinalHalt)
    · simpa [singletonHeadRefreshDescription] using
        (by decide : 1 ≠ singletonHeadRefreshFinalHalt)
    · simpa [singletonHeadRefreshDescription] using
        (by decide : 1 ≠ singletonHeadRefreshFinalHalt)
  · exact
      (singletonHeadLeftRepairDescription_subroutineReady
        hgap).right t hleft
  · exact
      (singletonHeadRightRepairDescription_subroutineReady
        hgap).right t hright
  · exact
      (singletonHeadTerminalProbeDescription_subroutineReady
        hgap).right t hterminal

theorem singletonHeadRefreshDescription_subroutineReady
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady) :
    (singletonHeadRefreshDescription gapCreator).SubroutineReady :=
  ⟨singletonHeadRefreshDescription_wellFormed hgap,
    singletonHeadRefreshDescription_haltTransitionFree hgap⟩

theorem singletonHeadLeftRepairDescription_haltsFrom_leftBoundary
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    (singletonHeadLeftRepairDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := [], head := head, right := right ++ [none] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := [], head := head, right := right } : Tape Bool) ::
            rest)) := by
  rcases hgap.leftBoundaryRefresh head right rest with
    ⟨actual, hhalts, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  simpa [singletonHeadLeftRepairDescription] using
    MachineDescription.offsetRetargetDescription_haltsFromTape
      singletonHeadRefreshFinalHalt_lt_leftRepairOffset
      (singletonLeftBoundaryHeadRefreshDescription_subroutineReady
        hgap.subroutineReady).right
      hhalts

theorem singletonHeadRightRepairDescription_haltsFrom_rightBoundary
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    (singletonHeadRightRepairDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := left, head := head, right := [] } : Tape Bool) ::
            rest)) := by
  rcases hgap.rightBoundaryRefresh left head rest with
    ⟨actual, hhalts, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  simpa [singletonHeadRightRepairDescription] using
    MachineDescription.offsetRetargetDescription_haltsFromTape
      (singletonHeadRefreshFinalHalt_lt_rightRepairOffset
        gapCreator)
      (singletonRightBoundaryHeadRefreshDescription_subroutineReady
        hgap.subroutineReady).right
      hhalts

private theorem find?_matches_none_of_sources_lt
    {l : List TransitionDescription} {state : Nat} {read : Option Bool}
    (hsource : forall t : TransitionDescription, t ∈ l -> t.source < state) :
    l.find? (MachineDescription.Matches state read) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have hstate : t.source = state := by
    unfold MachineDescription.Matches at hmatch
    simp at hmatch
    exact hmatch.left
  have hlt := hsource t ht
  lia

private theorem find?_matches_none_of_sources_gt
    {l : List TransitionDescription} {state : Nat} {read : Option Bool}
    (hsource : forall t : TransitionDescription, t ∈ l -> state < t.source) :
    l.find? (MachineDescription.Matches state read) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have hstate : t.source = state := by
    unfold MachineDescription.Matches at hmatch
    simp at hmatch
    exact hmatch.left
  have hlt := hsource t ht
  lia

theorem singletonHeadRefreshDescription_lookup_opening
    {gapCreator : MachineDescription} {state : Nat} {read : Option Bool}
    (hgap : gapCreator.SubroutineReady)
    (hstate : state < singletonHeadLeftRepairOffset) :
    MachineDescription.lookupTransition
        (singletonHeadRefreshDescription gapCreator) state read =
      MachineDescription.lookupTransition
        (singletonHeadRefreshOpeningDescription gapCreator) state read := by
  have hleft :
      (singletonHeadLeftRepairDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonHeadLeftRepairDescription_sources_in_block hgap t ht).left
    lia
  have hright :
      (singletonHeadRightRepairDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonHeadRightRepairDescription_sources_in_block hgap t ht).left
    have horder := singletonHeadLeftRepairOffset_le_rightRepairOffset hgap
    lia
  have hterminal :
      (singletonHeadTerminalProbeDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonHeadTerminalProbeDescription_sources_in_block
        gapCreator t ht).left
    have horder := singletonHeadLeftRepairOffset_le_terminalProbeOffset hgap
    lia
  simp [MachineDescription.lookupTransition,
    singletonHeadRefreshDescription, List.find?_append,
    hleft, hright, hterminal]

theorem singletonHeadRefreshDescription_lookup_leftRepair
    {gapCreator : MachineDescription} {state : Nat} {read : Option Bool}
    (hgap : gapCreator.SubroutineReady)
    (hlo : singletonHeadLeftRepairOffset ≤ state)
    (hhi : state < singletonHeadLeftRepairLimit gapCreator) :
    MachineDescription.lookupTransition
        (singletonHeadRefreshDescription gapCreator) state read =
      MachineDescription.lookupTransition
        (singletonHeadLeftRepairDescription gapCreator) state read := by
  have hopening :
      (singletonHeadRefreshOpeningDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      singletonHeadRefreshOpeningDescription_sources_below_leftRepairOffset
        gapCreator t ht
    lia
  have hright :
      (singletonHeadRightRepairDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonHeadRightRepairDescription_sources_in_block hgap t ht).left
    simp [singletonHeadRightRepairOffset] at hsrc
    lia
  have hterminal :
      (singletonHeadTerminalProbeDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonHeadTerminalProbeDescription_sources_in_block
        gapCreator t ht).left
    have hlimit := singletonHeadLeftRepairLimit_le_terminalProbeOffset hgap
    lia
  simp [MachineDescription.lookupTransition,
    singletonHeadRefreshDescription, List.find?_append,
    hopening, hright, hterminal]

theorem singletonHeadRefreshDescription_lookup_rightRepair
    {gapCreator : MachineDescription} {state : Nat} {read : Option Bool}
    (hgap : gapCreator.SubroutineReady)
    (hlo : singletonHeadRightRepairOffset gapCreator ≤ state)
    (hhi : state < singletonHeadRightRepairLimit gapCreator) :
    MachineDescription.lookupTransition
        (singletonHeadRefreshDescription gapCreator) state read =
      MachineDescription.lookupTransition
        (singletonHeadRightRepairDescription gapCreator) state read := by
  have hopening :
      (singletonHeadRefreshOpeningDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      singletonHeadRefreshOpeningDescription_sources_below_leftRepairOffset
        gapCreator t ht
    have horder := singletonHeadLeftRepairOffset_le_rightRepairOffset hgap
    lia
  have hleft :
      (singletonHeadLeftRepairDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (singletonHeadLeftRepairDescription_sources_in_block hgap t ht).right
    simp [singletonHeadRightRepairOffset] at hlo
    lia
  have hterminal :
      (singletonHeadTerminalProbeDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonHeadTerminalProbeDescription_sources_in_block
        gapCreator t ht).left
    simp [singletonHeadTerminalProbeOffset] at hsrc
    lia
  simp [MachineDescription.lookupTransition,
    singletonHeadRefreshDescription, List.find?_append,
    hopening, hleft, hterminal]

theorem singletonHeadRefreshDescription_lookup_terminalProbe
    {gapCreator : MachineDescription} {state : Nat} {read : Option Bool}
    (hgap : gapCreator.SubroutineReady)
    (hstate : singletonHeadTerminalProbeOffset gapCreator ≤ state) :
    MachineDescription.lookupTransition
        (singletonHeadRefreshDescription gapCreator) state read =
      MachineDescription.lookupTransition
        (singletonHeadTerminalProbeDescription gapCreator) state read := by
  have hopening :
      (singletonHeadRefreshOpeningDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      singletonHeadRefreshOpeningDescription_sources_below_leftRepairOffset
        gapCreator t ht
    have horder := singletonHeadLeftRepairOffset_le_terminalProbeOffset hgap
    lia
  have hleft :
      (singletonHeadLeftRepairDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (singletonHeadLeftRepairDescription_sources_in_block hgap t ht).right
    have hlimit := singletonHeadLeftRepairLimit_le_terminalProbeOffset hgap
    lia
  have hright :
      (singletonHeadRightRepairDescription gapCreator).transitions.find?
          (MachineDescription.Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (singletonHeadRightRepairDescription_sources_in_block hgap t ht).right
    have hsrc' :
        t.source < singletonHeadTerminalProbeOffset gapCreator := by
      simpa [singletonHeadTerminalProbeOffset] using hsrc
    lia
  simp [MachineDescription.lookupTransition,
    singletonHeadRefreshDescription, List.find?_append,
    hopening, hleft, hright]

theorem singletonHeadRefreshDescription_stepConfig_opening
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (c : MachineDescription.Configuration)
    (hstate : c.state < singletonHeadLeftRepairOffset) :
    MachineDescription.stepConfig (singletonHeadRefreshDescription gapCreator) c =
      MachineDescription.stepConfig
        (singletonHeadRefreshOpeningDescription gapCreator) c := by
  unfold MachineDescription.stepConfig
  rw [singletonHeadRefreshDescription_lookup_opening hgap hstate]

theorem singletonHeadRefreshDescription_stepConfig_leftRepair
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (c : MachineDescription.Configuration)
    (hlo : singletonHeadLeftRepairOffset ≤ c.state)
    (hhi : c.state < singletonHeadLeftRepairLimit gapCreator) :
    MachineDescription.stepConfig (singletonHeadRefreshDescription gapCreator) c =
      MachineDescription.stepConfig
        (singletonHeadLeftRepairDescription gapCreator) c := by
  unfold MachineDescription.stepConfig
  rw [singletonHeadRefreshDescription_lookup_leftRepair hgap hlo hhi]

theorem singletonHeadRefreshDescription_stepConfig_rightRepair
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (c : MachineDescription.Configuration)
    (hlo : singletonHeadRightRepairOffset gapCreator ≤ c.state)
    (hhi : c.state < singletonHeadRightRepairLimit gapCreator) :
    MachineDescription.stepConfig (singletonHeadRefreshDescription gapCreator) c =
      MachineDescription.stepConfig
        (singletonHeadRightRepairDescription gapCreator) c := by
  unfold MachineDescription.stepConfig
  rw [singletonHeadRefreshDescription_lookup_rightRepair hgap hlo hhi]

theorem singletonHeadRefreshDescription_stepConfig_terminalProbe
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (c : MachineDescription.Configuration)
    (hstate : singletonHeadTerminalProbeOffset gapCreator ≤ c.state) :
    MachineDescription.stepConfig (singletonHeadRefreshDescription gapCreator) c =
      MachineDescription.stepConfig
        (singletonHeadTerminalProbeDescription gapCreator) c := by
  unfold MachineDescription.stepConfig
  rw [singletonHeadRefreshDescription_lookup_terminalProbe hgap hstate]

private theorem source_eq_of_lookupTransition
    {D : MachineDescription} {state : Nat} {read : Option Bool}
    {t : TransitionDescription}
    (hlookup : D.lookupTransition state read = some t) :
    t.source = state := by
  have hmatch : MachineDescription.Matches state read t = true := by
    unfold MachineDescription.lookupTransition at hlookup
    exact List.find?_some hlookup
  unfold MachineDescription.Matches at hmatch
  simp at hmatch
  exact hmatch.left

private theorem singletonHeadRefreshDescription_stepConfig_of_opening_some
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig
        (singletonHeadRefreshOpeningDescription gapCreator) c =
          some next) :
    MachineDescription.stepConfig
        (singletonHeadRefreshDescription gapCreator) c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition
        (singletonHeadRefreshOpeningDescription gapCreator)
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbound :=
        singletonHeadRefreshOpeningDescription_sources_below_leftRepairOffset
          gapCreator t htmem
      have hstate : c.state < singletonHeadLeftRepairOffset := by
        lia
      rw [singletonHeadRefreshDescription_lookup_opening hgap hstate]
      simpa [hlookup] using hstep

private theorem singletonHeadRefreshDescription_stepConfig_of_leftRepair_some
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig
        (singletonHeadLeftRepairDescription gapCreator) c =
          some next) :
    MachineDescription.stepConfig
        (singletonHeadRefreshDescription gapCreator) c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition
        (singletonHeadLeftRepairDescription gapCreator)
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        singletonHeadLeftRepairDescription_sources_in_block hgap t htmem
      have hlo : singletonHeadLeftRepairOffset ≤ c.state := by
        lia
      have hhi : c.state < singletonHeadLeftRepairLimit gapCreator := by
        lia
      rw [singletonHeadRefreshDescription_lookup_leftRepair hgap hlo hhi]
      simpa [hlookup] using hstep

private theorem singletonHeadRefreshDescription_stepConfig_of_rightRepair_some
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig
        (singletonHeadRightRepairDescription gapCreator) c =
          some next) :
    MachineDescription.stepConfig
        (singletonHeadRefreshDescription gapCreator) c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition
        (singletonHeadRightRepairDescription gapCreator)
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        singletonHeadRightRepairDescription_sources_in_block hgap t htmem
      have hlo : singletonHeadRightRepairOffset gapCreator ≤ c.state := by
        lia
      have hhi : c.state < singletonHeadRightRepairLimit gapCreator := by
        lia
      rw [singletonHeadRefreshDescription_lookup_rightRepair hgap hlo hhi]
      simpa [hlookup] using hstep

private theorem singletonHeadRefreshDescription_stepConfig_of_terminalProbe_some
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig
        (singletonHeadTerminalProbeDescription gapCreator) c =
          some next) :
    MachineDescription.stepConfig
        (singletonHeadRefreshDescription gapCreator) c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition
        (singletonHeadTerminalProbeDescription gapCreator)
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        singletonHeadTerminalProbeDescription_sources_in_block
          gapCreator t htmem
      have hlo : singletonHeadTerminalProbeOffset gapCreator ≤ c.state := by
        lia
      rw [singletonHeadRefreshDescription_lookup_terminalProbe hgap hlo]
      simpa [hlookup] using hstep

private theorem singletonHeadRefreshDescription_runConfig_eq_to_halt
    {gapCreator D : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (hstep :
      forall {c next : MachineDescription.Configuration},
        MachineDescription.stepConfig D c = some next ->
          MachineDescription.stepConfig
              (singletonHeadRefreshDescription gapCreator) c =
            some next) :
    forall (n : Nat) (c : MachineDescription.Configuration) (T : Tape Bool),
      D.runConfig n c =
          { state := singletonHeadRefreshFinalHalt, tape := T } ->
        (singletonHeadRefreshDescription gapCreator).runConfig n c =
          { state := singletonHeadRefreshFinalHalt, tape := T } := by
  intro n
  induction n with
  | zero =>
      intro c T hrun
      simpa [MachineDescription.runConfig] using hrun
  | succ n ih =>
      intro c T hrun
      simp only [MachineDescription.runConfig] at hrun ⊢
      cases hlocal : MachineDescription.stepConfig D c with
      | none =>
          simp [hlocal] at hrun
          subst c
          have hfree :
              (singletonHeadRefreshDescription gapCreator).TransitionFreeAt
                singletonHeadRefreshFinalHalt := by
            intro t ht hsource
            exact singletonHeadRefreshDescription_haltTransitionFree
              hgap t ht (by
                simpa [singletonHeadRefreshDescription] using hsource)
          have hnone :
              MachineDescription.stepConfig
                  (singletonHeadRefreshDescription gapCreator)
                  { state := singletonHeadRefreshFinalHalt, tape := T } =
                none := by
            unfold MachineDescription.stepConfig
            rw [MachineDescription.lookupTransition_state_none hfree]
          simp [hnone]
      | some next =>
          have hfull := hstep hlocal
          have htail :
              D.runConfig n next =
                { state := singletonHeadRefreshFinalHalt, tape := T } := by
            simpa [hlocal] using hrun
          simp [hfull]
          exact ih next T htail

private theorem exists_first_le
    {p : Nat -> Prop} [DecidablePred p] :
    forall n : Nat,
      (exists k : Nat, k ≤ n ∧ p k) ->
        exists m : Nat, p m ∧ m ≤ n ∧
          forall k : Nat, k < m -> ¬ p k
  | 0, hexists => by
      rcases hexists with ⟨k, hk, hpk⟩
      have hk0 : k = 0 := by
        lia
      subst k
      exact ⟨0, hpk, by decide, by intro k hk; cases hk⟩
  | n + 1, hexists => by
      by_cases hprev : exists k : Nat, k ≤ n ∧ p k
      · rcases exists_first_le (p := p) n hprev with
          ⟨m, hpm, hmle, hmin⟩
        exact ⟨m, hpm, Nat.le_trans hmle (Nat.le_succ n), hmin⟩
      · rcases hexists with ⟨k, hk, hpk⟩
        have hk_last : k = n + 1 := by
          by_cases hkle : k ≤ n
          · exact False.elim (hprev ⟨k, hkle, hpk⟩)
          · lia
        subst k
        refine ⟨n + 1, hpk, Nat.le_refl _, ?_⟩
        intro k hk hpk'
        have hkle : k ≤ n := by
          lia
        exact hprev ⟨k, hkle, hpk'⟩

private theorem exists_first_of_exists
    {p : Nat -> Prop} [DecidablePred p]
    (hexists : exists n : Nat, p n) :
    exists m : Nat, p m ∧ forall k : Nat, k < m -> ¬ p k := by
  rcases hexists with ⟨n, hpn⟩
  rcases exists_first_le (p := p) n ⟨n, Nat.le_refl _, hpn⟩ with
    ⟨m, hpm, _hmle, hmin⟩
  exact ⟨m, hpm, hmin⟩

private theorem singletonHeadRefreshDescription_runConfig_eq_until
    {gapCreator D : MachineDescription}
    (hstep :
      forall {c next : MachineDescription.Configuration},
        MachineDescription.stepConfig D c = some next ->
          MachineDescription.stepConfig
              (singletonHeadRefreshDescription gapCreator) c =
            some next) :
    forall (n : Nat) (c final : MachineDescription.Configuration),
      (forall k : Nat, k < n -> D.runConfig k c ≠ final) ->
        D.runConfig n c = final ->
          (singletonHeadRefreshDescription gapCreator).runConfig n c =
            final := by
  intro n
  induction n with
  | zero =>
      intro c final _hfirst hrun
      simpa [MachineDescription.runConfig] using hrun
  | succ n ih =>
      intro c final hfirst hrun
      simp only [MachineDescription.runConfig] at hrun ⊢
      cases hlocal : MachineDescription.stepConfig D c with
      | none =>
          simp [hlocal] at hrun
          exact False.elim (hfirst 0 (Nat.succ_pos n) hrun)
      | some next =>
          have hfull := hstep hlocal
          have htail :
              D.runConfig n next = final := by
            simpa [hlocal] using hrun
          have hfirstTail :
              forall k : Nat, k < n -> D.runConfig k next ≠ final := by
            intro k hk hhit
            have hrunSucc :
                D.runConfig (k + 1) c = final := by
              simp [MachineDescription.runConfig, hlocal, hhit]
            exact hfirst (k + 1) (Nat.succ_lt_succ hk) hrunSucc
          simp [hfull]
          exact ih next final hfirstTail htail

theorem singletonHeadRefreshDescription_reaches_opening_canonical
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonHeadRefreshDescription gapCreator).runConfig steps
          { state := (singletonHeadRefreshDescription gapCreator).start
            tape :=
              encodedStructuredTapes (guardLogicalTape target :: rest) } =
        { state := singletonHeadTerminalProbeStart gapCreator
          tape :=
            encodedStructuredTapes (guardLogicalTape target :: rest) } := by
  let startConfig : MachineDescription.Configuration :=
    { state := (singletonHeadRefreshDescription gapCreator).start
      tape := encodedStructuredTapes (guardLogicalTape target :: rest) }
  let finalConfig : MachineDescription.Configuration :=
    { state := singletonHeadTerminalProbeStart gapCreator
      tape := encodedStructuredTapes (guardLogicalTape target :: rest) }
  have hopening :
      (singletonHeadRefreshOpeningDescription gapCreator).runConfig 2
          startConfig = finalConfig := by
    exact
      singletonOpeningProbeDescription_run_false_of_reads
        (singletonHeadTerminalProbeStart gapCreator)
        (singletonHeadLeftRepairStart gapCreator)
        (encodedStructuredTapes (guardLogicalTape target :: rest))
        (encodedStructuredTapes_read _)
        (by
          cases target with
          | mk left head right =>
              simp [encodedStructuredTapes, encodedStructuredTapeCells,
                guardLogicalTape, logicalTapeCode, logicalCellCode,
                logicalCellListBits, logicalCellBits, tapeSeparatorCells,
                tapeAtCells, Tape.read, Tape.moveRight])
  have hexists :
      exists steps : Nat,
        (singletonHeadRefreshOpeningDescription gapCreator).runConfig
          steps startConfig = finalConfig :=
    ⟨2, hopening⟩
  rcases exists_first_of_exists hexists with ⟨steps, hsteps, hfirst⟩
  exact
    ⟨steps,
      singletonHeadRefreshDescription_runConfig_eq_until
        (singletonHeadRefreshDescription_stepConfig_of_opening_some hgap)
        steps startConfig finalConfig hfirst hsteps⟩

theorem singletonHeadRefreshDescription_reaches_opening_leftBoundary
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonHeadRefreshDescription gapCreator).runConfig steps
          { state := (singletonHeadRefreshDescription gapCreator).start
            tape :=
              encodedStructuredTapes
                (({ left := [], head := head, right := right ++ [none] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadLeftRepairStart gapCreator
          tape :=
            encodedStructuredTapes
              (({ left := [], head := head, right := right ++ [none] } :
                Tape Bool) :: rest) } := by
  let startConfig : MachineDescription.Configuration :=
    { state := (singletonHeadRefreshDescription gapCreator).start
      tape :=
        encodedStructuredTapes
          (({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) :: rest) }
  let finalConfig : MachineDescription.Configuration :=
    { state := singletonHeadLeftRepairStart gapCreator
      tape :=
        encodedStructuredTapes
          (({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) :: rest) }
  have hopening :
      (singletonHeadRefreshOpeningDescription gapCreator).runConfig 2
          startConfig = finalConfig := by
    exact
      singletonOpeningProbeDescription_run_true_of_reads
        (singletonHeadTerminalProbeStart gapCreator)
        (singletonHeadLeftRepairStart gapCreator)
        (encodedStructuredTapes
          (({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) :: rest))
        (encodedStructuredTapes_read _)
        (by
          simp [encodedStructuredTapes, encodedStructuredTapeCells,
            logicalTapeCode, logicalCellCode, logicalCellListBits,
            logicalCellBits, headMarkerCells, tapeSeparatorCells,
            tapeAtCells, Tape.read, Tape.moveRight])
  have hexists :
      exists steps : Nat,
        (singletonHeadRefreshOpeningDescription gapCreator).runConfig
          steps startConfig = finalConfig :=
    ⟨2, hopening⟩
  rcases exists_first_of_exists hexists with ⟨steps, hsteps, hfirst⟩
  exact
    ⟨steps,
      singletonHeadRefreshDescription_runConfig_eq_until
        (singletonHeadRefreshDescription_stepConfig_of_opening_some hgap)
        steps startConfig finalConfig hfirst hsteps⟩

theorem singletonHeadRefreshDescription_reaches_opening_rightBoundary
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonHeadRefreshDescription gapCreator).runConfig steps
          { state := (singletonHeadRefreshDescription gapCreator).start
            tape :=
              encodedStructuredTapes
                (({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadTerminalProbeStart gapCreator
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) } := by
  let startConfig : MachineDescription.Configuration :=
    { state := (singletonHeadRefreshDescription gapCreator).start
      tape :=
        encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest) }
  let finalConfig : MachineDescription.Configuration :=
    { state := singletonHeadTerminalProbeStart gapCreator
      tape :=
        encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest) }
  have hopening :
      (singletonHeadRefreshOpeningDescription gapCreator).runConfig 2
          startConfig = finalConfig := by
    exact
      singletonOpeningProbeDescription_run_false_of_reads
        (singletonHeadTerminalProbeStart gapCreator)
        (singletonHeadLeftRepairStart gapCreator)
        (encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest))
        (encodedStructuredTapes_read _)
        (by
          simp [encodedStructuredTapes, encodedStructuredTapeCells,
            logicalTapeCode, logicalCellCode, logicalCellListBits,
            logicalCellBits, tapeSeparatorCells, tapeAtCells, Tape.read,
            Tape.moveRight, List.reverse_append])
  have hexists :
      exists steps : Nat,
        (singletonHeadRefreshOpeningDescription gapCreator).runConfig
          steps startConfig = finalConfig :=
    ⟨2, hopening⟩
  rcases exists_first_of_exists hexists with ⟨steps, hsteps, hfirst⟩
  exact
    ⟨steps,
      singletonHeadRefreshDescription_runConfig_eq_until
        (singletonHeadRefreshDescription_stepConfig_of_opening_some hgap)
        steps startConfig finalConfig hfirst hsteps⟩

theorem singletonHeadTerminalProbeDescription_reaches_canonical
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonHeadRefreshDescription gapCreator).runConfig steps
          { state := singletonHeadTerminalProbeStart gapCreator
            tape :=
              encodedStructuredTapes (guardLogicalTape target :: rest) } =
        { state := singletonHeadRefreshFinalHalt
          tape :=
            encodedStructuredTapes (guardLogicalTape target :: rest) } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_canonical_cons
        singletonHeadTerminalLocalCanonicalExit
        singletonHeadTerminalLocalRightBoundaryExit
        target rest with
    ⟨steps, hrun⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonHeadTerminalProbeOffset gapCreator)
      (localTarget := singletonHeadTerminalLocalTarget)
      (target := singletonHeadTerminalTarget gapCreator)
      (singletonHeadTerminalTarget_lt_probeOffset hgap)
      singletonHeadTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  have hterminal :
      (singletonHeadTerminalProbeDescription gapCreator).runConfig steps
          { state := singletonHeadTerminalProbeStart gapCreator
            tape :=
              encodedStructuredTapes (guardLogicalTape target :: rest) } =
        { state := singletonHeadRefreshFinalHalt
          tape :=
            encodedStructuredTapes (guardLogicalTape target :: rest) } := by
    simpa [singletonHeadTerminalProbeDescription,
      singletonHeadTerminalProbeStart, singletonHeadTerminalLocalDescription,
      singletonHeadTerminalLocalTarget, singletonHeadTerminalTarget,
      MachineDescription.readExitRetargetConfiguration,
      MachineDescription.retargetReadExitState] using hcopy
  exact
    ⟨steps,
      singletonHeadRefreshDescription_runConfig_eq_to_halt hgap
        (singletonHeadRefreshDescription_stepConfig_of_terminalProbe_some
          hgap)
        steps
        { state := singletonHeadTerminalProbeStart gapCreator
          tape :=
            encodedStructuredTapes (guardLogicalTape target :: rest) }
        (encodedStructuredTapes (guardLogicalTape target :: rest))
        hterminal⟩

theorem singletonHeadTerminalProbeDescription_reaches_rightBoundary
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonHeadRefreshDescription gapCreator).runConfig steps
          { state := singletonHeadTerminalProbeStart gapCreator
            tape :=
              encodedStructuredTapes
                (({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadRightRepairStart gapCreator
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) } := by
  let startConfig : MachineDescription.Configuration :=
    { state := singletonHeadTerminalProbeStart gapCreator
      tape :=
        encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest) }
  let finalConfig : MachineDescription.Configuration :=
    { state := singletonHeadRightRepairStart gapCreator
      tape :=
        encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest) }
  rcases
      singletonTerminalPairProbeDescription_reaches_rightBoundary_cons
        singletonHeadTerminalLocalCanonicalExit
        singletonHeadTerminalLocalRightBoundaryExit
        left head rest with
    ⟨steps, hrun⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonHeadTerminalProbeOffset gapCreator)
      (localTarget := singletonHeadTerminalLocalTarget)
      (target := singletonHeadTerminalTarget gapCreator)
      (singletonHeadTerminalTarget_lt_probeOffset hgap)
      singletonHeadTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  have hterminal :
      (singletonHeadTerminalProbeDescription gapCreator).runConfig steps
          startConfig = finalConfig := by
    simpa [startConfig, finalConfig, singletonHeadTerminalProbeDescription,
      singletonHeadTerminalProbeStart, singletonHeadTerminalLocalDescription,
      singletonHeadTerminalLocalTarget, singletonHeadTerminalTarget,
      MachineDescription.readExitRetargetConfiguration,
      MachineDescription.retargetReadExitState] using hcopy
  have hexists :
      exists steps : Nat,
        (singletonHeadTerminalProbeDescription gapCreator).runConfig
          steps startConfig = finalConfig :=
    ⟨steps, hterminal⟩
  rcases exists_first_of_exists hexists with ⟨firstSteps, hsteps, hfirst⟩
  exact
    ⟨firstSteps,
      singletonHeadRefreshDescription_runConfig_eq_until
        (singletonHeadRefreshDescription_stepConfig_of_terminalProbe_some
          hgap)
        firstSteps startConfig finalConfig hfirst hsteps⟩

theorem singletonHeadRefreshDescription_reaches_leftRepair
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    exists (actual : Tape Bool) (steps : Nat),
      (singletonHeadRefreshDescription gapCreator).runConfig steps
          { state := singletonHeadLeftRepairStart gapCreator
            tape :=
              encodedStructuredTapes
                (({ left := [], head := head, right := right ++ [none] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadRefreshFinalHalt, tape := actual } ∧
      Tape.Equiv actual
        (encodedStructuredTapes
          (guardLogicalTape
            ({ left := [], head := head, right := right } : Tape Bool) ::
              rest)) := by
  rcases singletonHeadLeftRepairDescription_haltsFrom_leftBoundary
      hgap head right rest with
    ⟨actual, hhalts, hequiv⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hhalts with
    ⟨steps, hrun⟩
  refine ⟨actual, steps, ?_, hequiv⟩
  have hrun' :
      (singletonHeadLeftRepairDescription gapCreator).runConfig steps
          { state := singletonHeadLeftRepairStart gapCreator
            tape :=
              encodedStructuredTapes
                (({ left := [], head := head, right := right ++ [none] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadRefreshFinalHalt, tape := actual } := by
    simpa [singletonHeadLeftRepairStart,
      singletonHeadLeftRepairDescription,
      MachineDescription.offsetRetargetDescription] using hrun
  exact
    singletonHeadRefreshDescription_runConfig_eq_to_halt
      hgap.subroutineReady
      (singletonHeadRefreshDescription_stepConfig_of_leftRepair_some
        hgap.subroutineReady)
      steps
      { state := singletonHeadLeftRepairStart gapCreator
        tape :=
          encodedStructuredTapes
            (({ left := [], head := head, right := right ++ [none] } :
              Tape Bool) :: rest) }
      actual
      hrun'

theorem singletonHeadRefreshDescription_reaches_rightRepair
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists (actual : Tape Bool) (steps : Nat),
      (singletonHeadRefreshDescription gapCreator).runConfig steps
          { state := singletonHeadRightRepairStart gapCreator
            tape :=
              encodedStructuredTapes
                (({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadRefreshFinalHalt, tape := actual } ∧
      Tape.Equiv actual
        (encodedStructuredTapes
          (guardLogicalTape
            ({ left := left, head := head, right := [] } : Tape Bool) ::
              rest)) := by
  rcases singletonHeadRightRepairDescription_haltsFrom_rightBoundary
      hgap left head rest with
    ⟨actual, hhalts, hequiv⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hhalts with
    ⟨steps, hrun⟩
  refine ⟨actual, steps, ?_, hequiv⟩
  have hrun' :
      (singletonHeadRightRepairDescription gapCreator).runConfig steps
          { state := singletonHeadRightRepairStart gapCreator
            tape :=
              encodedStructuredTapes
                (({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadRefreshFinalHalt, tape := actual } := by
    simpa [singletonHeadRightRepairStart,
      singletonHeadRightRepairDescription,
      MachineDescription.offsetRetargetDescription] using hrun
  exact
    singletonHeadRefreshDescription_runConfig_eq_to_halt
      hgap.subroutineReady
      (singletonHeadRefreshDescription_stepConfig_of_rightRepair_some
        hgap.subroutineReady)
      steps
      { state := singletonHeadRightRepairStart gapCreator
        tape :=
          encodedStructuredTapes
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest) }
      actual
      hrun'

theorem singletonHeadRefreshDescription_haltsFrom_canonical
    {gapCreator : MachineDescription}
    (hgap : gapCreator.SubroutineReady)
    (target : Tape Bool) (rest : List (Tape Bool)) :
    (singletonHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes (guardLogicalTape target :: rest))
      (encodedStructuredTapes (guardLogicalTape target :: rest)) := by
  rcases singletonHeadRefreshDescription_reaches_opening_canonical
      hgap target rest with
    ⟨openingSteps, hopening⟩
  rcases singletonHeadTerminalProbeDescription_reaches_canonical
      hgap target rest with
    ⟨terminalSteps, hterminal⟩
  refine
    ⟨encodedStructuredTapes (guardLogicalTape target :: rest), ?_,
      Tape.Equiv.refl _⟩
  refine ⟨openingSteps + terminalSteps, ?_⟩
  have hrun :
      (singletonHeadRefreshDescription gapCreator).runConfig
          (openingSteps + terminalSteps)
          { state := (singletonHeadRefreshDescription gapCreator).start
            tape :=
              encodedStructuredTapes (guardLogicalTape target :: rest) } =
        { state := singletonHeadRefreshFinalHalt
          tape :=
            encodedStructuredTapes (guardLogicalTape target :: rest) } := by
    rw [MachineDescription.runConfig_add]
    rw [hopening]
    exact hterminal
  change
    ((singletonHeadRefreshDescription gapCreator).runConfig
      (openingSteps + terminalSteps)
      { state := (singletonHeadRefreshDescription gapCreator).start
        tape :=
          encodedStructuredTapes (guardLogicalTape target :: rest) }).state =
        (singletonHeadRefreshDescription gapCreator).halt ∧
      ((singletonHeadRefreshDescription gapCreator).runConfig
        (openingSteps + terminalSteps)
        { state := (singletonHeadRefreshDescription gapCreator).start
          tape :=
            encodedStructuredTapes (guardLogicalTape target :: rest) }).tape =
        encodedStructuredTapes (guardLogicalTape target :: rest)
  rw [hrun]
  simp [singletonHeadRefreshDescription]

theorem singletonHeadRefreshDescription_haltsFrom_leftBoundary
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    (singletonHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := [], head := head, right := right ++ [none] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := [], head := head, right := right } : Tape Bool) ::
            rest)) := by
  rcases singletonHeadRefreshDescription_reaches_opening_leftBoundary
      hgap.subroutineReady head right rest with
    ⟨openingSteps, hopening⟩
  rcases singletonHeadRefreshDescription_reaches_leftRepair
      hgap head right rest with
    ⟨actual, repairSteps, hrepair, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  refine ⟨openingSteps + repairSteps, ?_⟩
  have hrun :
      (singletonHeadRefreshDescription gapCreator).runConfig
          (openingSteps + repairSteps)
          { state := (singletonHeadRefreshDescription gapCreator).start
            tape :=
              encodedStructuredTapes
                (({ left := [], head := head, right := right ++ [none] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadRefreshFinalHalt, tape := actual } := by
    rw [MachineDescription.runConfig_add]
    rw [hopening]
    exact hrepair
  change
    ((singletonHeadRefreshDescription gapCreator).runConfig
      (openingSteps + repairSteps)
      { state := (singletonHeadRefreshDescription gapCreator).start
        tape :=
          encodedStructuredTapes
            (({ left := [], head := head, right := right ++ [none] } :
              Tape Bool) :: rest) }).state =
        (singletonHeadRefreshDescription gapCreator).halt ∧
      ((singletonHeadRefreshDescription gapCreator).runConfig
        (openingSteps + repairSteps)
        { state := (singletonHeadRefreshDescription gapCreator).start
          tape :=
            encodedStructuredTapes
              (({ left := [], head := head, right := right ++ [none] } :
                Tape Bool) :: rest) }).tape =
        actual
  rw [hrun]
  simp [singletonHeadRefreshDescription]

theorem singletonHeadRefreshDescription_haltsFrom_rightBoundary
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    (singletonHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := left, head := head, right := [] } : Tape Bool) ::
            rest)) := by
  rcases singletonHeadRefreshDescription_reaches_opening_rightBoundary
      hgap.subroutineReady left head rest with
    ⟨openingSteps, hopening⟩
  rcases singletonHeadTerminalProbeDescription_reaches_rightBoundary
      hgap.subroutineReady left head rest with
    ⟨terminalSteps, hterminal⟩
  rcases singletonHeadRefreshDescription_reaches_rightRepair
      hgap left head rest with
    ⟨actual, repairSteps, hrepair, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  refine ⟨openingSteps + terminalSteps + repairSteps, ?_⟩
  have hprefix :
      (singletonHeadRefreshDescription gapCreator).runConfig
          (openingSteps + terminalSteps)
          { state := (singletonHeadRefreshDescription gapCreator).start
            tape :=
              encodedStructuredTapes
                (({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadRightRepairStart gapCreator
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) } := by
    rw [MachineDescription.runConfig_add]
    rw [hopening]
    exact hterminal
  have hrun :
      (singletonHeadRefreshDescription gapCreator).runConfig
          (openingSteps + terminalSteps + repairSteps)
          { state := (singletonHeadRefreshDescription gapCreator).start
            tape :=
              encodedStructuredTapes
                (({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool) :: rest) } =
        { state := singletonHeadRefreshFinalHalt, tape := actual } := by
    rw [MachineDescription.runConfig_add]
    rw [hprefix]
    exact hrepair
  change
    ((singletonHeadRefreshDescription gapCreator).runConfig
      (openingSteps + terminalSteps + repairSteps)
      { state := (singletonHeadRefreshDescription gapCreator).start
        tape :=
          encodedStructuredTapes
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest) }).state =
        (singletonHeadRefreshDescription gapCreator).halt ∧
      ((singletonHeadRefreshDescription gapCreator).runConfig
        (openingSteps + terminalSteps + repairSteps)
        { state := (singletonHeadRefreshDescription gapCreator).start
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) }).tape =
        actual
  rw [hrun]
  simp [singletonHeadRefreshDescription]

structure SingletonHeadGuardSlackRefreshCaseContract
    (refresh : MachineDescription) : Prop where
  subroutineReady : refresh.SubroutineReady
  canonical :
    forall (target : Tape Bool) (rest : List (Tape Bool)),
      refresh.HaltsFromTapeEquiv
        (encodedStructuredTapes (guardLogicalTape target :: rest))
        (encodedStructuredTapes (guardLogicalTape target :: rest))
  leftBoundary :
    forall (head : Option Bool) (right : List (Option Bool))
      (rest : List (Tape Bool)),
      refresh.HaltsFromTapeEquiv
        (encodedStructuredTapes
          (({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) :: rest))
        (encodedStructuredTapes
          (guardLogicalTape
            ({ left := [], head := head, right := right } : Tape Bool) ::
              rest))
  rightBoundary :
    forall (left : List (Option Bool)) (head : Option Bool)
      (rest : List (Tape Bool)),
      refresh.HaltsFromTapeEquiv
        (encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest))
        (encodedStructuredTapes
          (guardLogicalTape
            ({ left := left, head := head, right := [] } : Tape Bool) ::
              rest))

theorem singletonHeadRefreshDescription_caseContract
    {gapCreator : MachineDescription}
    (hgap : SingletonBoundaryGapCreatorContract gapCreator) :
    SingletonHeadGuardSlackRefreshCaseContract
      (singletonHeadRefreshDescription gapCreator) where
  subroutineReady :=
    singletonHeadRefreshDescription_subroutineReady hgap.subroutineReady
  canonical :=
    singletonHeadRefreshDescription_haltsFrom_canonical hgap.subroutineReady
  leftBoundary :=
    singletonHeadRefreshDescription_haltsFrom_leftBoundary hgap
  rightBoundary :=
    singletonHeadRefreshDescription_haltsFrom_rightBoundary hgap

namespace HeadSuffixGapCreatorContract

theorem leftBoundaryRefresh
    {gapCreator : MachineDescription}
    (hgap : HeadSuffixGapCreatorContract gapCreator)
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    (singletonLeftBoundaryHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := [], head := head, right := right ++ [none] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := [], head := head, right := right } : Tape Bool) ::
            rest)) :=
  (HeadSuffixGapCreatorContract.toSingletonBoundary hgap).leftBoundaryRefresh
    head right rest

theorem rightBoundaryRefresh
    {gapCreator : MachineDescription}
    (hgap : HeadSuffixGapCreatorContract gapCreator)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    (singletonRightBoundaryHeadRefreshDescription gapCreator).HaltsFromTapeEquiv
      (encodedStructuredTapes
        (({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes
        (guardLogicalTape
          ({ left := left, head := head, right := [] } : Tape Bool) ::
            rest)) :=
  (HeadSuffixGapCreatorContract.toSingletonBoundary hgap).rightBoundaryRefresh
    left head rest

end HeadSuffixGapCreatorContract

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
