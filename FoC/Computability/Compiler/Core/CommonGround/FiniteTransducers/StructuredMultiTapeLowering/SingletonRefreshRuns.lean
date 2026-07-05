import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.SingletonRefresh

set_option doc.verso true

/-!
# Singleton guard refresh dispatcher runs

This module lifts the component-level singleton refresh dispatcher facts
through the fully assembled {lit}`singletonShapeRefreshDescription` table.  The
first layer records that each reserved source range sees exactly the
corresponding component table.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

private theorem find?_matches_none_of_sources_lt
    {l : List TransitionDescription} {state : Nat} {read : Option Bool}
    (hsource : forall t : TransitionDescription, t ∈ l -> t.source < state) :
    l.find? (Matches state read) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have hstate : t.source = state := by
    unfold Matches at hmatch
    simp at hmatch
    exact hmatch.left
  have hlt := hsource t ht
  lia

private theorem find?_matches_none_of_sources_gt
    {l : List TransitionDescription} {state : Nat} {read : Option Bool}
    (hsource : forall t : TransitionDescription, t ∈ l -> state < t.source) :
    l.find? (Matches state read) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have hstate : t.source = state := by
    unfold Matches at hmatch
    simp at hmatch
    exact hmatch.left
  have hlt := hsource t ht
  lia

theorem singletonShapeRefreshDescription_lookup_opening
    {state : Nat} {read : Option Bool}
    (hstate : state < singletonShapeLeftRepairOffset) :
    MachineDescription.lookupTransition
        singletonShapeRefreshDescription state read =
      MachineDescription.lookupTransition
        singletonShapeRefreshOpeningDescription state read := by
  have hleft :
      (singletonShapeLeftRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonShapeLeftRepairDescription_sources_in_block t ht).left
    lia
  have hright :
      (singletonShapeRightRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonShapeRightRepairDescription_sources_in_block t ht).left
    have horder := singletonShapeLeftRepairOffset_le_rightRepairOffset
    lia
  have hterminal :
      (singletonShapeTerminalProbeDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonShapeTerminalProbeDescription_sources_in_block t ht).left
    have horder := singletonShapeLeftRepairOffset_le_terminalProbeOffset
    lia
  simp [MachineDescription.lookupTransition,
    singletonShapeRefreshDescription, List.find?_append,
    hleft, hright, hterminal]

theorem singletonShapeRefreshDescription_lookup_leftRepair
    {state : Nat} {read : Option Bool}
    (hlo : singletonShapeLeftRepairOffset ≤ state)
    (hhi : state < singletonShapeLeftRepairLimit) :
    MachineDescription.lookupTransition
        singletonShapeRefreshDescription state read =
      MachineDescription.lookupTransition
        singletonShapeLeftRepairDescription state read := by
  have hopening :
      (singletonShapeRefreshOpeningDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t ht
    lia
  have hright :
      (singletonShapeRightRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonShapeRightRepairDescription_sources_in_block t ht).left
    simp [singletonShapeRightRepairOffset] at hsrc
    lia
  have hterminal :
      (singletonShapeTerminalProbeDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonShapeTerminalProbeDescription_sources_in_block t ht).left
    have hlimit := singletonShapeLeftRepairLimit_le_terminalProbeOffset
    lia
  simp [MachineDescription.lookupTransition,
    singletonShapeRefreshDescription, List.find?_append,
    hopening, hright, hterminal]

theorem singletonShapeRefreshDescription_lookup_rightRepair
    {state : Nat} {read : Option Bool}
    (hlo : singletonShapeRightRepairOffset ≤ state)
    (hhi : state < singletonShapeRightRepairLimit) :
    MachineDescription.lookupTransition
        singletonShapeRefreshDescription state read =
      MachineDescription.lookupTransition
        singletonShapeRightRepairDescription state read := by
  have hopening :
      (singletonShapeRefreshOpeningDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t ht
    have horder := singletonShapeLeftRepairOffset_le_rightRepairOffset
    lia
  have hleft :
      (singletonShapeLeftRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (singletonShapeLeftRepairDescription_sources_in_block t ht).right
    simp [singletonShapeRightRepairOffset] at hlo
    lia
  have hterminal :
      (singletonShapeTerminalProbeDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (singletonShapeTerminalProbeDescription_sources_in_block t ht).left
    simp [singletonShapeTerminalProbeOffset] at hsrc
    lia
  simp [MachineDescription.lookupTransition,
    singletonShapeRefreshDescription, List.find?_append,
    hopening, hleft, hterminal]

theorem singletonShapeRefreshDescription_lookup_terminalProbe
    {state : Nat} {read : Option Bool}
    (hstate : singletonShapeTerminalProbeOffset ≤ state) :
    MachineDescription.lookupTransition
        singletonShapeRefreshDescription state read =
      MachineDescription.lookupTransition
        singletonShapeTerminalProbeDescription state read := by
  have hopening :
      (singletonShapeRefreshOpeningDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t ht
    have horder := singletonShapeLeftRepairOffset_le_terminalProbeOffset
    lia
  have hleft :
      (singletonShapeLeftRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (singletonShapeLeftRepairDescription_sources_in_block t ht).right
    have hlimit := singletonShapeLeftRepairLimit_le_terminalProbeOffset
    lia
  have hright :
      (singletonShapeRightRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (singletonShapeRightRepairDescription_sources_in_block t ht).right
    have hsrc' : t.source < singletonShapeTerminalProbeOffset := by
      simpa [singletonShapeTerminalProbeOffset] using hsrc
    lia
  simp [MachineDescription.lookupTransition,
    singletonShapeRefreshDescription, List.find?_append,
    hopening, hleft, hright]

theorem singletonShapeRefreshDescription_stepConfig_opening
    (c : MachineDescription.Configuration)
    (hstate : c.state < singletonShapeLeftRepairOffset) :
    MachineDescription.stepConfig singletonShapeRefreshDescription c =
      MachineDescription.stepConfig singletonShapeRefreshOpeningDescription c := by
  unfold MachineDescription.stepConfig
  rw [singletonShapeRefreshDescription_lookup_opening hstate]

theorem singletonShapeRefreshDescription_stepConfig_leftRepair
    (c : MachineDescription.Configuration)
    (hlo : singletonShapeLeftRepairOffset ≤ c.state)
    (hhi : c.state < singletonShapeLeftRepairLimit) :
    MachineDescription.stepConfig singletonShapeRefreshDescription c =
      MachineDescription.stepConfig singletonShapeLeftRepairDescription c := by
  unfold MachineDescription.stepConfig
  rw [singletonShapeRefreshDescription_lookup_leftRepair hlo hhi]

theorem singletonShapeRefreshDescription_stepConfig_rightRepair
    (c : MachineDescription.Configuration)
    (hlo : singletonShapeRightRepairOffset ≤ c.state)
    (hhi : c.state < singletonShapeRightRepairLimit) :
    MachineDescription.stepConfig singletonShapeRefreshDescription c =
      MachineDescription.stepConfig singletonShapeRightRepairDescription c := by
  unfold MachineDescription.stepConfig
  rw [singletonShapeRefreshDescription_lookup_rightRepair hlo hhi]

theorem singletonShapeRefreshDescription_stepConfig_terminalProbe
    (c : MachineDescription.Configuration)
    (hstate : singletonShapeTerminalProbeOffset ≤ c.state) :
    MachineDescription.stepConfig singletonShapeRefreshDescription c =
      MachineDescription.stepConfig singletonShapeTerminalProbeDescription c := by
  unfold MachineDescription.stepConfig
  rw [singletonShapeRefreshDescription_lookup_terminalProbe hstate]

theorem singletonShapeRefreshDescription_run_false_of_reads
    (physical : Tape Bool)
    (hstart : Tape.read physical = none)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape := physical } =
      { state := singletonShapeTerminalProbeStart
        tape := physical } := by
  cases physical with
  | mk left head right =>
      cases head with
      | none =>
          cases right with
          | nil =>
              simp [Tape.read, Tape.moveRight] at hread
          | cons cell rest =>
              cases cell with
              | none =>
                  simp [Tape.read, Tape.moveRight] at hread
              | some bit =>
                  cases bit
                  · simp [singletonShapeRefreshDescription,
                      singletonShapeRefreshOpeningDescription,
                      singletonOpeningProbeDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches, transition,
                      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                      Tape.moveRight]
                  · simp [Tape.read, Tape.moveRight] at hread
      | some bit =>
          cases bit <;> simp [Tape.read] at hstart

theorem singletonShapeRefreshDescription_run_true_of_reads
    (physical : Tape Bool)
    (hstart : Tape.read physical = none)
    (hread : Tape.read (Tape.moveRight physical) = some true) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape := physical } =
      { state := singletonShapeLeftRepairStart
        tape := physical } := by
  cases physical with
  | mk left head right =>
      cases head with
      | none =>
          cases right with
          | nil =>
              simp [Tape.read, Tape.moveRight] at hread
          | cons cell rest =>
              cases cell with
              | none =>
                  simp [Tape.read, Tape.moveRight] at hread
              | some bit =>
                  cases bit
                  · simp [Tape.read, Tape.moveRight] at hread
                  · simp [singletonShapeRefreshDescription,
                      singletonShapeRefreshOpeningDescription,
                      singletonOpeningProbeDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches, transition,
                      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                      Tape.moveRight]
      | some bit =>
          cases bit <;> simp [Tape.read] at hstart

theorem singletonShapeRefreshDescription_run_false_of_shape
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape := physical } =
      { state := singletonShapeTerminalProbeStart
        tape := physical } :=
  singletonShapeRefreshDescription_run_false_of_reads
    physical hshape.openingSeparator_read hread

theorem singletonShapeRefreshDescription_run_true_of_shape
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some true) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape := physical } =
      { state := singletonShapeLeftRepairStart
        tape := physical } :=
  singletonShapeRefreshDescription_run_true_of_reads
    physical hshape.openingSeparator_read hread

theorem singletonShapeRefreshDescription_run_canonical_opening
    (target : Tape Bool) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape := encodedGuardedStructuredTapes [target] } =
      { state := singletonShapeTerminalProbeStart
        tape := encodedGuardedStructuredTapes [target] } :=
  singletonShapeRefreshDescription_run_false_of_shape
    (SingletonGuardSlackEndpointShape.canonical rfl)
    (SingletonGuardSlackEndpointShape.canonical_singleton_afterOpening_read
      target)

theorem singletonShapeRefreshDescription_run_leftBoundary_opening
    (head : Option Bool) (right : List (Option Bool)) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape :=
            encodedStructuredTapes
              [({ left := [], head := head, right := right ++ [none] } :
                Tape Bool)] } =
      { state := singletonShapeLeftRepairStart
        tape :=
          encodedStructuredTapes
            [({ left := [], head := head, right := right ++ [none] } :
              Tape Bool)] } :=
  singletonShapeRefreshDescription_run_true_of_shape
    (SingletonGuardSlackEndpointShape.leftBoundary head right)
    (SingletonGuardSlackEndpointShape.leftBoundary_afterOpening_read
      head right)

theorem singletonShapeRefreshDescription_run_rightBoundary_opening
    (left : List (Option Bool)) (head : Option Bool) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape :=
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] } =
      { state := singletonShapeTerminalProbeStart
        tape :=
          encodedStructuredTapes
            [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] } :=
  singletonShapeRefreshDescription_run_false_of_shape
    (SingletonGuardSlackEndpointShape.rightBoundary left head)
    (SingletonGuardSlackEndpointShape.rightBoundary_afterOpening_read
      left head)

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
