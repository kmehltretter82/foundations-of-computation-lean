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

private theorem source_eq_of_lookupTransition
    {D : MachineDescription} {state : Nat} {read : Option Bool}
    {t : TransitionDescription}
    (hlookup : D.lookupTransition state read = some t) :
    t.source = state := by
  have hmatch : Matches state read t = true := by
    unfold MachineDescription.lookupTransition at hlookup
    exact List.find?_some hlookup
  unfold Matches at hmatch
  simp at hmatch
  exact hmatch.left

private theorem singletonShapeRefreshDescription_stepConfig_of_leftRepair_some
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig singletonShapeLeftRepairDescription c =
        some next) :
    MachineDescription.stepConfig singletonShapeRefreshDescription c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition singletonShapeLeftRepairDescription
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        singletonShapeLeftRepairDescription_sources_in_block t htmem
      have hlo : singletonShapeLeftRepairOffset ≤ c.state := by
        lia
      have hhi : c.state < singletonShapeLeftRepairLimit := by
        lia
      rw [singletonShapeRefreshDescription_lookup_leftRepair hlo hhi]
      simpa [hlookup] using hstep

private theorem singletonShapeRefreshDescription_stepConfig_of_rightRepair_some
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig singletonShapeRightRepairDescription c =
        some next) :
    MachineDescription.stepConfig singletonShapeRefreshDescription c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition singletonShapeRightRepairDescription
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        singletonShapeRightRepairDescription_sources_in_block t htmem
      have hlo : singletonShapeRightRepairOffset ≤ c.state := by
        lia
      have hhi : c.state < singletonShapeRightRepairLimit := by
        lia
      rw [singletonShapeRefreshDescription_lookup_rightRepair hlo hhi]
      simpa [hlookup] using hstep

private theorem singletonShapeRefreshDescription_stepConfig_of_terminalProbe_some
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig singletonShapeTerminalProbeDescription c =
        some next) :
    MachineDescription.stepConfig singletonShapeRefreshDescription c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition singletonShapeTerminalProbeDescription
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        singletonShapeTerminalProbeDescription_sources_in_block t htmem
      have hlo : singletonShapeTerminalProbeOffset ≤ c.state := by
        lia
      rw [singletonShapeRefreshDescription_lookup_terminalProbe hlo]
      simpa [hlookup] using hstep

private theorem singletonShapeRefreshDescription_runConfig_eq_to_halt
    {D : MachineDescription}
    (hstep :
      forall {c next : MachineDescription.Configuration},
        MachineDescription.stepConfig D c = some next ->
          MachineDescription.stepConfig singletonShapeRefreshDescription c =
            some next) :
    forall (n : Nat) (c : MachineDescription.Configuration) (T : Tape Bool),
      D.runConfig n c =
          { state := singletonShapeRefreshFinalHalt, tape := T } ->
        singletonShapeRefreshDescription.runConfig n c =
          { state := singletonShapeRefreshFinalHalt, tape := T } := by
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
              singletonShapeRefreshDescription.TransitionFreeAt
                singletonShapeRefreshFinalHalt := by
            intro t ht hsource
            exact singletonShapeRefreshDescription_haltTransitionFree
              t ht (by
                simpa [singletonShapeRefreshDescription] using hsource)
          have hnone :
              MachineDescription.stepConfig singletonShapeRefreshDescription
                { state := singletonShapeRefreshFinalHalt, tape := T } =
                none := by
            unfold MachineDescription.stepConfig
            rw [MachineDescription.lookupTransition_state_none hfree]
          simp [hnone]
      | some next =>
          have hfull := hstep hlocal
          have htail :
              D.runConfig n next =
                { state := singletonShapeRefreshFinalHalt, tape := T } := by
            simpa [hlocal] using hrun
          simp [hfull]
          exact ih next T htail

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

theorem singletonShapeRefreshDescription_reaches_terminal_canonical
    (target : Tape Bool) :
    exists steps : Nat,
      singletonShapeRefreshDescription.runConfig steps
          { state := singletonShapeTerminalProbeStart
            tape := encodedGuardedStructuredTapes [target] } =
        { state := singletonShapeRefreshFinalHalt
          tape := encodedGuardedStructuredTapes [target] } := by
  rcases singletonShapeTerminalProbeDescription_reaches_canonical
      target with
    ⟨steps, hrun⟩
  exact
    ⟨steps,
      singletonShapeRefreshDescription_runConfig_eq_to_halt
        singletonShapeRefreshDescription_stepConfig_of_terminalProbe_some
        steps
        { state := singletonShapeTerminalProbeStart
          tape := encodedGuardedStructuredTapes [target] }
        (encodedGuardedStructuredTapes [target])
        hrun⟩

theorem singletonShapeRefreshDescription_reaches_leftRepair_leftBoundary
    (head : Option Bool) (right : List (Option Bool)) :
    exists (actual : Tape Bool) (steps : Nat),
      singletonShapeRefreshDescription.runConfig steps
          { state := singletonShapeLeftRepairStart
            tape :=
              encodedStructuredTapes
                [({ left := [], head := head, right := right ++ [none] } :
                  Tape Bool)] } =
        { state := singletonShapeRefreshFinalHalt, tape := actual } ∧
      Tape.Equiv actual
        (encodedGuardedStructuredTapes
          [({ left := [], head := head, right := right } : Tape Bool)]) := by
  rcases singletonShapeLeftRepairDescription_haltsFrom_leftBoundary
      head right with
    ⟨actual, hhalts, hequiv⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hhalts with
    ⟨steps, hrun⟩
  refine ⟨actual, steps, ?_, hequiv⟩
  have hrun' :
      singletonShapeLeftRepairDescription.runConfig steps
          { state := singletonShapeLeftRepairStart
            tape :=
              encodedStructuredTapes
                [({ left := [], head := head, right := right ++ [none] } :
                  Tape Bool)] } =
        { state := singletonShapeRefreshFinalHalt, tape := actual } := by
    simpa [singletonShapeLeftRepairStart,
      singletonShapeLeftRepairDescription,
      MachineDescription.offsetRetargetDescription] using hrun
  exact
    singletonShapeRefreshDescription_runConfig_eq_to_halt
      singletonShapeRefreshDescription_stepConfig_of_leftRepair_some
      steps
      { state := singletonShapeLeftRepairStart
        tape :=
          encodedStructuredTapes
            [({ left := [], head := head, right := right ++ [none] } :
              Tape Bool)] }
      actual
      hrun'

theorem singletonShapeRefreshDescription_reaches_rightRepair_rightBoundary
    (left : List (Option Bool)) (head : Option Bool) :
    exists (actual : Tape Bool) (steps : Nat),
      singletonShapeRefreshDescription.runConfig steps
          { state := singletonShapeRightRepairStart
            tape :=
              encodedStructuredTapes
                [({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool)] } =
        { state := singletonShapeRefreshFinalHalt, tape := actual } ∧
      Tape.Equiv actual
        (encodedGuardedStructuredTapes
          [({ left := left, head := head, right := [] } : Tape Bool)]) := by
  rcases singletonShapeRightRepairDescription_haltsFrom_rightBoundary
      left head with
    ⟨actual, hhalts, hequiv⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hhalts with
    ⟨steps, hrun⟩
  refine ⟨actual, steps, ?_, hequiv⟩
  have hrun' :
      singletonShapeRightRepairDescription.runConfig steps
          { state := singletonShapeRightRepairStart
            tape :=
              encodedStructuredTapes
                [({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool)] } =
        { state := singletonShapeRefreshFinalHalt, tape := actual } := by
    simpa [singletonShapeRightRepairStart,
      singletonShapeRightRepairDescription,
      MachineDescription.offsetRetargetDescription] using hrun
  exact
    singletonShapeRefreshDescription_runConfig_eq_to_halt
      singletonShapeRefreshDescription_stepConfig_of_rightRepair_some
      steps
      { state := singletonShapeRightRepairStart
        tape :=
          encodedStructuredTapes
            [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] }
      actual
      hrun'

theorem singletonShapeRefreshDescription_haltsFrom_canonical
    (target : Tape Bool) :
    singletonShapeRefreshDescription.HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes [target])
      (encodedGuardedStructuredTapes [target]) := by
  rcases singletonShapeRefreshDescription_reaches_terminal_canonical
      target with
    ⟨steps, hterminal⟩
  refine ⟨encodedGuardedStructuredTapes [target], ?_, Tape.Equiv.refl _⟩
  refine ⟨2 + steps, ?_⟩
  have hrun :
      singletonShapeRefreshDescription.runConfig (2 + steps)
          { state := singletonShapeRefreshDescription.start
            tape := encodedGuardedStructuredTapes [target] } =
        { state := singletonShapeRefreshFinalHalt
          tape := encodedGuardedStructuredTapes [target] } := by
    rw [MachineDescription.runConfig_add]
    rw [singletonShapeRefreshDescription_run_canonical_opening target]
    exact hterminal
  change
    (singletonShapeRefreshDescription.runConfig (2 + steps)
      { state := singletonShapeRefreshDescription.start
        tape := encodedGuardedStructuredTapes [target] }).state =
        singletonShapeRefreshDescription.halt ∧
      (singletonShapeRefreshDescription.runConfig (2 + steps)
        { state := singletonShapeRefreshDescription.start
          tape := encodedGuardedStructuredTapes [target] }).tape =
        encodedGuardedStructuredTapes [target]
  rw [hrun]
  simp [singletonShapeRefreshDescription]

theorem singletonShapeRefreshDescription_haltsFrom_leftBoundary
    (head : Option Bool) (right : List (Option Bool)) :
    singletonShapeRefreshDescription.HaltsFromTapeEquiv
      (encodedStructuredTapes
        [({ left := [], head := head, right := right ++ [none] } :
          Tape Bool)])
      (encodedGuardedStructuredTapes
        [({ left := [], head := head, right := right } : Tape Bool)]) := by
  rcases singletonShapeRefreshDescription_reaches_leftRepair_leftBoundary
      head right with
    ⟨actual, steps, hrepair, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  refine ⟨2 + steps, ?_⟩
  have hrun :
      singletonShapeRefreshDescription.runConfig (2 + steps)
          { state := singletonShapeRefreshDescription.start
            tape :=
              encodedStructuredTapes
                [({ left := [], head := head, right := right ++ [none] } :
                  Tape Bool)] } =
        { state := singletonShapeRefreshFinalHalt, tape := actual } := by
    rw [MachineDescription.runConfig_add]
    rw [singletonShapeRefreshDescription_run_leftBoundary_opening head right]
    exact hrepair
  change
    (singletonShapeRefreshDescription.runConfig (2 + steps)
      { state := singletonShapeRefreshDescription.start
        tape :=
          encodedStructuredTapes
            [({ left := [], head := head, right := right ++ [none] } :
              Tape Bool)] }).state =
        singletonShapeRefreshDescription.halt ∧
      (singletonShapeRefreshDescription.runConfig (2 + steps)
        { state := singletonShapeRefreshDescription.start
          tape :=
            encodedStructuredTapes
              [({ left := [], head := head, right := right ++ [none] } :
                Tape Bool)] }).tape =
        actual
  rw [hrun]
  simp [singletonShapeRefreshDescription]

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
