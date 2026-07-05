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

private theorem singletonShapeRefreshDescription_runConfig_eq_until
    {D : MachineDescription}
    (hstep :
      forall {c next : MachineDescription.Configuration},
        MachineDescription.stepConfig D c = some next ->
          MachineDescription.stepConfig singletonShapeRefreshDescription c =
            some next) :
    forall (n : Nat) (c final : MachineDescription.Configuration),
      (forall k : Nat, k < n -> D.runConfig k c ≠ final) ->
        D.runConfig n c = final ->
          singletonShapeRefreshDescription.runConfig n c = final := by
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

theorem singletonShapeRefreshDescription_run_canonical_opening_cons
    (target : Tape Bool) (rest : List (Tape Bool)) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape := encodedStructuredTapes (guardLogicalTape target :: rest) } =
      { state := singletonShapeTerminalProbeStart
        tape := encodedStructuredTapes (guardLogicalTape target :: rest) } := by
  exact
    singletonShapeRefreshDescription_run_false_of_reads
      (encodedStructuredTapes (guardLogicalTape target :: rest))
      (encodedStructuredTapes_read _)
      (by
        cases target with
        | mk left head right =>
            simp [encodedStructuredTapes, encodedStructuredTapeCells,
              guardLogicalTape, logicalTapeCode, logicalCellCode,
              logicalCellListBits, logicalCellBits, tapeSeparatorCells,
              tapeAtCells, Tape.read, Tape.moveRight])

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

theorem singletonShapeRefreshDescription_run_leftBoundary_opening_cons
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape :=
            encodedStructuredTapes
              (({ left := [], head := head, right := right ++ [none] } :
                Tape Bool) :: rest) } =
      { state := singletonShapeLeftRepairStart
        tape :=
          encodedStructuredTapes
            (({ left := [], head := head, right := right ++ [none] } :
              Tape Bool) :: rest) } := by
  exact
    singletonShapeRefreshDescription_run_true_of_reads
      (encodedStructuredTapes
        (({ left := [], head := head, right := right ++ [none] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes_read _)
      (by
        simp [encodedStructuredTapes, encodedStructuredTapeCells,
          logicalTapeCode, logicalCellCode, logicalCellListBits,
          logicalCellBits, headMarkerCells, tapeSeparatorCells,
          tapeAtCells, Tape.read, Tape.moveRight])

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

theorem singletonShapeRefreshDescription_run_rightBoundary_opening_cons
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    singletonShapeRefreshDescription.runConfig 2
        { state := singletonShapeRefreshDescription.start
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) } =
      { state := singletonShapeTerminalProbeStart
        tape :=
          encodedStructuredTapes
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest) } := by
  exact
    singletonShapeRefreshDescription_run_false_of_reads
      (encodedStructuredTapes
        (({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) :: rest))
      (encodedStructuredTapes_read _)
      (by
        simp [encodedStructuredTapes, encodedStructuredTapeCells,
          logicalTapeCode, logicalCellCode, logicalCellListBits,
          logicalCellBits, tapeSeparatorCells, tapeAtCells, Tape.read,
          Tape.moveRight, List.reverse_append])

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

theorem singletonShapeRefreshDescription_reaches_terminal_canonical_cons
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      singletonShapeRefreshDescription.runConfig steps
          { state := singletonShapeTerminalProbeStart
            tape := encodedStructuredTapes (guardLogicalTape target :: rest) } =
        { state := singletonShapeRefreshFinalHalt
          tape := encodedStructuredTapes (guardLogicalTape target :: rest) } := by
  rcases singletonShapeTerminalProbeDescription_reaches_canonical_cons
      target rest with
    ⟨steps, hrun⟩
  exact
    ⟨steps,
      singletonShapeRefreshDescription_runConfig_eq_to_halt
        singletonShapeRefreshDescription_stepConfig_of_terminalProbe_some
        steps
        { state := singletonShapeTerminalProbeStart
          tape := encodedStructuredTapes (guardLogicalTape target :: rest) }
        (encodedStructuredTapes (guardLogicalTape target :: rest))
        hrun⟩

theorem singletonShapeRefreshDescription_reaches_terminal_rightBoundary
    (left : List (Option Bool)) (head : Option Bool) :
    exists steps : Nat,
      singletonShapeRefreshDescription.runConfig steps
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
  let startConfig : MachineDescription.Configuration :=
    { state := singletonShapeTerminalProbeStart
      tape :=
        encodedStructuredTapes
          [({ left := left ++ [none], head := head, right := [] } :
            Tape Bool)] }
  let finalConfig : MachineDescription.Configuration :=
    { state := singletonShapeRightRepairStart
      tape :=
        encodedStructuredTapes
          [({ left := left ++ [none], head := head, right := [] } :
            Tape Bool)] }
  rcases singletonShapeTerminalProbeDescription_reaches_rightBoundary
      left head with
    ⟨witnessSteps, hwitness⟩
  have hexists :
      exists steps : Nat,
        singletonShapeTerminalProbeDescription.runConfig steps startConfig =
          finalConfig := by
    exact ⟨witnessSteps, by
      simpa [startConfig, finalConfig] using hwitness⟩
  rcases exists_first_of_exists hexists with
    ⟨steps, hsteps, hfirst⟩
  exact
    ⟨steps,
      singletonShapeRefreshDescription_runConfig_eq_until
        singletonShapeRefreshDescription_stepConfig_of_terminalProbe_some
        steps startConfig finalConfig hfirst hsteps⟩

theorem singletonShapeRefreshDescription_reaches_terminal_rightBoundary_cons
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      singletonShapeRefreshDescription.runConfig steps
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
  let startConfig : MachineDescription.Configuration :=
    { state := singletonShapeTerminalProbeStart
      tape :=
        encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest) }
  let finalConfig : MachineDescription.Configuration :=
    { state := singletonShapeRightRepairStart
      tape :=
        encodedStructuredTapes
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest) }
  rcases singletonShapeTerminalProbeDescription_reaches_rightBoundary_cons
      left head rest with
    ⟨witnessSteps, hwitness⟩
  have hexists :
      exists steps : Nat,
        singletonShapeTerminalProbeDescription.runConfig steps startConfig =
          finalConfig := by
    exact ⟨witnessSteps, by
      simpa [startConfig, finalConfig] using hwitness⟩
  rcases exists_first_of_exists hexists with
    ⟨steps, hsteps, hfirst⟩
  exact
    ⟨steps,
      singletonShapeRefreshDescription_runConfig_eq_until
        singletonShapeRefreshDescription_stepConfig_of_terminalProbe_some
        steps startConfig finalConfig hfirst hsteps⟩

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

theorem singletonShapeRefreshDescription_haltsFrom_canonical_cons
    (target : Tape Bool) (rest : List (Tape Bool)) :
    singletonShapeRefreshDescription.HaltsFromTapeEquiv
      (encodedStructuredTapes (guardLogicalTape target :: rest))
      (encodedStructuredTapes (guardLogicalTape target :: rest)) := by
  rcases singletonShapeRefreshDescription_reaches_terminal_canonical_cons
      target rest with
    ⟨steps, hterminal⟩
  refine
    ⟨encodedStructuredTapes (guardLogicalTape target :: rest), ?_,
      Tape.Equiv.refl _⟩
  refine ⟨2 + steps, ?_⟩
  have hrun :
      singletonShapeRefreshDescription.runConfig (2 + steps)
          { state := singletonShapeRefreshDescription.start
            tape :=
              encodedStructuredTapes (guardLogicalTape target :: rest) } =
        { state := singletonShapeRefreshFinalHalt
          tape := encodedStructuredTapes (guardLogicalTape target :: rest) } := by
    rw [MachineDescription.runConfig_add]
    rw [singletonShapeRefreshDescription_run_canonical_opening_cons
      target rest]
    exact hterminal
  change
    (singletonShapeRefreshDescription.runConfig (2 + steps)
      { state := singletonShapeRefreshDescription.start
        tape :=
          encodedStructuredTapes (guardLogicalTape target :: rest) }).state =
        singletonShapeRefreshDescription.halt ∧
      (singletonShapeRefreshDescription.runConfig (2 + steps)
        { state := singletonShapeRefreshDescription.start
          tape :=
            encodedStructuredTapes (guardLogicalTape target :: rest) }).tape =
        encodedStructuredTapes (guardLogicalTape target :: rest)
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

theorem singletonShapeRefreshDescription_haltsFrom_rightBoundary
    (left : List (Option Bool)) (head : Option Bool) :
    singletonShapeRefreshDescription.HaltsFromTapeEquiv
      (encodedStructuredTapes
        [({ left := left ++ [none], head := head, right := [] } :
          Tape Bool)])
      (encodedGuardedStructuredTapes
        [({ left := left, head := head, right := [] } : Tape Bool)]) := by
  rcases singletonShapeRefreshDescription_reaches_terminal_rightBoundary
      left head with
    ⟨terminalSteps, hterminal⟩
  rcases singletonShapeRefreshDescription_reaches_rightRepair_rightBoundary
      left head with
    ⟨actual, repairSteps, hrepair, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  refine ⟨2 + terminalSteps + repairSteps, ?_⟩
  have hprefix :
      singletonShapeRefreshDescription.runConfig (2 + terminalSteps)
          { state := singletonShapeRefreshDescription.start
            tape :=
              encodedStructuredTapes
                [({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool)] } =
        { state := singletonShapeRightRepairStart
          tape :=
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] } := by
    rw [MachineDescription.runConfig_add]
    rw [singletonShapeRefreshDescription_run_rightBoundary_opening left head]
    exact hterminal
  have hrun :
      singletonShapeRefreshDescription.runConfig
          (2 + terminalSteps + repairSteps)
          { state := singletonShapeRefreshDescription.start
            tape :=
              encodedStructuredTapes
                [({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool)] } =
        { state := singletonShapeRefreshFinalHalt, tape := actual } := by
    rw [MachineDescription.runConfig_add]
    rw [hprefix]
    exact hrepair
  change
    (singletonShapeRefreshDescription.runConfig
      (2 + terminalSteps + repairSteps)
      { state := singletonShapeRefreshDescription.start
        tape :=
          encodedStructuredTapes
            [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] }).state =
        singletonShapeRefreshDescription.halt ∧
      (singletonShapeRefreshDescription.runConfig
        (2 + terminalSteps + repairSteps)
        { state := singletonShapeRefreshDescription.start
          tape :=
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] }).tape =
        actual
  rw [hrun]
  simp [singletonShapeRefreshDescription]

theorem singletonShapeRefreshDescription_caseContract :
    SingletonShapeGuardSlackRefreshCaseContract
      singletonShapeRefreshDescription where
  subroutineReady := singletonShapeRefreshDescription_subroutineReady
  canonical := singletonShapeRefreshDescription_haltsFrom_canonical
  leftBoundary := singletonShapeRefreshDescription_haltsFrom_leftBoundary
  rightBoundary := singletonShapeRefreshDescription_haltsFrom_rightBoundary

theorem singletonShapeRefreshDescription_contract :
    SingletonShapeGuardSlackRefreshContract singletonShapeRefreshDescription :=
  singletonShapeRefreshDescription_caseContract.toContract

def singletonShapeRefreshNormalizer :
    SingletonShapeGuardSlackRefreshNormalizer where
  machine := singletonShapeRefreshDescription
  contract := singletonShapeRefreshDescription_contract

theorem singletonShapeRefreshDescription_haltsFrom_structuredSingletonEndpoint_singleton
    {target : Tape Bool} {physical : Tape Bool}
    (hshape : StructuredSingletonGuardSlackEndpointShape [target] physical) :
    singletonShapeRefreshDescription.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes [target]) :=
  singletonShapeRefreshDescription_contract
    |>.realizes_structuredSingletonEndpoint_singleton hshape

theorem singletonShapeRefreshNormalizer_realizes_structuredSingletonEndpoint_singleton
    {target : Tape Bool} {physical : Tape Bool}
    (hshape : StructuredSingletonGuardSlackEndpointShape [target] physical) :
    singletonShapeRefreshNormalizer.machine.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes [target]) :=
  singletonShapeRefreshNormalizer
    |>.realizes_structuredSingletonEndpoint_singleton hshape

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
