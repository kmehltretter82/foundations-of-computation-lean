import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.SelectedSeparatorRefresh

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

theorem selectedShapeRefreshDescription_lookup_opening
    {state : Nat} {read : Option Bool}
    (hstate : state < selectedShapeLeftRepairOffset) :
    MachineDescription.lookupTransition
        selectedShapeRefreshDescription state read =
      MachineDescription.lookupTransition
        selectedShapeRefreshOpeningDescription state read := by
  have hleft :
      (selectedShapeLeftRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (selectedShapeLeftRepairDescription_sources_in_block t ht).left
    lia
  have hright :
      (selectedShapeRightRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (selectedShapeRightRepairDescription_sources_in_block t ht).left
    have horder :=
      Nat.le_of_lt selectedShapeLeftRepairOffset_lt_rightRepairOffset
    lia
  have hterminal :
      (selectedShapeTerminalProbeDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (selectedShapeTerminalProbeDescription_sources_in_block t ht).left
    have horder := selectedShapeLeftRepairOffset_le_terminalProbeOffset
    lia
  simp [MachineDescription.lookupTransition,
    selectedShapeRefreshDescription, List.find?_append,
    hleft, hright, hterminal]

theorem selectedShapeRefreshDescription_lookup_leftRepair
    {state : Nat} {read : Option Bool}
    (hlo : selectedShapeLeftRepairOffset ≤ state)
    (hhi : state < selectedShapeLeftRepairLimit) :
    MachineDescription.lookupTransition
        selectedShapeRefreshDescription state read =
      MachineDescription.lookupTransition
        selectedShapeLeftRepairDescription state read := by
  have hopening :
      (selectedShapeRefreshOpeningDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t ht
    lia
  have hright :
      (selectedShapeRightRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (selectedShapeRightRepairDescription_sources_in_block t ht).left
    simp [selectedShapeRightRepairOffset] at hsrc
    lia
  have hterminal :
      (selectedShapeTerminalProbeDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (selectedShapeTerminalProbeDescription_sources_in_block t ht).left
    have hlimit := selectedShapeLeftRepairLimit_le_terminalProbeOffset
    lia
  simp [MachineDescription.lookupTransition,
    selectedShapeRefreshDescription, List.find?_append,
    hopening, hright, hterminal]

theorem selectedShapeRefreshDescription_lookup_rightRepair
    {state : Nat} {read : Option Bool}
    (hlo : selectedShapeRightRepairOffset ≤ state)
    (hhi : state < selectedShapeRightRepairLimit) :
    MachineDescription.lookupTransition
        selectedShapeRefreshDescription state read =
      MachineDescription.lookupTransition
        selectedShapeRightRepairDescription state read := by
  have hopening :
      (selectedShapeRefreshOpeningDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t ht
    have horder :=
      Nat.le_of_lt selectedShapeLeftRepairOffset_lt_rightRepairOffset
    lia
  have hleft :
      (selectedShapeLeftRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (selectedShapeLeftRepairDescription_sources_in_block t ht).right
    simp [selectedShapeRightRepairOffset] at hlo
    lia
  have hterminal :
      (selectedShapeTerminalProbeDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_gt
    intro t ht
    have hsrc :=
      (selectedShapeTerminalProbeDescription_sources_in_block t ht).left
    simp [selectedShapeTerminalProbeOffset] at hsrc
    lia
  simp [MachineDescription.lookupTransition,
    selectedShapeRefreshDescription, List.find?_append,
    hopening, hleft, hterminal]

theorem selectedShapeRefreshDescription_lookup_terminalProbe
    {state : Nat} {read : Option Bool}
    (hstate : selectedShapeTerminalProbeOffset ≤ state) :
    MachineDescription.lookupTransition
        selectedShapeRefreshDescription state read =
      MachineDescription.lookupTransition
        selectedShapeTerminalProbeDescription state read := by
  have hopening :
      (selectedShapeRefreshOpeningDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t ht
    have horder := selectedShapeLeftRepairOffset_le_terminalProbeOffset
    lia
  have hleft :
      (selectedShapeLeftRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (selectedShapeLeftRepairDescription_sources_in_block t ht).right
    have hlimit := selectedShapeLeftRepairLimit_le_terminalProbeOffset
    lia
  have hright :
      (selectedShapeRightRepairDescription).transitions.find?
          (Matches state read) = none := by
    apply find?_matches_none_of_sources_lt
    intro t ht
    have hsrc :=
      (selectedShapeRightRepairDescription_sources_in_block t ht).right
    have hsrc' : t.source < selectedShapeTerminalProbeOffset := by
      simpa [selectedShapeTerminalProbeOffset] using hsrc
    lia
  simp [MachineDescription.lookupTransition,
    selectedShapeRefreshDescription, List.find?_append,
    hopening, hleft, hright]

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

private theorem encodedStructuredTapeCells_cons_eq_of_singleton_eq
    {actual expected : Tape Bool} {rest : List (Tape Bool)}
    (h :
      encodedStructuredTapes [actual] =
        encodedStructuredTapes [expected]) :
    encodedStructuredTapeCells (actual :: rest) =
      encodedStructuredTapeCells (expected :: rest) := by
  have hcode : logicalTapeCode actual = logicalTapeCode expected := by
    unfold encodedStructuredTapes at h
    simp [encodedStructuredTapeCells] at h
    injection h with _ _ hcode
    simpa using hcode
  simp [encodedStructuredTapeCells, hcode]

private theorem selectedShapeRefreshDescription_stepConfig_of_leftRepair_some
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig selectedShapeLeftRepairDescription c =
        some next) :
    MachineDescription.stepConfig selectedShapeRefreshDescription c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition selectedShapeLeftRepairDescription
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        selectedShapeLeftRepairDescription_sources_in_block t htmem
      have hlo : selectedShapeLeftRepairOffset ≤ c.state := by
        lia
      have hhi : c.state < selectedShapeLeftRepairLimit := by
        lia
      rw [selectedShapeRefreshDescription_lookup_leftRepair hlo hhi]
      simpa [hlookup] using hstep

private theorem selectedShapeRefreshDescription_stepConfig_of_rightRepair_some
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig selectedShapeRightRepairDescription c =
        some next) :
    MachineDescription.stepConfig selectedShapeRefreshDescription c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition selectedShapeRightRepairDescription
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        selectedShapeRightRepairDescription_sources_in_block t htmem
      have hlo : selectedShapeRightRepairOffset ≤ c.state := by
        lia
      have hhi : c.state < selectedShapeRightRepairLimit := by
        lia
      rw [selectedShapeRefreshDescription_lookup_rightRepair hlo hhi]
      simpa [hlookup] using hstep

private theorem selectedShapeRefreshDescription_stepConfig_of_terminalProbe_some
    {c next : MachineDescription.Configuration}
    (hstep :
      MachineDescription.stepConfig selectedShapeTerminalProbeDescription c =
        some next) :
    MachineDescription.stepConfig selectedShapeRefreshDescription c =
      some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup :
      MachineDescription.lookupTransition selectedShapeTerminalProbeDescription
        c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hsource := source_eq_of_lookupTransition hlookup
      have hbounds :=
        selectedShapeTerminalProbeDescription_sources_in_block t htmem
      have hlo : selectedShapeTerminalProbeOffset ≤ c.state := by
        lia
      rw [selectedShapeRefreshDescription_lookup_terminalProbe hlo]
      simpa [hlookup] using hstep

theorem selectedShapeRefreshDescription_haltTransitionFree :
    selectedShapeRefreshDescription.TransitionFreeAt
      selectedShapeRefreshFinalHalt := by
  intro t ht hsource
  simp [selectedShapeRefreshDescription] at ht
  rcases ht with hopening | hleft | hright | hterminal
  · simp [selectedShapeRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopening
    rcases hopening with rfl | rfl | rfl <;>
      simp [transition, selectedShapeRefreshFinalHalt] at hsource
  · have hsrc :=
      (selectedShapeLeftRepairDescription_sources_in_block t hleft).left
    have hhalt := selectedShapeRefreshFinalHalt_lt_leftRepairOffset
    lia
  · have hsrc :=
      (selectedShapeRightRepairDescription_sources_in_block t hright).left
    have hhalt := selectedShapeRefreshFinalHalt_lt_rightRepairOffset
    lia
  · have hsrc :=
      (selectedShapeTerminalProbeDescription_sources_in_block t hterminal).left
    have hhalt :=
      Nat.lt_of_lt_of_le selectedShapeRefreshFinalHalt_lt_rightRepairOffset
        selectedShapeRightRepairOffset_le_terminalProbeOffset
    lia

private theorem selectedShapeRefreshDescription_runConfig_eq_to_halt
    {D : MachineDescription}
    (hstep :
      forall {c next : MachineDescription.Configuration},
        MachineDescription.stepConfig D c = some next ->
          MachineDescription.stepConfig selectedShapeRefreshDescription c =
            some next) :
    forall (n : Nat) (c : MachineDescription.Configuration) (T : Tape Bool),
      D.runConfig n c =
          { state := selectedShapeRefreshFinalHalt, tape := T } ->
        selectedShapeRefreshDescription.runConfig n c =
          { state := selectedShapeRefreshFinalHalt, tape := T } := by
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
              selectedShapeRefreshDescription.TransitionFreeAt
                selectedShapeRefreshFinalHalt :=
            selectedShapeRefreshDescription_haltTransitionFree
          have hnone :
              MachineDescription.stepConfig selectedShapeRefreshDescription
                { state := selectedShapeRefreshFinalHalt, tape := T } =
                none := by
            unfold MachineDescription.stepConfig
            rw [MachineDescription.lookupTransition_state_none hfree]
          simp [hnone]
      | some next =>
          have hfull := hstep hlocal
          have htail :
              D.runConfig n next =
                { state := selectedShapeRefreshFinalHalt, tape := T } := by
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

private theorem selectedShapeRefreshDescription_runConfig_eq_until
    {D : MachineDescription}
    (hstep :
      forall {c next : MachineDescription.Configuration},
        MachineDescription.stepConfig D c = some next ->
          MachineDescription.stepConfig selectedShapeRefreshDescription c =
            some next) :
    forall (n : Nat) (c final : MachineDescription.Configuration),
      (forall k : Nat, k < n -> D.runConfig k c ≠ final) ->
        D.runConfig n c = final ->
          selectedShapeRefreshDescription.runConfig n c = final := by
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

theorem selectedShapeRefreshDescription_haltsFrom_canonical
    (encodedPrefix : List (Option Bool))
    (target actual : Tape Bool) (rest : List (Tape Bool))
    (hcanonical :
      encodedStructuredTapes [actual] =
        encodedGuardedStructuredTapes [target]) :
    selectedShapeRefreshDescription.HaltsFromTapeEquiv
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells (actual :: rest)))
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape target :: rest))) := by
  have hsingleton :
      encodedStructuredTapes [actual] =
        encodedStructuredTapes [guardLogicalTape target] := by
    simpa [encodedGuardedStructuredTapes, guardLogicalTapes] using
      hcanonical
  have hcells :
      encodedStructuredTapeCells (actual :: rest) =
        encodedStructuredTapeCells (guardLogicalTape target :: rest) :=
    encodedStructuredTapeCells_cons_eq_of_singleton_eq hsingleton
  rcases selectedShapeTerminalProbeDescription_reaches_selectedCanonical
      encodedPrefix target rest with
    ⟨steps, hterminalLocal⟩
  have hterminal :
      selectedShapeRefreshDescription.runConfig steps
          { state := selectedShapeTerminalProbeStart
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells
                  (guardLogicalTape target :: rest)) } =
        { state := selectedShapeRefreshFinalHalt
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)) } :=
    selectedShapeRefreshDescription_runConfig_eq_to_halt
      selectedShapeRefreshDescription_stepConfig_of_terminalProbe_some
      steps
      { state := selectedShapeTerminalProbeStart
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (guardLogicalTape target :: rest)) }
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape target :: rest)))
      hterminalLocal
  refine
    ⟨tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape target :: rest)), ?_, Tape.Equiv.refl _⟩
  refine ⟨2 + steps, ?_⟩
  have hrun :
      selectedShapeRefreshDescription.runConfig (2 + steps)
          { state := selectedShapeRefreshDescription.start
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells (actual :: rest)) } =
        { state := selectedShapeRefreshFinalHalt
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)) } := by
    rw [hcells]
    rw [MachineDescription.runConfig_add]
    rw [selectedShapeRefreshDescription_run_canonical_opening
      encodedPrefix target rest]
    exact hterminal
  change
    (selectedShapeRefreshDescription.runConfig (2 + steps)
      { state := selectedShapeRefreshDescription.start
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells (actual :: rest)) }).state =
        selectedShapeRefreshDescription.halt ∧
      (selectedShapeRefreshDescription.runConfig (2 + steps)
        { state := selectedShapeRefreshDescription.start
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells (actual :: rest)) }).tape =
        tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape target :: rest))
  rw [hrun]
  simp [selectedShapeRefreshDescription]

theorem selectedShapeRefreshDescription_haltsFrom_leftBoundary
    (encodedPrefix : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    selectedShapeRefreshDescription.HaltsFromTapeEquiv
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) :: rest)))
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape
            ({ left := [], head := head, right := right } :
              Tape Bool) :: rest))) := by
  rcases selectedShapeLeftRepairDescription_haltsFrom_leftBoundary
      encodedPrefix head right rest with
    ⟨actual, hhalts, hequiv⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hhalts with
    ⟨steps, hrunLocal⟩
  have hrunLocal' :
      selectedShapeLeftRepairDescription.runConfig steps
          { state := selectedShapeLeftRepairStart
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells
                  (({ left := [], head := head,
                      right := right ++ [none] } : Tape Bool) :: rest)) } =
        { state := selectedShapeRefreshFinalHalt, tape := actual } := by
    simpa [selectedShapeLeftRepairStart,
      selectedShapeLeftRepairDescription,
      MachineDescription.offsetRetargetDescription] using hrunLocal
  have hrepair :
      selectedShapeRefreshDescription.runConfig steps
          { state := selectedShapeLeftRepairStart
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells
                  (({ left := [], head := head,
                      right := right ++ [none] } : Tape Bool) :: rest)) } =
        { state := selectedShapeRefreshFinalHalt, tape := actual } :=
    selectedShapeRefreshDescription_runConfig_eq_to_halt
      selectedShapeRefreshDescription_stepConfig_of_leftRepair_some
      steps
      { state := selectedShapeLeftRepairStart
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := [], head := head,
                  right := right ++ [none] } : Tape Bool) :: rest)) }
      actual
      hrunLocal'
  refine ⟨actual, ?_, hequiv⟩
  refine ⟨2 + steps, ?_⟩
  have hrun :
      selectedShapeRefreshDescription.runConfig (2 + steps)
          { state := selectedShapeRefreshDescription.start
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells
                  (({ left := [], head := head,
                      right := right ++ [none] } : Tape Bool) :: rest)) } =
        { state := selectedShapeRefreshFinalHalt, tape := actual } := by
    rw [MachineDescription.runConfig_add]
    rw [selectedShapeRefreshDescription_run_leftBoundary_opening
      encodedPrefix head right rest]
    exact hrepair
  change
    (selectedShapeRefreshDescription.runConfig (2 + steps)
      { state := selectedShapeRefreshDescription.start
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := [], head := head,
                  right := right ++ [none] } : Tape Bool) :: rest)) }).state =
        selectedShapeRefreshDescription.halt ∧
      (selectedShapeRefreshDescription.runConfig (2 + steps)
        { state := selectedShapeRefreshDescription.start
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (({ left := [], head := head,
                    right := right ++ [none] } : Tape Bool) :: rest)) }).tape =
        actual
  rw [hrun]
  simp [selectedShapeRefreshDescription]

theorem selectedShapeRefreshDescription_haltsFrom_rightBoundary
    (encodedPrefix : List (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    selectedShapeRefreshDescription.HaltsFromTapeEquiv
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest)))
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape
            ({ left := left, head := head, right := [] } :
              Tape Bool) :: rest))) := by
  let startConfig : MachineDescription.Configuration :=
    { state := selectedShapeTerminalProbeStart
      tape :=
        tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (({ left := left ++ [none], head := head,
                right := [] } : Tape Bool) :: rest)) }
  let finalConfig : MachineDescription.Configuration :=
    { state := selectedShapeRightRepairStart
      tape :=
        tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (({ left := left ++ [none], head := head,
                right := [] } : Tape Bool) :: rest)) }
  rcases selectedShapeTerminalProbeDescription_reaches_selectedRightBoundary
      encodedPrefix left head rest with
    ⟨witnessSteps, hwitness⟩
  have hexists :
      exists steps : Nat,
        selectedShapeTerminalProbeDescription.runConfig steps startConfig =
          finalConfig := by
    exact ⟨witnessSteps, by
      simpa [startConfig, finalConfig] using hwitness⟩
  rcases exists_first_of_exists hexists with
    ⟨terminalSteps, hterminalLocal, hfirst⟩
  have hterminal :
      selectedShapeRefreshDescription.runConfig terminalSteps startConfig =
        finalConfig :=
    selectedShapeRefreshDescription_runConfig_eq_until
      selectedShapeRefreshDescription_stepConfig_of_terminalProbe_some
      terminalSteps startConfig finalConfig hfirst hterminalLocal
  rcases selectedShapeRightRepairDescription_haltsFrom_rightBoundary
      encodedPrefix left head rest with
    ⟨actual, hhalts, hequiv⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hhalts with
    ⟨repairSteps, hrunLocal⟩
  have hrunLocal' :
      selectedShapeRightRepairDescription.runConfig repairSteps
          { state := selectedShapeRightRepairStart
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells
                  (({ left := left ++ [none], head := head,
                      right := [] } : Tape Bool) :: rest)) } =
        { state := selectedShapeRefreshFinalHalt, tape := actual } := by
    simpa [selectedShapeRightRepairStart,
      selectedShapeRightRepairDescription,
      MachineDescription.offsetRetargetDescription] using hrunLocal
  have hrepair :
      selectedShapeRefreshDescription.runConfig repairSteps
          { state := selectedShapeRightRepairStart
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells
                  (({ left := left ++ [none], head := head,
                      right := [] } : Tape Bool) :: rest)) } =
        { state := selectedShapeRefreshFinalHalt, tape := actual } :=
    selectedShapeRefreshDescription_runConfig_eq_to_halt
      selectedShapeRefreshDescription_stepConfig_of_rightRepair_some
      repairSteps
      { state := selectedShapeRightRepairStart
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := left ++ [none], head := head,
                  right := [] } : Tape Bool) :: rest)) }
      actual
      hrunLocal'
  refine ⟨actual, ?_, hequiv⟩
  refine ⟨2 + terminalSteps + repairSteps, ?_⟩
  have hprefix :
      selectedShapeRefreshDescription.runConfig (2 + terminalSteps)
          { state := selectedShapeRefreshDescription.start
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells
                  (({ left := left ++ [none], head := head,
                      right := [] } : Tape Bool) :: rest)) } =
        { state := selectedShapeRightRepairStart
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (({ left := left ++ [none], head := head,
                    right := [] } : Tape Bool) :: rest)) } := by
    rw [MachineDescription.runConfig_add]
    rw [selectedShapeRefreshDescription_run_rightBoundary_opening
      encodedPrefix left head rest]
    exact hterminal
  have hrun :
      selectedShapeRefreshDescription.runConfig
          (2 + terminalSteps + repairSteps)
          { state := selectedShapeRefreshDescription.start
            tape :=
              tapeAtEncodedSplit encodedPrefix
                (encodedStructuredTapeCells
                  (({ left := left ++ [none], head := head,
                      right := [] } : Tape Bool) :: rest)) } =
        { state := selectedShapeRefreshFinalHalt, tape := actual } := by
    rw [MachineDescription.runConfig_add]
    rw [hprefix]
    exact hrepair
  change
    (selectedShapeRefreshDescription.runConfig
      (2 + terminalSteps + repairSteps)
      { state := selectedShapeRefreshDescription.start
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := left ++ [none], head := head,
                  right := [] } : Tape Bool) :: rest)) }).state =
        selectedShapeRefreshDescription.halt ∧
      (selectedShapeRefreshDescription.runConfig
        (2 + terminalSteps + repairSteps)
        { state := selectedShapeRefreshDescription.start
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (({ left := left ++ [none], head := head,
                    right := [] } : Tape Bool) :: rest)) }).tape =
        actual
  rw [hrun]
  simp [selectedShapeRefreshDescription]

theorem selectedShapeRefreshDescription_transitions_wellFormed :
    forall t : TransitionDescription,
      t ∈ selectedShapeRefreshDescription.transitions ->
        TransitionDescription.WellFormed
          selectedShapeRefreshDescription.stateCount t := by
  intro t ht
  simp [selectedShapeRefreshDescription] at ht
  rcases ht with hopen | hleft | hright | hterminal
  · simp [selectedShapeRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopen
    rcases hopen with rfl | rfl | rfl
    · constructor
      · exact Nat.lt_trans (by decide)
          selectedShapeRefreshFinalHalt_lt_stateCount
      · exact Nat.lt_trans (by decide)
          selectedShapeRefreshFinalHalt_lt_stateCount
    · constructor
      · exact Nat.lt_trans (by decide)
          selectedShapeRefreshFinalHalt_lt_stateCount
      · exact
          selectedShapeTerminalProbeDescription_subroutineReady.left.right.left
    · constructor
      · exact Nat.lt_trans (by decide)
          selectedShapeRefreshFinalHalt_lt_stateCount
      · exact
          Nat.lt_of_lt_of_le
            selectedShapeLeftRepairDescription_subroutineReady.left.right.left
            selectedShapeLeftRepairLimit_le_stateCount
  · have hformed :=
      selectedShapeLeftRepairDescription_subroutineReady.left.right.right.right.left
        t hleft
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        selectedShapeLeftRepairLimit_le_stateCount,
      Nat.lt_of_lt_of_le hformed.right
        selectedShapeLeftRepairLimit_le_stateCount⟩
  · have hformed :=
      selectedShapeRightRepairDescription_subroutineReady.left.right.right.right.left
        t hright
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        selectedShapeRightRepairLimit_le_stateCount,
      Nat.lt_of_lt_of_le hformed.right
        selectedShapeRightRepairLimit_le_stateCount⟩
  · exact
      selectedShapeTerminalProbeDescription_subroutineReady.left.right.right.right.left
        t hterminal

theorem selectedShapeRefreshDescription_deterministic :
    selectedShapeRefreshDescription.Deterministic := by
  intro t u ht hu hkey
  simp [selectedShapeRefreshDescription] at ht hu
  rcases ht with hopenT | hleftT | hrightT | hterminalT <;>
    rcases hu with hopenU | hleftU | hrightU | hterminalU
  · exact
      selectedShapeRefreshOpeningDescription_subroutineReady.left.right.right.right.right
        t u hopenT hopenU hkey
  · have htBound :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (selectedShapeLeftRepairDescription_sources_in_block u hleftU).left
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (selectedShapeRightRepairDescription_sources_in_block u hrightU).left
    have horder :=
      Nat.le_of_lt selectedShapeLeftRepairOffset_lt_rightRepairOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (selectedShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have horder := selectedShapeLeftRepairOffset_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (selectedShapeLeftRepairDescription_sources_in_block t hleftT).left
    exact False.elim (by
      have hs := hkey.left
      lia)
  · exact
      selectedShapeLeftRepairDescription_subroutineReady.left.right.right.right.right
        t u hleftT hleftU hkey
  · have htBound :=
      (selectedShapeLeftRepairDescription_sources_in_block t hleftT).right
    have huBound :=
      (selectedShapeRightRepairDescription_sources_in_block u hrightU).left
    exact False.elim (by
      have hs := hkey.left
      simp [selectedShapeRightRepairOffset] at huBound
      lia)
  · have htBound :=
      (selectedShapeLeftRepairDescription_sources_in_block t hleftT).right
    have huBound :=
      (selectedShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have horder := selectedShapeLeftRepairLimit_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (selectedShapeRightRepairDescription_sources_in_block t hrightT).left
    have horder :=
      Nat.le_of_lt selectedShapeLeftRepairOffset_lt_rightRepairOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (selectedShapeLeftRepairDescription_sources_in_block u hleftU).right
    have huBound :=
      (selectedShapeRightRepairDescription_sources_in_block t hrightT).left
    exact False.elim (by
      have hs := hkey.left
      simp [selectedShapeRightRepairOffset] at huBound
      lia)
  · exact
      selectedShapeRightRepairDescription_subroutineReady.left.right.right.right.right
        t u hrightT hrightU hkey
  · have htBound :=
      (selectedShapeRightRepairDescription_sources_in_block t hrightT).right
    have huLower :=
      (selectedShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have huBound : selectedShapeRightRepairLimit ≤ u.source := by
      simpa [selectedShapeTerminalProbeOffset] using huLower
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (selectedShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have horder := selectedShapeLeftRepairOffset_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (selectedShapeLeftRepairDescription_sources_in_block u hleftU).right
    have huBound :=
      (selectedShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have horder := selectedShapeLeftRepairLimit_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (selectedShapeRightRepairDescription_sources_in_block u hrightU).right
    have huLower :=
      (selectedShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have huBound : selectedShapeRightRepairLimit ≤ t.source := by
      simpa [selectedShapeTerminalProbeOffset] using huLower
    exact False.elim (by
      have hs := hkey.left
      lia)
  · exact
      selectedShapeTerminalProbeDescription_subroutineReady.left.right.right.right.right
        t u hterminalT hterminalU hkey

theorem selectedShapeRefreshDescription_wellFormed :
    selectedShapeRefreshDescription.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      Nat.lt_of_lt_of_le (by decide : 0 < selectedShapeRefreshFinalHalt)
        (Nat.le_of_lt selectedShapeRefreshFinalHalt_lt_stateCount)
  · exact
      Nat.lt_of_lt_of_le (by decide : 0 < selectedShapeRefreshFinalHalt)
        (Nat.le_of_lt selectedShapeRefreshFinalHalt_lt_stateCount)
  · exact selectedShapeRefreshFinalHalt_lt_stateCount
  · exact selectedShapeRefreshDescription_transitions_wellFormed
  · exact selectedShapeRefreshDescription_deterministic

theorem selectedShapeRefreshDescription_haltTransitionFree_all :
    selectedShapeRefreshDescription.HaltTransitionFree := by
  intro t ht
  simp [selectedShapeRefreshDescription] at ht
  rcases ht with hopening | hleft | hright | hterminal
  · simp [selectedShapeRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopening
    rcases hopening with rfl | rfl | rfl <;>
      decide
  · exact selectedShapeLeftRepairDescription_subroutineReady.right t hleft
  · exact selectedShapeRightRepairDescription_subroutineReady.right t hright
  · exact selectedShapeTerminalProbeDescription_subroutineReady.right
      t hterminal

theorem selectedShapeRefreshDescription_subroutineReady :
    selectedShapeRefreshDescription.SubroutineReady :=
  ⟨selectedShapeRefreshDescription_wellFormed,
    selectedShapeRefreshDescription_haltTransitionFree_all⟩

theorem selectedShapeRefreshDescription_caseContract :
    SelectedSeparatorGuardSlackRefreshCaseContract
      selectedShapeRefreshDescription where
  subroutineReady := selectedShapeRefreshDescription_subroutineReady
  canonical := selectedShapeRefreshDescription_haltsFrom_canonical
  leftBoundary := selectedShapeRefreshDescription_haltsFrom_leftBoundary
  rightBoundary := selectedShapeRefreshDescription_haltsFrom_rightBoundary

theorem selectedShapeRefreshDescription_contract (tapeIndex : Nat) :
    SelectedSeparatorGuardSlackRefreshContract
      selectedShapeRefreshDescription tapeIndex :=
  selectedShapeRefreshDescription_caseContract.toSelectedSeparatorContract
    tapeIndex

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
