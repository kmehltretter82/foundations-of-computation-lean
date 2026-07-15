import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.ValidB
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.InvRun

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

def EventuallyHalts
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (c : Structured.Configuration) : Prop :=
  (coreD attempt hattempt).HaltsFromConfig c

theorem eventuallyHalts_of_leads
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    {c d : Structured.Configuration}
    (hlead : Leads attempt hattempt c d)
    (hhalt : EventuallyHalts attempt hattempt c) :
    EventuallyHalts attempt hattempt d := by
  change (table attempt hattempt).Leads c d at hlead
  change (table attempt hattempt).description.HaltsFromConfig c at hhalt
  change (table attempt hattempt).description.HaltsFromConfig d
  rcases hhalt with ⟨n, hn⟩
  exact target_halts_of_leads
    (table attempt hattempt).description_haltTransitionFree hlead hn

theorem not_eventuallyHalts_spin
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (T0 T1 T2 : Tape Bool) :
    ¬ EventuallyHalts attempt hattempt
      (cfg attempt hattempt .spin T0 T1 T2) := by
  intro hhalt
  rcases hhalt with ⟨n, hn⟩
  have hstate := runConfig_spin_state attempt hattempt n T0 T1 T2
  have hid :
      (table attempt hattempt).stateId .spin =
        (table attempt hattempt).stateId .halt := by
    exact hstate.symm.trans hn
  have htyped := (table attempt hattempt).stateId_inj
    .spin (mem_states_of_stateBounded trivial)
    .halt (mem_states_of_stateBounded trivial) hid
  cases htyped

theorem false_of_leads_spin_of_eventuallyHalts
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    {c : Structured.Configuration} {T0 T1 T2 : Tape Bool}
    (hspin : Leads attempt hattempt c
      (cfg attempt hattempt .spin T0 T1 T2))
    (hhalt : EventuallyHalts attempt hattempt c) : False :=
  not_eventuallyHalts_spin attempt hattempt T0 T1 T2
    (eventuallyHalts_of_leads hspin hhalt)

theorem leads_result_bad_bit_from_stream
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (bit : Bool) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = bit :: bits)
    (hbad :
      next attempt (.result phase) (some bit) (some false) T2.read =
        some progressSpin) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt (.result phase)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt .spin T0' T1' T2) := by
  rcases stream_next_decomp bit bits work markers
      hcover hshape hfilter with
    ⟨gap, workTail, markerTail, hwork, hmarkers,
      _hcoverTail, _hshapeTail, _hfilterTail⟩
  subst work
  subst markers
  let T0a := tapeAtCells
    (List.append (List.replicate gap none) L0) (some bit :: workTail)
  let T1a := tapeAtCells
    (List.append (List.replicate gap (some false)) L1)
      (some false :: markerTail)
  have hblank := leads_result_blanks
    (attempt := attempt) (hattempt := hattempt)
    phase gap L0 L1 (some bit :: workTail)
      (some false :: markerTail) T2
  have hone :
      Leads attempt hattempt
        (cfg attempt hattempt (.result phase) T0a T1a T2)
        (cfg attempt hattempt .spin
          (keepR.apply T0a) T1a T2) := by
    exact leads_step
      (attempt := attempt) (hattempt := hattempt)
      (s := CoreState.result phase)
      (T0 := T0a) (T1 := T1a) (T2 := T2) trivial hbad
  have hmarker :
      List.append (List.replicate (gap + 1) (some false)) markerTail =
        List.append (List.replicate gap (some false))
          (some false :: markerTail) :=
    (list_replicate_append_self (some false) gap markerTail).symm
  exact ⟨keepR.apply T0a, T1a, by
    rw [hmarker]
    simpa [T0a, T1a] using hblank.trans hone⟩

theorem leads_resultFirst_bad_bit_from_stream
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (bit : Bool) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = bit :: bits)
    (hbad :
      next attempt .resultFirst (some bit) (some false) T2.read =
        some progressSpin) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt .resultFirst
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt .spin T0' T1' T2) := by
  rcases stream_next_decomp bit bits work markers
      hcover hshape hfilter with
    ⟨gap, workTail, markerTail, hwork, hmarkers,
      _hcoverTail, _hshapeTail, _hfilterTail⟩
  subst work
  subst markers
  let T0a := tapeAtCells
    (List.append (List.replicate gap none) L0) (some bit :: workTail)
  let T1a := tapeAtCells
    (List.append (List.replicate gap (some false)) L1)
      (some false :: markerTail)
  have hblank := leads_resultFirst_blanks
    (attempt := attempt) (hattempt := hattempt)
    gap L0 L1 (some bit :: workTail) (some false :: markerTail) T2
  have hone :
      Leads attempt hattempt
        (cfg attempt hattempt .resultFirst T0a T1a T2)
        (cfg attempt hattempt .spin
          (keepR.apply T0a) T1a T2) := by
    exact leads_step
      (attempt := attempt) (hattempt := hattempt)
      (s := CoreState.resultFirst)
      (T0 := T0a) (T1 := T1a) (T2 := T2) trivial hbad
  have hmarker :
      List.append (List.replicate (gap + 1) (some false)) markerTail =
        List.append (List.replicate gap (some false))
          (some false :: markerTail) :=
    (list_replicate_append_self (some false) gap markerTail).symm
  exact ⟨keepR.apply T0a, T1a, by
    rw [hmarker]
    simpa [T0a, T1a] using hblank.trans hone⟩

theorem leads_result_empty_to_spin
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (hphase : phase ≠ .seekCell)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = []) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt (.result phase)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt .spin T0' T1' T2) := by
  induction hshape generalizing work L0 L1 with
  | nil =>
      cases hcover with
      | extra works hall =>
          let T0 := tapeAtCells L0 work
          let T1 := tapeAtCells L1 []
          have hnext :
              next attempt (.result phase) T0.read T1.read T2.read =
                some progressSpin := by
            change next attempt (.result phase) T0.read none T2.read = _
            cases phase <;> simp_all [next]
          refine ⟨keepR.apply T0, T1, ?_⟩
          have hlead := leads_step
            (attempt := attempt) (hattempt := hattempt)
            (s := CoreState.result phase)
            (T0 := T0) (T1 := T1) (T2 := T2) trivial hnext
          have hstay1 : keepS.apply T1 = T1 := by rfl
          have hstay2 : keepS.apply T2 = T2 := by rfl
          change Leads attempt hattempt
            (cfg attempt hattempt (.result phase) T0 T1 T2)
            (cfg attempt hattempt .spin
              (keepR.apply T0) (keepS.apply T1) (keepS.apply T2)) at hlead
          rw [hstay1, hstay2] at hlead
          exact hlead
  | boundary =>
      cases hcover with
      | @cons workCell markerCell works markerCells hcell htail =>
          let T0 := tapeAtCells L0 (workCell :: works)
          let T1 := tapeAtCells L1 [none]
          have hnext :
              next attempt (.result phase) T0.read T1.read T2.read =
                some progressSpin := by
            change next attempt (.result phase) T0.read none T2.read = _
            cases phase <;> simp_all [next]
          refine ⟨keepR.apply T0, T1, ?_⟩
          exact leads_step
            (attempt := attempt) (hattempt := hattempt)
            (s := CoreState.result phase)
            (T0 := T0) (T1 := T1) (T2 := T2) trivial hnext
  | @marked markerTail hshapeTail ih =>
      cases hcover with
      | @cons workCell markerCell workTail markerTail' hcell hcoverTail =>
          have hworkCell : workCell = none := by
            cases workCell with
            | none => rfl
            | some bit => simp at hfilter
          subst workCell
          have hfilterTail : workTail.filterMap id = [] := by
            simpa using hfilter
          have hscan := leads_result_blank
            (attempt := attempt) (hattempt := hattempt)
            phase L0 L1 workTail markerTail T2
          rcases ih (work := workTail) (L0 := none :: L0)
              (L1 := some false :: L1) hcoverTail hfilterTail with
            ⟨T0', T1', htail⟩
          exact ⟨T0', T1', hscan.trans htail⟩

theorem leads_resultFirst_empty_to_spin
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = []) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt .resultFirst
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt .spin T0' T1' T2) := by
  induction hshape generalizing work L0 L1 with
  | nil =>
      cases hcover with
      | extra works hall =>
          let T0 := tapeAtCells L0 work
          let T1 := tapeAtCells L1 []
          have hnext :
              next attempt .resultFirst T0.read T1.read T2.read =
                some progressSpin := by
            rfl
          refine ⟨keepR.apply T0, T1, ?_⟩
          have hlead := leads_step
            (attempt := attempt) (hattempt := hattempt)
            (s := CoreState.resultFirst)
            (T0 := T0) (T1 := T1) (T2 := T2) trivial hnext
          have hstay1 : keepS.apply T1 = T1 := by rfl
          have hstay2 : keepS.apply T2 = T2 := by rfl
          change Leads attempt hattempt
            (cfg attempt hattempt .resultFirst T0 T1 T2)
            (cfg attempt hattempt .spin
              (keepR.apply T0) (keepS.apply T1) (keepS.apply T2)) at hlead
          rw [hstay1, hstay2] at hlead
          exact hlead
  | boundary =>
      cases hcover with
      | @cons workCell markerCell works markerCells hcell htail =>
          let T0 := tapeAtCells L0 (workCell :: works)
          let T1 := tapeAtCells L1 [none]
          have hnext :
              next attempt .resultFirst T0.read T1.read T2.read =
                some progressSpin := by
            rfl
          refine ⟨keepR.apply T0, T1, ?_⟩
          exact leads_step
            (attempt := attempt) (hattempt := hattempt)
            (s := CoreState.resultFirst)
            (T0 := T0) (T1 := T1) (T2 := T2) trivial hnext
  | @marked markerTail hshapeTail ih =>
      cases hcover with
      | @cons workCell markerCell workTail markerTail' hcell hcoverTail =>
          have hworkCell : workCell = none := by
            cases workCell with
            | none => rfl
            | some bit => simp at hfilter
          subst workCell
          have hfilterTail : workTail.filterMap id = [] := by
            simpa using hfilter
          have hscan := leads_resultFirst_blank
            (attempt := attempt) (hattempt := hattempt)
            L0 L1 workTail markerTail T2
          rcases ih (work := workTail) (L0 := none :: L0)
              (L1 := some false :: L1) hcoverTail hfilterTail with
            ⟨T0', T1', htail⟩
          exact ⟨T0', T1', hscan.trans htail⟩

theorem leads_counterLeft_none_to_spin
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (T0 T2 : Tape Bool) (L1 right1 : List (Option Bool)) :
    ∃ T0' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt .counterLeft T0
          (tapeAtCells L1 (none :: right1)) T2)
        (cfg attempt hattempt .spin T0'
          (tapeAtCells L1 (none :: right1)) T2) := by
  have hnext :
      next attempt .counterLeft T0.read none T2.read =
        some progressSpin := by
    rfl
  let T1 := tapeAtCells L1 (none :: right1)
  refine ⟨keepR.apply T0, ?_⟩
  have hlead := leads_step
    (attempt := attempt) (hattempt := hattempt)
    (s := CoreState.counterLeft)
    (T0 := T0) (T1 := T1) (T2 := T2) trivial hnext
  have hstay1 : keepS.apply T1 = T1 := by rfl
  have hstay2 : keepS.apply T2 = T2 := by rfl
  change Leads attempt hattempt
    (cfg attempt hattempt .counterLeft T0 T1 T2)
    (cfg attempt hattempt .spin
      (keepR.apply T0) (keepS.apply T1) (keepS.apply T2)) at hlead
  rw [hstay1, hstay2] at hlead
  exact hlead

theorem leads_counterLeft_zero_falses_to_spin
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (gap : Nat) (T0 T2 : Tape Bool) (right1 : List (Option Bool)) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt .counterLeft T0
          (tapeAtCells
            (List.append (List.replicate gap (some false)) [none])
            (some false :: right1)) T2)
        (cfg attempt hattempt .spin T0' T1' T2) := by
  induction gap generalizing right1 with
  | zero =>
      have hfalse := leads_counterLeft_false
        (attempt := attempt) (hattempt := hattempt)
        T0 T2 [] right1 none
      rcases leads_counterLeft_none_to_spin
          (attempt := attempt) (hattempt := hattempt)
          T0 T2 [] (some false :: right1) with
        ⟨T0', hspin⟩
      exact ⟨T0', tapeAtCells [] (none :: some false :: right1),
        hfalse.trans hspin⟩
  | succ gap ih =>
      have hfalse := leads_counterLeft_false
        (attempt := attempt) (hattempt := hattempt)
        T0 T2
        (List.append (List.replicate gap (some false)) [none])
        right1 (some false)
      rcases ih (some false :: right1) with ⟨T0', T1', hspin⟩
      refine ⟨T0', T1', ?_⟩
      simpa [List.replicate_succ] using hfalse.trans hspin

theorem leads_seekCell_zero_nonempty_to_spin
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = false :: bits)
    (hstack : MarkerStack 0 L1) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt .spin T0' T1' T2) := by
  rcases stream_next_decomp false bits work markers
      hcover hshape hfilter with
    ⟨gap, workTail, markerTail, hwork, hmarkers,
      _hcoverTail, _hshapeTail, _hfilterTail⟩
  subst work
  subst markers
  let L0a := List.append (List.replicate gap none) L0
  let L1a := List.append (List.replicate gap (some false)) L1
  have hscan := leads_result_blanks
    (attempt := attempt) (hattempt := hattempt)
    .seekCell gap L0 L1 (some false :: workTail)
      (some false :: markerTail) T2
  have hmarkersEq :
      List.append (List.replicate (gap + 1) (some false)) markerTail =
        List.append (List.replicate gap (some false))
          (some false :: markerTail) :=
    (list_replicate_append_self (some false) gap markerTail).symm
  rw [← hmarkersEq] at hscan
  change Leads attempt hattempt _
    (cfg attempt hattempt (.result .seekCell)
      (tapeAtCells L0a (some false :: workTail))
      (tapeAtCells L1a (some false :: markerTail)) T2) at hscan
  have hstacka : MarkerStack 0 L1a :=
    markerStack_false_replicate gap hstack
  rcases markerStack_zero_decomp hstacka with ⟨counterGap, hL1a⟩
  cases counterGap with
  | zero =>
      have hL1zero : L1a = [none] := by simpa using hL1a
      rw [hL1zero] at hscan
      have herase := leads_seekCell_erase
        (attempt := attempt) (hattempt := hattempt)
        L0a [] workTail markerTail none T2
      rcases leads_counterLeft_none_to_spin
          (attempt := attempt) (hattempt := hattempt)
          (tapeAtCells L0a (some false :: workTail)) T2
          [] (none :: markerTail) with
        ⟨T0', hspin⟩
      refine ⟨T0', tapeAtCells [] (none :: none :: markerTail), ?_⟩
      simpa [L0a, L1a] using hscan.trans (herase.trans hspin)
  | succ counterGap =>
      have hshapeL1 :
          L1a = some false ::
            List.append (List.replicate counterGap (some false)) [none] := by
        simpa [List.replicate_succ] using hL1a
      have herase := leads_seekCell_erase
        (attempt := attempt) (hattempt := hattempt)
        L0a
        (List.append (List.replicate counterGap (some false)) [none])
        workTail markerTail (some false) T2
      rcases leads_counterLeft_zero_falses_to_spin
          (attempt := attempt) (hattempt := hattempt)
          counterGap (tapeAtCells L0a (some false :: workTail)) T2
          (none :: markerTail) with
        ⟨T0', T1', hspin⟩
      refine ⟨T0', T1', ?_⟩
      rw [hshapeL1] at hscan
      simpa [L0a] using hscan.trans (herase.trans hspin)

theorem leads_checkCount_true_to_spin
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (T0 T2 : Tape Bool) (L1 right1 : List (Option Bool)) :
    ∃ T0' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt .checkCount T0
          (tapeAtCells L1 (some true :: right1)) T2)
        (cfg attempt hattempt .spin T0'
          (tapeAtCells L1 (some true :: right1)) T2) := by
  let T1 := tapeAtCells L1 (some true :: right1)
  have hnext :
      next attempt .checkCount T0.read T1.read T2.read =
        some progressSpin := by
    rfl
  refine ⟨keepR.apply T0, ?_⟩
  have hlead := leads_step
    (attempt := attempt) (hattempt := hattempt)
    (s := CoreState.checkCount)
    (T0 := T0) (T1 := T1) (T2 := T2) trivial hnext
  have hstay1 : keepS.apply T1 = T1 := by rfl
  have hstay2 : keepS.apply T2 = T2 := by rfl
  change Leads attempt hattempt
    (cfg attempt hattempt .checkCount T0 T1 T2)
    (cfg attempt hattempt .spin
      (keepR.apply T0) (keepS.apply T1) (keepS.apply T2)) at hlead
  rw [hstay1, hstay2] at hlead
  exact hlead

theorem leads_checkCount_falses_to_true
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (gap : Nat) (T0 T2 : Tape Bool)
    (tail right1 : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .checkCount T0
        (tapeAtCells
          (List.append (List.replicate gap (some false))
            (some true :: tail))
          (some false :: right1)) T2)
      (cfg attempt hattempt .checkCount T0
        (tapeAtCells tail
          (some true :: List.append
            (List.replicate (gap + 1) (some false)) right1)) T2) := by
  induction gap generalizing right1 with
  | zero =>
      simpa using
        (leads_checkCount_false
          (attempt := attempt) (hattempt := hattempt)
          T0 T2 tail right1 (some true))
  | succ gap ih =>
      simp only [List.replicate_succ]
      refine (leads_checkCount_false
        (attempt := attempt) (hattempt := hattempt)
        T0 T2
        (List.append (List.replicate gap (some false))
          (some true :: tail)) right1 (some false)).trans ?_
      have htail := ih (some false :: right1)
      have hmove :
          List.append (List.replicate gap (some false))
              (some false :: right1) =
            some false ::
              List.append (List.replicate gap (some false)) right1 :=
        list_replicate_append_cons_eq_cons_append (some false) gap right1
      have hsucc :
          List.replicate (gap + 1) (some false) =
            some false :: List.replicate gap (some false) := by
        simpa [Nat.add_comm] using
          (List.replicate_succ (n := gap) (a := some false))
      have hright :
          List.append (List.replicate (gap + 1) (some false))
              (some false :: right1) =
            List.append
              (some false :: some false ::
                List.replicate gap (some false)) right1 := by
        rw [hsucc]
        change some false ::
            List.append (List.replicate gap (some false))
              (some false :: right1) = _
        rw [hmove]
        rfl
      rw [hright] at htail
      exact htail

theorem leads_seekCell_marker_none_positive_to_spin
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (count : Nat) (T0 T2 : Tape Bool)
    (L1 right1 : List (Option Bool))
    (hstack : MarkerStack (count + 1) L1) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell) T0
          (tapeAtCells L1 (none :: right1)) T2)
        (cfg attempt hattempt .spin T0' T1' T2) := by
  rcases markerStack_succ_decomp hstack with
    ⟨gap, tail, hL1, htail⟩
  subst L1
  cases gap with
  | zero =>
      have hseek := leads_seekCell_marker_none
        (attempt := attempt) (hattempt := hattempt)
        T0 T2 tail right1 (some true)
      rcases leads_checkCount_true_to_spin
          (attempt := attempt) (hattempt := hattempt)
          T0 T2 tail (none :: right1) with
        ⟨T0', hspin⟩
      exact ⟨T0', tapeAtCells tail
        (some true :: none :: right1),
        hseek.trans hspin⟩
  | succ gap =>
      have hseek := leads_seekCell_marker_none
        (attempt := attempt) (hattempt := hattempt)
        T0 T2
        (List.append (List.replicate gap (some false))
          (some true :: tail))
        right1 (some false)
      have hscan := leads_checkCount_falses_to_true
        (attempt := attempt) (hattempt := hattempt)
        gap T0 T2 tail (none :: right1)
      rcases leads_checkCount_true_to_spin
          (attempt := attempt) (hattempt := hattempt)
          T0 T2 tail
          (List.append (List.replicate (gap + 1) (some false))
            (none :: right1)) with
        ⟨T0', hspin⟩
      refine ⟨T0', tapeAtCells tail
        (some true :: List.append
          (List.replicate (gap + 1) (some false)) (none :: right1)), ?_⟩
      simpa [List.replicate_succ] using
        hseek.trans (hscan.trans hspin)

theorem leads_seekCell_positive_empty_to_spin
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (count : Nat)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = [])
    (hstack : MarkerStack (count + 1) L1) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt .spin T0' T1' T2) := by
  induction hshape generalizing work L0 L1 with
  | nil =>
      cases hcover with
      | extra works hall =>
          rcases leads_seekCell_marker_none_positive_to_spin
              (attempt := attempt) (hattempt := hattempt)
              count (tapeAtCells L0 work) T2 L1 [] hstack with
            ⟨T0', T1', hspin⟩
          exact ⟨T0', T1', by simpa [tapeAtCells] using hspin⟩
  | boundary =>
      cases hcover with
      | @cons workCell markerCell works markerCells hcell htail =>
          exact leads_seekCell_marker_none_positive_to_spin
            (attempt := attempt) (hattempt := hattempt)
            count (tapeAtCells L0 (workCell :: works)) T2 L1 [] hstack
  | @marked markerTail hshapeTail ih =>
      cases hcover with
      | @cons workCell markerCell workTail markerTail' hcell hcoverTail =>
          have hworkCell : workCell = none := by
            cases workCell with
            | none => rfl
            | some bit => simp at hfilter
          subst workCell
          have hfilterTail : workTail.filterMap id = [] := by
            simpa using hfilter
          have hscan := leads_result_blank
            (attempt := attempt) (hattempt := hattempt)
            .seekCell L0 L1 workTail markerTail T2
          have hstackTail : MarkerStack (count + 1) (some false :: L1) :=
            MarkerStack.false hstack
          rcases ih (work := workTail) (L0 := none :: L0)
              (L1 := some false :: L1)
              hcoverTail hfilterTail hstackTail with
            ⟨T0', T1', htail⟩
          exact ⟨T0', T1', hscan.trans htail⟩

theorem eventuallyHalts_cell1_stream_shape
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hhalt : EventuallyHalts attempt hattempt
      (cfg attempt hattempt (.result .cell1)
        (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)) :
    ∃ bit : Bool, ∃ bits : Word Bool,
      work.filterMap id = true :: bit :: (!bit) :: bits := by
  generalize hstream : work.filterMap id = stream
  cases stream with
  | nil =>
      rcases leads_result_empty_to_spin
          (attempt := attempt) (hattempt := hattempt)
          .cell1 (by decide) L0 L1 work markers T2
          hcover hshape hstream with
        ⟨T0', T1', hspin⟩
      exact False.elim
        (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
  | cons first rest =>
      cases first with
      | false =>
          rcases leads_result_bad_bit_from_stream
              (attempt := attempt) (hattempt := hattempt)
              .cell1 false rest L0 L1 work markers T2
              hcover hshape hstream (by simp [next]) with
            ⟨T0', T1', hspin⟩
          exact False.elim
            (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
      | true =>
          rcases leads_result_from_stream
              (attempt := attempt) (hattempt := hattempt)
              .cell1 .cell1 true rest L0 L1 work markers T2
              hcover hshape hstream
              (by simp [next, beginWrite, someStep]) with
            ⟨gap1, work1, markers1, h1,
              hcover1, hshape1, hfilter1⟩
          let L01 := some true ::
            List.append (List.replicate gap1 none) L0
          let L11 := some false ::
            List.append (List.replicate gap1 (some false)) L1
          let T21 := (writeR (some true)).apply T2
          have h1' :
              Leads attempt hattempt
                (cfg attempt hattempt (.result .cell1)
                  (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
                (cfg attempt hattempt (.result .cell2)
                  (tapeAtCells L01 work1) (tapeAtCells L11 markers1) T21) := by
            simpa [L01, L11, T21, writePhaseTarget,
              writePhaseMarker, writePhaseBit] using h1
          have hhalt1 := eventuallyHalts_of_leads h1' hhalt
          cases rest with
          | nil =>
              rcases leads_result_empty_to_spin
                  (attempt := attempt) (hattempt := hattempt)
                  .cell2 (by decide) L01 L11 work1 markers1 T21
                  hcover1 hshape1 hfilter1 with
                ⟨T0', T1', hspin⟩
              exact False.elim
                (false_of_leads_spin_of_eventuallyHalts hspin hhalt1)
          | cons second rest2 =>
              cases second with
              | false =>
                  rcases leads_result_from_stream
                      (attempt := attempt) (hattempt := hattempt)
                      .cell2 .cell2False false rest2
                      L01 L11 work1 markers1 T21
                      hcover1 hshape1 hfilter1
                      (by simp [next, beginWrite, someStep]) with
                    ⟨gap2, work2, markers2, h2,
                      hcover2, hshape2, hfilter2⟩
                  let L02 := some false ::
                    List.append (List.replicate gap2 none) L01
                  let L12 := some false ::
                    List.append (List.replicate gap2 (some false)) L11
                  let T22 := (writeR (some false)).apply T21
                  have h2' :
                      Leads attempt hattempt
                        (cfg attempt hattempt (.result .cell2)
                          (tapeAtCells L01 work1)
                          (tapeAtCells L11 markers1) T21)
                        (cfg attempt hattempt (.result .cell3False)
                          (tapeAtCells L02 work2)
                          (tapeAtCells L12 markers2) T22) := by
                    simpa [L02, L12, T22, writePhaseTarget,
                      writePhaseMarker, writePhaseBit] using h2
                  have hhalt2 := eventuallyHalts_of_leads h2' hhalt1
                  cases rest2 with
                  | nil =>
                      rcases leads_result_empty_to_spin
                          (attempt := attempt) (hattempt := hattempt)
                          .cell3False (by decide)
                          L02 L12 work2 markers2 T22
                          hcover2 hshape2 hfilter2 with
                        ⟨T0', T1', hspin⟩
                      exact False.elim
                        (false_of_leads_spin_of_eventuallyHalts hspin hhalt2)
                  | cons third tail =>
                      cases third with
                      | false =>
                          rcases leads_result_bad_bit_from_stream
                              (attempt := attempt) (hattempt := hattempt)
                              .cell3False false tail
                              L02 L12 work2 markers2 T22
                              hcover2 hshape2 hfilter2
                              (by simp [next]) with
                            ⟨T0', T1', hspin⟩
                          exact False.elim
                            (false_of_leads_spin_of_eventuallyHalts
                              hspin hhalt2)
                      | true =>
                          exact ⟨false, tail, by simpa using hstream⟩
              | true =>
                  rcases leads_result_from_stream
                      (attempt := attempt) (hattempt := hattempt)
                      .cell2 .cell2True true rest2
                      L01 L11 work1 markers1 T21
                      hcover1 hshape1 hfilter1
                      (by simp [next, beginWrite, someStep]) with
                    ⟨gap2, work2, markers2, h2,
                      hcover2, hshape2, hfilter2⟩
                  let L02 := some true ::
                    List.append (List.replicate gap2 none) L01
                  let L12 := some false ::
                    List.append (List.replicate gap2 (some false)) L11
                  let T22 := (writeR (some true)).apply T21
                  have h2' :
                      Leads attempt hattempt
                        (cfg attempt hattempt (.result .cell2)
                          (tapeAtCells L01 work1)
                          (tapeAtCells L11 markers1) T21)
                        (cfg attempt hattempt (.result .cell3True)
                          (tapeAtCells L02 work2)
                          (tapeAtCells L12 markers2) T22) := by
                    simpa [L02, L12, T22, writePhaseTarget,
                      writePhaseMarker, writePhaseBit] using h2
                  have hhalt2 := eventuallyHalts_of_leads h2' hhalt1
                  cases rest2 with
                  | nil =>
                      rcases leads_result_empty_to_spin
                          (attempt := attempt) (hattempt := hattempt)
                          .cell3True (by decide)
                          L02 L12 work2 markers2 T22
                          hcover2 hshape2 hfilter2 with
                        ⟨T0', T1', hspin⟩
                      exact False.elim
                        (false_of_leads_spin_of_eventuallyHalts hspin hhalt2)
                  | cons third tail =>
                      cases third with
                      | false =>
                          exact ⟨true, tail, by simpa using hstream⟩
                      | true =>
                          rcases leads_result_bad_bit_from_stream
                              (attempt := attempt) (hattempt := hattempt)
                              .cell3True true tail
                              L02 L12 work2 markers2 T22
                              hcover2 hshape2 hfilter2
                              (by simp [next]) with
                            ⟨T0', T1', hspin⟩
                          exact False.elim
                            (false_of_leads_spin_of_eventuallyHalts
                              hspin hhalt2)

theorem eventuallyHalts_seekCell_stream_shape
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (count : Nat)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hstack : MarkerStack count L1)
    (hhalt : EventuallyHalts attempt hattempt
      (cfg attempt hattempt (.result .seekCell)
        (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)) :
    ∃ word : Word Bool,
      word.length = count ∧
      work.filterMap id = cellsBits word := by
  induction count generalizing L0 L1 work markers T2 with
  | zero =>
      generalize hstream : work.filterMap id = stream
      cases stream with
      | nil =>
          exact ⟨[], rfl, by simpa [cellsBits_nil] using hstream⟩
      | cons first rest =>
          cases first with
          | false =>
              rcases leads_seekCell_zero_nonempty_to_spin
                  (attempt := attempt) (hattempt := hattempt)
                  rest L0 L1 work markers T2
                  hcover hshape hstream hstack with
                ⟨T0', T1', hspin⟩
              exact False.elim
                (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
          | true =>
              rcases leads_result_bad_bit_from_stream
                  (attempt := attempt) (hattempt := hattempt)
                  .seekCell true rest L0 L1 work markers T2
                  hcover hshape hstream (by simp [next]) with
                ⟨T0', T1', hspin⟩
              exact False.elim
                (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
  | succ count ih =>
      generalize hstream : work.filterMap id = stream
      cases stream with
      | nil =>
          rcases leads_seekCell_positive_empty_to_spin
              (attempt := attempt) (hattempt := hattempt)
              count L0 L1 work markers T2
              hcover hshape hstream hstack with
            ⟨T0', T1', hspin⟩
          exact False.elim
            (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
      | cons first rest =>
          cases first with
          | true =>
              rcases leads_result_bad_bit_from_stream
                  (attempt := attempt) (hattempt := hattempt)
                  .seekCell true rest L0 L1 work markers T2
                  hcover hshape hstream (by simp [next]) with
                ⟨T0', T1', hspin⟩
              exact False.elim
                (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
          | false =>
              rcases leads_seekCell_from_stream
                  (attempt := attempt) (hattempt := hattempt)
                  count rest L0 L1 work markers T2
                  hcover hshape hstream hstack with
                ⟨L0a, L1a, worka, markersa,
                  hfirst, hcovera, hshapea, hfiltera, hstacka⟩
              let T2a := (writeR (some false)).apply T2
              have hfirst' :
                  Leads attempt hattempt
                    (cfg attempt hattempt (.result .seekCell)
                      (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
                    (cfg attempt hattempt (.result .cell1)
                      (tapeAtCells L0a worka)
                      (tapeAtCells L1a markersa) T2a) := by
                simpa [T2a] using hfirst
              have hhalta := eventuallyHalts_of_leads hfirst' hhalt
              rcases eventuallyHalts_cell1_stream_shape
                  (attempt := attempt) (hattempt := hattempt)
                  L0a L1a worka markersa T2a
                  hcovera hshapea hhalta with
                ⟨bit, tail, hcellTail⟩
              have hrest : rest = true :: bit :: (!bit) :: tail :=
                hfiltera.symm.trans hcellTail
              have hcellFilter :
                  work.filterMap id = List.append (cellBits bit) tail := by
                rw [hstream, hrest]
                cases bit <;> rfl
              rcases leads_cell
                  (attempt := attempt) (hattempt := hattempt)
                  count bit tail L0 L1 work markers T2
                  hcover hshape hcellFilter hstack with
                ⟨L0b, L1b, workb, markersb,
                  hcell, hcoverb, hshapeb, hfilterb, hstackb⟩
              let T2b := writeOutputPrefix (cellBits bit) tail T2
              have hcell' :
                  Leads attempt hattempt
                    (cfg attempt hattempt (.result .seekCell)
                      (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
                    (cfg attempt hattempt (.result .seekCell)
                      (tapeAtCells L0b workb)
                      (tapeAtCells L1b markersb) T2b) := by
                simpa [T2b] using hcell
              have hhaltb := eventuallyHalts_of_leads hcell' hhalt
              rcases ih L0b L1b workb markersb T2b
                  hcoverb hshapeb hstackb hhaltb with
                ⟨word, hlength, hword⟩
              have htail : tail = cellsBits word :=
                hfilterb.symm.trans hword
              refine ⟨bit :: word, ?_, ?_⟩
              · simp [hlength]
              · rw [cellsBits_cons, ← htail]
                exact hstream.symm.trans hcellFilter

theorem eventuallyHalts_length0_stream_shape
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hhalt : EventuallyHalts attempt hattempt
      (cfg attempt hattempt (.result .length0)
        (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)) :
    ∃ terminal : Bool, ∃ bits : Word Bool,
      work.filterMap id =
        false :: false :: true :: terminal :: bits := by
  generalize hstream : work.filterMap id = stream
  cases stream with
  | nil =>
      rcases leads_result_empty_to_spin
          (attempt := attempt) (hattempt := hattempt)
          .length0 (by decide) L0 L1 work markers T2
          hcover hshape hstream with
        ⟨T0', T1', hspin⟩
      exact False.elim
        (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
  | cons first rest =>
      cases first with
      | true =>
          rcases leads_result_bad_bit_from_stream
              (attempt := attempt) (hattempt := hattempt)
              .length0 true rest L0 L1 work markers T2
              hcover hshape hstream (by simp [next]) with
            ⟨T0', T1', hspin⟩
          exact False.elim
            (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
      | false =>
          rcases leads_result_from_stream
              (attempt := attempt) (hattempt := hattempt)
              .length0 .length0 false rest
              L0 L1 work markers T2 hcover hshape hstream
              (by simp [next, beginWrite, someStep]) with
            ⟨gap0, work0, markers0, h0,
              hcover0, hshape0, hfilter0⟩
          let L00 := some false ::
            List.append (List.replicate gap0 none) L0
          let L10 := some false ::
            List.append (List.replicate gap0 (some false)) L1
          let T20 := (writeR (some false)).apply T2
          have h0' :
              Leads attempt hattempt
                (cfg attempt hattempt (.result .length0)
                  (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
                (cfg attempt hattempt (.result .length1)
                  (tapeAtCells L00 work0) (tapeAtCells L10 markers0) T20) := by
            simpa [L00, L10, T20, writePhaseTarget,
              writePhaseMarker, writePhaseBit] using h0
          have hhalt0 := eventuallyHalts_of_leads h0' hhalt
          cases rest with
          | nil =>
              rcases leads_result_empty_to_spin
                  (attempt := attempt) (hattempt := hattempt)
                  .length1 (by decide) L00 L10 work0 markers0 T20
                  hcover0 hshape0 hfilter0 with
                ⟨T0', T1', hspin⟩
              exact False.elim
                (false_of_leads_spin_of_eventuallyHalts hspin hhalt0)
          | cons second rest1 =>
              cases second with
              | true =>
                  rcases leads_result_bad_bit_from_stream
                      (attempt := attempt) (hattempt := hattempt)
                      .length1 true rest1 L00 L10 work0 markers0 T20
                      hcover0 hshape0 hfilter0 (by simp [next]) with
                    ⟨T0', T1', hspin⟩
                  exact False.elim
                    (false_of_leads_spin_of_eventuallyHalts hspin hhalt0)
              | false =>
                  rcases leads_result_from_stream
                      (attempt := attempt) (hattempt := hattempt)
                      .length1 .length1 false rest1
                      L00 L10 work0 markers0 T20
                      hcover0 hshape0 hfilter0
                      (by simp [next, beginWrite, someStep]) with
                    ⟨gap1, work1, markers1, h1,
                      hcover1, hshape1, hfilter1⟩
                  let L01 := some false ::
                    List.append (List.replicate gap1 none) L00
                  let L11 := some false ::
                    List.append (List.replicate gap1 (some false)) L10
                  let T21 := (writeR (some false)).apply T20
                  have h1' :
                      Leads attempt hattempt
                        (cfg attempt hattempt (.result .length1)
                          (tapeAtCells L00 work0)
                          (tapeAtCells L10 markers0) T20)
                        (cfg attempt hattempt (.result .length2)
                          (tapeAtCells L01 work1)
                          (tapeAtCells L11 markers1) T21) := by
                    simpa [L01, L11, T21, writePhaseTarget,
                      writePhaseMarker, writePhaseBit] using h1
                  have hhalt1 := eventuallyHalts_of_leads h1' hhalt0
                  cases rest1 with
                  | nil =>
                      rcases leads_result_empty_to_spin
                          (attempt := attempt) (hattempt := hattempt)
                          .length2 (by decide)
                          L01 L11 work1 markers1 T21
                          hcover1 hshape1 hfilter1 with
                        ⟨T0', T1', hspin⟩
                      exact False.elim
                        (false_of_leads_spin_of_eventuallyHalts hspin hhalt1)
                  | cons third rest2 =>
                      cases third with
                      | false =>
                          rcases leads_result_bad_bit_from_stream
                              (attempt := attempt) (hattempt := hattempt)
                              .length2 false rest2
                              L01 L11 work1 markers1 T21
                              hcover1 hshape1 hfilter1
                              (by simp [next]) with
                            ⟨T0', T1', hspin⟩
                          exact False.elim
                            (false_of_leads_spin_of_eventuallyHalts
                              hspin hhalt1)
                      | true =>
                          rcases leads_result_from_stream
                              (attempt := attempt) (hattempt := hattempt)
                              .length2 .length2 true rest2
                              L01 L11 work1 markers1 T21
                              hcover1 hshape1 hfilter1
                              (by simp [next, beginWrite, someStep]) with
                            ⟨gap2, work2, markers2, h2,
                              hcover2, hshape2, hfilter2⟩
                          let L02 := some true ::
                            List.append (List.replicate gap2 none) L01
                          let L12 := some false ::
                            List.append
                              (List.replicate gap2 (some false)) L11
                          let T22 := (writeR (some true)).apply T21
                          have h2' :
                              Leads attempt hattempt
                                (cfg attempt hattempt (.result .length2)
                                  (tapeAtCells L01 work1)
                                  (tapeAtCells L11 markers1) T21)
                                (cfg attempt hattempt (.result .length3)
                                  (tapeAtCells L02 work2)
                                  (tapeAtCells L12 markers2) T22) := by
                            simpa [L02, L12, T22, writePhaseTarget,
                              writePhaseMarker, writePhaseBit] using h2
                          have hhalt2 :=
                            eventuallyHalts_of_leads h2' hhalt1
                          cases rest2 with
                          | nil =>
                              rcases leads_result_empty_to_spin
                                  (attempt := attempt) (hattempt := hattempt)
                                  .length3 (by decide)
                                  L02 L12 work2 markers2 T22
                                  hcover2 hshape2 hfilter2 with
                                ⟨T0', T1', hspin⟩
                              exact False.elim
                                (false_of_leads_spin_of_eventuallyHalts
                                  hspin hhalt2)
                          | cons terminal tail =>
                              exact ⟨terminal, tail, by simpa using hstream⟩

theorem eventuallyHalts_length0_valid_aux
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (fuel count : Nat)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hbound : (work.filterMap id).length ≤ fuel)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hstack : MarkerStack count L1)
    (hhalt : EventuallyHalts attempt hattempt
      (cfg attempt hattempt (.result .length0)
        (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)) :
    ∃ n : Nat, ∃ word : Word Bool,
      word.length = count + n ∧
      work.filterMap id =
        List.append (stageNatBits n) (cellsBits word) := by
  induction fuel generalizing count L0 L1 work markers T2 with
  | zero =>
      rcases eventuallyHalts_length0_stream_shape
          (attempt := attempt) (hattempt := hattempt)
          L0 L1 work markers T2 hcover hshape hhalt with
        ⟨terminal, tail, htoken⟩
      rw [htoken] at hbound
      simp at hbound
  | succ fuel ih =>
      rcases eventuallyHalts_length0_stream_shape
          (attempt := attempt) (hattempt := hattempt)
          L0 L1 work markers T2 hcover hshape hhalt with
        ⟨terminal, tail, htoken⟩
      cases terminal with
      | false =>
          rcases leads_length_tick
              (attempt := attempt) (hattempt := hattempt)
              count tail L0 L1 work markers T2
              hcover hshape htoken hstack with
            ⟨L0a, L1a, worka, markersa,
              htick, hcovera, hshapea, hfiltera, hstacka⟩
          let T2a := writeOutputBits [false, false, true, false] T2
          have htick' :
              Leads attempt hattempt
                (cfg attempt hattempt (.result .length0)
                  (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
                (cfg attempt hattempt (.result .length0)
                  (tapeAtCells L0a worka)
                  (tapeAtCells L1a markersa) T2a) := by
            simpa [T2a] using htick
          have hhalta := eventuallyHalts_of_leads htick' hhalt
          have htailBound : (worka.filterMap id).length ≤ fuel := by
            rw [hfiltera]
            rw [htoken] at hbound
            simp at hbound
            lia
          rcases ih (count + 1) L0a L1a worka markersa T2a
              htailBound hcovera hshapea hstacka hhalta with
            ⟨n, word, hlength, htailShape⟩
          have htail :
              tail = List.append (stageNatBits n) (cellsBits word) :=
            hfiltera.symm.trans htailShape
          refine ⟨n + 1, word, ?_, ?_⟩
          · lia
          · rw [htoken, htail]
            change
              false :: false :: true :: false ::
                  List.append (stageNatBits n) (cellsBits word) =
                List.append (stageNatBits (n + 1)) (cellsBits word)
            rw [show n + 1 = Nat.succ n by rfl]
            simp
      | true =>
          rcases leads_length_done
              (attempt := attempt) (hattempt := hattempt)
              count tail L0 L1 work markers T2
              hcover hshape htoken hstack with
            ⟨L0a, L1a, worka, markersa,
              hdone, hcovera, hshapea, hfiltera, hstacka⟩
          let T2a := writeOutputPrefix [false, false, true, true] tail T2
          have hdone' :
              Leads attempt hattempt
                (cfg attempt hattempt (.result .length0)
                  (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
                (cfg attempt hattempt (.result .seekCell)
                  (tapeAtCells L0a worka)
                  (tapeAtCells L1a markersa) T2a) := by
            simpa [T2a] using hdone
          have hhalta := eventuallyHalts_of_leads hdone' hhalt
          rcases eventuallyHalts_seekCell_stream_shape
              (attempt := attempt) (hattempt := hattempt)
              count L0a L1a worka markersa T2a
              hcovera hshapea hstacka hhalta with
            ⟨word, hlength, hword⟩
          have htail : tail = cellsBits word :=
            hfiltera.symm.trans hword
          refine ⟨0, word, by simpa using hlength, ?_⟩
          rw [htoken, htail]
          simp [stageNatBits_zero]

theorem eventuallyHalts_length0_valid
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (count : Nat)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hstack : MarkerStack count L1)
    (hhalt : EventuallyHalts attempt hattempt
      (cfg attempt hattempt (.result .length0)
        (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)) :
    ∃ n : Nat, ∃ word : Word Bool,
      word.length = count + n ∧
      work.filterMap id =
        List.append (stageNatBits n) (cellsBits word) := by
  exact eventuallyHalts_length0_valid_aux
    (attempt := attempt) (hattempt := hattempt)
    (work.filterMap id).length count L0 L1 work markers T2
    (Nat.le_refl _) hcover hshape hstack hhalt

theorem eventuallyHalts_length1_stream_shape
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hhalt : EventuallyHalts attempt hattempt
      (cfg attempt hattempt (.result .length1)
        (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)) :
    ∃ terminal : Bool, ∃ bits : Word Bool,
      work.filterMap id = false :: true :: terminal :: bits := by
  generalize hstream : work.filterMap id = stream
  cases stream with
  | nil =>
      rcases leads_result_empty_to_spin
          (attempt := attempt) (hattempt := hattempt)
          .length1 (by decide) L0 L1 work markers T2
          hcover hshape hstream with
        ⟨T0', T1', hspin⟩
      exact False.elim
        (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
  | cons first rest =>
      cases first with
      | true =>
          rcases leads_result_bad_bit_from_stream
              (attempt := attempt) (hattempt := hattempt)
              .length1 true rest L0 L1 work markers T2
              hcover hshape hstream (by simp [next]) with
            ⟨T0', T1', hspin⟩
          exact False.elim
            (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
      | false =>
          rcases leads_result_from_stream
              (attempt := attempt) (hattempt := hattempt)
              .length1 .length1 false rest
              L0 L1 work markers T2 hcover hshape hstream
              (by simp [next, beginWrite, someStep]) with
            ⟨gap1, work1, markers1, h1,
              hcover1, hshape1, hfilter1⟩
          let L01 := some false ::
            List.append (List.replicate gap1 none) L0
          let L11 := some false ::
            List.append (List.replicate gap1 (some false)) L1
          let T21 := (writeR (some false)).apply T2
          have h1' :
              Leads attempt hattempt
                (cfg attempt hattempt (.result .length1)
                  (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
                (cfg attempt hattempt (.result .length2)
                  (tapeAtCells L01 work1) (tapeAtCells L11 markers1) T21) := by
            simpa [L01, L11, T21, writePhaseTarget,
              writePhaseMarker, writePhaseBit] using h1
          have hhalt1 := eventuallyHalts_of_leads h1' hhalt
          cases rest with
          | nil =>
              rcases leads_result_empty_to_spin
                  (attempt := attempt) (hattempt := hattempt)
                  .length2 (by decide) L01 L11 work1 markers1 T21
                  hcover1 hshape1 hfilter1 with
                ⟨T0', T1', hspin⟩
              exact False.elim
                (false_of_leads_spin_of_eventuallyHalts hspin hhalt1)
          | cons second rest2 =>
              cases second with
              | false =>
                  rcases leads_result_bad_bit_from_stream
                      (attempt := attempt) (hattempt := hattempt)
                      .length2 false rest2 L01 L11 work1 markers1 T21
                      hcover1 hshape1 hfilter1 (by simp [next]) with
                    ⟨T0', T1', hspin⟩
                  exact False.elim
                    (false_of_leads_spin_of_eventuallyHalts hspin hhalt1)
              | true =>
                  rcases leads_result_from_stream
                      (attempt := attempt) (hattempt := hattempt)
                      .length2 .length2 true rest2
                      L01 L11 work1 markers1 T21
                      hcover1 hshape1 hfilter1
                      (by simp [next, beginWrite, someStep]) with
                    ⟨gap2, work2, markers2, h2,
                      hcover2, hshape2, hfilter2⟩
                  let L02 := some true ::
                    List.append (List.replicate gap2 none) L01
                  let L12 := some false ::
                    List.append (List.replicate gap2 (some false)) L11
                  let T22 := (writeR (some true)).apply T21
                  have h2' :
                      Leads attempt hattempt
                        (cfg attempt hattempt (.result .length2)
                          (tapeAtCells L01 work1)
                          (tapeAtCells L11 markers1) T21)
                        (cfg attempt hattempt (.result .length3)
                          (tapeAtCells L02 work2)
                          (tapeAtCells L12 markers2) T22) := by
                    simpa [L02, L12, T22, writePhaseTarget,
                      writePhaseMarker, writePhaseBit] using h2
                  have hhalt2 := eventuallyHalts_of_leads h2' hhalt1
                  cases rest2 with
                  | nil =>
                      rcases leads_result_empty_to_spin
                          (attempt := attempt) (hattempt := hattempt)
                          .length3 (by decide)
                          L02 L12 work2 markers2 T22
                          hcover2 hshape2 hfilter2 with
                        ⟨T0', T1', hspin⟩
                      exact False.elim
                        (false_of_leads_spin_of_eventuallyHalts hspin hhalt2)
                  | cons terminal tail =>
                      exact ⟨terminal, tail, by simpa using hstream⟩

theorem eventuallyHalts_resultFirst_valid
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hstack : MarkerStack 0 L1)
    (hhalt : EventuallyHalts attempt hattempt
      (cfg attempt hattempt .resultFirst
        (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)) :
    ∃ word : Word Bool,
      work.filterMap id = resultBits word := by
  generalize hstream : work.filterMap id = stream
  cases stream with
  | nil =>
      rcases leads_resultFirst_empty_to_spin
          (attempt := attempt) (hattempt := hattempt)
          L0 L1 work markers T2 hcover hshape hstream with
        ⟨T0', T1', hspin⟩
      exact False.elim
        (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
  | cons first rest =>
      cases first with
      | true =>
          rcases leads_resultFirst_bad_bit_from_stream
              (attempt := attempt) (hattempt := hattempt)
              true rest L0 L1 work markers T2
              hcover hshape hstream (by simp [next]) with
            ⟨T0', T1', hspin⟩
          exact False.elim
            (false_of_leads_spin_of_eventuallyHalts hspin hhalt)
      | false =>
          rcases leads_resultFirst_from_stream
              (attempt := attempt) (hattempt := hattempt)
              rest L0 L1 work markers T2 hcover hshape hstream with
            ⟨gap0, work0, markers0, h0,
              hcover0, hshape0, hfilter0⟩
          let L00 := some false ::
            List.append (List.replicate gap0 none) L0
          let L10 := some false ::
            List.append (List.replicate gap0 (some false)) L1
          let T20 := (writeR (some false)).apply T2
          have h0' :
              Leads attempt hattempt
                (cfg attempt hattempt .resultFirst
                  (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
                (cfg attempt hattempt (.result .length1)
                  (tapeAtCells L00 work0) (tapeAtCells L10 markers0) T20) := by
            simpa [L00, L10, T20] using h0
          have hhalt0 := eventuallyHalts_of_leads h0' hhalt
          have hstack0 : MarkerStack 0 L10 := by
            exact MarkerStack.false
              (markerStack_false_replicate gap0 hstack)
          rcases eventuallyHalts_length1_stream_shape
              (attempt := attempt) (hattempt := hattempt)
              L00 L10 work0 markers0 T20 hcover0 hshape0 hhalt0 with
            ⟨terminal, tail, htoken⟩
          cases terminal with
          | false =>
              rcases leads_length_tick_tail
                  (attempt := attempt) (hattempt := hattempt)
                  0 tail L00 L10 work0 markers0 T20
                  hcover0 hshape0 htoken hstack0 with
                ⟨L0a, L1a, worka, markersa,
                  htick, hcovera, hshapea, hfiltera, hstacka⟩
              let T2a := writeOutputBits [false, true, false] T20
              have htick' :
                  Leads attempt hattempt
                    (cfg attempt hattempt (.result .length1)
                      (tapeAtCells L00 work0)
                      (tapeAtCells L10 markers0) T20)
                    (cfg attempt hattempt (.result .length0)
                      (tapeAtCells L0a worka)
                      (tapeAtCells L1a markersa) T2a) := by
                simpa [T2a] using htick
              have hhalta := eventuallyHalts_of_leads htick' hhalt0
              rcases eventuallyHalts_length0_valid
                  (attempt := attempt) (hattempt := hattempt)
                  1 L0a L1a worka markersa T2a
                  hcovera hshapea hstacka hhalta with
                ⟨n, word, hlength, htailShape⟩
              have htail :
                  tail = List.append (stageNatBits n) (cellsBits word) :=
                hfiltera.symm.trans htailShape
              have hrest : rest = false :: true :: false :: tail :=
                hfilter0.symm.trans htoken
              have hlength' : word.length = Nat.succ n := by lia
              refine ⟨word, ?_⟩
              rw [resultBits_eq_length_cells, hlength']
              rw [hrest, htail]
              change
                false :: false :: true :: false ::
                    List.append (stageNatBits n) (cellsBits word) =
                  List.append (stageNatBits (Nat.succ n)) (cellsBits word)
              rw [stageNatBits_succ']
              rfl
          | true =>
              rcases leads_length_done_tail
                  (attempt := attempt) (hattempt := hattempt)
                  0 tail L00 L10 work0 markers0 T20
                  hcover0 hshape0 htoken hstack0 with
                ⟨L0a, L1a, worka, markersa,
                  hdone, hcovera, hshapea, hfiltera, hstacka⟩
              let T2a := writeOutputPrefix [false, true, true] tail T20
              have hdone' :
                  Leads attempt hattempt
                    (cfg attempt hattempt (.result .length1)
                      (tapeAtCells L00 work0)
                      (tapeAtCells L10 markers0) T20)
                    (cfg attempt hattempt (.result .seekCell)
                      (tapeAtCells L0a worka)
                      (tapeAtCells L1a markersa) T2a) := by
                simpa [T2a] using hdone
              have hhalta := eventuallyHalts_of_leads hdone' hhalt0
              rcases eventuallyHalts_seekCell_stream_shape
                  (attempt := attempt) (hattempt := hattempt)
                  0 L0a L1a worka markersa T2a
                  hcovera hshapea hstacka hhalta with
                ⟨word, hlength, hword⟩
              have htail : tail = cellsBits word :=
                hfiltera.symm.trans hword
              have hrest : rest = false :: true :: true :: tail :=
                hfilter0.symm.trans htoken
              refine ⟨word, ?_⟩
              rw [resultBits_eq_length_cells, hlength]
              rw [hrest, htail]
              simp [stageNatBits_zero]

theorem validator_result_of_run_halt
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (work marker T2 : Tape Bool)
    (hcovered : CoveredTapes work marker)
    (hhalt : EventuallyHalts attempt hattempt
      (cfg attempt hattempt (.run attempt.halt) work marker T2)) :
    ∃ result : Word Bool,
      Tape.normalizedOutput work = resultBits result := by
  rcases leads_run_halt_to_result_first
      (attempt := attempt) (hattempt := hattempt)
      work marker T2 hcovered with
    ⟨workStream, markerRest, hnormalize,
      hcover, hshape, hnormalizeOutput⟩
  have hhaltResult := eventuallyHalts_of_leads hnormalize hhalt
  rcases eventuallyHalts_resultFirst_valid
      (attempt := attempt) (hattempt := hattempt)
      [none] [none] workStream (some false :: markerRest) T2
      hcover hshape MarkerStack.boundary hhaltResult with
    ⟨result, hresult⟩
  refine ⟨result, hnormalizeOutput.symm.trans ?_⟩
  exact (normalizedOutput_tapeAtCells_left_none workStream).trans hresult

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
