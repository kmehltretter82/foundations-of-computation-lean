import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Norm

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

theorem normalizedOutput_tapeAtCells_left_none
    (stream : List (Option Bool)) :
    Tape.normalizedOutput (tapeAtCells [none] stream) =
      stream.filterMap id := by
  cases stream <;> rfl

theorem filterMap_eq_nil_of_allNone (work : List (Option Bool))
    (h : AllNone work) : work.filterMap id = [] := by
  induction work with
  | nil => rfl
  | cons cell rest ih =>
      have hcell : cell = none := h cell (by simp)
      subst cell
      exact ih (allNone_tail h)

/-- The marker cells already passed by the result validator, nearest first.
Only the fourth bit of a unary length tick is marked `true`; the terminal
`none` is the left boundary installed by normalization. -/
inductive MarkerStack : Nat → List (Option Bool) → Prop where
  | boundary : MarkerStack 0 [none]
  | false {count : Nat} {rest : List (Option Bool)} :
      MarkerStack count rest → MarkerStack count (some false :: rest)
  | true {count : Nat} {rest : List (Option Bool)} :
      MarkerStack count rest → MarkerStack (count + 1) (some true :: rest)

theorem markerStack_false_replicate {count : Nat}
    {rest : List (Option Bool)} (gap : Nat)
    (h : MarkerStack count rest) :
    MarkerStack count
      (List.append (List.replicate gap (some false)) rest) := by
  induction gap with
  | zero => exact h
  | succ gap ih =>
      simpa [List.replicate_succ] using MarkerStack.false ih

theorem markerStack_succ_decomp_aux {total : Nat}
    {stack : List (Option Bool)} (h : MarkerStack total stack) :
    ∀ count : Nat, total = count + 1 →
    ∃ gap : Nat, ∃ rest : List (Option Bool),
      stack = List.append (List.replicate gap (some false))
        (some true :: rest) ∧
      MarkerStack count rest := by
  induction h with
  | boundary =>
      intro count heq
      simp at heq
  | @false n rest h ih =>
      intro count heq
      rcases ih count heq with ⟨gap, tail, hrest, htail⟩
      refine ⟨gap + 1, tail, ?_, htail⟩
      rw [hrest]
      simp [List.replicate_succ]
  | @true n rest h ih =>
      intro count heq
      have hn : n = count := Nat.add_right_cancel heq
      subst count
      refine ⟨0, rest, rfl, ?_⟩
      exact h

theorem markerStack_succ_decomp {count : Nat}
    {stack : List (Option Bool)} (h : MarkerStack (count + 1) stack) :
    ∃ gap : Nat, ∃ rest : List (Option Bool),
      stack = List.append (List.replicate gap (some false))
        (some true :: rest) ∧
      MarkerStack count rest :=
  markerStack_succ_decomp_aux h count rfl

theorem stream_next_decomp
    (bit : Bool) (bits : Word Bool)
    (work markers : List (Option Bool))
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = bit :: bits) :
    ∃ gap : Nat, ∃ workTail markerTail : List (Option Bool),
      work = List.append (List.replicate gap none) (some bit :: workTail) ∧
      markers = List.append
        (List.replicate (gap + 1) (some false)) markerTail ∧
      RightCovers workTail markerTail ∧
      MarkerSide markerTail ∧
      workTail.filterMap id = bits := by
  induction work generalizing markers with
  | nil => simp at hfilter
  | cons cell workTail ih =>
      cases markers with
      | nil =>
          cases hcover with
          | extra _ hall =>
              have hempty := filterMap_eq_nil_of_allNone _ hall
              rw [hempty] at hfilter
              cases hfilter
      | cons marker markerTail =>
          cases hcover with
          | @cons workCell markerCell works markerCells hcell htail =>
              cases cell with
              | none =>
                  have hfilterTail : workTail.filterMap id = bit :: bits := by
                    exact hfilter
                  rcases hcell with hfalse | ⟨_workNone, hnone⟩
                  · subst marker
                    rcases ih markerTail htail (markerSide_tail hshape)
                        hfilterTail with
                      ⟨gap, restWork, restMarker,
                        hwork, hmarker, hcoverRest, hshapeRest, hfilterRest⟩
                    refine ⟨gap + 1, restWork, restMarker, ?_, ?_,
                      hcoverRest, hshapeRest, hfilterRest⟩
                    · rw [hwork]
                      simp [List.replicate_succ]
                    · rw [hmarker]
                      simp [List.replicate_succ, Nat.add_assoc]
                  · subst marker
                    have hmarkerNil := markerSide_none_head_tail_nil hshape
                    subst markerTail
                    cases htail with
                    | extra _ hall =>
                        have hempty := filterMap_eq_nil_of_allNone _ hall
                        rw [hempty] at hfilterTail
                        cases hfilterTail
              | some actual =>
                  have hmarkerFalse : marker = some false := by
                    rcases hcell with hfalse | ⟨hworkNone, _⟩
                    · exact hfalse
                    · cases hworkNone
                  subst marker
                  have hbits : actual = bit ∧
                      workTail.filterMap id = bits := by
                    simpa using hfilter
                  refine ⟨0, workTail, markerTail, ?_, rfl, htail,
                    markerSide_tail hshape, hbits.right⟩
                  rw [hbits.left]
                  rfl

theorem leads_resultFirst_blank {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (L0 L1 right0 right1 : List (Option Bool)) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .resultFirst
        (tapeAtCells L0 (none :: right0))
        (tapeAtCells L1 (some false :: right1)) T2)
      (cfg attempt hattempt .resultFirst
        (tapeAtCells (none :: L0) right0)
        (tapeAtCells (some false :: L1) right1) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.resultFirst)
      (T0 := tapeAtCells L0 (none :: right0))
      (T1 := tapeAtCells L1 (some false :: right1)) (T2 := T2)
      (st := ⟨CoreState.resultFirst, keepR, writeR (some false), keepS⟩)
      (T0' := tapeAtCells (none :: L0) right0)
      (T1' := tapeAtCells (some false :: L1) right1) (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl)
      (keepR_apply_tapeAtCells L0 none right0)
      (writeR_apply_tapeAtCells (some false) L1 (some false) right1) rfl

theorem leads_result_blank {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase)
    (L0 L1 right0 right1 : List (Option Bool)) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result phase)
        (tapeAtCells L0 (none :: right0))
        (tapeAtCells L1 (some false :: right1)) T2)
      (cfg attempt hattempt (.result phase)
        (tapeAtCells (none :: L0) right0)
        (tapeAtCells (some false :: L1) right1) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.result phase)
      (T0 := tapeAtCells L0 (none :: right0))
      (T1 := tapeAtCells L1 (some false :: right1)) (T2 := T2)
      (st := ⟨CoreState.result phase, keepR, writeR (some false), keepS⟩)
      (T0' := tapeAtCells (none :: L0) right0)
      (T1' := tapeAtCells (some false :: L1) right1) (T2' := T2)
      (mem_states_of_stateBounded trivial) (by cases phase <;> rfl)
      (keepR_apply_tapeAtCells L0 none right0)
      (writeR_apply_tapeAtCells (some false) L1 (some false) right1) rfl

theorem leads_resultFirst_blanks {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (gap : Nat) (L0 L1 tail0 tail1 : List (Option Bool)) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .resultFirst
        (tapeAtCells L0
          (List.append (List.replicate gap none) tail0))
        (tapeAtCells L1
          (List.append (List.replicate gap (some false)) tail1)) T2)
      (cfg attempt hattempt .resultFirst
        (tapeAtCells
          (List.append (List.replicate gap none) L0) tail0)
        (tapeAtCells
          (List.append (List.replicate gap (some false)) L1) tail1) T2) := by
  induction gap generalizing L0 L1 with
  | zero => exact Leads.refl _ _ _
  | succ gap ih =>
      simp only [List.replicate_succ]
      refine (leads_resultFirst_blank (attempt := attempt)
        (hattempt := hattempt) L0 L1 _ _ T2).trans ?_
      have hih := ih (none :: L0) (some false :: L1)
      have h0 :
          List.append (List.replicate gap (none : Option Bool)) (none :: L0) =
            none :: List.append (List.replicate gap none) L0 :=
        list_replicate_append_cons_eq_cons_append none gap L0
      have h1 :
          List.append (List.replicate gap (some false)) (some false :: L1) =
            some false :: List.append (List.replicate gap (some false)) L1 :=
        list_replicate_append_cons_eq_cons_append (some false) gap L1
      rw [h0, h1] at hih
      exact hih

theorem leads_result_blanks {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (gap : Nat)
    (L0 L1 tail0 tail1 : List (Option Bool)) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result phase)
        (tapeAtCells L0
          (List.append (List.replicate gap none) tail0))
        (tapeAtCells L1
          (List.append (List.replicate gap (some false)) tail1)) T2)
      (cfg attempt hattempt (.result phase)
        (tapeAtCells
          (List.append (List.replicate gap none) L0) tail0)
        (tapeAtCells
          (List.append (List.replicate gap (some false)) L1) tail1) T2) := by
  induction gap generalizing L0 L1 with
  | zero => exact Leads.refl _ _ _
  | succ gap ih =>
      simp only [List.replicate_succ]
      refine (leads_result_blank (attempt := attempt) (hattempt := hattempt)
        phase L0 L1 _ _ T2).trans ?_
      have hih := ih (none :: L0) (some false :: L1)
      have h0 :
          List.append (List.replicate gap (none : Option Bool)) (none :: L0) =
            none :: List.append (List.replicate gap none) L0 :=
        list_replicate_append_cons_eq_cons_append none gap L0
      have h1 :
          List.append (List.replicate gap (some false)) (some false :: L1) =
            some false :: List.append (List.replicate gap (some false)) L1 :=
        list_replicate_append_cons_eq_cons_append (some false) gap L1
      rw [h0, h1] at hih
      exact hih

inductive PendingPhase : WritePhase → Prop where
  | lengthDone : PendingPhase .lengthDone
  | cell3False : PendingPhase .cell3False
  | cell3True : PendingPhase .cell3True

theorem leads_pending_blank {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : WritePhase) (L0 L1 right0 right1 : List (Option Bool))
    (T2 : Tape Bool) (hphase : PendingPhase phase) :
    Leads attempt hattempt
      (cfg attempt hattempt (.writeResult phase)
        (tapeAtCells L0 (none :: right0))
        (tapeAtCells L1 (some false :: right1)) T2)
      (cfg attempt hattempt (.writeResult phase)
        (tapeAtCells (none :: L0) right0)
        (tapeAtCells (some false :: L1) right1) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.writeResult phase)
      (T0 := tapeAtCells L0 (none :: right0))
      (T1 := tapeAtCells L1 (some false :: right1)) (T2 := T2)
      (st := ⟨CoreState.writeResult phase, keepR,
        writeR (some false), keepS⟩)
      (T0' := tapeAtCells (none :: L0) right0)
      (T1' := tapeAtCells (some false :: L1) right1) (T2' := T2)
      (mem_states_of_stateBounded trivial)
      (by cases hphase <;> rfl)
      (keepR_apply_tapeAtCells L0 none right0)
      (writeR_apply_tapeAtCells (some false) L1 (some false) right1) rfl

theorem leads_pending_blanks {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : WritePhase) (gap : Nat)
    (L0 L1 tail0 tail1 : List (Option Bool)) (T2 : Tape Bool)
    (hphase : PendingPhase phase) :
    Leads attempt hattempt
      (cfg attempt hattempt (.writeResult phase)
        (tapeAtCells L0
          (List.append (List.replicate gap none) tail0))
        (tapeAtCells L1
          (List.append (List.replicate gap (some false)) tail1)) T2)
      (cfg attempt hattempt (.writeResult phase)
        (tapeAtCells
          (List.append (List.replicate gap none) L0) tail0)
        (tapeAtCells
          (List.append (List.replicate gap (some false)) L1) tail1) T2) := by
  induction gap generalizing L0 L1 with
  | zero => exact Leads.refl _ _ _
  | succ gap ih =>
      simp only [List.replicate_succ]
      refine (leads_pending_blank (attempt := attempt) (hattempt := hattempt)
        phase L0 L1 _ _ T2 hphase).trans ?_
      have hih := ih (none :: L0) (some false :: L1)
      have h0 :
          List.append (List.replicate gap (none : Option Bool)) (none :: L0) =
            none :: List.append (List.replicate gap none) L0 :=
        list_replicate_append_cons_eq_cons_append none gap L0
      have h1 :
          List.append (List.replicate gap (some false)) (some false :: L1) =
            some false :: List.append (List.replicate gap (some false)) L1 :=
        list_replicate_append_cons_eq_cons_append (some false) gap L1
      rw [h0, h1] at hih
      exact hih

theorem leads_pending_flush_right {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : WritePhase) (bit : Bool)
    (L0 L1 right0 right1 : List (Option Bool))
    (T2 : Tape Bool) (hphase : PendingPhase phase) :
    Leads attempt hattempt
      (cfg attempt hattempt (.writeResult phase)
        (tapeAtCells L0 (some bit :: right0))
        (tapeAtCells L1 (some false :: right1)) T2)
      (cfg attempt hattempt (.result .seekCell)
        (tapeAtCells L0 (some bit :: right0))
        (tapeAtCells L1 (some false :: right1))
        ((writeR (some (writePhaseBit phase))).apply T2)) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.writeResult phase)
      (T0 := tapeAtCells L0 (some bit :: right0))
      (T1 := tapeAtCells L1 (some false :: right1)) (T2 := T2)
      (st := ⟨CoreState.result .seekCell, keepS, keepS,
        writeR (some (writePhaseBit phase))⟩)
      (T0' := tapeAtCells L0 (some bit :: right0))
      (T1' := tapeAtCells L1 (some false :: right1))
      (T2' := (writeR (some (writePhaseBit phase))).apply T2)
      (mem_states_of_stateBounded trivial)
      (by cases hphase <;> rfl) rfl rfl rfl

theorem leads_pending_flush_stay {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : WritePhase) (T0 T1 T2 : Tape Bool)
    (hphase : PendingPhase phase) (hread : Tape.read T1 = none) :
    Leads attempt hattempt
      (cfg attempt hattempt (.writeResult phase) T0 T1 T2)
      (cfg attempt hattempt (.result .seekCell) T0 T1
        ((writeS (some (writePhaseBit phase))).apply T2)) := by
  have hnext :
      (table attempt hattempt).next (.writeResult phase)
          (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some ⟨CoreState.result .seekCell, keepS, keepS,
          writeS (some (writePhaseBit phase))⟩ := by
    change next attempt (.writeResult phase)
      (Tape.read T0) (Tape.read T1) (Tape.read T2) = _
    rw [hread]
    cases hphase <;> rfl
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.writeResult phase) (T0 := T0) (T1 := T1) (T2 := T2)
      (st := ⟨CoreState.result .seekCell, keepS, keepS,
        writeS (some (writePhaseBit phase))⟩)
      (T0' := T0) (T1' := T1)
      (T2' := (writeS (some (writePhaseBit phase))).apply T2)
      (mem_states_of_stateBounded trivial)
      hnext rfl rfl rfl

theorem leads_pending_next {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : WritePhase) (bit : Bool) (gap : Nat)
    (L0 L1 workTail markerTail : List (Option Bool)) (T2 : Tape Bool)
    (hphase : PendingPhase phase) :
    Leads attempt hattempt
      (cfg attempt hattempt (.writeResult phase)
        (tapeAtCells L0
          (List.append (List.replicate gap none) (some bit :: workTail)))
        (tapeAtCells L1
          (List.append (List.replicate (gap + 1) (some false)) markerTail))
        T2)
      (cfg attempt hattempt (.result .seekCell)
        (tapeAtCells (List.append (List.replicate gap none) L0)
          (some bit :: workTail))
        (tapeAtCells
          (List.append (List.replicate gap (some false)) L1)
          (some false :: markerTail))
        ((writeR (some (writePhaseBit phase))).apply T2)) := by
  have hmark :
      List.append (List.replicate (gap + 1) (some false)) markerTail =
        List.append (List.replicate gap (some false))
          (some false :: markerTail) :=
    (list_replicate_append_self (some false) gap markerTail).symm
  rw [hmark]
  refine (leads_pending_blanks (attempt := attempt) (hattempt := hattempt)
    phase gap L0 L1 (some bit :: workTail)
      (some false :: markerTail) T2 hphase).trans ?_
  exact leads_pending_flush_right
    (attempt := attempt) (hattempt := hattempt)
    phase bit _ _ workTail markerTail T2 hphase

theorem leads_resultFirst_false {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (L0 L1 right0 right1 : List (Option Bool)) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .resultFirst
        (tapeAtCells L0 (some false :: right0))
        (tapeAtCells L1 (some false :: right1)) T2)
      (cfg attempt hattempt (.result .length1)
        (tapeAtCells (some false :: L0) right0)
        (tapeAtCells (some false :: L1) right1)
        ((writeR (some false)).apply T2)) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.resultFirst)
      (T0 := tapeAtCells L0 (some false :: right0))
      (T1 := tapeAtCells L1 (some false :: right1)) (T2 := T2)
      (st := ⟨CoreState.result .length1, keepR,
        writeR (some false), writeR (some false)⟩)
      (T0' := tapeAtCells (some false :: L0) right0)
      (T1' := tapeAtCells (some false :: L1) right1)
      (T2' := (writeR (some false)).apply T2)
      (mem_states_of_stateBounded trivial) (by rfl)
      (keepR_apply_tapeAtCells L0 (some false) right0)
      (writeR_apply_tapeAtCells (some false) L1 (some false) right1) rfl

theorem leads_result_write {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (wp : WritePhase) (bit : Bool)
    (L0 L1 right0 right1 : List (Option Bool)) (T2 : Tape Bool)
    (hbegin :
      next attempt (.result phase) (some bit) (some false) (Tape.read T2) =
        some ⟨writePhaseTarget wp,
          keepR, writeR (some (writePhaseMarker wp)),
          writeR (some (writePhaseBit wp))⟩) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result phase)
        (tapeAtCells L0 (some bit :: right0))
        (tapeAtCells L1 (some false :: right1)) T2)
      (cfg attempt hattempt (writePhaseTarget wp)
        (tapeAtCells (some bit :: L0) right0)
        (tapeAtCells (some (writePhaseMarker wp) :: L1) right1)
        ((writeR (some (writePhaseBit wp))).apply T2)) := by
  have hnext :
      (table attempt hattempt).next (.result phase)
          (some bit) (some false) (Tape.read T2) =
        some ⟨writePhaseTarget wp,
          keepR, writeR (some (writePhaseMarker wp)),
          writeR (some (writePhaseBit wp))⟩ := by
    change next attempt (.result phase)
        (some bit) (some false) (Tape.read T2) = _
    exact hbegin
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.result phase)
      (T0 := tapeAtCells L0 (some bit :: right0))
      (T1 := tapeAtCells L1 (some false :: right1)) (T2 := T2)
      (st := ⟨writePhaseTarget wp, keepR,
        writeR (some (writePhaseMarker wp)),
        writeR (some (writePhaseBit wp))⟩)
      (T0' := tapeAtCells (some bit :: L0) right0)
      (T1' := tapeAtCells (some (writePhaseMarker wp) :: L1) right1)
      (T2' := (writeR (some (writePhaseBit wp))).apply T2)
      (mem_states_of_stateBounded trivial)
      (by simpa only [read_tapeAtCells_cons] using hnext)
      (keepR_apply_tapeAtCells L0 (some bit) right0)
      (writeR_apply_tapeAtCells (some (writePhaseMarker wp))
        L1 (some false) right1) rfl

theorem leads_resultFirst_next_false {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (gap : Nat) (L0 L1 workTail markerTail : List (Option Bool))
    (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .resultFirst
        (tapeAtCells L0
          (List.append (List.replicate gap none) (some false :: workTail)))
        (tapeAtCells L1
          (List.append (List.replicate (gap + 1) (some false)) markerTail))
        T2)
      (cfg attempt hattempt (.result .length1)
        (tapeAtCells
          (some false :: List.append (List.replicate gap none) L0) workTail)
        (tapeAtCells
          (some false :: List.append (List.replicate gap (some false)) L1)
          markerTail)
        ((writeR (some false)).apply T2)) := by
  have hmark :
      List.append (List.replicate (gap + 1) (some false)) markerTail =
        List.append (List.replicate gap (some false))
          (some false :: markerTail) :=
    (list_replicate_append_self (some false) gap markerTail).symm
  rw [hmark]
  refine (leads_resultFirst_blanks (attempt := attempt) (hattempt := hattempt)
    gap L0 L1 (some false :: workTail) (some false :: markerTail) T2).trans ?_
  exact leads_resultFirst_false (attempt := attempt) (hattempt := hattempt)
    _ _ workTail markerTail T2

theorem leads_result_next {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (wp : WritePhase) (bit : Bool) (gap : Nat)
    (L0 L1 workTail markerTail : List (Option Bool)) (T2 : Tape Bool)
    (hbegin :
      next attempt (.result phase) (some bit) (some false) (Tape.read T2) =
        some ⟨writePhaseTarget wp,
          keepR, writeR (some (writePhaseMarker wp)),
          writeR (some (writePhaseBit wp))⟩) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result phase)
        (tapeAtCells L0
          (List.append (List.replicate gap none) (some bit :: workTail)))
        (tapeAtCells L1
          (List.append (List.replicate (gap + 1) (some false)) markerTail))
        T2)
      (cfg attempt hattempt (writePhaseTarget wp)
        (tapeAtCells
          (some bit :: List.append (List.replicate gap none) L0) workTail)
        (tapeAtCells
          (some (writePhaseMarker wp) ::
            List.append (List.replicate gap (some false)) L1)
          markerTail)
        ((writeR (some (writePhaseBit wp))).apply T2)) := by
  have hmark :
      List.append (List.replicate (gap + 1) (some false)) markerTail =
        List.append (List.replicate gap (some false))
          (some false :: markerTail) :=
    (list_replicate_append_self (some false) gap markerTail).symm
  rw [hmark]
  refine (leads_result_blanks (attempt := attempt) (hattempt := hattempt)
    phase gap L0 L1 (some bit :: workTail) (some false :: markerTail) T2).trans ?_
  exact leads_result_write (attempt := attempt) (hattempt := hattempt)
    phase wp bit _ _ workTail markerTail T2 hbegin

theorem leads_result_pending {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (wp : WritePhase) (bit : Bool)
    (L0 L1 right0 right1 : List (Option Bool)) (T2 : Tape Bool)
    (hbegin :
      next attempt (.result phase) (some bit) (some false) (Tape.read T2) =
        some ⟨CoreState.writeResult wp, keepR,
          writeR (some (writePhaseMarker wp)), keepS⟩) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result phase)
        (tapeAtCells L0 (some bit :: right0))
        (tapeAtCells L1 (some false :: right1)) T2)
      (cfg attempt hattempt (.writeResult wp)
        (tapeAtCells (some bit :: L0) right0)
        (tapeAtCells (some (writePhaseMarker wp) :: L1) right1) T2) := by
  have hnext :
      (table attempt hattempt).next (.result phase)
          (some bit) (some false) (Tape.read T2) =
        some ⟨CoreState.writeResult wp, keepR,
          writeR (some (writePhaseMarker wp)), keepS⟩ := by
    change next attempt (.result phase)
        (some bit) (some false) (Tape.read T2) = _
    exact hbegin
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.result phase)
      (T0 := tapeAtCells L0 (some bit :: right0))
      (T1 := tapeAtCells L1 (some false :: right1)) (T2 := T2)
      (st := ⟨CoreState.writeResult wp, keepR,
        writeR (some (writePhaseMarker wp)), keepS⟩)
      (T0' := tapeAtCells (some bit :: L0) right0)
      (T1' := tapeAtCells (some (writePhaseMarker wp) :: L1) right1)
      (T2' := T2) (mem_states_of_stateBounded trivial)
      (by simpa only [read_tapeAtCells_cons] using hnext)
      (keepR_apply_tapeAtCells L0 (some bit) right0)
      (writeR_apply_tapeAtCells (some (writePhaseMarker wp))
        L1 (some false) right1) rfl

theorem leads_result_pending_next {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (wp : WritePhase) (bit : Bool) (gap : Nat)
    (L0 L1 workTail markerTail : List (Option Bool)) (T2 : Tape Bool)
    (hbegin :
      next attempt (.result phase) (some bit) (some false) (Tape.read T2) =
        some ⟨CoreState.writeResult wp, keepR,
          writeR (some (writePhaseMarker wp)), keepS⟩) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result phase)
        (tapeAtCells L0
          (List.append (List.replicate gap none) (some bit :: workTail)))
        (tapeAtCells L1
          (List.append (List.replicate (gap + 1) (some false)) markerTail))
        T2)
      (cfg attempt hattempt (.writeResult wp)
        (tapeAtCells
          (some bit :: List.append (List.replicate gap none) L0) workTail)
        (tapeAtCells
          (some (writePhaseMarker wp) ::
            List.append (List.replicate gap (some false)) L1)
          markerTail) T2) := by
  have hmark :
      List.append (List.replicate (gap + 1) (some false)) markerTail =
        List.append (List.replicate gap (some false))
          (some false :: markerTail) :=
    (list_replicate_append_self (some false) gap markerTail).symm
  rw [hmark]
  refine (leads_result_blanks (attempt := attempt) (hattempt := hattempt)
    phase gap L0 L1 (some bit :: workTail)
      (some false :: markerTail) T2).trans ?_
  exact leads_result_pending (attempt := attempt) (hattempt := hattempt)
    phase wp bit _ _ workTail markerTail T2 hbegin

theorem leads_result_pending_from_stream {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (wp : WritePhase)
    (bit : Bool) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = bit :: bits)
    (hbegin :
      next attempt (.result phase) (some bit) (some false) (Tape.read T2) =
        some ⟨CoreState.writeResult wp, keepR,
          writeR (some (writePhaseMarker wp)), keepS⟩) :
    ∃ gap : Nat, ∃ workTail markerTail : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result phase)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.writeResult wp)
          (tapeAtCells
            (some bit :: List.append (List.replicate gap none) L0)
            workTail)
          (tapeAtCells
            (some (writePhaseMarker wp) ::
              List.append (List.replicate gap (some false)) L1)
            markerTail) T2) ∧
      RightCovers workTail markerTail ∧
      MarkerSide markerTail ∧
      workTail.filterMap id = bits := by
  rcases stream_next_decomp bit bits work markers
      hcover hshape hfilter with
    ⟨gap, workTail, markerTail, hwork, hmarkers,
      hcoverTail, hshapeTail, hfilterTail⟩
  subst work
  subst markers
  exact ⟨gap, workTail, markerTail,
    leads_result_pending_next
      (attempt := attempt) (hattempt := hattempt)
      phase wp bit gap L0 L1 workTail markerTail T2 hbegin,
    hcoverTail, hshapeTail, hfilterTail⟩

def writeOutputBits : Word Bool → Tape Bool → Tape Bool
  | [], T => T
  | bit :: bits, T =>
      writeOutputBits bits ((writeR (some bit)).apply T)

theorem writeOutputBits_append (a b : Word Bool) (T : Tape Bool) :
    writeOutputBits (List.append a b) T =
      writeOutputBits b (writeOutputBits a T) := by
  induction a generalizing T with
  | nil => rfl
  | cons bit rest ih =>
      change writeOutputBits (List.append rest b)
          ((writeR (some bit)).apply T) = _
      exact ih ((writeR (some bit)).apply T)

theorem writeOutputBits_tapeAtCells (bits : Word Bool)
    (left : List (Option Bool)) :
    writeOutputBits bits (tapeAtCells left []) =
      tapeAtCells (pushWord bits left) [] := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit rest ih =>
      change writeOutputBits rest
          ((writeR (some bit)).apply (tapeAtCells left [])) = _
      have hwrite :
          (writeR (some bit)).apply (tapeAtCells left []) =
            tapeAtCells (some bit :: left) [] := by rfl
      rw [hwrite, ih]
      exact congrArg (fun xs => tapeAtCells xs [])
        (pushWord_cons bit rest left).symm

def writeOutputBitsFinal : Word Bool → Tape Bool → Tape Bool
  | [], T => T
  | [bit], T => (writeS (some bit)).apply T
  | bit :: next :: rest, T =>
      writeOutputBitsFinal (next :: rest) ((writeR (some bit)).apply T)

def writeOutputPrefix (bits remaining : Word Bool) (T : Tape Bool) :
    Tape Bool :=
  if remaining = [] then writeOutputBitsFinal bits T
  else writeOutputBits bits T

theorem writeOutputBitsFinal_append_of_ne_nil
    (a b : Word Bool) (hb : b ≠ []) (T : Tape Bool) :
    writeOutputBitsFinal (List.append a b) T =
      writeOutputBitsFinal b (writeOutputBits a T) := by
  induction a generalizing T with
  | nil => rfl
  | cons bit rest ih =>
      cases rest with
      | nil =>
          cases b with
          | nil => exact False.elim (hb rfl)
          | cons next tail => rfl
      | cons next tail =>
          change writeOutputBitsFinal
              (List.append (next :: tail) b)
              ((writeR (some bit)).apply T) =
            writeOutputBitsFinal b
              (writeOutputBits (next :: tail)
                ((writeR (some bit)).apply T))
          exact ih ((writeR (some bit)).apply T)

theorem writeOutputPrefix_append (a b remaining : Word Bool)
    (T : Tape Bool) :
    writeOutputPrefix (List.append a b) remaining T =
      writeOutputPrefix b remaining
        (writeOutputPrefix a (List.append b remaining) T) := by
  cases remaining with
  | nil =>
      cases b with
      | nil => simp [writeOutputPrefix, writeOutputBitsFinal]
      | cons bit rest =>
          have hb : (bit :: rest : Word Bool) ≠ [] := by simp
          simpa [writeOutputPrefix] using
            (writeOutputBitsFinal_append_of_ne_nil
              a (bit :: rest) hb T)
  | cons bit rest =>
      cases b with
      | nil =>
          simp [writeOutputPrefix]
          rfl
      | cons head tail =>
          simp [writeOutputPrefix]
          exact writeOutputBits_append a (head :: tail) T

theorem stageNatBits_append_ne_nil (n : Nat) (bits : Word Bool) :
    List.append (stageNatBits n) bits ≠ [] := by
  cases n <;> simp [stageNatBits_zero]

theorem leads_resultFirst_from_stream {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bits : Word Bool) (L0 L1 work markers : List (Option Bool))
    (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = false :: bits) :
    ∃ gap : Nat, ∃ workTail markerTail : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt .resultFirst
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .length1)
          (tapeAtCells
            (some false :: List.append (List.replicate gap none) L0)
            workTail)
          (tapeAtCells
            (some false ::
              List.append (List.replicate gap (some false)) L1)
            markerTail)
          ((writeR (some false)).apply T2)) ∧
      RightCovers workTail markerTail ∧
      MarkerSide markerTail ∧
      workTail.filterMap id = bits := by
  rcases stream_next_decomp false bits work markers
      hcover hshape hfilter with
    ⟨gap, workTail, markerTail, hwork, hmarkers,
      hcoverTail, hshapeTail, hfilterTail⟩
  subst work
  subst markers
  exact ⟨gap, workTail, markerTail,
    leads_resultFirst_next_false
      (attempt := attempt) (hattempt := hattempt)
      gap L0 L1 workTail markerTail T2,
    hcoverTail, hshapeTail, hfilterTail⟩

theorem leads_result_from_stream {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (wp : WritePhase)
    (bit : Bool) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = bit :: bits)
    (hbegin :
      next attempt (.result phase) (some bit) (some false) (Tape.read T2) =
        some ⟨writePhaseTarget wp,
          keepR, writeR (some (writePhaseMarker wp)),
          writeR (some (writePhaseBit wp))⟩) :
    ∃ gap : Nat, ∃ workTail markerTail : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result phase)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (writePhaseTarget wp)
          (tapeAtCells
            (some bit :: List.append (List.replicate gap none) L0)
            workTail)
          (tapeAtCells
            (some (writePhaseMarker wp) ::
              List.append (List.replicate gap (some false)) L1)
            markerTail)
          ((writeR (some (writePhaseBit wp))).apply T2)) ∧
      RightCovers workTail markerTail ∧
      MarkerSide markerTail ∧
      workTail.filterMap id = bits := by
  rcases stream_next_decomp bit bits work markers
      hcover hshape hfilter with
    ⟨gap, workTail, markerTail, hwork, hmarkers,
      hcoverTail, hshapeTail, hfilterTail⟩
  subst work
  subst markers
  exact ⟨gap, workTail, markerTail,
    leads_result_next (attempt := attempt) (hattempt := hattempt)
      phase wp bit gap L0 L1 workTail markerTail T2 hbegin,
    hcoverTail, hshapeTail, hfilterTail⟩

theorem leads_pending_from_stream {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : WritePhase) (bit : Bool) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = bit :: bits)
    {count : Nat} (hstack : MarkerStack count L1)
    (hphase : PendingPhase phase) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.writeResult phase)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          ((writeR (some (writePhaseBit phase))).apply T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bit :: bits ∧
      MarkerStack count L1' := by
  rcases stream_next_decomp bit bits work markers
      hcover hshape hfilter with
    ⟨gap, workTail, markerTail, hwork, hmarkers,
      hcoverTail, hshapeTail, hfilterTail⟩
  subst work
  subst markers
  let L0' := List.append (List.replicate gap none) L0
  let L1' := List.append (List.replicate gap (some false)) L1
  refine ⟨L0', L1', some bit :: workTail, some false :: markerTail,
    ?_, RightCovers.cons (cellCovered_false _) hcoverTail,
    MarkerSide.marked hshapeTail, ?_, ?_⟩
  · simpa [L0', L1'] using
      (leads_pending_next
        (attempt := attempt) (hattempt := hattempt)
        phase bit gap L0 L1 workTail markerTail T2 hphase)
  · simpa using hfilterTail
  · exact markerStack_false_replicate gap hstack

theorem leads_pending_from_empty_stream {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : WritePhase)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = [])
    {count : Nat} (hstack : MarkerStack count L1)
    (hphase : PendingPhase phase) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.writeResult phase)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          ((writeS (some (writePhaseBit phase))).apply T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = [] ∧
      MarkerStack count L1' := by
  induction hshape generalizing work L0 L1 with
  | nil =>
      cases hcover with
      | extra works hall =>
          refine ⟨L0, L1, work, [], ?_, RightCovers.extra work hall,
            MarkerSide.nil, hfilter, hstack⟩
          exact leads_pending_flush_stay
            (attempt := attempt) (hattempt := hattempt)
            phase (tapeAtCells L0 work) (tapeAtCells L1 []) T2
            hphase rfl
  | boundary =>
      cases hcover with
      | @cons workCell markerCell works markerCells hcell htail =>
          refine ⟨L0, L1, workCell :: works, [none], ?_,
            RightCovers.cons hcell htail, MarkerSide.boundary,
            hfilter, hstack⟩
          exact leads_pending_flush_stay
            (attempt := attempt) (hattempt := hattempt)
            phase (tapeAtCells L0 (workCell :: works))
              (tapeAtCells L1 [none]) T2 hphase rfl
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
          have hscan := leads_pending_blank
            (attempt := attempt) (hattempt := hattempt)
            phase L0 L1 workTail markerTail T2 hphase
          have hstackTail : MarkerStack count (some false :: L1) :=
            MarkerStack.false hstack
          rcases ih (work := workTail) (L0 := none :: L0)
              (L1 := some false :: L1)
              hcoverTail hfilterTail hstackTail with
            ⟨L0', L1', work', markers', htail,
              hcover', hshape', hfilter', hstack'⟩
          exact ⟨L0', L1', work', markers', hscan.trans htail,
            hcover', hshape', hfilter', hstack'⟩

theorem leads_result_terminal_from_stream {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (phase : ResultPhase) (wp : WritePhase)
    (terminal : Bool) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = terminal :: bits)
    {count : Nat} (hstack : MarkerStack count L1)
    (hphase : PendingPhase wp)
    (hbegin :
      next attempt (.result phase) (some terminal) (some false)
          (Tape.read T2) =
        some ⟨CoreState.writeResult wp, keepR,
          writeR (some (writePhaseMarker wp)), keepS⟩) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result phase)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix [writePhaseBit wp] bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack count L1' := by
  rcases leads_result_pending_from_stream
      (attempt := attempt) (hattempt := hattempt)
      phase wp terminal bits L0 L1 work markers T2
      hcover hshape hfilter hbegin with
    ⟨gap, workTail, markerTail, hconsume,
      hcoverTail, hshapeTail, hfilterTail⟩
  let L0p := some terminal :: List.append (List.replicate gap none) L0
  let L1p := some false ::
    List.append (List.replicate gap (some false)) L1
  have hstackp : MarkerStack count L1p := by
    exact MarkerStack.false (markerStack_false_replicate gap hstack)
  have hconsume' :
      Leads attempt hattempt
        (cfg attempt hattempt (.result phase)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.writeResult wp)
          (tapeAtCells L0p workTail) (tapeAtCells L1p markerTail) T2) := by
    cases hphase <;> simpa [L0p, L1p, writePhaseMarker] using hconsume
  cases bits with
  | nil =>
      rcases leads_pending_from_empty_stream
          (attempt := attempt) (hattempt := hattempt)
          wp L0p L1p workTail markerTail T2
          hcoverTail hshapeTail hfilterTail hstackp hphase with
        ⟨L0', L1', work', markers', hflush,
          hcover', hshape', hfilter', hstack'⟩
      refine ⟨L0', L1', work', markers', ?_, hcover', hshape',
        hfilter', hstack'⟩
      simpa [writeOutputPrefix, writeOutputBitsFinal] using
        hconsume'.trans hflush
  | cons next rest =>
      rcases leads_pending_from_stream
          (attempt := attempt) (hattempt := hattempt)
          wp next rest L0p L1p workTail markerTail T2
          hcoverTail hshapeTail hfilterTail hstackp hphase with
        ⟨L0', L1', work', markers', hflush,
          hcover', hshape', hfilter', hstack'⟩
      refine ⟨L0', L1', work', markers', ?_, hcover', hshape',
        hfilter', hstack'⟩
      simpa [writeOutputPrefix, writeOutputBits] using
        hconsume'.trans hflush

theorem leads_length_tick {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter :
      work.filterMap id = false :: false :: true :: false :: bits)
    (hstack : MarkerStack count L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .length0)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .length0)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputBits [false, false, true, false] T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack (count + 1) L1' := by
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length0 .length0 false (false :: true :: false :: bits)
      L0 L1 work markers T2 hcover hshape (by simpa using hfilter)
      (by simp [next, beginWrite, someStep]) with
    ⟨gap0, work0, markers0, h0, hcover0, hshape0, hfilter0⟩
  let L00 := some false ::
    List.append (List.replicate gap0 none) L0
  let L10 := some false ::
    List.append (List.replicate gap0 (some false)) L1
  have hstack0 : MarkerStack count L10 := by
    exact MarkerStack.false (markerStack_false_replicate gap0 hstack)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length1 .length1 false (true :: false :: bits)
      L00 L10 work0 markers0 ((writeR (some false)).apply T2)
      hcover0 hshape0 hfilter0
      (by simp [next, beginWrite, someStep]) with
    ⟨gap1, work1, markers1, h1, hcover1, hshape1, hfilter1⟩
  let L01 := some false ::
    List.append (List.replicate gap1 none) L00
  let L11 := some false ::
    List.append (List.replicate gap1 (some false)) L10
  have hstack1 : MarkerStack count L11 := by
    exact MarkerStack.false (markerStack_false_replicate gap1 hstack0)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length2 .length2 true (false :: bits)
      L01 L11 work1 markers1
      ((writeR (some false)).apply ((writeR (some false)).apply T2))
      hcover1 hshape1 hfilter1
      (by simp [next, beginWrite, someStep]) with
    ⟨gap2, work2, markers2, h2, hcover2, hshape2, hfilter2⟩
  let L02 := some true ::
    List.append (List.replicate gap2 none) L01
  let L12 := some false ::
    List.append (List.replicate gap2 (some false)) L11
  have hstack2 : MarkerStack count L12 := by
    exact MarkerStack.false (markerStack_false_replicate gap2 hstack1)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length3 .lengthTick false bits
      L02 L12 work2 markers2
      ((writeR (some true)).apply
        ((writeR (some false)).apply ((writeR (some false)).apply T2)))
      hcover2 hshape2 hfilter2
      (by simp [next, beginWrite, someStep]) with
    ⟨gap3, work3, markers3, h3, hcover3, hshape3, hfilter3⟩
  let L03 := some false ::
    List.append (List.replicate gap3 none) L02
  let L13 := some true ::
    List.append (List.replicate gap3 (some false)) L12
  have hstack3 : MarkerStack (count + 1) L13 := by
    exact MarkerStack.true (markerStack_false_replicate gap3 hstack2)
  refine ⟨L03, L13, work3, markers3, ?_, hcover3, hshape3,
    hfilter3, hstack3⟩
  simpa [L00, L10, L01, L11, L02, L12, L03, L13,
    writePhaseTarget, writePhaseBit, writePhaseMarker, writeOutputBits] using
    h0.trans (h1.trans (h2.trans h3))

theorem leads_length_done {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = false :: false :: true :: true :: bits)
    (hstack : MarkerStack count L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .length0)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix [false, false, true, true] bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack count L1' := by
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length0 .length0 false (false :: true :: true :: bits)
      L0 L1 work markers T2 hcover hshape (by simpa using hfilter)
      (by simp [next, beginWrite, someStep]) with
    ⟨gap0, work0, markers0, h0, hcover0, hshape0, hfilter0⟩
  let L00 := some false ::
    List.append (List.replicate gap0 none) L0
  let L10 := some false ::
    List.append (List.replicate gap0 (some false)) L1
  have hstack0 : MarkerStack count L10 := by
    exact MarkerStack.false (markerStack_false_replicate gap0 hstack)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length1 .length1 false (true :: true :: bits)
      L00 L10 work0 markers0 ((writeR (some false)).apply T2)
      hcover0 hshape0 hfilter0
      (by simp [next, beginWrite, someStep]) with
    ⟨gap1, work1, markers1, h1, hcover1, hshape1, hfilter1⟩
  let L01 := some false ::
    List.append (List.replicate gap1 none) L00
  let L11 := some false ::
    List.append (List.replicate gap1 (some false)) L10
  have hstack1 : MarkerStack count L11 := by
    exact MarkerStack.false (markerStack_false_replicate gap1 hstack0)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length2 .length2 true (true :: bits)
      L01 L11 work1 markers1
      ((writeR (some false)).apply ((writeR (some false)).apply T2))
      hcover1 hshape1 hfilter1
      (by simp [next, beginWrite, someStep]) with
    ⟨gap2, work2, markers2, h2, hcover2, hshape2, hfilter2⟩
  let L02 := some true ::
    List.append (List.replicate gap2 none) L01
  let L12 := some false ::
    List.append (List.replicate gap2 (some false)) L11
  have hstack2 : MarkerStack count L12 := by
    exact MarkerStack.false (markerStack_false_replicate gap2 hstack1)
  rcases leads_result_terminal_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length3 .lengthDone true bits
      L02 L12 work2 markers2
      ((writeR (some true)).apply
        ((writeR (some false)).apply ((writeR (some false)).apply T2)))
      hcover2 hshape2 hfilter2 hstack2 PendingPhase.lengthDone
      (by simp [next, beginPendingWrite, someStep]) with
    ⟨L03, L13, work3, markers3, h3, hcover3, hshape3,
      hfilter3, hstack3⟩
  refine ⟨L03, L13, work3, markers3, ?_, hcover3, hshape3,
    hfilter3, hstack3⟩
  have hwrite :
      writeOutputPrefix [false, false, true, true] bits T2 =
        writeOutputPrefix [true] bits
          ((writeR (some true)).apply
            ((writeR (some false)).apply ((writeR (some false)).apply T2))) := by
    simpa [writeOutputPrefix, writeOutputBits] using
      (writeOutputPrefix_append [false, false, true] [true] bits T2)
  rw [hwrite]
  simpa [L00, L10, L01, L11, L02, L12,
    writePhaseTarget, writePhaseBit, writePhaseMarker, writeOutputBits] using
    h0.trans (h1.trans (h2.trans h3))

theorem leads_length {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count n : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = List.append (stageNatBits n) bits)
    (hstack : MarkerStack count L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .length0)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix (stageNatBits n) bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack (count + n) L1' := by
  induction n generalizing count bits L0 L1 work markers T2 with
  | zero =>
      simpa [stageNatBits_zero] using
        (leads_length_done (attempt := attempt) (hattempt := hattempt)
          count bits L0 L1 work markers T2 hcover hshape
          (by simpa [stageNatBits_zero] using hfilter) hstack)
  | succ n ih =>
      have hfilterTick :
          work.filterMap id =
            false :: false :: true :: false ::
              List.append (stageNatBits n) bits := by
        simpa [stageNatBits_succ'] using hfilter
      rcases leads_length_tick
          (attempt := attempt) (hattempt := hattempt)
          count (List.append (stageNatBits n) bits)
          L0 L1 work markers T2 hcover hshape hfilterTick hstack with
        ⟨L0a, L1a, worka, markersa,
          htick, hcovera, hshapea, hfiltera, hstacka⟩
      rcases ih (count + 1) bits L0a L1a worka markersa
          (writeOutputBits [false, false, true, false] T2)
          hcovera hshapea hfiltera hstacka with
        ⟨L0b, L1b, workb, markersb,
          htail, hcoverb, hshapeb, hfilterb, hstackb⟩
      have hcount : (count + 1) + n = count + Nat.succ n := by lia
      rw [hcount] at hstackb
      refine ⟨L0b, L1b, workb, markersb, ?_, hcoverb, hshapeb,
        hfilterb, hstackb⟩
      have hremaining :
          List.append (stageNatBits n) bits ≠ [] :=
        stageNatBits_append_ne_nil n bits
      have htoken :
          writeOutputPrefix [false, false, true, false]
              (List.append (stageNatBits n) bits) T2 =
            writeOutputBits [false, false, true, false] T2 := by
        unfold writeOutputPrefix
        split
        · next heq => exact False.elim (hremaining heq)
        · rfl
      have hwrite :
          writeOutputPrefix (stageNatBits (Nat.succ n)) bits T2 =
            writeOutputPrefix (stageNatBits n) bits
              (writeOutputBits [false, false, true, false] T2) := by
        calc
          _ = writeOutputPrefix
                (List.append ([false, false, true, false] : Word Bool)
                  (stageNatBits n)) bits T2 := by
              rw [stageNatBits_succ' n]
              rfl
          _ = writeOutputPrefix (stageNatBits n) bits
                (writeOutputPrefix [false, false, true, false]
                  (List.append (stageNatBits n) bits) T2) :=
              writeOutputPrefix_append _ _ _ _
          _ = _ := by rw [htoken]
      rw [hwrite]
      exact htick.trans htail

theorem leads_length_tick_tail {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = false :: true :: false :: bits)
    (hstack : MarkerStack count L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .length1)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .length0)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputBits [false, true, false] T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack (count + 1) L1' := by
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length1 .length1 false (true :: false :: bits)
      L0 L1 work markers T2 hcover hshape hfilter
      (by simp [next, beginWrite, someStep]) with
    ⟨gap1, work1, markers1, h1, hcover1, hshape1, hfilter1⟩
  let L01 := some false ::
    List.append (List.replicate gap1 none) L0
  let L11 := some false ::
    List.append (List.replicate gap1 (some false)) L1
  have hstack1 : MarkerStack count L11 := by
    exact MarkerStack.false (markerStack_false_replicate gap1 hstack)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length2 .length2 true (false :: bits)
      L01 L11 work1 markers1 ((writeR (some false)).apply T2)
      hcover1 hshape1 hfilter1
      (by simp [next, beginWrite, someStep]) with
    ⟨gap2, work2, markers2, h2, hcover2, hshape2, hfilter2⟩
  let L02 := some true ::
    List.append (List.replicate gap2 none) L01
  let L12 := some false ::
    List.append (List.replicate gap2 (some false)) L11
  have hstack2 : MarkerStack count L12 := by
    exact MarkerStack.false (markerStack_false_replicate gap2 hstack1)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length3 .lengthTick false bits
      L02 L12 work2 markers2
      ((writeR (some true)).apply ((writeR (some false)).apply T2))
      hcover2 hshape2 hfilter2
      (by simp [next, beginWrite, someStep]) with
    ⟨gap3, work3, markers3, h3, hcover3, hshape3, hfilter3⟩
  let L03 := some false ::
    List.append (List.replicate gap3 none) L02
  let L13 := some true ::
    List.append (List.replicate gap3 (some false)) L12
  have hstack3 : MarkerStack (count + 1) L13 := by
    exact MarkerStack.true (markerStack_false_replicate gap3 hstack2)
  refine ⟨L03, L13, work3, markers3, ?_, hcover3, hshape3,
    hfilter3, hstack3⟩
  simpa [L01, L11, L02, L12, L03, L13,
    writePhaseTarget, writePhaseBit, writePhaseMarker, writeOutputBits] using
    h1.trans (h2.trans h3)

theorem leads_length_done_tail {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = false :: true :: true :: bits)
    (hstack : MarkerStack count L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .length1)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix [false, true, true] bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack count L1' := by
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length1 .length1 false (true :: true :: bits)
      L0 L1 work markers T2 hcover hshape hfilter
      (by simp [next, beginWrite, someStep]) with
    ⟨gap1, work1, markers1, h1, hcover1, hshape1, hfilter1⟩
  let L01 := some false ::
    List.append (List.replicate gap1 none) L0
  let L11 := some false ::
    List.append (List.replicate gap1 (some false)) L1
  have hstack1 : MarkerStack count L11 := by
    exact MarkerStack.false (markerStack_false_replicate gap1 hstack)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length2 .length2 true (true :: bits)
      L01 L11 work1 markers1 ((writeR (some false)).apply T2)
      hcover1 hshape1 hfilter1
      (by simp [next, beginWrite, someStep]) with
    ⟨gap2, work2, markers2, h2, hcover2, hshape2, hfilter2⟩
  let L02 := some true ::
    List.append (List.replicate gap2 none) L01
  let L12 := some false ::
    List.append (List.replicate gap2 (some false)) L11
  have hstack2 : MarkerStack count L12 := by
    exact MarkerStack.false (markerStack_false_replicate gap2 hstack1)
  rcases leads_result_terminal_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .length3 .lengthDone true bits
      L02 L12 work2 markers2
      ((writeR (some true)).apply ((writeR (some false)).apply T2))
      hcover2 hshape2 hfilter2 hstack2 PendingPhase.lengthDone
      (by simp [next, beginPendingWrite, someStep]) with
    ⟨L03, L13, work3, markers3, h3, hcover3, hshape3,
      hfilter3, hstack3⟩
  refine ⟨L03, L13, work3, markers3, ?_, hcover3, hshape3,
    hfilter3, hstack3⟩
  have hwrite :
      writeOutputPrefix [false, true, true] bits T2 =
        writeOutputPrefix [true] bits
          ((writeR (some true)).apply ((writeR (some false)).apply T2)) := by
    simpa [writeOutputPrefix, writeOutputBits] using
      (writeOutputPrefix_append [false, true] [true] bits T2)
  rw [hwrite]
  simpa [L01, L11, L02, L12,
    writePhaseTarget, writePhaseBit, writePhaseMarker, writeOutputBits] using
    h1.trans (h2.trans h3)

theorem leads_resultFirst_length {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count n : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = List.append (stageNatBits n) bits)
    (hstack : MarkerStack count L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt .resultFirst
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix (stageNatBits n) bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack (count + n) L1' := by
  cases n with
  | zero =>
      have hfilterFirst :
          work.filterMap id = false :: false :: true :: true :: bits := by
        simpa [stageNatBits_zero] using hfilter
      rcases leads_resultFirst_from_stream
          (attempt := attempt) (hattempt := hattempt)
          (false :: true :: true :: bits) L0 L1 work markers T2
          hcover hshape hfilterFirst with
        ⟨gap0, work0, markers0, h0, hcover0, hshape0, hfilter0⟩
      let L00 := some false ::
        List.append (List.replicate gap0 none) L0
      let L10 := some false ::
        List.append (List.replicate gap0 (some false)) L1
      have hstack0 : MarkerStack count L10 := by
        exact MarkerStack.false (markerStack_false_replicate gap0 hstack)
      rcases leads_length_done_tail
          (attempt := attempt) (hattempt := hattempt)
          count bits L00 L10 work0 markers0
          ((writeR (some false)).apply T2)
          hcover0 hshape0 hfilter0 hstack0 with
        ⟨L0a, L1a, worka, markersa,
          htail, hcovera, hshapea, hfiltera, hstacka⟩
      refine ⟨L0a, L1a, worka, markersa, ?_, hcovera, hshapea,
        hfiltera, ?_⟩
      · have hwrite :
            writeOutputPrefix (stageNatBits 0) bits T2 =
              writeOutputPrefix [false, true, true] bits
                ((writeR (some false)).apply T2) := by
            calc
              _ = writeOutputPrefix
                    (List.append ([false] : Word Bool)
                      [false, true, true]) bits T2 := by
                  rw [stageNatBits_zero]
                  rfl
              _ = writeOutputPrefix [false, true, true] bits
                    (writeOutputPrefix [false]
                      (List.append [false, true, true] bits) T2) :=
                  writeOutputPrefix_append _ _ _ _
              _ = _ := by
                  simp [writeOutputPrefix, writeOutputBits]
        rw [hwrite]
        simpa [L00, L10] using h0.trans htail
      · simpa using hstacka
  | succ n =>
      have hfilterFirst :
          work.filterMap id =
            false :: false :: true :: false ::
              List.append (stageNatBits n) bits := by
        simpa [stageNatBits_succ'] using hfilter
      rcases leads_resultFirst_from_stream
          (attempt := attempt) (hattempt := hattempt)
          (false :: true :: false :: List.append (stageNatBits n) bits)
          L0 L1 work markers T2 hcover hshape hfilterFirst with
        ⟨gap0, work0, markers0, h0, hcover0, hshape0, hfilter0⟩
      let L00 := some false ::
        List.append (List.replicate gap0 none) L0
      let L10 := some false ::
        List.append (List.replicate gap0 (some false)) L1
      have hstack0 : MarkerStack count L10 := by
        exact MarkerStack.false (markerStack_false_replicate gap0 hstack)
      rcases leads_length_tick_tail
          (attempt := attempt) (hattempt := hattempt)
          count (List.append (stageNatBits n) bits)
          L00 L10 work0 markers0 ((writeR (some false)).apply T2)
          hcover0 hshape0 hfilter0 hstack0 with
        ⟨L0a, L1a, worka, markersa,
          htick, hcovera, hshapea, hfiltera, hstacka⟩
      rcases leads_length
          (attempt := attempt) (hattempt := hattempt)
          (count + 1) n bits L0a L1a worka markersa
          (writeOutputBits [false, true, false]
            ((writeR (some false)).apply T2))
          hcovera hshapea hfiltera hstacka with
        ⟨L0b, L1b, workb, markersb,
          htail, hcoverb, hshapeb, hfilterb, hstackb⟩
      have hcount : (count + 1) + n = count + Nat.succ n := by lia
      rw [hcount] at hstackb
      refine ⟨L0b, L1b, workb, markersb, ?_, hcoverb, hshapeb,
        hfilterb, hstackb⟩
      have hremaining :
          List.append (stageNatBits n) bits ≠ [] :=
        stageNatBits_append_ne_nil n bits
      have htoken :
          writeOutputPrefix [false, false, true, false]
              (List.append (stageNatBits n) bits) T2 =
            writeOutputBits [false, true, false]
              ((writeR (some false)).apply T2) := by
        unfold writeOutputPrefix
        split
        · next heq => exact False.elim (hremaining heq)
        · rfl
      have hwrite :
          writeOutputPrefix (stageNatBits (Nat.succ n)) bits T2 =
            writeOutputPrefix (stageNatBits n) bits
              (writeOutputBits [false, true, false]
                ((writeR (some false)).apply T2)) := by
        calc
          _ = writeOutputPrefix
                (List.append ([false, false, true, false] : Word Bool)
                  (stageNatBits n)) bits T2 := by
              rw [stageNatBits_succ' n]
              rfl
          _ = writeOutputPrefix (stageNatBits n) bits
                (writeOutputPrefix [false, false, true, false]
                  (List.append (stageNatBits n) bits) T2) :=
              writeOutputPrefix_append _ _ _ _
          _ = _ := by rw [htoken]
      rw [hwrite]
      exact h0.trans (htick.trans htail)

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
