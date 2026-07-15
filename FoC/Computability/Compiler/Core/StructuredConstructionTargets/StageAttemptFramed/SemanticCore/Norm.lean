import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Relation

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

theorem leads_run_halt_normalize
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (work marker T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt (.run attempt.halt) work marker T2)
      (cfg attempt hattempt .normalizeLeft
        (keepL.apply work) ((writeL (some false)).apply marker) T2) := by
  have hs : StateBounded attempt (.run attempt.halt) := by
    simpa [StateBounded] using hattempt.left.right.right.left
  have hnext :
      next attempt (.run attempt.halt) work.read marker.read T2.read =
        some ⟨.normalizeLeft, keepL, writeL (some false), keepS⟩ := by
    simp [next, someStep]
  have hlead := leads_step (attempt := attempt) (hattempt := hattempt)
    (T0 := work) (T1 := marker) (T2 := T2) hs hnext
  have hkeep : keepS.apply T2 = T2 := by rfl
  rw [hkeep] at hlead
  exact hlead

theorem leads_normalize_false
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (work marker T2 : Tape Bool) (hread : Tape.read marker = some false) :
    Leads attempt hattempt
      (cfg attempt hattempt .normalizeLeft work marker T2)
      (cfg attempt hattempt .normalizeLeft
        (keepL.apply work) (keepL.apply marker) T2) := by
  have hnext :
      next attempt .normalizeLeft work.read marker.read T2.read =
        some ⟨.normalizeLeft, keepL, keepL, keepS⟩ := by
    simp [next, hread, someStep]
  have hlead := leads_step (attempt := attempt) (hattempt := hattempt)
    (T0 := work) (T1 := marker) (T2 := T2) (by trivial) hnext
  have hkeep : keepS.apply T2 = T2 := by rfl
  rw [hkeep] at hlead
  exact hlead

theorem leads_normalize_boundary
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (work marker T2 : Tape Bool) (hread : Tape.read marker = none) :
    Leads attempt hattempt
      (cfg attempt hattempt .normalizeLeft work marker T2)
      (cfg attempt hattempt .resultFirst
        (keepR.apply work) (keepR.apply marker) T2) := by
  have hnext :
      next attempt .normalizeLeft work.read marker.read T2.read =
        some ⟨.resultFirst, keepR, keepR, keepS⟩ := by
    simp [next, hread, someStep]
  have hlead := leads_step (attempt := attempt) (hattempt := hattempt)
    (T0 := work) (T1 := marker) (T2 := T2) (by trivial) hnext
  have hkeep : keepS.apply T2 = T2 := by rfl
  rw [hkeep] at hlead
  exact hlead

theorem write_head_eq (T : Tape Bool) :
    Tape.write T.head T = T := by
  cases T
  rfl

theorem exactCovers_length {work marker : List (Option Bool)}
    (h : ExactCovers work marker) : work.length = marker.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem keepL_apply_of_left_nil (T : Tape Bool) (h : T.left = []) :
    keepL.apply T = { left := [], head := none, right := T.head :: T.right } := by
  rcases T with ⟨left, head, right⟩
  simp only at h
  subst left
  rfl

theorem keepL_apply_of_left_cons (T : Tape Bool)
    (cell : Option Bool) (rest : List (Option Bool))
    (h : T.left = cell :: rest) :
    keepL.apply T =
      { left := rest, head := cell, right := T.head :: T.right } := by
  rcases T with ⟨left, head, right⟩
  simp only at h
  subst left
  rfl

theorem writeL_apply_of_left_nil (T : Tape Bool) (cell : Option Bool)
    (h : T.left = []) :
    (writeL cell).apply T =
      { left := [], head := none, right := cell :: T.right } := by
  rcases T with ⟨left, head, right⟩
  simp only at h
  subst left
  rfl

theorem writeL_apply_of_left_cons (T : Tape Bool) (write cell : Option Bool)
    (rest : List (Option Bool)) (h : T.left = cell :: rest) :
    (writeL write).apply T =
      { left := rest, head := cell, right := write :: T.right } := by
  rcases T with ⟨left, head, right⟩
  simp only at h
  subst left
  rfl

theorem covered_move_left_false
    (work marker : Tape Bool) (h : CoveredTapes work marker)
    (hmarker : marker.head = some false) :
    CoveredTapes (keepL.apply work) (keepL.apply marker) := by
  have hmove := covered_write_move_left work marker work.head h
  have hwrite : Tape.write (some false) marker = marker := by
    rcases marker with ⟨left, head, right⟩
    simp only at hmarker
    subst head
    rfl
  rw [write_head_eq, hwrite] at hmove
  simpa [keepL_eq, TapeAction.apply, HeadMove.apply] using hmove

theorem normalize_boundary_shape
    (work marker : Tape Bool)
    (h : CoveredTapes work marker)
    (hworkLeft : work.left = [])
    (hmarkerLeft : marker.left = [])
    (hmarkerHead : marker.head = none)
    {markerRest : List (Option Bool)}
    (hmarkerRight : marker.right = some false :: markerRest) :
    ∃ workHead workRest,
      keepR.apply work = tapeAtCells [none] (workHead :: workRest) ∧
      keepR.apply marker =
        tapeAtCells [none] (some false :: markerRest) ∧
      RightCovers (workHead :: workRest) (some false :: markerRest) := by
  rcases work with ⟨workLeft', workHead', workRight'⟩
  rcases marker with ⟨markerLeft', markerHead', markerRight'⟩
  simp only at hworkLeft hmarkerLeft hmarkerHead hmarkerRight
  subst workLeft'
  subst markerLeft'
  subst markerHead'
  subst markerRight'
  rcases h with ⟨hleft, hhead, hright, _hmleft, _hmhead, _hmright⟩
  cases hright with
  | @cons workCell markerCell works markers hcell htail =>
      refine ⟨workCell, works, ?_, ?_, RightCovers.cons hcell htail⟩
      · rcases hhead with hfalse | ⟨hworkHead, _⟩
        · cases hfalse
        · have hworkHead' : workHead' = none := by simpa using hworkHead
          subst workHead'
          rfl
      · rfl

theorem markerSide_none_head_tail_nil
    {rest : List (Option Bool)}
    (h : MarkerSide (none :: rest)) : rest = [] := by
  cases h
  rfl

theorem normalizedOutput_keepL (T : Tape Bool) :
    Tape.normalizedOutput (keepL.apply T) = Tape.normalizedOutput T := by
  simpa [keepL_eq, TapeAction.apply, HeadMove.apply] using
    Tape.normalizedOutput_move Direction.left T

theorem normalizedOutput_keepR (T : Tape Bool) :
    Tape.normalizedOutput (keepR.apply T) = Tape.normalizedOutput T := by
  simpa [keepR_eq, TapeAction.apply, HeadMove.apply] using
    Tape.normalizedOutput_move Direction.right T

theorem normalize_left_core
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (n : Nat) (work marker T2 : Tape Bool)
    (hcovered : CoveredTapes work marker)
    (hlen : marker.left.length = n)
    (hboundary : marker.head = none → marker.left = [])
    (hright : ∃ rest, marker.right = some false :: rest) :
    ∃ workStream markerRest,
      Leads attempt hattempt
        (cfg attempt hattempt .normalizeLeft work marker T2)
        (cfg attempt hattempt .resultFirst
          (tapeAtCells [none] workStream)
          (tapeAtCells [none] (some false :: markerRest)) T2) ∧
      RightCovers workStream (some false :: markerRest) ∧
      MarkerSide (some false :: markerRest) ∧
      Tape.normalizedOutput (tapeAtCells [none] workStream) =
        Tape.normalizedOutput work := by
  induction n generalizing work marker with
  | zero =>
      have hmarkerLeft : marker.left = [] :=
        List.eq_nil_of_length_eq_zero hlen
      have hworkLeft : work.left = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [exactCovers_length hcovered.left, hmarkerLeft]
        rfl
      rcases hright with ⟨markerRest, hmarkerRight⟩
      rcases hcovered.markerHead with hhead | hhead
      · rcases normalize_boundary_shape work marker hcovered hworkLeft
            hmarkerLeft hhead hmarkerRight with
          ⟨workHead, workRest, hworkMove, hmarkerMove, hrightFinal⟩
        refine ⟨workHead :: workRest, markerRest, ?_, hrightFinal, ?_, ?_⟩
        have hlead := leads_normalize_boundary
          (attempt := attempt) (hattempt := hattempt) work marker T2 hhead
        rw [hworkMove, hmarkerMove] at hlead
        exact hlead
        simpa [hmarkerRight] using hcovered.markerRight
        rw [← hworkMove]
        exact normalizedOutput_keepR work
      · have hcoveredMove := covered_move_left_false work marker hcovered hhead
        have hworkMoveLeft : (keepL.apply work).left = [] := by
          rw [keepL_apply_of_left_nil work hworkLeft]
        have hmarkerMoveLeft : (keepL.apply marker).left = [] := by
          rw [keepL_apply_of_left_nil marker hmarkerLeft]
        have hmarkerMoveHead : (keepL.apply marker).head = none := by
          rw [keepL_apply_of_left_nil marker hmarkerLeft]
        have hmarkerMoveRight :
            (keepL.apply marker).right = some false :: marker.right := by
          rw [keepL_apply_of_left_nil marker hmarkerLeft, hhead]
        rcases normalize_boundary_shape
            (keepL.apply work) (keepL.apply marker) hcoveredMove
            hworkMoveLeft hmarkerMoveLeft hmarkerMoveHead
            hmarkerMoveRight with
          ⟨workHead, workRest, hworkRight, hmarkerRight', hrightFinal⟩
        refine ⟨workHead :: workRest, marker.right, ?_, hrightFinal,
          MarkerSide.marked hcovered.markerRight, ?_⟩
        refine (leads_normalize_false
          (attempt := attempt) (hattempt := hattempt) work marker T2 hhead).trans ?_
        have hboundLead := leads_normalize_boundary
          (attempt := attempt) (hattempt := hattempt)
          (keepL.apply work) (keepL.apply marker) T2 hmarkerMoveHead
        rw [hworkRight, hmarkerRight'] at hboundLead
        exact hboundLead
        rw [← hworkRight]
        exact (normalizedOutput_keepR (keepL.apply work)).trans
          (normalizedOutput_keepL work)
  | succ n ih =>
      have hmarkerLeftNe : marker.left ≠ [] := by
        intro hnil
        simp [hnil] at hlen
      rcases List.exists_cons_of_ne_nil hmarkerLeftNe with
        ⟨markerCell, markerTail, hmarkerLeft⟩
      have hworkLeftNe : work.left ≠ [] := by
        intro hnil
        have hlength := exactCovers_length hcovered.left
        rw [hnil, hmarkerLeft] at hlength
        simp at hlength
      rcases List.exists_cons_of_ne_nil hworkLeftNe with
        ⟨workCell, workTail, hworkLeft⟩
      have hhead : marker.head = some false := by
        rcases hcovered.markerHead with hnone | hfalse
        · exact False.elim (hmarkerLeftNe (hboundary hnone))
        · exact hfalse
      have hlead := leads_normalize_false
        (attempt := attempt) (hattempt := hattempt) work marker T2 hhead
      have hcoveredMove := covered_move_left_false work marker hcovered hhead
      have htailLen : (keepL.apply marker).left.length = n := by
        rw [keepL_apply_of_left_cons marker markerCell markerTail hmarkerLeft]
        have hlen' := hlen
        rw [hmarkerLeft] at hlen'
        simpa using hlen'
      have hmoveRight :
          ∃ rest, (keepL.apply marker).right = some false :: rest := by
        refine ⟨marker.right, ?_⟩
        rw [keepL_apply_of_left_cons marker markerCell markerTail hmarkerLeft,
          hhead]
      have hmoveBoundary :
          (keepL.apply marker).head = none →
            (keepL.apply marker).left = [] := by
        intro hnone
        have hcell : markerCell = none := by
          rw [keepL_apply_of_left_cons marker markerCell markerTail hmarkerLeft]
            at hnone
          exact hnone
        subst markerCell
        have hmleft := hcovered.markerLeft
        rw [hmarkerLeft] at hmleft
        have htail := markerSide_none_head_tail_nil hmleft
        rw [keepL_apply_of_left_cons marker none markerTail hmarkerLeft, htail]
      rcases ih (keepL.apply work) (keepL.apply marker)
          hcoveredMove htailLen hmoveBoundary hmoveRight with
        ⟨workStream, markerRest, htail, hrightFinal, hmarkerFinal, houtput⟩
      exact ⟨workStream, markerRest, hlead.trans htail, hrightFinal,
        hmarkerFinal, houtput.trans (normalizedOutput_keepL work)⟩

theorem leads_run_halt_to_result_first
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (work marker T2 : Tape Bool) (hcovered : CoveredTapes work marker) :
    ∃ workStream markerRest,
      Leads attempt hattempt
        (cfg attempt hattempt (.run attempt.halt) work marker T2)
        (cfg attempt hattempt .resultFirst
          (tapeAtCells [none] workStream)
          (tapeAtCells [none] (some false :: markerRest)) T2) ∧
      RightCovers workStream (some false :: markerRest) ∧
      MarkerSide (some false :: markerRest) ∧
      Tape.normalizedOutput (tapeAtCells [none] workStream) =
        Tape.normalizedOutput work := by
  let work' := keepL.apply work
  let marker' := (writeL (some false)).apply marker
  have hcovered' : CoveredTapes work' marker' := by
    have hmove := covered_write_move_left work marker work.head hcovered
    simpa [work', marker', keepL, writeL, TapeAction.apply, HeadMove.apply,
      write_head_eq] using hmove
  have hright' : ∃ rest, marker'.right = some false :: rest := by
    refine ⟨marker.right, ?_⟩
    cases hleft : marker.left with
    | nil =>
        simp [marker', writeL_apply_of_left_nil marker (some false) hleft]
    | cons cell rest =>
        simp [marker', writeL_apply_of_left_cons marker (some false)
          cell rest hleft]
  have hboundary' : marker'.head = none → marker'.left = [] := by
    intro hnone
    rcases marker with ⟨left, head, right⟩
    cases left with
    | nil => rfl
    | cons cell rest =>
        have hcell : cell = none := by
          change
            ((writeL (some false)).apply
              { left := cell :: rest, head := head, right := right }).head =
              none at hnone
          rw [writeL_apply_of_left_cons
            { left := cell :: rest, head := head, right := right }
            (some false) cell rest rfl] at hnone
          exact hnone
        subst cell
        have htail := markerSide_none_head_tail_nil hcovered.markerLeft
        change
          ((writeL (some false)).apply
            { left := none :: rest, head := head, right := right }).left = []
        rw [writeL_apply_of_left_cons
          { left := none :: rest, head := head, right := right }
          (some false) none rest rfl, htail]
  rcases normalize_left_core (attempt := attempt) (hattempt := hattempt)
      marker'.left.length work' marker' T2 hcovered' rfl hboundary' hright' with
    ⟨workStream, markerRest, hnormalize, hrightFinal,
      hmarkerFinal, hnormalizeOutput⟩
  refine ⟨workStream, markerRest,
    (leads_run_halt_normalize (attempt := attempt) (hattempt := hattempt)
      work marker T2).trans hnormalize,
    hrightFinal, hmarkerFinal, ?_⟩
  have hmoveLeft : Tape.normalizedOutput work' = Tape.normalizedOutput work := by
    simp [work', keepL, TapeAction.apply, HeadMove.apply,
      Tape.normalizedOutput_move]
  have hrunOutput :
      Tape.normalizedOutput (tapeAtCells [none] workStream) =
        Tape.normalizedOutput work' := by
    exact hnormalizeOutput
  exact hrunOutput.trans hmoveLeft

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
