import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.ValidA

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
theorem leads_seekCell_erase {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (L0 left1 right0 right1 : List (Option Bool))
    (previous : Option Bool) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result .seekCell)
        (tapeAtCells L0 (some false :: right0))
        (tapeAtCells (previous :: left1) (some false :: right1)) T2)
      (cfg attempt hattempt .counterLeft
        (tapeAtCells L0 (some false :: right0))
        (tapeAtCells left1 (previous :: none :: right1)) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.result .seekCell)
      (T0 := tapeAtCells L0 (some false :: right0))
      (T1 := tapeAtCells (previous :: left1) (some false :: right1))
      (T2 := T2)
      (st := ⟨CoreState.counterLeft, keepS, eraseL, keepS⟩)
      (T0' := tapeAtCells L0 (some false :: right0))
      (T1' := tapeAtCells left1 (previous :: none :: right1))
      (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl) rfl
      (by
        change (writeL none).apply
            (tapeAtCells (previous :: left1) (some false :: right1)) = _
        exact writeL_apply_tapeAtCells none left1 previous
          (some false) right1) rfl

theorem leads_counterLeft_false {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (T0 T2 : Tape Bool) (left1 right1 : List (Option Bool))
    (previous : Option Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .counterLeft T0
        (tapeAtCells (previous :: left1) (some false :: right1)) T2)
      (cfg attempt hattempt .counterLeft T0
        (tapeAtCells left1 (previous :: some false :: right1)) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.counterLeft) (T0 := T0)
      (T1 := tapeAtCells (previous :: left1) (some false :: right1))
      (T2 := T2)
      (st := ⟨CoreState.counterLeft, keepS, keepL, keepS⟩)
      (T0' := T0)
      (T1' := tapeAtCells left1 (previous :: some false :: right1))
      (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl) rfl
      (keepL_apply_tapeAtCells left1 previous (some false) right1) rfl

theorem leads_counterLeft_true {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (T0 T2 : Tape Bool) (left1 right1 : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .counterLeft T0
        (tapeAtCells left1 (some true :: right1)) T2)
      (cfg attempt hattempt .counterRight T0
        (tapeAtCells (some false :: left1) right1) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.counterLeft) (T0 := T0)
      (T1 := tapeAtCells left1 (some true :: right1)) (T2 := T2)
      (st := ⟨CoreState.counterRight, keepS,
        writeR (some false), keepS⟩)
      (T0' := T0) (T1' := tapeAtCells (some false :: left1) right1)
      (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl) rfl
      (writeR_apply_tapeAtCells (some false) left1 (some true) right1) rfl

theorem leads_counterRight_false {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (T0 T2 : Tape Bool) (left1 right1 : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .counterRight T0
        (tapeAtCells left1 (some false :: right1)) T2)
      (cfg attempt hattempt .counterRight T0
        (tapeAtCells (some false :: left1) right1) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.counterRight) (T0 := T0)
      (T1 := tapeAtCells left1 (some false :: right1)) (T2 := T2)
      (st := ⟨CoreState.counterRight, keepS, keepR, keepS⟩)
      (T0' := T0) (T1' := tapeAtCells (some false :: left1) right1)
      (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl) rfl
      (keepR_apply_tapeAtCells left1 (some false) right1) rfl

theorem leads_counterRight_boundary {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (L0 L1 right0 right1 : List (Option Bool)) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .counterRight
        (tapeAtCells L0 (some false :: right0))
        (tapeAtCells L1 (none :: right1)) T2)
      (cfg attempt hattempt (.result .cell1)
        (tapeAtCells (some false :: L0) right0)
        (tapeAtCells (some false :: L1) right1)
        ((writeR (some false)).apply T2)) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.counterRight)
      (T0 := tapeAtCells L0 (some false :: right0))
      (T1 := tapeAtCells L1 (none :: right1)) (T2 := T2)
      (st := ⟨CoreState.result .cell1, keepR,
        writeR (some false), writeR (some false)⟩)
      (T0' := tapeAtCells (some false :: L0) right0)
      (T1' := tapeAtCells (some false :: L1) right1)
      (T2' := (writeR (some false)).apply T2)
      (mem_states_of_stateBounded trivial) (by rfl)
      (keepR_apply_tapeAtCells L0 (some false) right0)
      (writeR_apply_tapeAtCells (some false) L1 none right1) rfl

theorem leads_counterLeft_falses {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (gap : Nat) (T0 T2 : Tape Bool)
    (tail right : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .counterLeft T0
        (tapeAtCells
          (List.append (List.replicate gap (some false))
            (some true :: tail))
          (some false :: right)) T2)
      (cfg attempt hattempt .counterLeft T0
        (tapeAtCells tail
          (some true :: List.append
            (List.replicate (gap + 1) (some false)) right)) T2) := by
  induction gap generalizing right with
  | zero =>
      simpa using
        (leads_counterLeft_false (attempt := attempt) (hattempt := hattempt)
          T0 T2 tail right (some true))
  | succ gap ih =>
      simp only [List.replicate_succ]
      refine (leads_counterLeft_false
        (attempt := attempt) (hattempt := hattempt)
        T0 T2
        (List.append (List.replicate gap (some false))
          (some true :: tail)) right (some false)).trans ?_
      have htail := ih (some false :: right)
      have hmove :
          List.append (List.replicate gap (some false))
              (some false :: right) =
            some false ::
              List.append (List.replicate gap (some false)) right :=
        list_replicate_append_cons_eq_cons_append (some false) gap right
      have hsucc :
          List.replicate (gap + 1) (some false) =
            some false :: List.replicate gap (some false) := by
        simpa [Nat.add_comm] using
          (List.replicate_succ (n := gap) (a := some false))
      have hright :
          List.append (List.replicate (gap + 1) (some false))
              (some false :: right) =
            List.append
              (some false :: some false ::
                List.replicate gap (some false)) right := by
        rw [hsucc]
        change some false ::
            List.append (List.replicate gap (some false))
              (some false :: right) = _
        rw [hmove]
        rfl
      rw [hright] at htail
      exact htail

theorem leads_counterRight_falses {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (gap : Nat) (T0 T2 : Tape Bool)
    (left right : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .counterRight T0
        (tapeAtCells left
          (List.append (List.replicate gap (some false))
            (none :: right))) T2)
      (cfg attempt hattempt .counterRight T0
        (tapeAtCells
          (List.append (List.replicate gap (some false)) left)
          (none :: right)) T2) := by
  induction gap generalizing left with
  | zero => exact Leads.refl _ _ _
  | succ gap ih =>
      simp only [List.replicate_succ]
      refine (leads_counterRight_false
        (attempt := attempt) (hattempt := hattempt)
        T0 T2 left
        (List.append (List.replicate gap (some false)) (none :: right))).trans ?_
      have htail := ih (some false :: left)
      have hleft :
          List.append (List.replicate gap (some false))
              (some false :: left) =
            some false ::
              List.append (List.replicate gap (some false)) left :=
        list_replicate_append_cons_eq_cons_append (some false) gap left
      rw [hleft] at htail
      exact htail

theorem leads_seekCell_to_counter_true {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (gap : Nat) (L0 tail right0 right1 : List (Option Bool))
    (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result .seekCell)
        (tapeAtCells L0 (some false :: right0))
        (tapeAtCells
          (List.append (List.replicate gap (some false))
            (some true :: tail))
          (some false :: right1)) T2)
      (cfg attempt hattempt .counterLeft
        (tapeAtCells L0 (some false :: right0))
        (tapeAtCells tail
          (some true :: List.append (List.replicate gap (some false))
            (none :: right1))) T2) := by
  cases gap with
  | zero =>
      simpa using
        (leads_seekCell_erase (attempt := attempt) (hattempt := hattempt)
          L0 tail right0 right1 (some true) T2)
  | succ gap =>
      simp only [List.replicate_succ]
      refine (leads_seekCell_erase
        (attempt := attempt) (hattempt := hattempt)
        L0
        (List.append (List.replicate gap (some false))
          (some true :: tail))
        right0 right1 (some false) T2).trans ?_
      simpa [List.replicate_succ] using
        (leads_counterLeft_falses
          (attempt := attempt) (hattempt := hattempt)
          gap (tapeAtCells L0 (some false :: right0)) T2
          tail (none :: right1))

theorem leads_seekCell_decrement {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (L0 L1 right0 right1 : List (Option Bool))
    (T2 : Tape Bool) (hstack : MarkerStack (count + 1) L1) :
    ∃ L1' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0 (some false :: right0))
          (tapeAtCells L1 (some false :: right1)) T2)
        (cfg attempt hattempt (.result .cell1)
          (tapeAtCells (some false :: L0) right0)
          (tapeAtCells L1' right1)
          ((writeR (some false)).apply T2)) ∧
      MarkerStack count L1' := by
  rcases markerStack_succ_decomp hstack with
    ⟨gap, tail, hL1, htailStack⟩
  subst L1
  let crossed := List.append (List.replicate gap (some false))
    (none :: right1)
  have hseek := leads_seekCell_to_counter_true
    (attempt := attempt) (hattempt := hattempt)
    gap L0 tail right0 right1 T2
  have htrue := leads_counterLeft_true
    (attempt := attempt) (hattempt := hattempt)
    (tapeAtCells L0 (some false :: right0)) T2 tail crossed
  have hreturn := leads_counterRight_falses
    (attempt := attempt) (hattempt := hattempt)
    gap (tapeAtCells L0 (some false :: right0)) T2
    (some false :: tail) right1
  let L1' := some false ::
    List.append (List.replicate gap (some false)) (some false :: tail)
  have hboundary := leads_counterRight_boundary
    (attempt := attempt) (hattempt := hattempt)
    L0
    (List.append (List.replicate gap (some false))
      (some false :: tail))
    right0 right1 T2
  refine ⟨L1', ?_, ?_⟩
  · exact hseek.trans (htrue.trans (hreturn.trans hboundary))
  · exact MarkerStack.false
      (markerStack_false_replicate gap (MarkerStack.false htailStack))

theorem leads_seekCell_from_stream {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = false :: bits)
    (hstack : MarkerStack (count + 1) L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .cell1)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          ((writeR (some false)).apply T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack count L1' := by
  rcases stream_next_decomp false bits work markers
      hcover hshape hfilter with
    ⟨gap, workTail, markerTail, hwork, hmarkers,
      hcoverTail, hshapeTail, hfilterTail⟩
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
  have hstacka : MarkerStack (count + 1) L1a := by
    exact markerStack_false_replicate gap hstack
  rcases leads_seekCell_decrement
      (attempt := attempt) (hattempt := hattempt)
      count L0a L1a workTail markerTail T2 hstacka with
    ⟨L1b, hdecrement, hstackb⟩
  refine ⟨some false :: L0a, L1b, workTail, markerTail, ?_,
    hcoverTail, hshapeTail, hfilterTail, hstackb⟩
  simpa [L0a, L1a] using hscan.trans hdecrement

theorem leads_cell_false_tail {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = true :: false :: true :: bits)
    (hstack : MarkerStack count L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .cell1)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix [true, false, true] bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack count L1' := by
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .cell1 .cell1 true (false :: true :: bits)
      L0 L1 work markers T2 hcover hshape hfilter
      (by simp [next, beginWrite, someStep]) with
    ⟨gap1, work1, markers1, h1, hcover1, hshape1, hfilter1⟩
  let L01 := some true ::
    List.append (List.replicate gap1 none) L0
  let L11 := some false ::
    List.append (List.replicate gap1 (some false)) L1
  have hstack1 : MarkerStack count L11 := by
    exact MarkerStack.false (markerStack_false_replicate gap1 hstack)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .cell2 .cell2False false (true :: bits)
      L01 L11 work1 markers1 ((writeR (some true)).apply T2)
      hcover1 hshape1 hfilter1
      (by simp [next, beginWrite, someStep]) with
    ⟨gap2, work2, markers2, h2, hcover2, hshape2, hfilter2⟩
  let L02 := some false ::
    List.append (List.replicate gap2 none) L01
  let L12 := some false ::
    List.append (List.replicate gap2 (some false)) L11
  have hstack2 : MarkerStack count L12 := by
    exact MarkerStack.false (markerStack_false_replicate gap2 hstack1)
  rcases leads_result_terminal_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .cell3False .cell3False true bits
      L02 L12 work2 markers2
      ((writeR (some false)).apply ((writeR (some true)).apply T2))
      hcover2 hshape2 hfilter2 hstack2 PendingPhase.cell3False
      (by simp [next, beginPendingWrite, someStep]) with
    ⟨L03, L13, work3, markers3, h3, hcover3, hshape3,
      hfilter3, hstack3⟩
  refine ⟨L03, L13, work3, markers3, ?_, hcover3, hshape3,
    hfilter3, hstack3⟩
  have hwrite :
      writeOutputPrefix [true, false, true] bits T2 =
        writeOutputPrefix [true] bits
          ((writeR (some false)).apply ((writeR (some true)).apply T2)) := by
    simpa [writeOutputPrefix, writeOutputBits] using
      (writeOutputPrefix_append [true, false] [true] bits T2)
  rw [hwrite]
  simpa [L01, L11, L02, L12,
    writePhaseTarget, writePhaseBit, writePhaseMarker, writeOutputBits] using
    h1.trans (h2.trans h3)

theorem leads_cell_true_tail {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = true :: true :: false :: bits)
    (hstack : MarkerStack count L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .cell1)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix [true, true, false] bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack count L1' := by
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .cell1 .cell1 true (true :: false :: bits)
      L0 L1 work markers T2 hcover hshape hfilter
      (by simp [next, beginWrite, someStep]) with
    ⟨gap1, work1, markers1, h1, hcover1, hshape1, hfilter1⟩
  let L01 := some true ::
    List.append (List.replicate gap1 none) L0
  let L11 := some false ::
    List.append (List.replicate gap1 (some false)) L1
  have hstack1 : MarkerStack count L11 := by
    exact MarkerStack.false (markerStack_false_replicate gap1 hstack)
  rcases leads_result_from_stream
      (attempt := attempt) (hattempt := hattempt)
      .cell2 .cell2True true (false :: bits)
      L01 L11 work1 markers1 ((writeR (some true)).apply T2)
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
      .cell3True .cell3True false bits
      L02 L12 work2 markers2
      ((writeR (some true)).apply ((writeR (some true)).apply T2))
      hcover2 hshape2 hfilter2 hstack2 PendingPhase.cell3True
      (by simp [next, beginPendingWrite, someStep]) with
    ⟨L03, L13, work3, markers3, h3, hcover3, hshape3,
      hfilter3, hstack3⟩
  refine ⟨L03, L13, work3, markers3, ?_, hcover3, hshape3,
    hfilter3, hstack3⟩
  have hwrite :
      writeOutputPrefix [true, true, false] bits T2 =
        writeOutputPrefix [false] bits
          ((writeR (some true)).apply ((writeR (some true)).apply T2)) := by
    simpa [writeOutputPrefix, writeOutputBits] using
      (writeOutputPrefix_append [true, true] [false] bits T2)
  rw [hwrite]
  simpa [L01, L11, L02, L12,
    writePhaseTarget, writePhaseBit, writePhaseMarker, writeOutputBits] using
    h1.trans (h2.trans h3)

theorem leads_cell {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (bit : Bool) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = List.append (cellBits bit) bits)
    (hstack : MarkerStack (count + 1) L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix (cellBits bit) bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack count L1' := by
  cases bit with
  | false =>
      have hfilterFirst :
          work.filterMap id = false :: true :: false :: true :: bits := by
        simpa [cellBits, encodeCodeSymbolAsInput] using hfilter
      rcases leads_seekCell_from_stream
          (attempt := attempt) (hattempt := hattempt)
          count (true :: false :: true :: bits)
          L0 L1 work markers T2 hcover hshape hfilterFirst hstack with
        ⟨L0a, L1a, worka, markersa,
          hfirst, hcovera, hshapea, hfiltera, hstacka⟩
      rcases leads_cell_false_tail
          (attempt := attempt) (hattempt := hattempt)
          count bits L0a L1a worka markersa
          ((writeR (some false)).apply T2)
          hcovera hshapea hfiltera hstacka with
        ⟨L0b, L1b, workb, markersb,
          htail, hcoverb, hshapeb, hfilterb, hstackb⟩
      refine ⟨L0b, L1b, workb, markersb, ?_, hcoverb, hshapeb,
        hfilterb, hstackb⟩
      have hwrite :
          writeOutputPrefix (cellBits false) bits T2 =
            writeOutputPrefix [true, false, true] bits
              ((writeR (some false)).apply T2) := by
        calc
          _ = writeOutputPrefix
                (List.append ([false] : Word Bool)
                  [true, false, true]) bits T2 := by rfl
          _ = writeOutputPrefix [true, false, true] bits
                (writeOutputPrefix [false]
                  (List.append [true, false, true] bits) T2) :=
              writeOutputPrefix_append _ _ _ _
          _ = _ := by simp [writeOutputPrefix, writeOutputBits]
      rw [hwrite]
      exact hfirst.trans htail
  | true =>
      have hfilterFirst :
          work.filterMap id = false :: true :: true :: false :: bits := by
        simpa [cellBits, encodeCodeSymbolAsInput] using hfilter
      rcases leads_seekCell_from_stream
          (attempt := attempt) (hattempt := hattempt)
          count (true :: true :: false :: bits)
          L0 L1 work markers T2 hcover hshape hfilterFirst hstack with
        ⟨L0a, L1a, worka, markersa,
          hfirst, hcovera, hshapea, hfiltera, hstacka⟩
      rcases leads_cell_true_tail
          (attempt := attempt) (hattempt := hattempt)
          count bits L0a L1a worka markersa
          ((writeR (some false)).apply T2)
          hcovera hshapea hfiltera hstacka with
        ⟨L0b, L1b, workb, markersb,
          htail, hcoverb, hshapeb, hfilterb, hstackb⟩
      refine ⟨L0b, L1b, workb, markersb, ?_, hcoverb, hshapeb,
        hfilterb, hstackb⟩
      have hwrite :
          writeOutputPrefix (cellBits true) bits T2 =
            writeOutputPrefix [true, true, false] bits
              ((writeR (some false)).apply T2) := by
        calc
          _ = writeOutputPrefix
                (List.append ([false] : Word Bool)
                  [true, true, false]) bits T2 := by rfl
          _ = writeOutputPrefix [true, true, false] bits
                (writeOutputPrefix [false]
                  (List.append [true, true, false] bits) T2) :=
              writeOutputPrefix_append _ _ _ _
          _ = _ := by simp [writeOutputPrefix, writeOutputBits]
      rw [hwrite]
      exact hfirst.trans htail

theorem leads_cells {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (count : Nat) (word : Word Bool) (bits : Word Bool)
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = List.append (cellsBits word) bits)
    (hstack : MarkerStack (word.length + count) L1) :
    ∃ L0' L1' work' markers' : List (Option Bool),
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0' work') (tapeAtCells L1' markers')
          (writeOutputPrefix (cellsBits word) bits T2)) ∧
      RightCovers work' markers' ∧
      MarkerSide markers' ∧
      work'.filterMap id = bits ∧
      MarkerStack count L1' := by
  induction word generalizing count bits L0 L1 work markers T2 with
  | nil =>
      refine ⟨L0, L1, work, markers, ?_, hcover, hshape, ?_, ?_⟩
      · simpa [cellsBits_nil, writeOutputPrefix,
          writeOutputBitsFinal, writeOutputBits] using
          (Leads.refl attempt hattempt
            (cfg attempt hattempt (.result .seekCell)
              (tapeAtCells L0 work) (tapeAtCells L1 markers) T2))
      · rw [cellsBits_nil] at hfilter
        exact hfilter.trans (@List.nil_append Bool bits)
      · simpa using hstack
  | cons bit rest ih =>
      change Word Bool at rest
      have hfilterCell :
          work.filterMap id =
            List.append (cellBits bit)
              (List.append (cellsBits rest) bits) := by
        rw [cellsBits_cons] at hfilter
        exact hfilter.trans
          (@List.append_assoc Bool (cellBits bit) (cellsBits rest) bits)
      have hcount :
          (bit :: rest).length + count = (rest.length + count) + 1 := by
        simp
        lia
      rw [hcount] at hstack
      rcases leads_cell
          (attempt := attempt) (hattempt := hattempt)
          (rest.length + count) bit (List.append (cellsBits rest) bits)
          L0 L1 work markers T2 hcover hshape hfilterCell hstack with
        ⟨L0a, L1a, worka, markersa,
          hcell, hcovera, hshapea, hfiltera, hstacka⟩
      rcases ih count bits L0a L1a worka markersa
          (writeOutputPrefix (cellBits bit)
            (List.append (cellsBits rest) bits) T2)
          hcovera hshapea hfiltera hstacka with
        ⟨L0b, L1b, workb, markersb,
          htail, hcoverb, hshapeb, hfilterb, hstackb⟩
      refine ⟨L0b, L1b, workb, markersb, ?_, hcoverb, hshapeb,
        hfilterb, hstackb⟩
      have hwrite :
          writeOutputPrefix (cellsBits (bit :: rest)) bits T2 =
            writeOutputPrefix (cellsBits rest) bits
              (writeOutputPrefix (cellBits bit)
                (List.append (cellsBits rest) bits) T2) := by
        rw [cellsBits_cons]
        exact writeOutputPrefix_append _ _ _ _
      rw [hwrite]
      exact hcell.trans htail

theorem markerStack_zero_decomp_aux {total : Nat}
    {stack : List (Option Bool)} (h : MarkerStack total stack) :
    total = 0 →
      ∃ gap : Nat,
        stack = List.append (List.replicate gap (some false)) [none] := by
  intro htotal
  induction h with
  | boundary => exact ⟨0, rfl⟩
  | @false count rest h ih =>
      rcases ih htotal with ⟨gap, hrest⟩
      refine ⟨gap + 1, ?_⟩
      rw [hrest]
      simp [List.replicate_succ]
  | @true count rest h ih => simp at htotal

theorem markerStack_zero_decomp {stack : List (Option Bool)}
    (h : MarkerStack 0 stack) :
    ∃ gap : Nat,
      stack = List.append (List.replicate gap (some false)) [none] :=
  markerStack_zero_decomp_aux h rfl

theorem leads_seekCell_marker_none {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (T0 T2 : Tape Bool) (left1 right1 : List (Option Bool))
    (previous : Option Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt (.result .seekCell) T0
        (tapeAtCells (previous :: left1) (none :: right1)) T2)
      (cfg attempt hattempt .checkCount T0
        (tapeAtCells left1 (previous :: none :: right1)) T2) := by
  have hnext :
      (table attempt hattempt).next (.result .seekCell)
          (Tape.read T0)
          (Tape.read (tapeAtCells (previous :: left1) (none :: right1)))
          (Tape.read T2) =
        some ⟨CoreState.checkCount, keepS, keepL, keepS⟩ := by
    change next attempt (.result .seekCell) (Tape.read T0) none
        (Tape.read T2) = _
    rfl
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.result .seekCell) (T0 := T0)
      (T1 := tapeAtCells (previous :: left1) (none :: right1))
      (T2 := T2)
      (st := ⟨CoreState.checkCount, keepS, keepL, keepS⟩)
      (T0' := T0)
      (T1' := tapeAtCells left1 (previous :: none :: right1))
      (T2' := T2)
      (mem_states_of_stateBounded trivial)
      hnext rfl
      (keepL_apply_tapeAtCells left1 previous none right1) rfl

theorem leads_checkCount_false {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (T0 T2 : Tape Bool) (left1 right1 : List (Option Bool))
    (previous : Option Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .checkCount T0
        (tapeAtCells (previous :: left1) (some false :: right1)) T2)
      (cfg attempt hattempt .checkCount T0
        (tapeAtCells left1 (previous :: some false :: right1)) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.checkCount) (T0 := T0)
      (T1 := tapeAtCells (previous :: left1) (some false :: right1))
      (T2 := T2)
      (st := ⟨CoreState.checkCount, keepS, keepL, keepS⟩)
      (T0' := T0)
      (T1' := tapeAtCells left1 (previous :: some false :: right1))
      (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl) rfl
      (keepL_apply_tapeAtCells left1 previous (some false) right1) rfl

theorem leads_checkCount_none {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (T0 T2 : Tape Bool) (left1 right1 : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .checkCount T0
        (tapeAtCells left1 (none :: right1)) T2)
      (cfg attempt hattempt .rewindA T0
        (tapeAtCells left1 (none :: right1)) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.checkCount) (T0 := T0)
      (T1 := tapeAtCells left1 (none :: right1)) (T2 := T2)
      (st := ⟨CoreState.rewindA, keepS, keepS, keepS⟩)
      (T0' := T0) (T1' := tapeAtCells left1 (none :: right1))
      (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl) rfl rfl rfl

theorem leads_checkCount_falses {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (gap : Nat) (T0 T2 : Tape Bool)
    (right1 : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .checkCount T0
        (tapeAtCells
          (List.append (List.replicate gap (some false)) [none])
          (some false :: right1)) T2)
      (cfg attempt hattempt .checkCount T0
        (tapeAtCells []
          (none :: List.append
            (List.replicate (gap + 1) (some false)) right1)) T2) := by
  induction gap generalizing right1 with
  | zero =>
      simpa using
        (leads_checkCount_false (attempt := attempt) (hattempt := hattempt)
          T0 T2 [] right1 none)
  | succ gap ih =>
      simp only [List.replicate_succ]
      refine (leads_checkCount_false
        (attempt := attempt) (hattempt := hattempt)
        T0 T2
        (List.append (List.replicate gap (some false)) [none])
        right1 (some false)).trans ?_
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

theorem leads_seekCell_zero_stack_to_rewind {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (gap : Nat) (T0 T2 : Tape Bool)
    (right1 : List (Option Bool)) :
    ∃ T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell) T0
          (tapeAtCells
            (List.append (List.replicate gap (some false)) [none])
            (none :: right1)) T2)
        (cfg attempt hattempt .rewindA T0 T1' T2) := by
  cases gap with
  | zero =>
      have hseek := leads_seekCell_marker_none
        (attempt := attempt) (hattempt := hattempt)
        T0 T2 [] right1 none
      have hdone := leads_checkCount_none
        (attempt := attempt) (hattempt := hattempt)
        T0 T2 [] (none :: right1)
      exact ⟨tapeAtCells [] (none :: none :: right1), hseek.trans hdone⟩
  | succ gap =>
      have hseek := leads_seekCell_marker_none
        (attempt := attempt) (hattempt := hattempt)
        T0 T2
        (List.append (List.replicate gap (some false)) [none])
        right1 (some false)
      have hscan := leads_checkCount_falses
        (attempt := attempt) (hattempt := hattempt)
        gap T0 T2 (none :: right1)
      have hdone := leads_checkCount_none
        (attempt := attempt) (hattempt := hattempt)
        T0 T2 []
        (List.append (List.replicate (gap + 1) (some false))
          (none :: right1))
      refine ⟨tapeAtCells []
        (none :: List.append (List.replicate (gap + 1) (some false))
          (none :: right1)), ?_⟩
      simpa [List.replicate_succ] using hseek.trans (hscan.trans hdone)

theorem leads_seekCell_finish {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (L0 L1 work markers : List (Option Bool)) (T2 : Tape Bool)
    (hcover : RightCovers work markers)
    (hshape : MarkerSide markers)
    (hfilter : work.filterMap id = [])
    (hstack : MarkerStack 0 L1) :
    ∃ T0' T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt (.result .seekCell)
          (tapeAtCells L0 work) (tapeAtCells L1 markers) T2)
        (cfg attempt hattempt .rewindA T0' T1' T2) := by
  induction hshape generalizing work L0 L1 with
  | nil =>
      cases hcover with
      | extra works hall =>
          rcases markerStack_zero_decomp hstack with ⟨gap, hL1⟩
          subst L1
          rcases leads_seekCell_zero_stack_to_rewind
              (attempt := attempt) (hattempt := hattempt)
              gap (tapeAtCells L0 work) T2 [] with
            ⟨T1', hlead⟩
          exact ⟨tapeAtCells L0 work, T1',
            by simpa [tapeAtCells] using hlead⟩
  | boundary =>
      cases hcover with
      | @cons workCell markerCell works markerCells hcell htail =>
          rcases markerStack_zero_decomp hstack with ⟨gap, hL1⟩
          subst L1
          rcases leads_seekCell_zero_stack_to_rewind
              (attempt := attempt) (hattempt := hattempt)
              gap (tapeAtCells L0 (workCell :: works)) T2 [] with
            ⟨T1', hlead⟩
          exact ⟨tapeAtCells L0 (workCell :: works), T1', hlead⟩
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
          have hstackTail : MarkerStack 0 (some false :: L1) :=
            MarkerStack.false hstack
          rcases ih (work := workTail) (L0 := none :: L0)
              (L1 := some false :: L1)
              hcoverTail hfilterTail hstackTail with
            ⟨T0', T1', htail⟩
          exact ⟨T0', T1', hscan.trans htail⟩

theorem leads_keepL2 {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (s target : CoreState) (T0 T1 : Tape Bool)
    (left2 right2 : List (Option Bool))
    (previous cell : Option Bool)
    (hs : StateBounded attempt s)
    (hnext :
      next attempt s (Tape.read T0) (Tape.read T1) cell =
        some ⟨target, keepS, keepS, keepL⟩) :
    Leads attempt hattempt
      (cfg attempt hattempt s T0 T1
        (tapeAtCells (previous :: left2) (cell :: right2)))
      (cfg attempt hattempt target T0 T1
        (tapeAtCells left2 (previous :: cell :: right2))) := by
  have htable :
      (table attempt hattempt).next s (Tape.read T0) (Tape.read T1)
          (Tape.read (tapeAtCells (previous :: left2) (cell :: right2))) =
        some ⟨target, keepS, keepS, keepL⟩ := by
    change next attempt s (Tape.read T0) (Tape.read T1) cell = _
    exact hnext
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := s) (T0 := T0) (T1 := T1)
      (T2 := tapeAtCells (previous :: left2) (cell :: right2))
      (st := ⟨target, keepS, keepS, keepL⟩)
      (T0' := T0) (T1' := T1)
      (T2' := tapeAtCells left2 (previous :: cell :: right2))
      (mem_states_of_stateBounded hs) htable rfl rfl
      (keepL_apply_tapeAtCells left2 previous cell right2)

theorem leads_rewind_false_token_exact {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (a b c : Bool) (T0 T1 : Tape Bool)
    (previous : Option Bool) (left suffix : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .rewindA T0 T1
        (tapeAtCells
          (some b :: some a :: some false :: previous :: left)
          (some c :: suffix)))
      (cfg attempt hattempt .rewindA T0 T1
        (tapeAtCells left
          (previous :: List.append (cells [false, a, b, c]) suffix))) := by
  have hA := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .rewindA .rewindB T0 T1
    (some a :: some false :: previous :: left) suffix
    (some b) (some c) trivial (by rfl)
  have hB := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .rewindB .rewindC T0 T1
    (some false :: previous :: left) (some c :: suffix)
    (some a) (some b) trivial (by rfl)
  have hC := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .rewindC .rewindTokenFirst T0 T1
    (previous :: left) (some b :: some c :: suffix)
    (some false) (some a) trivial (by rfl)
  have hFirst := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .rewindTokenFirst .rewindA T0 T1 left
    (some a :: some b :: some c :: suffix)
    previous (some false) trivial (by rfl)
  simpa [cells] using hA.trans (hB.trans (hC.trans hFirst))

inductive RewindableBits : Word Bool → Prop where
  | nil : RewindableBits []
  | token (a b c : Bool) {rest : Word Bool} :
      RewindableBits rest →
        RewindableBits (false :: a :: b :: c :: rest)

theorem rewindableBits_append {a b : Word Bool}
    (ha : RewindableBits a) (hb : RewindableBits b) :
    RewindableBits (List.append a b) := by
  induction ha with
  | nil => exact hb
  | token x y z h ih =>
      exact RewindableBits.token x y z ih

theorem rewindableBits_stageNatBits (n : Nat) :
    RewindableBits (stageNatBits n) := by
  induction n with
  | zero =>
      simpa [stageNatBits_zero] using
        (RewindableBits.token false true true RewindableBits.nil)
  | succ n ih =>
      rw [stageNatBits_succ']
      exact RewindableBits.token false true false ih

theorem rewindableBits_cellBits (bit : Bool) :
    RewindableBits (cellBits bit) := by
  cases bit <;>
    simp [cellBits, encodeCodeSymbolAsInput] <;>
    constructor <;> constructor

theorem rewindableBits_cellsBits (word : Word Bool) :
    RewindableBits (cellsBits word) := by
  induction word with
  | nil => simpa using RewindableBits.nil
  | cons bit rest ih =>
      rw [cellsBits_cons]
      exact rewindableBits_append (rewindableBits_cellBits bit) ih

theorem leads_rewindableBits_exact {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    {bits : Word Bool} (hbits : RewindableBits bits)
    (hbitsNe : bits ≠ [])
    (T0 T1 : Tape Bool) (previous : Option Bool)
    (left : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .rewindA T0 T1
        (writeOutputBitsFinal bits
          (tapeAtCells (previous :: left) [])))
      (cfg attempt hattempt .rewindA T0 T1
        (tapeAtCells left (previous :: cells bits))) := by
  induction hbits generalizing previous left with
  | nil => exact False.elim (hbitsNe rfl)
  | @token a b c rest hrest ih =>
      let tokenBits : Word Bool := [false, a, b, c]
      by_cases hrestNe : rest ≠ []
      · have htail := ih hrestNe (some c)
          (some b :: some a :: some false :: previous :: left)
        have hprefix :
            writeOutputBits tokenBits
                (tapeAtCells (previous :: left) []) =
              tapeAtCells
                (some c :: some b :: some a :: some false ::
                  previous :: left) [] := by
          rfl
        rw [← hprefix] at htail
        have htoken := leads_rewind_false_token_exact
          (attempt := attempt) (hattempt := hattempt)
          a b c T0 T1 previous left (cells rest)
        have hbitsEq :
            false :: a :: b :: c :: rest =
              List.append tokenBits rest := by rfl
        rw [hbitsEq,
          writeOutputBitsFinal_append_of_ne_nil tokenBits rest hrestNe]
        refine htail.trans ?_
        rw [cells_append]
        exact htoken
      · cases rest with
        | cons bit rest =>
            exact False.elim (hrestNe (by simp))
        | nil =>
            have htoken := leads_rewind_false_token_exact
              (attempt := attempt) (hattempt := hattempt)
              a b c T0 T1 previous left []
            have hsource :
                writeOutputBitsFinal [false, a, b, c]
                    (tapeAtCells (previous :: left) []) =
                  tapeAtCells
                    (some b :: some a :: some false :: previous :: left)
                    [some c] := by rfl
            rw [hsource]
            exact htoken

theorem leads_keepR2 {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (s target : CoreState) (T0 T1 : Tape Bool)
    (left2 right2 : List (Option Bool)) (cell : Option Bool)
    (hs : StateBounded attempt s)
    (hnext :
      next attempt s (Tape.read T0) (Tape.read T1) cell =
        some ⟨target, keepS, keepS, keepR⟩) :
    Leads attempt hattempt
      (cfg attempt hattempt s T0 T1
        (tapeAtCells left2 (cell :: right2)))
      (cfg attempt hattempt target T0 T1
        (tapeAtCells (cell :: left2) right2)) := by
  have htable :
      (table attempt hattempt).next s (Tape.read T0) (Tape.read T1)
          (Tape.read (tapeAtCells left2 (cell :: right2))) =
        some ⟨target, keepS, keepS, keepR⟩ := by
    change next attempt s (Tape.read T0) (Tape.read T1) cell = _
    exact hnext
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := s) (T0 := T0) (T1 := T1)
      (T2 := tapeAtCells left2 (cell :: right2))
      (st := ⟨target, keepS, keepS, keepR⟩)
      (T0' := T0) (T1' := T1)
      (T2' := tapeAtCells (cell :: left2) right2)
      (mem_states_of_stateBounded hs) htable rfl rfl
      (keepR_apply_tapeAtCells left2 cell right2)

theorem leads_writeR2 {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (s target : CoreState) (T0 T1 : Tape Bool)
    (left2 right2 : List (Option Bool)) (cell value : Option Bool)
    (hs : StateBounded attempt s)
    (hnext :
      next attempt s (Tape.read T0) (Tape.read T1) cell =
        some ⟨target, keepS, keepS, writeR value⟩) :
    Leads attempt hattempt
      (cfg attempt hattempt s T0 T1
        (tapeAtCells left2 (cell :: right2)))
      (cfg attempt hattempt target T0 T1
        (tapeAtCells (value :: left2) right2)) := by
  have htable :
      (table attempt hattempt).next s (Tape.read T0) (Tape.read T1)
          (Tape.read (tapeAtCells left2 (cell :: right2))) =
        some ⟨target, keepS, keepS, writeR value⟩ := by
    change next attempt s (Tape.read T0) (Tape.read T1) cell = _
    exact hnext
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := s) (T0 := T0) (T1 := T1)
      (T2 := tapeAtCells left2 (cell :: right2))
      (st := ⟨target, keepS, keepS, writeR value⟩)
      (T0' := T0) (T1' := T1)
      (T2' := tapeAtCells (value :: left2) right2)
      (mem_states_of_stateBounded hs) htable rfl rfl
      (writeR_apply_tapeAtCells value left2 cell right2)

theorem leads_writeL2 {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (s target : CoreState) (T0 T1 : Tape Bool)
    (left2 right2 : List (Option Bool))
    (previous cell value : Option Bool)
    (hs : StateBounded attempt s)
    (hnext :
      next attempt s (Tape.read T0) (Tape.read T1) cell =
        some ⟨target, keepS, keepS, writeL value⟩) :
    Leads attempt hattempt
      (cfg attempt hattempt s T0 T1
        (tapeAtCells (previous :: left2) (cell :: right2)))
      (cfg attempt hattempt target T0 T1
        (tapeAtCells left2 (previous :: value :: right2))) := by
  have htable :
      (table attempt hattempt).next s (Tape.read T0) (Tape.read T1)
          (Tape.read (tapeAtCells (previous :: left2) (cell :: right2))) =
        some ⟨target, keepS, keepS, writeL value⟩ := by
    change next attempt s (Tape.read T0) (Tape.read T1) cell = _
    exact hnext
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := s) (T0 := T0) (T1 := T1)
      (T2 := tapeAtCells (previous :: left2) (cell :: right2))
      (st := ⟨target, keepS, keepS, writeL value⟩)
      (T0' := T0) (T1' := T1)
      (T2' := tapeAtCells left2 (previous :: value :: right2))
      (mem_states_of_stateBounded hs) htable rfl rfl
      (writeL_apply_tapeAtCells value left2 previous cell right2)

theorem leads_restoreFirst {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (T0 T1 : Tape Bool) (right2 : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .restoreFirst T0 T1
        (tapeAtCells [] (some true :: right2)))
      (cfg attempt hattempt .halt (keepR.apply T0) T1
        (tapeAtCells [] (some false :: right2))) := by
  have hnext :
      (table attempt hattempt).next .restoreFirst
          (Tape.read T0) (Tape.read T1) (some true) =
        some ⟨CoreState.halt, keepR, keepS, writeS (some false)⟩ := by
    change next attempt .restoreFirst
        (Tape.read T0) (Tape.read T1) (some true) = _
    rfl
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.restoreFirst) (T0 := T0) (T1 := T1)
      (T2 := tapeAtCells [] (some true :: right2))
      (st := ⟨CoreState.halt, keepR, keepS, writeS (some false)⟩)
      (T0' := keepR.apply T0) (T1' := T1)
      (T2' := tapeAtCells [] (some false :: right2))
      (mem_states_of_stateBounded trivial) hnext rfl rfl rfl

theorem leads_restore_header {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (T0 T1 : Tape Bool) (suffix : List (Option Bool))
    (hsuffix : suffix ≠ []) :
    Leads attempt hattempt
      (cfg attempt hattempt .rewindA T0 T1
        (keepL.apply
          (tapeAtCells
            [some true, some true, some true, some true] suffix)))
      (cfg attempt hattempt .halt (keepR.apply T0) T1
        (tapeAtCells []
          (some false :: some false :: some false :: some false :: suffix))) := by
  rcases List.exists_cons_of_ne_nil hsuffix with
    ⟨suffixHead, suffixTail, hsuffixEq⟩
  subst suffix
  have hA := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .rewindA .rewindB T0 T1
    [some true, some true] (suffixHead :: suffixTail)
    (some true) (some true) trivial (by rfl)
  have hB := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .rewindB .rewindC T0 T1
    [some true] (some true :: suffixHead :: suffixTail)
    (some true) (some true) trivial (by rfl)
  have hC := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .rewindC .rewindTokenFirst T0 T1
    [] (some true :: some true :: suffixHead :: suffixTail)
    (some true) (some true) trivial (by rfl)
  have hfirst := leads_keepR2
    (attempt := attempt) (hattempt := hattempt)
    .rewindTokenFirst .markerSecond T0 T1 []
    (some true :: some true :: some true :: suffixHead :: suffixTail)
    (some true) trivial (by rfl)
  have hsecond := leads_writeR2
    (attempt := attempt) (hattempt := hattempt)
    .markerSecond .restoreThird T0 T1 [some true]
    (some true :: some true :: suffixHead :: suffixTail)
    (some true) (some false) trivial (by rfl)
  have hthird := leads_writeR2
    (attempt := attempt) (hattempt := hattempt)
    .restoreThird .restoreFourth T0 T1 [some false, some true]
    (some true :: suffixHead :: suffixTail)
    (some true) (some false) trivial (by rfl)
  have hfourth := leads_writeL2
    (attempt := attempt) (hattempt := hattempt)
    .restoreFourth .restoreBackThird T0 T1
    [some false, some true] (suffixHead :: suffixTail)
    (some false) (some true) (some false) trivial (by rfl)
  have hbackThird := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .restoreBackThird .restoreBackSecond T0 T1
    [some true] (some false :: suffixHead :: suffixTail)
    (some false) (some false) trivial (by rfl)
  have hbackSecond := leads_keepL2
    (attempt := attempt) (hattempt := hattempt)
    .restoreBackSecond .restoreFirst T0 T1 []
    (some false :: some false :: suffixHead :: suffixTail)
    (some true) (some false) trivial (by rfl)
  have hdone := leads_restoreFirst
    (attempt := attempt) (hattempt := hattempt)
    T0 T1 (some false :: some false :: some false :: suffixHead :: suffixTail)
  simpa [keepL_eq, TapeAction.apply, HeadMove.apply, Tape.move,
    Tape.moveLeft, tapeAtCells] using
    hA.trans (hB.trans (hC.trans
      (hfirst.trans (hsecond.trans (hthird.trans
        (hfourth.trans (hbackThird.trans (hbackSecond.trans hdone))))))))

theorem leads_restore_header_exact {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bits : Word Bool) (hbits : bits ≠ [])
    (T0 T1 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .rewindA T0 T1
        (tapeAtCells [some true, some true, some true]
          (some true :: cells bits)))
      (cfg attempt hattempt .halt (keepR.apply T0) T1
        (tapeAtCells []
          (cells (false :: false :: false :: false :: bits)))) := by
  cases bits with
  | nil => exact False.elim (hbits rfl)
  | cons bit rest =>
      have hrestore := leads_restore_header
        (attempt := attempt) (hattempt := hattempt)
        T0 T1 (cells (bit :: rest)) (by simp [cells])
      simpa [cells, keepL_eq, TapeAction.apply, HeadMove.apply,
        Tape.move, Tape.moveLeft, tapeAtCells] using hrestore

theorem resultBits_eq_length_cells (word : Word Bool) :
    resultBits word =
      List.append (stageNatBits word.length) (cellsBits word) := by
  unfold resultBits encodeBoolWord
  rw [boolWordBits_eq_encodeBoolWordAppend word []]
  rw [← cellsBits_eq_cellsCodeBits]
  simp [encodeCodeWordAsInput]

theorem rewindableBits_resultBits (word : Word Bool) :
    RewindableBits (resultBits word) := by
  rw [resultBits_eq_length_cells]
  exact rewindableBits_append
    (rewindableBits_stageNatBits word.length)
    (rewindableBits_cellsBits word)

theorem rewindableBits_stageInputBits (C : DovetailControllerLayout) :
    RewindableBits (stageInputBits C) := by
  rw [stageInputBits_eq]
  exact rewindableBits_append
    (rewindableBits_stageNatBits C.input.length)
    (rewindableBits_append
      (rewindableBits_cellsBits C.input)
      (rewindableBits_stageNatBits C.stage))

def framedPayloadBits (C : DovetailControllerLayout)
    (result : Word Bool) : Word Bool :=
  List.append (stageInputBits C) (resultBits result)

theorem rewindableBits_framedPayloadBits
    (C : DovetailControllerLayout) (result : Word Bool) :
    RewindableBits (framedPayloadBits C result) :=
  rewindableBits_append
    (rewindableBits_stageInputBits C)
    (rewindableBits_resultBits result)

theorem parsedInputLeft2_eq_payload_prefix
    (C : DovetailControllerLayout) :
    parsedInputLeft2 C =
      pushWord (stageInputBits C)
        [some true, some true, some true, some true] := by
  rw [stageInputBits_eq]
  rw [pushWord_append, pushWord_append]
  rfl

theorem framedPayloadBits_ne_nil
    (C : DovetailControllerLayout) (result : Word Bool) :
    framedPayloadBits C result ≠ [] := by
  unfold framedPayloadBits
  cases hstage : stageInputBits C with
  | nil => exact False.elim ((stageInputBits_ne_nil C) hstage)
  | cons bit rest => simp

theorem stageAttemptFramedOutputTape_eq_exact
    (C : DovetailControllerLayout) (result : Word Bool) :
    CommonGround.ControllerInvocation.StageAttemptFramedOutputTape C result =
      tapeAtCells []
        (cells
          (false :: false :: false :: false ::
            framedPayloadBits C result)) := by
  rw [show CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
      C result =
        Tape.input
          (false :: false :: false :: false ::
            framedPayloadBits C result) by
    unfold CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
    rw [outputBits_eq]
    rfl]
  rfl

theorem leads_rewind_framedPayload_exact {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (C : DovetailControllerLayout) (result : Word Bool)
    (T0 T1 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .rewindA T0 T1
        (writeOutputBitsFinal (resultBits result)
          (tapeAtCells (parsedInputLeft2 C) [])))
      (cfg attempt hattempt .halt (keepR.apply T0) T1
        (CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
          C result)) := by
  have hpayloadNe := framedPayloadBits_ne_nil C result
  have hscan := leads_rewindableBits_exact
    (attempt := attempt) (hattempt := hattempt)
    (rewindableBits_framedPayloadBits C result) hpayloadNe
    T0 T1 (some true) [some true, some true, some true]
  have hstage :
      writeOutputBits (stageInputBits C)
          (tapeAtCells
            [some true, some true, some true, some true] []) =
        tapeAtCells (parsedInputLeft2 C) [] := by
    rw [writeOutputBits_tapeAtCells]
    rw [parsedInputLeft2_eq_payload_prefix]
  have hsource :
      writeOutputBitsFinal (framedPayloadBits C result)
          (tapeAtCells
            [some true, some true, some true, some true] []) =
        writeOutputBitsFinal (resultBits result)
          (tapeAtCells (parsedInputLeft2 C) []) := by
    unfold framedPayloadBits
    rw [writeOutputBitsFinal_append_of_ne_nil
      (stageInputBits C) (resultBits result) (resultBits_ne_nil result)]
    rw [hstage]
  rw [hsource] at hscan
  have hrestore := leads_restore_header_exact
    (attempt := attempt) (hattempt := hattempt)
    (framedPayloadBits C result) hpayloadNe T0 T1
  rw [stageAttemptFramedOutputTape_eq_exact]
  exact hscan.trans hrestore

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
