import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.SelectorSplice

set_option doc.verso true

/-!
# Fixed-start selector/dispatcher execution

This module proves the exact combined selector, dispatcher, and witness-closeout
run and lowers that one genuine fixed-start structured machine to the guarded
one-tape representation.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.SelectorSplice

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open FieldDecomposition.ClassifiedBoundary

theorem leads_ingress_step2
    (D : MachineDescription)
    (source target : FieldDecomposition.SelectorIngress.State D)
    (hsource : source ∈ FieldDecomposition.SelectorIngress.states D)
    (T0 T1 T2 : Tape Bool) (action2 : TapeAction)
    (hnext :
      next D (.ingress source)
          (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some
          { target := .ingress target
            action0 := keepS
            action1 := keepS
            action2 := action2 })
    (T2' : Tape Bool) (h2 : action2.apply T2 = T2') :
    (table D).Leads
      ((table D).config (.ingress source) T0 T1 T2)
      ((table D).config (.ingress target) T0 T1 T2') := by
  apply TypedStateTable.leads_step (table D)
    (ingress_mem_states hsource) hnext
  · rfl
  · rfl
  · exact h2
  done

theorem leads_ingress_bool_other
    (D : MachineDescription) (hit : Bool)
    (T0 T1 : Tape Bool) (nextCell : Option Bool)
    (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.bool0 hit)) T0 T1
        (tapeAtCells
          (some true :: some false :: some true :: nextCell :: left)
          (some false :: right)))
      ((table D).config
        (.ingress (.seekDelimiter hit
          (StateClass.other : StateClass D))) T0 T1
        (tapeAtCells left
          (nextCell :: some true :: some true :: some true ::
            some true :: right))) := by
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.bool1 hit)) T0 T1
      (tapeAtCells (some false :: some true :: nextCell :: left)
        (some true :: some true :: right)))
  · apply leads_ingress_step2 D (.bool0 hit) (.bool1 hit)
      (FieldDecomposition.SelectorIngress.bool0_mem_states D hit)
      T0 T1 _ (writeL (some true)) (by rfl) _ (by rfl)
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.bool2 hit)) T0 T1
      (tapeAtCells (some true :: nextCell :: left)
        (some false :: some true :: some true :: right)))
  · apply leads_ingress_step2 D (.bool1 hit) (.bool2 hit)
      (FieldDecomposition.SelectorIngress.bool1_mem_states D hit)
      T0 T1 _ (writeL (some true)) (by rfl) _ (by rfl)
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.bool3 hit false)) T0 T1
      (tapeAtCells (nextCell :: left)
        (some true :: some true :: some true :: some true :: right)))
  · apply leads_ingress_step2 D (.bool2 hit) (.bool3 hit false)
      (FieldDecomposition.SelectorIngress.bool2_mem_states D hit)
      T0 T1 _ (writeL (some true)) (by rfl) _ (by rfl)
  apply leads_ingress_step2 D (.bool3 hit false)
    (.seekDelimiter hit .other)
    (FieldDecomposition.SelectorIngress.bool3_mem_states D hit false)
    T0 T1 _ (writeL (some true)) (by rfl) _ (by rfl)
  done

theorem leads_ingress_bool_known
    (D : MachineDescription) (hit : Bool)
    (T0 T1 : Tape Bool) (nextCell : Option Bool)
    (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.bool0 hit)) T0 T1
        (tapeAtCells
          (some true :: some true :: some false :: nextCell :: left)
          (some false :: right)))
      ((table D).config (.ingress (.nat0 hit 0)) T0 T1
        (tapeAtCells left
          (nextCell :: some true :: some true :: some true ::
            some true :: right))) := by
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.bool1 hit)) T0 T1
      (tapeAtCells (some true :: some false :: nextCell :: left)
        (some true :: some true :: right)))
  · apply leads_ingress_step2 D (.bool0 hit) (.bool1 hit)
      (FieldDecomposition.SelectorIngress.bool0_mem_states D hit)
      T0 T1 _ (writeL (some true)) (by rfl) _ (by rfl)
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.bool2 hit)) T0 T1
      (tapeAtCells (some false :: nextCell :: left)
        (some true :: some true :: some true :: right)))
  · apply leads_ingress_step2 D (.bool1 hit) (.bool2 hit)
      (FieldDecomposition.SelectorIngress.bool1_mem_states D hit)
      T0 T1 _ (writeL (some true)) (by rfl) _ (by rfl)
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.bool3 hit true)) T0 T1
      (tapeAtCells (nextCell :: left)
        (some false :: some true :: some true :: some true :: right)))
  · apply leads_ingress_step2 D (.bool2 hit) (.bool3 hit true)
      (FieldDecomposition.SelectorIngress.bool2_mem_states D hit)
      T0 T1 _ (writeL (some true)) (by rfl) _ (by rfl)
  apply leads_ingress_step2 D (.bool3 hit true) (.nat0 hit 0)
    (FieldDecomposition.SelectorIngress.bool3_mem_states D hit true)
    T0 T1 _ (writeL (some true)) (by rfl) _ (by rfl)
  done

theorem next_ingress_nat0
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value ≤ FieldDecomposition.SelectorIngress.stateValueBound D)
    (r0 r1 : Option Bool) :
    next D (.ingress (.nat0 hit value)) r0 r1 (some false) =
      some
        { target := .ingress (.nat1 hit value)
          action0 := keepS
          action1 := keepS
          action2 := writeL (some true) } := by
  simp only [next, FieldDecomposition.SelectorIngress.next,
    if_pos hvalue]
  rfl
  done

theorem next_ingress_nat1
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value ≤ FieldDecomposition.SelectorIngress.stateValueBound D)
    (r0 r1 : Option Bool) :
    next D (.ingress (.nat1 hit value)) r0 r1 (some false) =
      some
        { target := .ingress (.nat2 hit value)
          action0 := keepS
          action1 := keepS
          action2 := writeL (some true) } := by
  simp only [next, FieldDecomposition.SelectorIngress.next,
    if_pos hvalue]
  rfl
  done

theorem next_ingress_nat2
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value ≤ FieldDecomposition.SelectorIngress.stateValueBound D)
    (r0 r1 : Option Bool) :
    next D (.ingress (.nat2 hit value)) r0 r1 (some true) =
      some
        { target := .ingress (.nat3 hit value)
          action0 := keepS
          action1 := keepS
          action2 := writeL (some true) } := by
  simp only [next, FieldDecomposition.SelectorIngress.next,
    if_pos hvalue]
  rfl
  done

theorem next_ingress_nat3_tick
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value < FieldDecomposition.SelectorIngress.stateValueBound D)
    (r0 r1 : Option Bool) :
    next D (.ingress (.nat3 hit value)) r0 r1 (some false) =
      some
        { target := .ingress (.nat0 hit (value + 1))
          action0 := keepS
          action1 := keepS
          action2 := writeL (some true) } := by
  simp only [next, FieldDecomposition.SelectorIngress.next,
    if_pos hvalue]
  rfl
  done

theorem leads_ingress_nat_tick
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value < FieldDecomposition.SelectorIngress.stateValueBound D)
    (T0 T1 : Tape Bool) (nextCell : Option Bool)
    (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.nat0 hit value)) T0 T1
        (tapeAtCells
          (some false :: some true :: some false :: nextCell :: left)
          (some false :: right)))
      ((table D).config (.ingress (.nat0 hit (value + 1))) T0 T1
        (tapeAtCells left
          (nextCell :: some true :: some true :: some true ::
            some true :: right))) := by
  have hvalueLe :
      value ≤ FieldDecomposition.SelectorIngress.stateValueBound D :=
    Nat.le_of_lt hvalue
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.nat1 hit value)) T0 T1
      (tapeAtCells (some true :: some false :: nextCell :: left)
        (some false :: some true :: right)))
  · apply leads_ingress_step2 D (.nat0 hit value) (.nat1 hit value)
      (FieldDecomposition.SelectorIngress.nat0_mem_states D hit value hvalueLe)
      T0 T1 _ (writeL (some true))
      (next_ingress_nat0 D hit value hvalueLe _ _) _ (by rfl)
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.nat2 hit value)) T0 T1
      (tapeAtCells (some false :: nextCell :: left)
        (some true :: some true :: some true :: right)))
  · apply leads_ingress_step2 D (.nat1 hit value) (.nat2 hit value)
      (FieldDecomposition.SelectorIngress.nat1_mem_states D hit value hvalueLe)
      T0 T1 _ (writeL (some true))
      (next_ingress_nat1 D hit value hvalueLe _ _) _ (by rfl)
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.nat3 hit value)) T0 T1
      (tapeAtCells (nextCell :: left)
        (some false :: some true :: some true :: some true :: right)))
  · apply leads_ingress_step2 D (.nat2 hit value) (.nat3 hit value)
      (FieldDecomposition.SelectorIngress.nat2_mem_states D hit value hvalueLe)
      T0 T1 _ (writeL (some true))
      (next_ingress_nat2 D hit value hvalueLe _ _) _ (by rfl)
  apply leads_ingress_step2 D (.nat3 hit value) (.nat0 hit (value + 1))
    (FieldDecomposition.SelectorIngress.nat3_mem_states D hit value hvalueLe)
    T0 T1 _ (writeL (some true))
    (next_ingress_nat3_tick D hit value hvalue _ _) _ (by rfl)
  done

theorem next_ingress_nat3_done
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hstate : value ∈ fixedStepValues D) (r0 r1 : Option Bool) :
    next D (.ingress (.nat3 hit value)) r0 r1 (some true) =
      some
        { target := .ingress (.seekDelimiter hit (.known value hstate))
          action0 := keepS
          action1 := keepS
          action2 := writeL (some true) } := by
  simp only [next, FieldDecomposition.SelectorIngress.next]
  split
  · rfl
  · contradiction
  done

theorem leads_ingress_nat_done
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hstate : value ∈ fixedStepValues D)
    (T0 T1 : Tape Bool) (nextCell : Option Bool)
    (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.nat0 hit value)) T0 T1
        (tapeAtCells
          (some false :: some true :: some true :: nextCell :: left)
          (some false :: right)))
      ((table D).config
        (.ingress (.seekDelimiter hit (.known value hstate))) T0 T1
        (tapeAtCells left
          (nextCell :: some true :: some true :: some true ::
            some true :: right))) := by
  have hvalueLe :=
    FieldDecomposition.SelectorIngress.knownState_le_stateValueBound hstate
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.nat1 hit value)) T0 T1
      (tapeAtCells (some true :: some true :: nextCell :: left)
        (some false :: some true :: right)))
  · apply leads_ingress_step2 D (.nat0 hit value) (.nat1 hit value)
      (FieldDecomposition.SelectorIngress.nat0_mem_states D hit value hvalueLe)
      T0 T1 _ (writeL (some true))
      (next_ingress_nat0 D hit value hvalueLe _ _) _ (by rfl)
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.nat2 hit value)) T0 T1
      (tapeAtCells (some true :: nextCell :: left)
        (some true :: some true :: some true :: right)))
  · apply leads_ingress_step2 D (.nat1 hit value) (.nat2 hit value)
      (FieldDecomposition.SelectorIngress.nat1_mem_states D hit value hvalueLe)
      T0 T1 _ (writeL (some true))
      (next_ingress_nat1 D hit value hvalueLe _ _) _ (by rfl)
  apply TypedStateTable.Leads.trans (d :=
    (table D).config (.ingress (.nat3 hit value)) T0 T1
      (tapeAtCells (nextCell :: left)
        (some true :: some true :: some true :: some true :: right)))
  · apply leads_ingress_step2 D (.nat2 hit value) (.nat3 hit value)
      (FieldDecomposition.SelectorIngress.nat2_mem_states D hit value hvalueLe)
      T0 T1 _ (writeL (some true))
      (next_ingress_nat2 D hit value hvalueLe _ _) _ (by rfl)
  apply leads_ingress_step2 D (.nat3 hit value)
    (.seekDelimiter hit (.known value hstate))
    (FieldDecomposition.SelectorIngress.nat3_mem_states D hit value hvalueLe)
    T0 T1 _ (writeL (some true))
    (next_ingress_nat3_done D hit value hstate _ _) _ (by rfl)
  done

theorem leads_ingress_natSelector
    (D : MachineDescription) (hit : Bool)
    (value remaining : Nat)
    (hstate : value + remaining ∈ fixedStepValues D)
    (T0 T1 : Tape Bool) (nextCell : Option Bool)
    (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.nat0 hit value)) T0 T1
        (tapeAtCells
          (FieldDecomposition.SelectorIngress.natSelectorTail
            remaining nextCell left)
          (some false :: right)))
      ((table D).config
        (.ingress (.seekDelimiter hit (.known (value + remaining) hstate)))
        T0 T1
        (tapeAtCells left
          (nextCell ::
            FieldDecomposition.SelectorIngress.restoredNatRight
              remaining right))) := by
  induction remaining generalizing value right with
  | zero =>
      have hvalue : value ∈ fixedStepValues D := by simpa using hstate
      simpa [FieldDecomposition.SelectorIngress.natSelectorTail,
        FieldDecomposition.SelectorIngress.restoredNatRight] using
        leads_ingress_nat_done D hit value hvalue
          T0 T1 nextCell left right
  | succ remaining ih =>
      have hbound :=
        FieldDecomposition.SelectorIngress.knownState_le_stateValueBound
          hstate
      have hvalue :
          value < FieldDecomposition.SelectorIngress.stateValueBound D := by
        lia
      have hstate' : value + 1 + remaining ∈ fixedStepValues D := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstate
      have htick := leads_ingress_nat_tick D hit value hvalue T0 T1
        (some false)
        (FieldDecomposition.SelectorIngress.natSelectorTail
          remaining nextCell left) right
      have hrest := ih (value + 1) hstate'
        ([some true, some true, some true, some true] ++ right)
      refine TypedStateTable.Leads.trans (d :=
        (table D).config (.ingress (.nat0 hit (value + 1))) T0 T1
          (tapeAtCells
            (FieldDecomposition.SelectorIngress.natSelectorTail
              remaining nextCell left)
            (some false ::
              [some true, some true, some true, some true] ++ right))) ?_ ?_
      · simpa [FieldDecomposition.SelectorIngress.natSelectorTail] using htick
      · simpa [FieldDecomposition.SelectorIngress.restoredNatRight,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest
  done

theorem leads_ingress_selector
    (D : MachineDescription) (hit : Bool) (tag : StateClass D)
    (T0 T1 : Tape Bool) (nextCell : Option Bool)
    (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.bool0 hit)) T0 T1
        (tapeAtCells
          (FieldDecomposition.SelectorIngress.selectorTailCells
            tag nextCell left)
          (some false :: right)))
      ((table D).config (.ingress (.seekDelimiter hit tag)) T0 T1
        (tapeAtCells left
          (nextCell ::
            List.replicate
              (FieldDecomposition.ClassifiedBoundary.selectorBits tag).length
              (some true) ++ right))) := by
  cases tag with
  | other =>
      have hrun := leads_ingress_bool_other D hit T0 T1 nextCell left right
      rw [FieldDecomposition.ClassifiedBoundary.selectorBits_length_other D]
      simpa [FieldDecomposition.SelectorIngress.selectorTailCells] using hrun
  | known state hstate =>
      have hbool := leads_ingress_bool_known D hit T0 T1 (some false)
        (FieldDecomposition.SelectorIngress.natSelectorTail
          state nextCell left) right
      have hnat := leads_ingress_natSelector D hit 0 state
        (by simpa using hstate) T0 T1 nextCell left
        ([some true, some true, some true, some true] ++ right)
      refine TypedStateTable.Leads.trans (d :=
        (table D).config (.ingress (.nat0 hit 0)) T0 T1
          (tapeAtCells
            (FieldDecomposition.SelectorIngress.natSelectorTail
              state nextCell left)
            (some false ::
              [some true, some true, some true, some true] ++ right))) ?_ ?_
      · simpa [FieldDecomposition.SelectorIngress.selectorTailCells]
          using hbool
      · rw [FieldDecomposition.SelectorIngress.restoredNatRight_eq] at hnat
        rw [FieldDecomposition.ClassifiedBoundary.selectorBits_length_known hstate]
        have hrep :
            List.replicate (4 * (state + 1)) (some true) ++
                ([some true, some true, some true, some true] ++ right) =
              List.replicate (4 * (state + 2)) (some true) ++ right := by
          change
            List.replicate (4 * (state + 1)) (some true) ++
                (List.replicate 4 (some true) ++ right) =
              List.replicate (4 * (state + 2)) (some true) ++ right
          rw [← FoC.Computability.list_replicate_add_append
            (some true : Option Bool) (4 * (state + 1)) 4 right]
          congr 2
        rw [hrep] at hnat
        simpa using hnat
  done

theorem leads_ingress_seekMarkers
    (D : MachineDescription) (hit : Bool) (tag : StateClass D)
    (count : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.seekDelimiter hit tag)) T0 T1
        (tapeAtCells
          (List.replicate count (some true) ++ none :: left)
          (some true :: right)))
      ((table D).config (.ingress (.seekDelimiter hit tag)) T0 T1
        (tapeAtCells left
          (none :: List.replicate (count + 1) (some true) ++ right))) := by
  induction count generalizing right with
  | zero =>
      have hstep := leads_ingress_step2 D
        (.seekDelimiter hit tag) (.seekDelimiter hit tag)
        (FieldDecomposition.SelectorIngress.seekDelimiter_mem_states D hit tag)
        T0 T1 (tapeAtCells (none :: left) (some true :: right)) keepL
        (by rfl)
        (tapeAtCells left (none :: some true :: right)) (by rfl)
      simpa using hstep
  | succ count ih =>
      have hstep := leads_ingress_step2 D
        (.seekDelimiter hit tag) (.seekDelimiter hit tag)
        (FieldDecomposition.SelectorIngress.seekDelimiter_mem_states D hit tag)
        T0 T1
        (tapeAtCells
          (some true ::
            (List.replicate count (some true) ++ none :: left))
          (some true :: right))
        keepL (by rfl)
        (tapeAtCells
          (List.replicate count (some true) ++ none :: left)
          (some true :: some true :: right)) (by rfl)
      have hrest := ih (some true :: right)
      refine TypedStateTable.Leads.trans (d :=
        (table D).config (.ingress (.seekDelimiter hit tag)) T0 T1
          (tapeAtCells
            (List.replicate count (some true) ++ none :: left)
            (some true :: some true :: right))) ?_ ?_
      · simpa [List.replicate_succ] using hstep
      · have hrep := FoC.Computability.list_replicate_append_self
          (some true : Option Bool) (count + 1) right
        have hright :
            (none :: List.replicate (count + 1) (some true)) ++
                some true :: right =
              (none :: List.replicate (count + 1 + 1) (some true)) ++
                right := by
          simpa only [List.cons_append] using congrArg (List.cons none) hrep
        rw [hright] at hrest
        exact hrest
  done

theorem leads_ingress_seekDelimiter
    (D : MachineDescription) (hit : Bool) (tag : StateClass D)
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.seekDelimiter hit tag)) T0 T1
        (tapeAtCells left (none :: some true :: right)))
      ((table D).config (.ingress (.returnToHit hit tag)) T0 T1
        (tapeAtCells (none :: left) (some true :: right))) := by
  exact leads_ingress_step2 D
    (.seekDelimiter hit tag) (.returnToHit hit tag)
    (FieldDecomposition.SelectorIngress.seekDelimiter_mem_states D hit tag)
    T0 T1 (tapeAtCells left (none :: some true :: right)) keepR
    (by rfl)
    (tapeAtCells (none :: left) (some true :: right)) (by rfl)
  done

theorem leads_ingress_returnMarkers
    (D : MachineDescription) (hit : Bool) (tag : StateClass D)
    (count : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.returnToHit hit tag)) T0 T1
        (tapeAtCells left
          (List.replicate count (some true) ++ some false :: right)))
      ((table D).config (.ingress (.returnToHit hit tag)) T0 T1
        (tapeAtCells
          (List.replicate count (some true) ++ left)
          (some false :: right))) := by
  induction count generalizing left with
  | zero => exact TypedStateTable.Leads.refl _ _
  | succ count ih =>
      have hstep := leads_ingress_step2 D
        (.returnToHit hit tag) (.returnToHit hit tag)
        (FieldDecomposition.SelectorIngress.returnToHit_mem_states D hit tag)
        T0 T1
        (tapeAtCells left
          (some true ::
            (List.replicate count (some true) ++ some false :: right)))
        keepR (by rfl)
        (tapeAtCells (some true :: left)
          (List.replicate count (some true) ++ some false :: right))
        (ThreeTape.keepR_apply_tapeAtCells left (some true)
          (List.replicate count (some true) ++ some false :: right))
      have hrest := ih (some true :: left)
      refine TypedStateTable.Leads.trans (d :=
        (table D).config (.ingress (.returnToHit hit tag)) T0 T1
          (tapeAtCells (some true :: left)
            (List.replicate count (some true) ++ some false :: right))) ?_ ?_
      · simpa [List.replicate_succ] using hstep
      · have hrep := FoC.Computability.list_replicate_append_self
          (some true : Option Bool) count left
        rw [hrep] at hrest
        exact hrest
  done

theorem leads_ingress_restoreHit
    (D : MachineDescription) (hit : Bool) (tag : StateClass D)
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress (.returnToHit hit tag)) T0 T1
        (tapeAtCells left (some false :: none :: right)))
      ((table D).config (.ingress (.done tag)) T0 T1
        (tapeAtCells left (some hit :: none :: right))) := by
  have hwrite := leads_ingress_step2 D
    (.returnToHit hit tag) (.restoreHit hit tag)
    (FieldDecomposition.SelectorIngress.returnToHit_mem_states D hit tag)
    T0 T1 (tapeAtCells left (some false :: none :: right))
    (writeR (some hit)) (by rfl)
    (tapeAtCells (some hit :: left) (none :: right)) (by rfl)
  have hfinish := leads_ingress_step2 D
    (.restoreHit hit tag) (.done tag)
    (FieldDecomposition.SelectorIngress.restoreHit_mem_states D hit tag)
    T0 T1 (tapeAtCells (some hit :: left) (none :: right))
    keepL (by rfl)
    (tapeAtCells left (some hit :: none :: right)) (by rfl)
  exact hwrite.trans hfinish
  done

theorem leads_ingress_done_bridge
    (D : MachineDescription) (tag : StateClass D)
    (T0 T1 T2 : Tape Bool) :
    (table D).Leads
      ((table D).config (.ingress (.done tag)) T0 T1 T2)
      ((table D).config (.core (.base (.dispatch tag))) T0 T1 T2) := by
  apply TypedStateTable.leads_step (table D)
    (ingress_mem_states
      (FieldDecomposition.SelectorIngress.done_mem_states D tag))
    (st :=
      { target := .core (.base (.dispatch tag))
        action0 := keepS
        action1 := keepS
        action2 := keepS })
    (hnext := by rfl)
  · rfl
  · rfl
  · rfl
  done

theorem leads_ingress_startSelector
    (D : MachineDescription) (hit : Bool) (tag : StateClass D)
    (T0 T1 : Tape Bool) (nextCell : Option Bool)
    (left : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress .start) T0 T1
        (tapeAtCells
          ((selectorBits tag).map some ++ nextCell :: left)
          [some hit, none]))
      ((table D).config (.ingress (.bool0 hit)) T0 T1
        (tapeAtCells
          (FieldDecomposition.SelectorIngress.selectorTailCells
            tag nextCell left)
          [some false, some false, none])) := by
  apply leads_ingress_step2 D .start (.bool0 hit)
    (FieldDecomposition.SelectorIngress.start_mem_states D)
    T0 T1
    (tapeAtCells
      ((selectorBits tag).map some ++ nextCell :: left)
      [some hit, none])
    (writeL (some false)) (by rfl)
    (tapeAtCells
      (FieldDecomposition.SelectorIngress.selectorTailCells
        tag nextCell left)
      [some false, some false, none])
  · rw [FieldDecomposition.SelectorIngress.selectorBits_cells_eq]
    exact ThreeTape.writeL_apply_tapeAtCells (some false)
      (FieldDecomposition.SelectorIngress.selectorTailCells
        tag nextCell left)
      (some false) (some hit) [none]
  done

theorem selectorBits_length_pos
    {D : MachineDescription} (tag : StateClass D) :
    0 < (selectorBits tag).length := by
  cases tag with
  | other =>
      rw [selectorBits_length_other D]
      decide
  | known state hstate =>
      rw [selectorBits_length_known hstate]
      lia
  done

theorem leads_ingress_selectorLayout
    (D : MachineDescription) (hit : Bool) (tag : StateClass D)
    (remaining : Nat) (T0 T1 : Tape Bool)
    (metadata : List (Option Bool)) :
    (table D).Leads
      ((table D).config (.ingress .start) T0 T1
        (tapeAtCells
          ((selectorBits tag).map some ++
            List.replicate remaining (some true) ++ none :: metadata)
          [some hit, none]))
      ((table D).config (.core (.base (.dispatch tag))) T0 T1
        (tapeAtCells
          (List.replicate (selectorBits tag).length (some true) ++
            List.replicate remaining (some true) ++ none :: metadata)
          [some hit, none])) := by
  cases remaining with
  | zero =>
      cases hlen : (selectorBits tag).length with
      | zero =>
          have hpos := selectorBits_length_pos tag
          rw [hlen] at hpos
          lia
      | succ count =>
          have hstart := leads_ingress_startSelector D hit tag T0 T1 none metadata
          have hparse := leads_ingress_selector D hit tag T0 T1 none metadata
            [some false, none]
          have hdelimiter := leads_ingress_seekDelimiter D hit tag T0 T1 metadata
            (List.replicate count (some true) ++ some false :: none :: [])
          have hreturn := leads_ingress_returnMarkers D hit tag (count + 1)
            T0 T1 (none :: metadata) [none]
          have hrestore := leads_ingress_restoreHit D hit tag T0 T1
            (List.replicate (count + 1) (some true) ++ none :: metadata) []
          have hbridge := leads_ingress_done_bridge D tag T0 T1
            (tapeAtCells
              (List.replicate (count + 1) (some true) ++ none :: metadata)
              [some hit, none])
          rw [hlen] at hparse
          have hchain := hstart.trans (hparse.trans
            (hdelimiter.trans (hreturn.trans (hrestore.trans hbridge))))
          simpa [hlen, List.replicate_succ, List.append_assoc] using hchain
  | succ remaining =>
      have hstart := leads_ingress_startSelector D hit tag T0 T1 (some true)
        (List.replicate remaining (some true) ++ none :: metadata)
      have hparse := leads_ingress_selector D hit tag T0 T1 (some true)
        (List.replicate remaining (some true) ++ none :: metadata)
        [some false, none]
      have hseek := leads_ingress_seekMarkers D hit tag remaining T0 T1 metadata
        (List.replicate (selectorBits tag).length (some true) ++
          some false :: none :: [])
      have hdelimiter := leads_ingress_seekDelimiter D hit tag T0 T1 metadata
        (List.replicate remaining (some true) ++
          (List.replicate (selectorBits tag).length (some true) ++
            some false :: none :: []))
      have hreturn := leads_ingress_returnMarkers D hit tag
        ((remaining + 1) + (selectorBits tag).length)
        T0 T1 (none :: metadata) [none]
      have hmarkers := FoC.Computability.list_replicate_add_append
        (some true : Option Bool) (remaining + 1)
        (selectorBits tag).length [some false, none]
      rw [hmarkers] at hreturn
      simp only [List.replicate_succ, List.cons_append] at hreturn
      have hrestore := leads_ingress_restoreHit D hit tag T0 T1
        (List.replicate
          ((remaining + 1) + (selectorBits tag).length) (some true) ++
          none :: metadata)
        []
      have hbridge := leads_ingress_done_bridge D tag T0 T1
        (tapeAtCells
          (List.replicate
            ((remaining + 1) + (selectorBits tag).length) (some true) ++
            none :: metadata)
          [some hit, none])
      have hchain := hstart.trans (hparse.trans (hseek.trans
        (hdelimiter.trans (hreturn.trans (hrestore.trans hbridge)))))
      have hfinal :
          List.replicate
              ((remaining + 1) + (selectorBits tag).length) (some true) ++
              none :: metadata =
            List.replicate (selectorBits tag).length (some true) ++
              (some true ::
                (List.replicate remaining (some true) ++ none :: metadata)) := by
        rw [Nat.add_comm]
        rw [FoC.Computability.list_replicate_add_append]
        rfl
      rw [hfinal] at hchain
      simpa [List.replicate_succ, List.append_assoc] using hchain
  done

theorem leads_ingress_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    (table D).Leads
      ((table D).config (.ingress .start) L.config.tape
        (FieldDecomposition.stageCounterTape L.stage)
        (metadataHitTapeWithSelector D L))
      ((table D).config
          (.core (.base (.dispatch (classifyState D L.config.state))))
        L.config.tape (FieldDecomposition.stageCounterTape L.stage)
        (metadataHitTapeAfterSelectorRestore D L)) := by
  simpa [metadataHitTapeWithSelector, classifiedMetadataLeft,
    remainingScratchMarkers, metadataHitTapeAfterSelectorRestore,
    restoredScratchMarkers, List.append_assoc] using
    leads_ingress_selectorLayout D L.hit (classifyState D L.config.state)
      ((RunConfigEmitterTheory.scratchWidthMarkers L).length -
        (selectorBits (classifyState D L.config.state)).length)
      L.config.tape (FieldDecomposition.stageCounterTape L.stage)
      ((FieldDecomposition.metadataBits L).map some).reverse
  done

theorem firstReaches_eq
    (M : Structured.Description) {steps : Nat}
    {source target : Structured.Configuration}
    (hrun : M.runConfig steps source = target) :
    exists first : Nat,
      first ≤ steps ∧
      M.runConfig first source = target ∧
      forall k : Nat, k < first -> M.runConfig k source ≠ target := by
  induction steps generalizing source with
  | zero =>
      refine ⟨0, Nat.le_refl 0, ?_, ?_⟩
      · simpa [Structured.Description.runConfig] using hrun
      · intro k hk
        lia
  | succ steps ih =>
      by_cases hsource : source = target
      · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
        · simpa [Structured.Description.runConfig] using hsource
        · intro k hk
          lia
      · cases hstep : M.stepConfig source with
        | none =>
            have hsame :=
              Structured.Description.runConfig_of_stepConfig_none
                hstep (Nat.succ steps)
            have : source = target := by
              rw [← hsame]
              exact hrun
            exact False.elim (hsource this)
        | some nextConfig =>
            have hnext : M.runConfig steps nextConfig = target := by
              simpa [Structured.Description.runConfig, hstep] using hrun
            rcases ih hnext with ⟨first, hle, hfirst, hminimal⟩
            refine ⟨first + 1, by lia, ?_, ?_⟩
            · simpa [Structured.Description.runConfig, hstep] using hfirst
            · intro k hk
              cases k with
              | zero =>
                  simpa [Structured.Description.runConfig] using hsource
              | succ k =>
                  have hk' : k < first := by lia
                  simpa [Structured.Description.runConfig, hstep] using
                    hminimal k hk'
  done

theorem closeoutNext_base_of_some
    (D : MachineDescription) (state : LoopDispatcherState D)
    (r0 r1 r2 : Option Bool) (step : TypedStep (LoopDispatcherState D))
    (hnext : loopDispatcherNext D state r0 r1 r2 = some step) :
    loopDispatcherCloseoutNext D (.base state) r0 r1 r2 =
      some (liftDispatcherStep step) := by
  cases state with
  | dispatch tag =>
      simp [loopDispatcherCloseoutNext, hnext]
  | known state =>
      cases state with
      | done state => simp [loopDispatcherNext] at hnext
      | seed state => simp [loopDispatcherCloseoutNext, hnext]
      | loop state => simp [loopDispatcherCloseoutNext, hnext]
      | halt => simp [loopDispatcherCloseoutNext, hnext]
  | other state =>
      cases state with
      | done => simp [loopDispatcherNext] at hnext
      | loop => simp [loopDispatcherCloseoutNext, hnext]
      | halt => simp [loopDispatcherCloseoutNext, hnext]
  | halt =>
      simp [loopDispatcherNext] at hnext
  done

theorem closeout_runConfig_base_of_first
    (D : MachineDescription) (steps : Nat)
    (state : LoopDispatcherState D)
    (hstate : state ∈ loopDispatcherStates D)
    (T0 T1 T2 : Tape Bool) (target : Structured.Configuration)
    (hrun :
      (loopDispatcherTable D).description.runConfig steps
          (ThreeTape.config ((loopDispatcherTable D).stateId state)
            T0 T1 T2) = target)
    (hfirst : forall k : Nat, k < steps ->
      (loopDispatcherTable D).description.runConfig k
          (ThreeTape.config ((loopDispatcherTable D).stateId state)
            T0 T1 T2) ≠ target) :
    (loopDispatcherCloseoutTable D).description.runConfig steps
        (ThreeTape.config
          ((loopDispatcherCloseoutTable D).stateId (.base state))
          T0 T1 T2) =
      target := by
  induction steps generalizing state T0 T1 T2 with
  | zero =>
      change
        ThreeTape.config
            ((loopDispatcherCloseoutTable D).stateId (.base state))
            T0 T1 T2 = target
      change
        ThreeTape.config ((loopDispatcherTable D).stateId state)
            T0 T1 T2 = target at hrun
      simpa [loopDispatcherCloseoutTable,
        loopDispatcherCloseoutStateId_base] using hrun
  | succ steps ih =>
      cases hnext : loopDispatcherNext D state
          (Tape.read T0) (Tape.read T1) (Tape.read T2) with
      | none =>
          have hstepNone := (loopDispatcherTable D).stepConfig_config_none
            hstate hnext
          have hsame :=
            Structured.Description.runConfig_of_stepConfig_none
              hstepNone (Nat.succ steps)
          have heq :
              ThreeTape.config ((loopDispatcherTable D).stateId state)
                T0 T1 T2 = target := by
            rw [← hsame]
            exact hrun
          exact False.elim
            (hfirst 0 (by lia) (by
              simpa [Structured.Description.runConfig] using heq))
      | some step =>
          have hclose := closeoutNext_base_of_some D state
            (Tape.read T0) (Tape.read T1) (Tape.read T2) step hnext
          have htarget := (loopDispatcherTable D).next_target_mem
            state hstate (Tape.read T0) (Tape.read T1) (Tape.read T2)
            step hnext
          have hrunTail :
              (loopDispatcherTable D).description.runConfig steps
                  (ThreeTape.config
                    ((loopDispatcherTable D).stateId step.target)
                    (step.action0.apply T0)
                    (step.action1.apply T1)
                    (step.action2.apply T2)) = target := by
            rw [← (loopDispatcherTable D).runConfig_succ_config
              hstate hnext steps]
            simpa [Nat.succ_eq_add_one] using hrun
          have hfirstTail : forall k : Nat, k < steps ->
              (loopDispatcherTable D).description.runConfig k
                  (ThreeTape.config
                    ((loopDispatcherTable D).stateId step.target)
                    (step.action0.apply T0)
                    (step.action1.apply T1)
                    (step.action2.apply T2)) ≠ target := by
            intro k hk heq
            apply hfirst (k + 1) (by lia)
            rw [(loopDispatcherTable D).runConfig_succ_config
              hstate hnext k]
            exact heq
          rw [(loopDispatcherCloseoutTable D).runConfig_succ_config
            (base_mem_loopDispatcherCloseoutStates hstate) hclose steps]
          exact ih step.target htarget
            (step.action0.apply T0) (step.action1.apply T1)
            (step.action2.apply T2) hrunTail hfirstTail
  done

theorem closeout_runConfig_source_to_endpoint
    (D : MachineDescription) (L : SimulatorLayout) :
    exists steps : Nat,
      (loopDispatcherCloseoutDescription D).runConfig steps
          (loopDispatcherSourceConfig D L) =
        loopDispatcherEndpointConfig D L := by
  have hsemantic := loopDispatcherSemanticEndpoint D L
  rcases firstReaches_eq (loopDispatcherDescription D) hsemantic with
    ⟨steps, _hle, hrun, hfirst⟩
  refine ⟨steps, ?_⟩
  have htransfer := closeout_runConfig_base_of_first D steps
    (.dispatch (classifyState D L.config.state))
    (dispatch_mem_loopDispatcherStates (classifyState D L.config.state))
    L.config.tape (FieldDecomposition.stageCounterTape L.stage)
    (FieldDecomposition.metadataHitTape L)
    (loopDispatcherEndpointConfig D L) hrun hfirst
  simpa [loopDispatcherDescription, loopDispatcherCloseoutDescription,
    loopDispatcherSourceConfig, loopDispatcherCloseoutTable,
    loopDispatcherCloseoutStateId_base] using htransfer
  done

theorem loopDispatcherEndpointState_mem
    (D : MachineDescription) (L : SimulatorLayout) :
    loopDispatcherEndpointState D L ∈ loopDispatcherStates D := by
  by_cases hstate : L.config.state ∈ fixedStepValues D
  · rw [loopDispatcherEndpointState, classifyState_of_mem hstate]
    apply known_mem_loopDispatcherStates
    apply done_mem_knownStateLoopStates
    rw [← RunConfigEmitterTheory.iterateStep_seedHit_eq_run]
    exact iterateStep_config_state_mem_fixedStepValues D
      (RunConfigEmitterTheory.seedHit D L)
      (by simpa [RunConfigEmitterTheory.seedHit] using hstate)
      L.stage
  · rw [loopDispatcherEndpointState, classifyState_of_not_mem hstate]
    exact other_mem_loopDispatcherStates done_mem_otherStateLoopStates
  done

theorem runConfig_core_source_to_endpoint
    (D : MachineDescription) (L : SimulatorLayout) :
    exists steps : Nat,
      (description D).runConfig steps
          ((table D).config
            (.core (.base
              (.dispatch (classifyState D L.config.state))))
            L.config.tape
            (FieldDecomposition.stageCounterTape L.stage)
            (FieldDecomposition.metadataHitTape L)) =
        loopDispatcherEndpointConfig D L := by
  rcases closeout_runConfig_source_to_endpoint D L with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  rw [runConfig_core D steps
    (.base (.dispatch (classifyState D L.config.state)))
    (base_mem_loopDispatcherCloseoutStates
      (dispatch_mem_loopDispatcherStates
        (classifyState D L.config.state)))]
  simpa [loopDispatcherSourceConfig, TypedStateTable.config,
    loopDispatcherCloseoutTable, loopDispatcherCloseoutStateId_base] using hrun
  done

theorem runConfig_core_endpoint_to_halt
    (D : MachineDescription) (L : SimulatorLayout) :
    (description D).runConfig
        (loopDispatcherCloseoutSteps (loopDispatcherDoneWitness D L))
        (loopDispatcherEndpointConfig D L) =
      { state := (description D).halt
        tapes := loopDispatcherDoneWitnessTapes D L } := by
  have hrun := loopDispatcherCloseoutDescription_runConfig_endpoint D L
  have hcore := runConfig_core D
    (loopDispatcherCloseoutSteps (loopDispatcherDoneWitness D L))
    (.base (loopDispatcherEndpointState D L))
    (base_mem_loopDispatcherCloseoutStates
      (loopDispatcherEndpointState_mem D L))
    (SimulatorLayout.run D L.stage L).config.tape
    (loopDispatcherConsumedStageCounterTape L.stage)
    (loopDispatcherHitTape L (SimulatorLayout.run D L.stage L).hit)
  change
    (description D).runConfig
        (loopDispatcherCloseoutSteps (loopDispatcherDoneWitness D L))
        ((table D).config
          (.core (.base (loopDispatcherEndpointState D L)))
          (SimulatorLayout.run D L.stage L).config.tape
          (loopDispatcherConsumedStageCounterTape L.stage)
          (loopDispatcherHitTape L
            (SimulatorLayout.run D L.stage L).hit)) = _
  rw [hcore]
  simpa [loopDispatcherEndpointConfig, description,
    table, stateId, loopDispatcherCloseoutDescription,
    loopDispatcherCloseoutTable, loopDispatcherCloseoutStateId_base,
    TypedStateTable.config] using hrun
  done

theorem description_runConfig_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    exists steps : Nat,
      (description D).runConfig steps
          ((table D).config (.ingress .start)
            L.config.tape
            (FieldDecomposition.stageCounterTape L.stage)
            (metadataHitTapeWithSelector D L)) =
        { state := (description D).halt
          tapes := loopDispatcherDoneWitnessTapes D L } := by
  rcases (leads_ingress_layout D L).to_runConfig with
    ⟨ingressSteps, hingress⟩
  rw [metadataHitTapeAfterSelectorRestore_eq] at hingress
  rcases runConfig_core_source_to_endpoint D L with
    ⟨prefixSteps, hprefix⟩
  have hclose := runConfig_core_endpoint_to_halt D L
  change (table D).description.runConfig prefixSteps _ = _ at hprefix
  change
    (table D).description.runConfig
        (loopDispatcherCloseoutSteps (loopDispatcherDoneWitness D L)) _ = _
      at hclose
  refine
    ⟨ingressSteps +
        (prefixSteps +
          loopDispatcherCloseoutSteps (loopDispatcherDoneWitness D L)), ?_⟩
  change (table D).description.runConfig _ _ = _
  rw [Structured.Description.runConfig_add]
  rw [hingress]
  rw [Structured.Description.runConfig_add]
  rw [hprefix]
  exact hclose
  done

theorem description_wellFormed (D : MachineDescription) :
    (description D).WellFormed :=
  (table D).description_wellFormed

theorem description_haltTransitionFree (D : MachineDescription) :
    (description D).HaltTransitionFree :=
  (table D).description_haltTransitionFree

theorem description_supportsReadWriteRows3 (D : MachineDescription) :
    SupportsReadWriteRows3 (description D) :=
  (table D).description_supportsReadWriteRows3

def entryState (D : MachineDescription) (tag : StateClass D) : Nat :=
  (table D).stateId (.core (.base (.dispatch tag)))

theorem selectorIngressEndpointSpec
    (D : MachineDescription) :
    FieldDecomposition.ClassifiedBoundary.SelectorIngressEndpointSpec
      D (description D) (entryState D) := by
  refine
    ⟨description_wellFormed D,
      description_haltTransitionFree D,
      description_supportsReadWriteRows3 D, ?_, ?_⟩
  · intro tag
    exact (table D).stateId_lt _
      (core_mem_states
        (base_mem_loopDispatcherCloseoutStates
          (dispatch_mem_loopDispatcherStates tag)))
  · intro L
    rcases (leads_ingress_layout D L).to_runConfig with ⟨steps, hrun⟩
    refine ⟨steps, ?_⟩
    rw [metadataHitTapeAfterSelectorRestore_eq] at hrun
    change
      (table D).description.runConfig steps
          ((table D).config (table D).start
            L.config.tape
            (FieldDecomposition.stageCounterTape L.stage)
            (metadataHitTapeWithSelector D L)) = _ at hrun
    simpa [entryState, description, TypedStateTable.config] using hrun
  done

def loweredDescription (D : MachineDescription) : MachineDescription :=
  lowerStructured3Description (description D)

theorem loweredDescription_subroutineReady (D : MachineDescription) :
    (loweredDescription D).SubroutineReady :=
  lowerStructured3Description_subroutineReady
    (description_wellFormed D)
    (description_supportsReadWriteRows3 D)

theorem loweredDescription_haltsFromTapeEquiv
    (D : MachineDescription) (L : SimulatorLayout) :
    (loweredDescription D).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes
        [ L.config.tape
        , FieldDecomposition.stageCounterTape L.stage
        , metadataHitTapeWithSelector D L ])
      (encodedGuardedStructuredTapes
        (loopDispatcherDoneWitnessTapes D L)) := by
  unfold loweredDescription
  apply lowerStructured3Description_haltsFromConfigWithTapes
    (description_wellFormed D)
    (description_haltTransitionFree D)
    (description_supportsReadWriteRows3 D)
    (c := (table D).config (.ingress .start)
      L.config.tape
      (FieldDecomposition.stageCounterTape L.stage)
      (metadataHitTapeWithSelector D L))
  · rfl
  · rfl
  · rcases description_runConfig_layout D L with ⟨steps, hrun⟩
    exact ⟨steps, hrun⟩
  done

end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.SelectorSplice
