import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Runs

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

def AllSome (xs : List (Option Bool)) : Prop :=
  ∀ x : Option Bool, x ∈ xs → ∃ bit : Bool, x = some bit

theorem allSome_cells (bits : Word Bool) : AllSome (cells bits) := by
  intro x hx
  unfold cells at hx
  rcases List.mem_map.mp hx with ⟨bit, _hbit, rfl⟩
  exact ⟨bit, rfl⟩

theorem replicate_succ_append_none (n : Nat)
    (right : List (Option Bool)) :
    List.append (List.replicate (n + 1) none) (none :: right) =
      List.append (List.replicate (n + 2) none) right := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change none ::
          List.append (List.replicate (n + 1) none) (none :: right) =
        none :: List.append (List.replicate (n + 2) none) right
      rw [ih]

theorem allSome_tail {x : Option Bool} {xs : List (Option Bool)}
    (h : AllSome (x :: xs)) : AllSome xs := by
  intro y hy
  exact h y (by simp [hy])

theorem allSome_pushWord (bits : Word Bool)
    (left : List (Option Bool)) (hleft : AllSome left) :
    AllSome (pushWord bits left) := by
  intro x hx
  rw [pushWord] at hx
  rcases List.mem_append.mp hx with hx | hx
  · have hrev : x ∈ cells bits := List.mem_reverse.mp hx
    exact allSome_cells bits x hrev
  · exact hleft x hx

theorem leads_eraseRight_bit {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bit : Bool) (L0 right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .eraseRight
        (tapeAtCells L0 (some bit :: right)) T1 T2)
      (cfg attempt hattempt .eraseRight
        (tapeAtCells (some bit :: L0) right) T1 T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.eraseRight)
      (T0 := tapeAtCells L0 (some bit :: right)) (T1 := T1) (T2 := T2)
      (st := ⟨CoreState.eraseRight, keepR, keepS, keepS⟩)
      (T0' := tapeAtCells (some bit :: L0) right) (T1' := T1) (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl)
      (keepR_apply_tapeAtCells L0 (some bit) right) rfl rfl

theorem leads_eraseRight_word {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bits : Word Bool) (L0 : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .eraseRight
        (tapeAtCells L0 (cells bits)) T1 T2)
      (cfg attempt hattempt .eraseRight
        (tapeAtCells (pushWord bits L0) []) T1 T2) := by
  induction bits generalizing L0 with
  | nil => exact Leads.refl _ _ _
  | cons bit rest ih =>
      refine (leads_eraseRight_bit (attempt := attempt)
        (hattempt := hattempt) bit L0 (cells rest) T1 T2).trans ?_
      simpa only [pushWord_cons] using ih (some bit :: L0)

theorem leads_eraseRight_end {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bit : Bool) (left : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .eraseRight
        (tapeAtCells (some bit :: left) []) T1 T2)
      (cfg attempt hattempt .eraseLeft
        (tapeAtCells left [some bit, none]) T1 T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.eraseRight)
      (T0 := tapeAtCells (some bit :: left) []) (T1 := T1) (T2 := T2)
      (st := ⟨CoreState.eraseLeft, keepL, keepS, keepS⟩)
      (T0' := tapeAtCells left [some bit, none]) (T1' := T1) (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl)
      (keepL_apply_tapeAtCells_nil left (some bit)) rfl rfl

theorem leads_eraseLeft_all {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (left : List (Option Bool)) (hleft : AllSome left)
    (bit : Bool) (right : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .eraseLeft
        (tapeAtCells left (some bit :: right)) T1 T2)
      (cfg attempt hattempt .eraseLeft
        (tapeAtCells []
          (none :: List.append (List.replicate (left.length + 1) none) right))
        T1 T2) := by
  induction left generalizing bit right with
  | nil =>
      have h0 : eraseL.apply (tapeAtCells [] (some bit :: right)) =
          tapeAtCells [] (none :: none :: right) := by
        cases right <;> rfl
      simpa [Leads, cfg] using
        TypedStateTable.leads_step (table attempt hattempt)
          (s := CoreState.eraseLeft)
          (T0 := tapeAtCells [] (some bit :: right)) (T1 := T1) (T2 := T2)
          (st := ⟨CoreState.eraseLeft, eraseL, keepS, keepS⟩)
          (T0' := tapeAtCells [] (none :: none :: right))
          (T1' := T1) (T2' := T2)
          (mem_states_of_stateBounded trivial) (by rfl) h0 rfl rfl
  | cons cell rest ih =>
      rcases hleft cell (by simp) with ⟨prev, rfl⟩
      have h0 :
          eraseL.apply
              (tapeAtCells (some prev :: rest) (some bit :: right)) =
            tapeAtCells rest (some prev :: none :: right) := by
        cases right <;> rfl
      have hstep : Leads attempt hattempt
          (cfg attempt hattempt .eraseLeft
            (tapeAtCells (some prev :: rest) (some bit :: right)) T1 T2)
          (cfg attempt hattempt .eraseLeft
            (tapeAtCells rest (some prev :: none :: right)) T1 T2) := by
        simpa [Leads, cfg] using
          TypedStateTable.leads_step (table attempt hattempt)
            (s := CoreState.eraseLeft)
            (T0 := tapeAtCells (some prev :: rest) (some bit :: right))
            (T1 := T1) (T2 := T2)
            (st := ⟨CoreState.eraseLeft, eraseL, keepS, keepS⟩)
            (T0' := tapeAtCells rest (some prev :: none :: right))
            (T1' := T1) (T2' := T2)
            (mem_states_of_stateBounded trivial) (by rfl) h0 rfl rfl
      refine hstep.trans ?_
      have hih := ih (allSome_tail hleft) prev (none :: right)
      rw [replicate_succ_append_none rest.length right] at hih
      simpa only [List.length_cons, Nat.succ_eq_add_one] using hih

theorem leads_eraseLeft_finish {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (right0 left1 : List (Option Bool)) (bit : Bool) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .eraseLeft
        (tapeAtCells [] (none :: right0))
        (tapeAtCells (some bit :: left1) []) T2)
      (cfg attempt hattempt .auxLeft
        (tapeAtCells [none] right0)
        (tapeAtCells left1 [some bit, none]) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.eraseLeft)
      (T0 := tapeAtCells [] (none :: right0))
      (T1 := tapeAtCells (some bit :: left1) []) (T2 := T2)
      (st := ⟨CoreState.auxLeft, keepR, keepL, keepS⟩)
      (T0' := tapeAtCells [none] right0)
      (T1' := tapeAtCells left1 [some bit, none]) (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl)
      (keepR_apply_tapeAtCells [] none right0)
      (keepL_apply_tapeAtCells_nil left1 (some bit)) rfl

theorem leads_auxLeft_bit {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (prev bit : Bool) (left right : List (Option Bool))
    (T0 T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .auxLeft T0
        (tapeAtCells (some prev :: left) (some bit :: right)) T2)
      (cfg attempt hattempt .auxLeft T0
        (tapeAtCells left (some prev :: some bit :: right)) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.auxLeft) (T0 := T0)
      (T1 := tapeAtCells (some prev :: left) (some bit :: right)) (T2 := T2)
      (st := ⟨CoreState.auxLeft, keepS, keepL, keepS⟩)
      (T0' := T0)
      (T1' := tapeAtCells left (some prev :: some bit :: right)) (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl) rfl
      (keepL_apply_tapeAtCells left (some prev) (some bit) right) rfl

theorem leads_auxLeft_boundary {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bit : Bool) (right : List (Option Bool)) (T0 T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .auxLeft T0
        (tapeAtCells [] (some bit :: right)) T2)
      (cfg attempt hattempt .reconstruct T0
        (tapeAtCells [none] (some bit :: right)) T2) := by
  have hleft :
      keepL.apply (tapeAtCells [] (some bit :: right)) =
        tapeAtCells [] (none :: some bit :: right) :=
    keepL_apply_tapeAtCells_left_nil (some bit) right
  have hright :
      keepR.apply (tapeAtCells [] (none :: some bit :: right)) =
        tapeAtCells [none] (some bit :: right) :=
    keepR_apply_tapeAtCells [] none (some bit :: right)
  have hfirst : Leads attempt hattempt
      (cfg attempt hattempt .auxLeft T0
        (tapeAtCells [] (some bit :: right)) T2)
      (cfg attempt hattempt .auxLeft T0
        (tapeAtCells [] (none :: some bit :: right)) T2) := by
    simpa [Leads, cfg] using
      TypedStateTable.leads_step (table attempt hattempt)
        (s := CoreState.auxLeft) (T0 := T0)
        (T1 := tapeAtCells [] (some bit :: right)) (T2 := T2)
        (st := ⟨CoreState.auxLeft, keepS, keepL, keepS⟩)
        (T0' := T0)
        (T1' := tapeAtCells [] (none :: some bit :: right)) (T2' := T2)
        (mem_states_of_stateBounded trivial) (by rfl) rfl hleft rfl
  refine hfirst.trans ?_
  exact (by
    simpa [Leads, cfg] using
      TypedStateTable.leads_step (table attempt hattempt)
        (s := CoreState.auxLeft) (T0 := T0)
        (T1 := tapeAtCells [] (none :: some bit :: right)) (T2 := T2)
        (st := ⟨CoreState.reconstruct, keepS, keepR, keepS⟩)
        (T0' := T0)
        (T1' := tapeAtCells [none] (some bit :: right)) (T2' := T2)
        (mem_states_of_stateBounded trivial) (by rfl) rfl hright rfl)

theorem leads_auxLeft_all {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (left : List (Option Bool)) (hleft : AllSome left)
    (bit : Bool) (right : List (Option Bool)) (T0 T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .auxLeft T0
        (tapeAtCells left (some bit :: right)) T2)
      (cfg attempt hattempt .reconstruct T0
        (tapeAtCells [none]
          (List.append left.reverse (some bit :: right))) T2) := by
  induction left generalizing bit right with
  | nil =>
      simpa using leads_auxLeft_boundary (attempt := attempt)
        (hattempt := hattempt) bit right T0 T2
  | cons cell rest ih =>
      rcases hleft cell (by simp) with ⟨prev, rfl⟩
      refine (leads_auxLeft_bit (attempt := attempt) (hattempt := hattempt)
        prev bit rest right T0 T2).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        (ih (allSome_tail hleft) prev (some bit :: right))

theorem parsedInputLeft1_reverse (C : DovetailControllerLayout) :
    (parsedInputLeft1 C).reverse = cells (stageInputBits C) := by
  have h : parsedInputLeft1 C = pushWord (stageInputBits C) [] := by
    rw [stageInputBits_eq, pushWord_append, pushWord_append]
    rfl
  rw [h, pushWord]
  simp

theorem allSome_parsedInputLeft0 (C : DovetailControllerLayout) :
    AllSome (parsedInputLeft0 C) := by
  unfold parsedInputLeft0
  apply allSome_pushWord
  apply allSome_pushWord
  apply allSome_pushWord
  intro x hx
  simp at hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals exact ⟨false, rfl⟩

theorem allSome_parsedInputLeft1 (C : DovetailControllerLayout) :
    AllSome (parsedInputLeft1 C) := by
  unfold parsedInputLeft1
  exact allSome_pushWord _ _
    (allSome_pushWord _ _ (allSome_pushWord _ _ (by simp [AllSome])))

theorem resultBits_ne_nil (w : Word Bool) : resultBits w ≠ [] := by
  change encodeCodeWordAsInput (encodeBoolWordAppend w []) ≠ []
  rw [EncRewriters.CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
  rcases EncRewriters.CanonicalLayouts.DovetailLayoutScanner.stageNatBits_cons_false
      w.length with ⟨tail, htail⟩
  rw [htail]
  simp

theorem pushWord_ne_nil (bits : Word Bool) (left : List (Option Bool))
    (hbits : bits ≠ []) : pushWord bits left ≠ [] := by
  cases bits with
  | nil => exact False.elim (hbits rfl)
  | cons bit rest =>
      intro h
      have hlen := congrArg List.length h
      simp [pushWord, cells] at hlen

def pushFalseWord : Word Bool -> List (Option Bool) -> List (Option Bool)
  | [], left => left
  | _ :: rest, left => pushFalseWord rest (some false :: left)

theorem replicate_append_cons_false (n : Nat)
    (left : List (Option Bool)) :
    List.append (List.replicate n (some false)) (some false :: left) =
      some false :: List.append (List.replicate n (some false)) left := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change some false ::
          List.append (List.replicate n (some false)) (some false :: left) =
        some false :: some false ::
          List.append (List.replicate n (some false)) left
      rw [ih]

theorem pushFalseWord_eq (bits : Word Bool) (left : List (Option Bool)) :
    pushFalseWord bits left =
      List.append (List.replicate bits.length (some false)) left := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit rest ih =>
      rw [pushFalseWord, ih]
      rw [replicate_append_cons_false]
      rfl

theorem cells_cons (bit : Bool) (rest : Word Bool) :
    cells (bit :: rest) = some bit :: cells rest := rfl

theorem leads_reconstruct_bit {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bit : Bool) (L0 L1 tail0 tail1 : List (Option Bool))
    (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .reconstruct
        (tapeAtCells L0 (none :: tail0))
        (tapeAtCells L1 (some bit :: tail1)) T2)
      (cfg attempt hattempt .reconstruct
        (tapeAtCells (some bit :: L0) tail0)
        (tapeAtCells (some false :: L1) tail1) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.reconstruct)
      (T0 := tapeAtCells L0 (none :: tail0))
      (T1 := tapeAtCells L1 (some bit :: tail1)) (T2 := T2)
      (st := ⟨CoreState.reconstruct,
        writeR (some bit), writeR (some false), keepS⟩)
      (T0' := tapeAtCells (some bit :: L0) tail0)
      (T1' := tapeAtCells (some false :: L1) tail1) (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl)
      (writeR_apply_tapeAtCells (some bit) L0 none tail0)
      (writeR_apply_tapeAtCells (some false) L1 (some bit) tail1) rfl

theorem leads_reconstruct_word {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bits : Word Bool) (L0 L1 tail0 tail1 : List (Option Bool))
    (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .reconstruct
        (tapeAtCells L0
          (List.append (List.replicate bits.length none) tail0))
        (tapeAtCells L1 (List.append (cells bits) tail1)) T2)
      (cfg attempt hattempt .reconstruct
        (tapeAtCells (pushWord bits L0) tail0)
        (tapeAtCells (pushFalseWord bits L1) tail1) T2) := by
  induction bits generalizing L0 L1 with
  | nil => exact Leads.refl _ _ _
  | cons bit rest ih =>
      simp only [List.length_cons, List.replicate_succ, cells_cons]
      refine (leads_reconstruct_bit (attempt := attempt) (hattempt := hattempt)
        bit L0 L1 _ _ T2).trans ?_
      simpa only [pushWord_cons, pushFalseWord] using
        (ih (some bit :: L0) (some false :: L1))

theorem leads_workLeft_step {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (prev current : Option Bool)
    (left0 left1 right0 right1 : List (Option Bool)) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .workLeft
        (tapeAtCells (prev :: left0) (current :: right0))
        (tapeAtCells (some false :: left1) (some false :: right1)) T2)
      (cfg attempt hattempt .workLeft
        (tapeAtCells left0 (prev :: current :: right0))
        (tapeAtCells left1 (some false :: some false :: right1)) T2) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.workLeft)
      (T0 := tapeAtCells (prev :: left0) (current :: right0))
      (T1 := tapeAtCells (some false :: left1) (some false :: right1))
      (T2 := T2)
      (st := ⟨CoreState.workLeft, keepL, keepL, keepS⟩)
      (T0' := tapeAtCells left0 (prev :: current :: right0))
      (T1' := tapeAtCells left1 (some false :: some false :: right1))
      (T2' := T2) (mem_states_of_stateBounded trivial) (by rfl)
      (keepL_apply_tapeAtCells left0 prev current right0)
      (keepL_apply_tapeAtCells left1 (some false) (some false) right1) rfl

theorem leads_workLeft_boundary {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (current : Option Bool) (right0 right1 : List (Option Bool))
    (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .workLeft
        (tapeAtCells [none] (current :: right0))
        (tapeAtCells [none] (some false :: right1)) T2)
      (cfg attempt hattempt (.run attempt.start)
        (tapeAtCells [none] (current :: right0))
        (tapeAtCells [none] (some false :: right1)) T2) := by
  have h0L := keepL_apply_tapeAtCells [] none current right0
  have h1L := keepL_apply_tapeAtCells [] none (some false) right1
  have h0R := keepR_apply_tapeAtCells [] none (current :: right0)
  have h1R := keepR_apply_tapeAtCells [] none (some false :: right1)
  have hfirst : Leads attempt hattempt
      (cfg attempt hattempt .workLeft
        (tapeAtCells [none] (current :: right0))
        (tapeAtCells [none] (some false :: right1)) T2)
      (cfg attempt hattempt .workLeft
        (tapeAtCells [] (none :: current :: right0))
        (tapeAtCells [] (none :: some false :: right1)) T2) := by
    simpa [Leads, cfg] using
      TypedStateTable.leads_step (table attempt hattempt)
        (s := CoreState.workLeft)
        (T0 := tapeAtCells [none] (current :: right0))
        (T1 := tapeAtCells [none] (some false :: right1)) (T2 := T2)
        (st := ⟨CoreState.workLeft, keepL, keepL, keepS⟩)
        (T0' := tapeAtCells [] (none :: current :: right0))
        (T1' := tapeAtCells [] (none :: some false :: right1)) (T2' := T2)
        (mem_states_of_stateBounded trivial) (by rfl) h0L h1L rfl
  refine hfirst.trans ?_
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (s := CoreState.workLeft)
      (T0 := tapeAtCells [] (none :: current :: right0))
      (T1 := tapeAtCells [] (none :: some false :: right1)) (T2 := T2)
      (st := ⟨CoreState.run attempt.start, keepR, keepR, keepS⟩)
      (T0' := tapeAtCells [none] (current :: right0))
      (T1' := tapeAtCells [none] (some false :: right1)) (T2' := T2)
      (mem_states_of_stateBounded trivial) (by rfl) h0R h1R rfl

theorem leads_workLeft_all {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (left0 : List (Option Bool)) (current : Option Bool)
    (right0 right1 : List (Option Bool)) (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .workLeft
        (tapeAtCells (List.append left0 [none]) (current :: right0))
        (tapeAtCells
          (List.append (List.replicate left0.length (some false)) [none])
          (some false :: right1)) T2)
      (cfg attempt hattempt (.run attempt.start)
        (tapeAtCells [none]
          (List.append left0.reverse (current :: right0)))
        (tapeAtCells [none]
          (List.append
            (List.replicate (left0.length + 1) (some false)) right1)) T2) := by
  induction left0 generalizing current right0 right1 with
  | nil =>
      simpa using leads_workLeft_boundary (attempt := attempt)
        (hattempt := hattempt) current right0 right1 T2
  | cons prev rest ih =>
      simp only [List.length_cons, List.replicate_succ]
      refine (leads_workLeft_step (attempt := attempt) (hattempt := hattempt)
        prev current (List.append rest [none])
        (List.append (List.replicate rest.length (some false)) [none])
        right0 right1 T2).trans ?_
      have hih := ih prev (current :: right0) (some false :: right1)
      have hmarker :
          List.append (List.replicate (rest.length + 1) (some false))
              (some false :: right1) =
            some false :: some false ::
              List.append (List.replicate rest.length (some false)) right1 := by
        rw [List.replicate_succ]
        change some false ::
            List.append (List.replicate rest.length (some false))
              (some false :: right1) = _
        exact congrArg (fun xs => some false :: xs)
          (replicate_append_cons_false rest.length right1)
      rw [hmarker] at hih
      simpa [List.reverse_cons, List.append_assoc, List.replicate_succ] using hih

theorem cells_length (bits : Word Bool) : (cells bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      change (some bit :: cells rest).length = (bit :: rest).length
      simp [ih]

theorem leads_reconstruct_and_rewind {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bits : Word Bool) (hbits : bits ≠ [])
    (blank : Option Bool) (right0 right1 : List (Option Bool))
    (T2 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .reconstruct
        (tapeAtCells [none]
          (List.append (List.replicate bits.length none) (blank :: right0)))
        (tapeAtCells [none]
          (List.append (cells bits) (none :: right1))) T2)
      (cfg attempt hattempt (.run attempt.start)
        (tapeAtCells [none]
          (List.append (cells bits) (blank :: right0)))
        (tapeAtCells [none]
          (List.append (List.replicate bits.length (some false))
            (none :: right1))) T2) := by
  refine (leads_reconstruct_word (attempt := attempt) (hattempt := hattempt)
    bits [none] [none] (blank :: right0) (none :: right1) T2).trans ?_
  cases hrev : (cells bits).reverse with
  | nil =>
      have hlen := congrArg List.length hrev
      simp [cells_length] at hlen
      exact False.elim (hbits hlen)
  | cons current left0 =>
      have hlen0 : bits.length = left0.length + 1 := by
        have hlen := congrArg List.length hrev
        simpa [cells_length] using hlen
      have hp0 : pushWord bits [none] =
          current :: List.append left0 [none] := by
        rw [pushWord, hrev]
        rfl
      have hp1 : pushFalseWord bits [none] =
          some false ::
            List.append (List.replicate left0.length (some false)) [none] := by
        rw [pushFalseWord_eq, hlen0, List.replicate_succ]
        rfl
      rw [hp0, hp1]
      have hstep : Leads attempt hattempt
          (cfg attempt hattempt .reconstruct
            (tapeAtCells (current :: List.append left0 [none])
              (blank :: right0))
            (tapeAtCells
              (some false ::
                List.append (List.replicate left0.length (some false)) [none])
              (none :: right1)) T2)
          (cfg attempt hattempt .workLeft
            (tapeAtCells (List.append left0 [none])
              (current :: blank :: right0))
            (tapeAtCells
              (List.append (List.replicate left0.length (some false)) [none])
              (some false :: none :: right1)) T2) := by
        simpa [Leads, cfg] using
          TypedStateTable.leads_step (table attempt hattempt)
            (s := CoreState.reconstruct)
            (T0 := tapeAtCells (current :: List.append left0 [none])
              (blank :: right0))
            (T1 := tapeAtCells
              (some false ::
                List.append (List.replicate left0.length (some false)) [none])
              (none :: right1)) (T2 := T2)
            (st := ⟨CoreState.workLeft, keepL, keepL, keepS⟩)
            (T0' := tapeAtCells (List.append left0 [none])
              (current :: blank :: right0))
            (T1' := tapeAtCells
              (List.append (List.replicate left0.length (some false)) [none])
              (some false :: none :: right1)) (T2' := T2)
            (mem_states_of_stateBounded trivial) (by rfl)
            (keepL_apply_tapeAtCells (List.append left0 [none])
              current blank right0)
            (keepL_apply_tapeAtCells
              (List.append (List.replicate left0.length (some false)) [none])
              (some false) none right1) rfl
      refine hstep.trans ?_
      have hcells : cells bits =
          List.append left0.reverse [current] := by
        have hr := congrArg List.reverse hrev
        simpa using hr
      simpa [hcells, hlen0, List.append_assoc] using
        (leads_workLeft_all (attempt := attempt) (hattempt := hattempt)
          left0 current (blank :: right0) (none :: right1) T2)

theorem pushWord_length (bits : Word Bool) (left : List (Option Bool)) :
    (pushWord bits left).length = bits.length + left.length := by
  simp [pushWord, cells_length]

theorem parsedInputLeft0_eq (C : DovetailControllerLayout) :
    parsedInputLeft0 C =
      pushWord (stageInputBits C)
        [some false, some false, some false, some false] := by
  rw [stageInputBits_eq, pushWord_append, pushWord_append]
  rfl

theorem parsedInputLeft0_length (C : DovetailControllerLayout) :
    (parsedInputLeft0 C).length = (stageInputBits C).length + 4 := by
  rw [parsedInputLeft0_eq, pushWord_length]
  rfl

theorem stageInputBits_ne_nil (C : DovetailControllerLayout) :
    stageInputBits C ≠ [] := by
  rw [stageInputBits_eq]
  rcases
      EncRewriters.CanonicalLayouts.DovetailLayoutScanner.stageNatBits_cons_false
        C.input.length with
    ⟨tail, htail⟩
  rw [htail]
  simp

theorem reconstructedTape_equiv_input (bits : Word Bool)
    (hbits : bits ≠ []) (padding : Nat) :
    Tape.Equiv
      (tapeAtCells [none]
        (List.append (cells bits)
          (List.replicate (padding + 1) none)))
      (Tape.input bits) := by
  cases bits with
  | nil => exact False.elim (hbits rfl)
  | cons bit rest =>
      change Word Bool at rest
      constructor
      · rfl
      constructor
      · rfl
      · change
          Tape.dropTrailingNone
              (List.append (cells rest)
                (List.replicate (padding + 1) none)) =
            Tape.dropTrailingNone (cells rest)
        exact dropTrailingNone_append_replicate_none
          (cells rest) (padding + 1)

def markerTape (bits : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append (List.replicate bits.length (some false)) [none])

def reconstructedTape (bits result : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append (cells bits)
      (List.replicate (result.length + 5) none))

theorem cleanup_blanks_split (n m : Nat) :
    List.append
        (List.replicate (n + (m + 4)) (none : Option Bool)) [none] =
      List.append (List.replicate n none)
        (none :: List.append (List.replicate (m + 3) none) [none]) := by
  calc
    List.append (List.replicate (n + (m + 4)) none) [none] =
        List.append (List.replicate n none)
          (List.append (List.replicate (m + 4) none) [none]) :=
      list_replicate_add_append none n (m + 4) [none]
    _ = List.append (List.replicate n none)
          (none :: List.append (List.replicate (m + 3) none) [none]) := by
      congr 1

theorem cleanup_padding_eq (m : Nat) :
    none :: List.append (List.replicate (m + 3) (none : Option Bool)) [none] =
      List.replicate (m + 5) none := by
  have hout : List.replicate ((m + 4) + 1) (none : Option Bool) =
      none :: List.replicate (m + 4) none := List.replicate_succ
  rw [show m + 5 = (m + 4) + 1 by lia, hout]
  congr 1
  have h := list_replicate_append_self (none : Option Bool) (m + 3) []
  rw [List.append_nil] at h
  exact h

theorem reconstructedTape_equiv_input_result
    (bits result : Word Bool) (hbits : bits ≠ []) :
    Tape.Equiv (reconstructedTape bits result) (Tape.input bits) := by
  simpa [reconstructedTape, Nat.add_assoc] using
    (reconstructedTape_equiv_input bits hbits (result.length + 4))

theorem leads_cleanup_to_run_start {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bits result : Word Bool) (hbits : bits ≠ []) (hresult : result ≠ [])
    (L0 L1 : List (Option Bool)) (T2 : Tape Bool)
    (hlen0 : L0.length = bits.length + 4)
    (hrev1 : L1.reverse = cells bits)
    (hall0 : AllSome L0) (hall1 : AllSome L1) :
    Leads attempt hattempt
      (cfg attempt hattempt .eraseRight
        (tapeAtCells L0 (cells result)) (tapeAtCells L1 []) T2)
      (cfg attempt hattempt (.run attempt.start)
        (reconstructedTape bits result) (markerTape bits) T2) := by
  have hall : AllSome (pushWord result L0) :=
    allSome_pushWord result L0 hall0
  have hne : pushWord result L0 ≠ [] :=
    pushWord_ne_nil result L0 hresult
  rcases List.exists_cons_of_ne_nil hne with ⟨cell, left, hleft⟩
  rcases hall cell (by rw [hleft]; simp) with ⟨bit, hcell⟩
  subst cell
  have hallLeft : AllSome left := by
    rw [hleft] at hall
    exact allSome_tail hall
  have hlen : left.length + 1 = bits.length + (result.length + 4) := by
    have h := congrArg List.length hleft
    rw [pushWord_length, hlen0] at h
    simp at h
    lia
  have hL1ne : L1 ≠ [] := by
    intro hnil
    have hcells : cells bits = [] := by
      simpa [hnil] using hrev1.symm
    have hbLen := congrArg List.length hcells
    rw [cells_length] at hbLen
    exact hbits (List.eq_nil_of_length_eq_zero hbLen)
  rcases List.exists_cons_of_ne_nil hL1ne with ⟨cell1, left1, hleft1⟩
  rcases hall1 cell1 (by rw [hleft1]; simp) with ⟨bit1, hcell1⟩
  subst cell1
  have hallLeft1 : AllSome left1 := by
    rw [hleft1] at hall1
    exact allSome_tail hall1
  have hshape1 :
      List.append left1.reverse (some bit1 :: [none]) =
        List.append (cells bits) [none] := by
    calc
      List.append left1.reverse (some bit1 :: [none]) =
          List.append (List.append left1.reverse [some bit1]) [none] :=
        (List.append_assoc left1.reverse [some bit1] [none]).symm
      _ = List.append L1.reverse [none] := by
        apply congrArg (fun xs => List.append xs [none])
        have hr := congrArg List.reverse hleft1
        simpa [List.reverse_cons] using hr.symm
      _ = List.append (cells bits) [none] := by rw [hrev1]
  refine (leads_eraseRight_word (attempt := attempt) (hattempt := hattempt)
    result L0 (tapeAtCells L1 []) T2).trans ?_
  rw [hleft]
  refine (leads_eraseRight_end (attempt := attempt) (hattempt := hattempt)
    bit left (tapeAtCells L1 []) T2).trans ?_
  refine (leads_eraseLeft_all (attempt := attempt) (hattempt := hattempt)
    left hallLeft bit [none] (tapeAtCells L1 []) T2).trans ?_
  rw [hleft1]
  refine (leads_eraseLeft_finish (attempt := attempt) (hattempt := hattempt)
    (List.append (List.replicate (left.length + 1) none) [none])
    left1 bit1 T2).trans ?_
  refine (leads_auxLeft_all (attempt := attempt) (hattempt := hattempt)
    left1 hallLeft1 bit1 [none]
    (tapeAtCells [none]
      (List.append (List.replicate (left.length + 1) none) [none])) T2).trans ?_
  rw [hshape1, hlen, cleanup_blanks_split]
  rw [cleanup_padding_eq]
  have hrun :=
    leads_reconstruct_and_rewind (attempt := attempt) (hattempt := hattempt)
      bits hbits none
      (List.append (List.replicate (result.length + 3) none) [none])
      [] T2
  rw [cleanup_padding_eq] at hrun
  simpa [reconstructedTape, markerTape] using hrun

theorem leads_controller_to_run_start {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady} (C : DovetailControllerLayout) :
    Leads attempt hattempt
      (cfg attempt hattempt .header0
        (Tape.input
          (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits C))
        Tape.blank Tape.blank)
      (cfg attempt hattempt (.run attempt.start)
        (reconstructedTape (stageInputBits C) (resultBits C.result))
        (markerTape (stageInputBits C))
        (tapeAtCells (parsedInputLeft2 C) [])) := by
  refine (leads_parse_controller (attempt := attempt) (hattempt := hattempt)
    C).trans ?_
  exact leads_cleanup_to_run_start
    (attempt := attempt) (hattempt := hattempt)
    (stageInputBits C) (resultBits C.result)
    (stageInputBits_ne_nil C) (resultBits_ne_nil C.result)
    (parsedInputLeft0 C) (parsedInputLeft1 C)
    (tapeAtCells (parsedInputLeft2 C) [])
    (parsedInputLeft0_length C) (parsedInputLeft1_reverse C)
    (allSome_parsedInputLeft0 C) (allSome_parsedInputLeft1 C)

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
