import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Sequence semantics for machine-description subroutines

This module contains reusable execution facts for sequencing finite
machine-description fragments and subroutines.
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription
namespace Fragment

theorem lookup_seq_left
    {A B : Fragment} {handoffMove : Direction}
    (hB : B.WellFormed)
    {state : Nat} {cell : Option Bool}
    (hstate : state < A.stateCount)
    (hnotExit : state ≠ A.exit) :
    (seq A B handoffMove).toDescription.lookupTransition state cell =
      A.toDescription.lookupTransition state cell := by
  unfold MachineDescription.lookupTransition
  simp [MachineDescription.Fragment.seq,
    MachineDescription.Fragment.toDescription, List.find?_append]
  cases hfindA :
      List.find? (MachineDescription.Matches state cell)
        A.transitions with
  | some t =>
      simp
  | none =>
      have hfindH :
          List.find? (MachineDescription.Matches state cell)
            (handoffTransitions A.exit
              (A.stateCount + B.entry) handoffMove) = none := by
        rw [List.find?_eq_none]
        intro t ht hmatch
        simp [handoffTransitions, branchOnCell,
          preserveTransition, transition] at ht
        rcases ht with rfl | rfl | rfl
        · rcases (by
            simpa [MachineDescription.Matches] using hmatch) with
            ⟨hsource, _hread⟩
          exact hnotExit hsource.symm
        · rcases (by
            simpa [MachineDescription.Matches] using hmatch) with
            ⟨hsource, _hread⟩
          exact hnotExit hsource.symm
        · rcases (by
            simpa [MachineDescription.Matches] using hmatch) with
            ⟨hsource, _hread⟩
          exact hnotExit hsource.symm
      have hfindB :
          List.find? (MachineDescription.Matches state cell)
            (B.transitions.map
              (TransitionDescription.offsetStates A.stateCount)) =
            none := by
        apply (List.find?_eq_none).mpr
        intro t ht hmatch
        rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
        have hbaseSource :
            base.source < B.stateCount :=
          (hB.right.right.right.left base hbase).left
        have hmatchPair :
            A.stateCount + base.source = state ∧ base.read = cell := by
          simpa [MachineDescription.Matches,
            TransitionDescription.offsetStates] using hmatch
        have hsource :
            A.stateCount + base.source = state :=
          hmatchPair.left
        omega
      simpa [hfindA, hfindH, List.find?_eq_none] using hfindB

theorem stepConfig_seq_left
    {A B : Fragment} {handoffMove : Direction}
    (hB : B.WellFormed)
    {c : MachineDescription.Configuration}
    (hstate : c.state < A.stateCount)
    (hnotExit : c.state ≠ A.exit) :
    (seq A B handoffMove).toDescription.stepConfig c =
      A.toDescription.stepConfig c := by
  simp [MachineDescription.stepConfig,
    lookup_seq_left hB hstate hnotExit]

theorem runConfig_seq_left_of_no_exit
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {n : Nat} {c : MachineDescription.Configuration}
    (hstate : c.state < A.stateCount)
    (hnoExit : forall k : Nat,
      k < n ->
        (A.toDescription.runConfig k c).state ≠ A.exit) :
    (seq A B handoffMove).toDescription.runConfig n c =
      A.toDescription.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hcNotExit : c.state ≠ A.exit := by
        simpa [MachineDescription.runConfig] using
          hnoExit 0 (Nat.succ_pos n)
      have hstepSeq :
          (seq A B handoffMove).toDescription.stepConfig c =
            A.toDescription.stepConfig c :=
        stepConfig_seq_left hB hstate hcNotExit
      cases hstepA : A.toDescription.stepConfig c with
      | none =>
          simp [MachineDescription.runConfig, hstepSeq, hstepA]
      | some cnext =>
          have hnextState : cnext.state < A.stateCount := by
            have hbound :=
              MachineDescription.stepConfig_state_bound
                (D := A.toDescription)
                (Fragment.toDescription_wellFormed hA)
                hstepA
            simpa [Fragment.toDescription] using hbound
          have hnextNoExit : forall k : Nat,
              k < n ->
                (A.toDescription.runConfig k cnext).state ≠
                  A.exit := by
            intro k hk
            have hno := hnoExit (k + 1) (Nat.succ_lt_succ hk)
            simpa [MachineDescription.runConfig, hstepA] using hno
          simp [MachineDescription.runConfig, hstepSeq, hstepA,
            ih hnextState hnextNoExit]

theorem stepConfig_seq_handoff
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed)
    (T : Tape Bool) :
    (seq A B handoffMove).toDescription.stepConfig
        { state := A.exit, tape := T } =
      some
        { state := A.stateCount + B.entry
          tape := Tape.move handoffMove T } := by
  have hfindA :
      List.find? (MachineDescription.Matches A.exit (Tape.read T))
        A.transitions = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    have hmatchPair : t.source = A.exit ∧ t.read = Tape.read T := by
      simpa [MachineDescription.Matches] using hmatch
    have hsource : t.source = A.exit :=
      hmatchPair.left
    exact hA.right.right.right.right.right t ht hsource
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          have hfindA' :
              List.find? (MachineDescription.Matches A.exit none)
                A.transitions = none := by
            simpa [Tape.read] using hfindA
          cases handoffMove <;>
            simp [MachineDescription.stepConfig,
              MachineDescription.lookupTransition, Fragment.seq,
              Fragment.toDescription, List.find?_append, hfindA',
              handoffTransitions, branchOnCell,
              preserveTransition, transition, preserveCell,
              MachineDescription.Matches, Tape.read, Tape.write,
              Tape.move, Tape.moveLeft, Tape.moveRight]
      | some b =>
          cases b
          · have hfindA' :
                List.find?
                    (MachineDescription.Matches A.exit (some false))
                    A.transitions = none := by
              simpa [Tape.read] using hfindA
            cases handoffMove <;>
              simp [MachineDescription.stepConfig,
                MachineDescription.lookupTransition, Fragment.seq,
                Fragment.toDescription, List.find?_append, hfindA',
                handoffTransitions, branchOnCell,
                preserveTransition, transition, preserveCell,
                MachineDescription.Matches, Tape.read, Tape.write,
                Tape.move, Tape.moveLeft, Tape.moveRight]
          · have hfindA' :
                List.find?
                    (MachineDescription.Matches A.exit (some true))
                    A.transitions = none := by
              simpa [Tape.read] using hfindA
            cases handoffMove <;>
              simp [MachineDescription.stepConfig,
                MachineDescription.lookupTransition, Fragment.seq,
                Fragment.toDescription, List.find?_append, hfindA',
                handoffTransitions, branchOnCell,
                preserveTransition, transition, preserveCell,
                MachineDescription.Matches, Tape.read, Tape.write,
                Tape.move, Tape.moveLeft, Tape.moveRight]

def offsetConfiguration
    (offset : Nat) (c : MachineDescription.Configuration) :
    MachineDescription.Configuration :=
  { state := offset + c.state, tape := c.tape }

theorem lookup_seq_right
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed)
    {state : Nat} {cell : Option Bool} :
    (seq A B handoffMove).toDescription.lookupTransition
        (A.stateCount + state) cell =
      Option.map (TransitionDescription.offsetStates A.stateCount)
        (B.toDescription.lookupTransition state cell) := by
  unfold MachineDescription.lookupTransition
  have hfindA :
      List.find? (MachineDescription.Matches
          (A.stateCount + state) cell) A.transitions = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    have htSource : t.source < A.stateCount :=
      (hA.right.right.right.left t ht).left
    have hsource : t.source = A.stateCount + state := by
      have hmatchPair :
          t.source = A.stateCount + state ∧ t.read = cell := by
        simpa [MachineDescription.Matches] using hmatch
      exact hmatchPair.left
    omega
  have hfindH :
      List.find? (MachineDescription.Matches
          (A.stateCount + state) cell)
        (handoffTransitions A.exit
          (A.stateCount + B.entry) handoffMove) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    simp [handoffTransitions, branchOnCell,
      preserveTransition, transition] at ht
    rcases ht with rfl | rfl | rfl
    · have hsource : A.exit = A.stateCount + state := by
        have hmatchPair :
            A.exit = A.stateCount + state ∧ none = cell := by
          simpa [MachineDescription.Matches] using hmatch
        exact hmatchPair.left
      have hAexit : A.exit < A.stateCount := hA.right.right.left
      omega
    · have hsource : A.exit = A.stateCount + state := by
        have hmatchPair :
            A.exit = A.stateCount + state ∧ some false = cell := by
          simpa [MachineDescription.Matches] using hmatch
        exact hmatchPair.left
      have hAexit : A.exit < A.stateCount := hA.right.right.left
      omega
    · have hsource : A.exit = A.stateCount + state := by
        have hmatchPair :
            A.exit = A.stateCount + state ∧ some true = cell := by
          simpa [MachineDescription.Matches] using hmatch
        exact hmatchPair.left
      have hAexit : A.exit < A.stateCount := hA.right.right.left
      omega
  have hpredicate :
      (MachineDescription.Matches (A.stateCount + state) cell ∘
          TransitionDescription.offsetStates A.stateCount) =
        MachineDescription.Matches state cell := by
    funext t
    have hsourceBeq :
        (A.stateCount + t.source == A.stateCount + state) =
          (t.source == state) := by
      by_cases hsource : t.source = state
      · have hoffset :
            A.stateCount + t.source = A.stateCount + state := by
          omega
        have hleft :
            (A.stateCount + t.source == A.stateCount + state) =
              true := by
          rw [beq_iff_eq]
          exact hoffset
        have hright : (t.source == state) = true := by
          rw [beq_iff_eq]
          exact hsource
        rw [hleft, hright]
      · have hoffset :
            A.stateCount + t.source ≠ A.stateCount + state := by
          omega
        have hleft :
            (A.stateCount + t.source == A.stateCount + state) =
              false := by
          rw [beq_eq_false_iff_ne]
          exact hoffset
        have hright : (t.source == state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hsource
        rw [hleft, hright]
    simp [Function.comp, MachineDescription.Matches,
      TransitionDescription.offsetStates, hsourceBeq]
  simp [Fragment.seq, Fragment.toDescription, List.find?_append,
    hfindA, hfindH, List.find?_map, hpredicate]

theorem stepConfig_seq_right
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed)
    (c : MachineDescription.Configuration) :
    (seq A B handoffMove).toDescription.stepConfig
        (offsetConfiguration A.stateCount c) =
      Option.map (offsetConfiguration A.stateCount)
        (B.toDescription.stepConfig c) := by
  cases c with
  | mk state tape =>
      simp [MachineDescription.stepConfig, offsetConfiguration,
        lookup_seq_right (A := A) (B := B)
          (handoffMove := handoffMove) hA]
      cases hlookup :
          B.toDescription.lookupTransition state (Tape.read tape) with
      | none =>
          simp
      | some t =>
          simp [TransitionDescription.offsetStates, offsetConfiguration]

theorem runConfig_seq_right
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed)
    (n : Nat) (c : MachineDescription.Configuration) :
    (seq A B handoffMove).toDescription.runConfig n
        (offsetConfiguration A.stateCount c) =
      offsetConfiguration A.stateCount
        (B.toDescription.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      simp [MachineDescription.runConfig,
        stepConfig_seq_right (A := A) (B := B)
          (handoffMove := handoffMove) hA c]
      cases hstep : B.toDescription.stepConfig c with
      | none =>
          simp [offsetConfiguration]
      | some next =>
          simp [ih next]

theorem seq_runConfig_reaches
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {nA nB : Nat} {Tin Tmid Tout : Tape Bool}
    (hArun :
      A.toDescription.runConfig nA
          { state := A.entry, tape := Tin } =
        { state := A.exit, tape := Tmid })
    (hAnoExit :
      forall k : Nat,
        k < nA ->
          (A.toDescription.runConfig k
            { state := A.entry, tape := Tin }).state ≠ A.exit)
    (hBrun :
      B.toDescription.runConfig nB
          { state := B.entry,
            tape := Tape.move handoffMove Tmid } =
        { state := B.exit, tape := Tout }) :
    (seq A B handoffMove).toDescription.runConfig
        (nA + (1 + nB))
        { state := (seq A B handoffMove).entry, tape := Tin } =
      { state := (seq A B handoffMove).exit, tape := Tout } := by
  have hseqA :
      (seq A B handoffMove).toDescription.runConfig nA
          { state := (seq A B handoffMove).entry, tape := Tin } =
        { state := A.exit, tape := Tmid } := by
    calc
      (seq A B handoffMove).toDescription.runConfig nA
          { state := (seq A B handoffMove).entry, tape := Tin } =
        A.toDescription.runConfig nA
          { state := A.entry, tape := Tin } := by
          simpa [Fragment.seq] using
            runConfig_seq_left_of_no_exit
              (A := A) (B := B) (handoffMove := handoffMove)
              hA hB (n := nA)
              (c := { state := A.entry, tape := Tin })
              hA.right.left hAnoExit
      _ = { state := A.exit, tape := Tmid } := hArun
  calc
    (seq A B handoffMove).toDescription.runConfig
        (nA + (1 + nB))
        { state := (seq A B handoffMove).entry, tape := Tin }
        =
      (seq A B handoffMove).toDescription.runConfig
        (1 + nB)
        ((seq A B handoffMove).toDescription.runConfig nA
          { state := (seq A B handoffMove).entry, tape := Tin }) := by
        rw [MachineDescription.runConfig_add]
    _ =
      (seq A B handoffMove).toDescription.runConfig
        (1 + nB)
        { state := A.exit, tape := Tmid } := by
        rw [hseqA]
    _ =
      (seq A B handoffMove).toDescription.runConfig nB
        { state := A.stateCount + B.entry,
          tape := Tape.move handoffMove Tmid } := by
        rw [Nat.add_comm 1 nB]
        change
          (match
            (seq A B handoffMove).toDescription.stepConfig
              { state := A.exit, tape := Tmid } with
          | none => { state := A.exit, tape := Tmid }
          | some next =>
              (seq A B handoffMove).toDescription.runConfig nB next) =
            (seq A B handoffMove).toDescription.runConfig nB
              { state := A.stateCount + B.entry,
                tape := Tape.move handoffMove Tmid }
        rw [stepConfig_seq_handoff
          (A := A) (B := B) (handoffMove := handoffMove) hA Tmid]
    _ =
      offsetConfiguration A.stateCount
        (B.toDescription.runConfig nB
          { state := B.entry,
            tape := Tape.move handoffMove Tmid }) := by
        exact runConfig_seq_right
          (A := A) (B := B) (handoffMove := handoffMove)
          hA nB
          { state := B.entry,
            tape := Tape.move handoffMove Tmid }
    _ =
      offsetConfiguration A.stateCount
        { state := B.exit, tape := Tout } := by
        rw [hBrun]
    _ =
      { state := (seq A B handoffMove).exit, tape := Tout } := by
        rfl

theorem seq_reaches
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {Tin Tmid Tout : Tape Bool}
    (hAReach :
      exists nA : Nat,
        A.toDescription.runConfig nA
            { state := A.entry, tape := Tin } =
          { state := A.exit, tape := Tmid } ∧
          forall k : Nat,
            k < nA ->
              (A.toDescription.runConfig k
                { state := A.entry, tape := Tin }).state ≠ A.exit)
    (hBReach :
      exists nB : Nat,
        B.toDescription.runConfig nB
            { state := B.entry,
              tape := Tape.move handoffMove Tmid } =
          { state := B.exit, tape := Tout }) :
    exists n : Nat,
      (seq A B handoffMove).toDescription.runConfig n
          { state := (seq A B handoffMove).entry, tape := Tin } =
        { state := (seq A B handoffMove).exit, tape := Tout } := by
  rcases hAReach with ⟨nA, hArun, hAnoExit⟩
  rcases hBReach with ⟨nB, hBrun⟩
  exists nA + (1 + nB)
  exact seq_runConfig_reaches
    (A := A) (B := B) (handoffMove := handoffMove)
    hA hB hArun hAnoExit hBrun

theorem seq_firstReaches
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {Tin Tmid Tout : Tape Bool}
    (hAReach :
      exists nA : Nat,
        A.toDescription.runConfig nA
            { state := A.entry, tape := Tin } =
          { state := A.exit, tape := Tmid } ∧
          forall k : Nat,
            k < nA ->
              (A.toDescription.runConfig k
                { state := A.entry, tape := Tin }).state ≠ A.exit)
    (hBReach :
      exists nB : Nat,
        B.toDescription.runConfig nB
            { state := B.entry,
              tape := Tape.move handoffMove Tmid } =
          { state := B.exit, tape := Tout } ∧
          forall k : Nat,
            k < nB ->
              (B.toDescription.runConfig k
                { state := B.entry,
                  tape := Tape.move handoffMove Tmid }).state ≠ B.exit) :
    exists n : Nat,
      (seq A B handoffMove).toDescription.runConfig n
          { state := (seq A B handoffMove).entry, tape := Tin } =
        { state := (seq A B handoffMove).exit, tape := Tout } ∧
      forall k : Nat,
        k < n ->
          ((seq A B handoffMove).toDescription.runConfig k
            { state := (seq A B handoffMove).entry,
              tape := Tin }).state ≠
            (seq A B handoffMove).exit := by
  rcases hAReach with ⟨nA, hArun, hAnoExit⟩
  rcases hBReach with ⟨nB, hBrun, hBnoExit⟩
  let startSeq : MachineDescription.Configuration :=
    { state := (seq A B handoffMove).entry, tape := Tin }
  let startA : MachineDescription.Configuration :=
    { state := A.entry, tape := Tin }
  let startB : MachineDescription.Configuration :=
    { state := B.entry, tape := Tape.move handoffMove Tmid }
  have hseqA :
      (seq A B handoffMove).toDescription.runConfig nA startSeq =
        { state := A.exit, tape := Tmid } := by
    calc
      (seq A B handoffMove).toDescription.runConfig nA startSeq =
        A.toDescription.runConfig nA startA := by
          simpa [startSeq, startA, Fragment.seq] using
            runConfig_seq_left_of_no_exit
              (A := A) (B := B) (handoffMove := handoffMove)
              hA hB (n := nA)
              (c := { state := A.entry, tape := Tin })
              hA.right.left hAnoExit
      _ = { state := A.exit, tape := Tmid } := hArun
  exists nA + (1 + nB)
  constructor
  · simpa [startSeq] using
      seq_runConfig_reaches
        (A := A) (B := B) (handoffMove := handoffMove)
        hA hB hArun hAnoExit hBrun
  · intro k hk
    intro hfinal
    have hfinalSeq :
        ((seq A B handoffMove).toDescription.runConfig k
          startSeq).state =
          (seq A B handoffMove).exit := by
      simpa [startSeq] using hfinal
    by_cases hkLeft : k < nA
    · have hseqk :
          (seq A B handoffMove).toDescription.runConfig k startSeq =
            A.toDescription.runConfig k startA := by
        simpa [startSeq, startA, Fragment.seq] using
          runConfig_seq_left_of_no_exit
            (A := A) (B := B) (handoffMove := handoffMove)
            hA hB (n := k)
            (c := { state := A.entry, tape := Tin })
            hA.right.left
            (fun j hj => hAnoExit j (Nat.lt_trans hj hkLeft))
      have hstateBound :
          ((seq A B handoffMove).toDescription.runConfig k
            startSeq).state < A.stateCount := by
        rw [hseqk]
        exact MachineDescription.runConfig_state_bound
          (MachineDescription.Fragment.toDescription_wellFormed hA)
          hA.right.left
      have hexitBound :
          (seq A B handoffMove).exit < A.stateCount := by
        rw [hfinalSeq] at hstateBound
        exact hstateBound
      have hbad :
          A.stateCount + B.exit < A.stateCount := by
        simpa [Fragment.seq] using hexitBound
      omega
    · have hnA_le_k : nA ≤ k := Nat.le_of_not_gt hkLeft
      let d : Nat := k - nA
      have hk_eq : k = nA + d := by
        omega
      have hd_bound : d < 1 + nB := by
        omega
      cases hd : d with
      | zero =>
          have hk_nA : k = nA := by
            omega
          have hstateBound :
              ((seq A B handoffMove).toDescription.runConfig k
                startSeq).state < A.stateCount := by
            rw [hk_nA, hseqA]
            exact hA.right.right.left
          have hexitBound :
              (seq A B handoffMove).exit < A.stateCount := by
            rw [hfinalSeq] at hstateBound
            exact hstateBound
          have hbad :
              A.stateCount + B.exit < A.stateCount := by
            simpa [Fragment.seq] using hexitBound
          omega
      | succ j =>
          have hj_bound : j < nB := by
            omega
          have hk_succ : k = nA + (1 + j) := by
            omega
          have hseqk :
              (seq A B handoffMove).toDescription.runConfig k
                  startSeq =
                offsetConfiguration A.stateCount
                  (B.toDescription.runConfig j startB) := by
            calc
              (seq A B handoffMove).toDescription.runConfig k
                  startSeq =
                (seq A B handoffMove).toDescription.runConfig
                    (nA + (1 + j)) startSeq := by
                    rw [hk_succ]
              _ =
                (seq A B handoffMove).toDescription.runConfig
                    (1 + j)
                    ((seq A B handoffMove).toDescription.runConfig nA
                      startSeq) := by
                    rw [MachineDescription.runConfig_add]
              _ =
                (seq A B handoffMove).toDescription.runConfig
                    (1 + j)
                    { state := A.exit, tape := Tmid } := by
                    rw [hseqA]
              _ =
                (seq A B handoffMove).toDescription.runConfig j
                    { state := A.stateCount + B.entry,
                      tape := Tape.move handoffMove Tmid } := by
                    rw [Nat.add_comm 1 j]
                    change
                      (match
                        (seq A B handoffMove).toDescription.stepConfig
                          { state := A.exit, tape := Tmid } with
                      | none => { state := A.exit, tape := Tmid }
                      | some next =>
                          (seq A B handoffMove).toDescription.runConfig
                            j next) =
                        (seq A B handoffMove).toDescription.runConfig j
                          { state := A.stateCount + B.entry,
                            tape := Tape.move handoffMove Tmid }
                    rw [stepConfig_seq_handoff
                      (A := A) (B := B) (handoffMove := handoffMove)
                      hA Tmid]
              _ =
                offsetConfiguration A.stateCount
                  (B.toDescription.runConfig j startB) := by
                    simpa [startB] using
                      runConfig_seq_right
                        (A := A) (B := B)
                        (handoffMove := handoffMove)
                        hA j
                        { state := B.entry,
                          tape := Tape.move handoffMove Tmid }
          have hstateEq :
              (offsetConfiguration A.stateCount
                (B.toDescription.runConfig j startB)).state =
                (seq A B handoffMove).exit := by
            simpa [hseqk] using hfinalSeq
          have hBexit :
              (B.toDescription.runConfig j startB).state = B.exit := by
            apply Nat.add_left_cancel (n := A.stateCount)
            simpa [offsetConfiguration, Fragment.seq] using hstateEq
          exact hBnoExit j hj_bound hBexit

theorem seq_reaches_inv
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {Tin Tout : Tape Bool}
    (hseq :
      exists n : Nat,
        (seq A B handoffMove).toDescription.runConfig n
            { state := (seq A B handoffMove).entry, tape := Tin } =
          { state := (seq A B handoffMove).exit, tape := Tout }) :
    exists Tmid : Tape Bool,
      (exists nA : Nat,
        A.toDescription.runConfig nA
            { state := A.entry, tape := Tin } =
          { state := A.exit, tape := Tmid } ∧
        forall k : Nat,
          k < nA ->
            (A.toDescription.runConfig k
              { state := A.entry, tape := Tin }).state ≠ A.exit) ∧
        exists nB : Nat,
          B.toDescription.runConfig nB
              { state := B.entry,
                tape := Tape.move handoffMove Tmid } =
            { state := B.exit, tape := Tout } := by
  rcases hseq with ⟨n, hnrun⟩
  let startSeq : MachineDescription.Configuration :=
    { state := (seq A B handoffMove).entry, tape := Tin }
  let startA : MachineDescription.Configuration :=
    { state := A.entry, tape := Tin }
  have hhit :
      exists k : Nat,
        k < n ∧
          (A.toDescription.runConfig k startA).state = A.exit := by
    by_cases hsome :
        exists k : Nat,
          k < n ∧
            (A.toDescription.runConfig k startA).state = A.exit
    · exact hsome
    · exfalso
      have hnoExit : forall k : Nat,
          k < n ->
            (A.toDescription.runConfig k startA).state ≠ A.exit := by
        intro k hk hstate
        exact hsome ⟨k, hk, hstate⟩
      have hleft :
          (seq A B handoffMove).toDescription.runConfig n startSeq =
            A.toDescription.runConfig n startA := by
        simpa [startSeq, startA, Fragment.seq] using
          runConfig_seq_left_of_no_exit
            (A := A) (B := B) (handoffMove := handoffMove)
            hA hB (n := n)
            (c := { state := A.entry, tape := Tin })
            hA.right.left hnoExit
      have hstateBound :
          ((seq A B handoffMove).toDescription.runConfig n
            startSeq).state < A.stateCount := by
        rw [hleft]
        exact MachineDescription.runConfig_state_bound
          (MachineDescription.Fragment.toDescription_wellFormed hA)
          hA.right.left
      have hexitBound :
          (seq A B handoffMove).exit < A.stateCount := by
        rw [hnrun] at hstateBound
        exact hstateBound
      have hbad : A.stateCount + B.exit < A.stateCount := by
        simpa [Fragment.seq] using hexitBound
      omega
  rcases hhit with ⟨k, hklt, hkstate⟩
  let Tmid : Tape Bool :=
    (A.toDescription.runConfig k startA).tape
  have hArunK :
      A.toDescription.runConfig k startA =
        { state := A.exit, tape := Tmid } := by
    cases hfinal : A.toDescription.runConfig k startA with
    | mk state tape =>
        simp [hfinal] at hkstate
        simp [hfinal, hkstate, Tmid]
  rcases MachineDescription.firstReaches_halt_of_runConfig_eq
      (D := A.toDescription)
      (MachineDescription.Fragment.toDescription_haltTransitionFree hA)
      hArunK with
    ⟨nA, hnA_le_k, hArunA, hAfirst⟩
  have hnA_lt_n : nA < n := Nat.lt_of_le_of_lt hnA_le_k hklt
  let nB : Nat := n - (nA + 1)
  have hn_eq : n = nA + (1 + nB) := by
    omega
  have hseqA :
      (seq A B handoffMove).toDescription.runConfig nA startSeq =
        { state := A.exit, tape := Tmid } := by
    calc
      (seq A B handoffMove).toDescription.runConfig nA startSeq =
          A.toDescription.runConfig nA startA := by
            simpa [startSeq, startA, Fragment.seq] using
              runConfig_seq_left_of_no_exit
                (A := A) (B := B) (handoffMove := handoffMove)
                hA hB (n := nA)
                (c := { state := A.entry, tape := Tin })
                hA.right.left hAfirst
      _ = { state := A.exit, tape := Tmid } := hArunA
  let startB : MachineDescription.Configuration :=
    { state := B.entry, tape := Tape.move handoffMove Tmid }
  have hrightOffset :
      offsetConfiguration A.stateCount
          (B.toDescription.runConfig nB startB) =
        { state := (seq A B handoffMove).exit, tape := Tout } := by
    calc
      offsetConfiguration A.stateCount
          (B.toDescription.runConfig nB startB) =
          (seq A B handoffMove).toDescription.runConfig nB
            { state := A.stateCount + B.entry,
              tape := Tape.move handoffMove Tmid } := by
            symm
            simpa [startB] using
              runConfig_seq_right
                (A := A) (B := B) (handoffMove := handoffMove)
                hA nB
                { state := B.entry,
                  tape := Tape.move handoffMove Tmid }
      _ =
          (seq A B handoffMove).toDescription.runConfig (1 + nB)
            { state := A.exit, tape := Tmid } := by
            rw [Nat.add_comm 1 nB]
            change
              (seq A B handoffMove).toDescription.runConfig nB
                { state := A.stateCount + B.entry,
                  tape := Tape.move handoffMove Tmid } =
              (match
                (seq A B handoffMove).toDescription.stepConfig
                  { state := A.exit, tape := Tmid } with
              | none => { state := A.exit, tape := Tmid }
              | some next =>
                  (seq A B handoffMove).toDescription.runConfig nB next)
            rw [stepConfig_seq_handoff
              (A := A) (B := B) (handoffMove := handoffMove)
              hA Tmid]
      _ =
          (seq A B handoffMove).toDescription.runConfig
            (nA + (1 + nB)) startSeq := by
            symm
            calc
              (seq A B handoffMove).toDescription.runConfig
                  (nA + (1 + nB)) startSeq =
                  (seq A B handoffMove).toDescription.runConfig
                    (1 + nB)
                    ((seq A B handoffMove).toDescription.runConfig nA
                      startSeq) := by
                    rw [MachineDescription.runConfig_add]
              _ =
                  (seq A B handoffMove).toDescription.runConfig
                    (1 + nB)
                    { state := A.exit, tape := Tmid } := by
                    rw [hseqA]
      _ =
          (seq A B handoffMove).toDescription.runConfig n startSeq := by
            rw [hn_eq]
      _ = { state := (seq A B handoffMove).exit, tape := Tout } :=
            hnrun
  have hBrun :
      B.toDescription.runConfig nB startB =
        { state := B.exit, tape := Tout } := by
    cases hBfinal : B.toDescription.runConfig nB startB with
    | mk state tape =>
        have hstateEq :
            A.stateCount + state =
              (seq A B handoffMove).exit := by
          simpa [offsetConfiguration, hBfinal] using
            congrArg MachineDescription.Configuration.state hrightOffset
        have hstate : state = B.exit := by
          apply Nat.add_left_cancel (n := A.stateCount)
          simpa [Fragment.seq] using hstateEq
        have htape : tape = Tout := by
          simpa [offsetConfiguration, hBfinal] using
            congrArg MachineDescription.Configuration.tape hrightOffset
        simp [hstate, htape]
  exact ⟨Tmid, ⟨nA, hArunA, hAfirst⟩, ⟨nB, hBrun⟩⟩

end Fragment

theorem seqSubroutine_reaches
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAReach :
      exists nA : Nat,
        A.runConfig nA { state := A.start, tape := Tin } =
          { state := A.halt, tape := Tmid } ∧
        forall k : Nat,
          k < nA ->
            (A.runConfig k
              { state := A.start, tape := Tin }).state ≠ A.halt)
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start,
              tape := Tape.move handoffMove Tmid } =
          { state := B.halt, tape := Tout }) :
    exists n : Nat,
      (seqSubroutine A B handoffMove).runConfig n
          { state := (seqSubroutine A B handoffMove).start,
            tape := Tin } =
        { state := (seqSubroutine A B handoffMove).halt,
          tape := Tout } := by
  simpa [seqSubroutine, asFragment] using
    Fragment.seq_reaches
      (A := A.asFragment) (B := B.asFragment)
      (handoffMove := handoffMove)
      (asFragment_wellFormed hA) (asFragment_wellFormed hB)
      hAReach hBReach

theorem seqSubroutine_reaches_of_runConfig_eq
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {nA : Nat} {Tin Tmid Tout : Tape Bool}
    (hArun :
      A.runConfig nA { state := A.start, tape := Tin } =
        { state := A.halt, tape := Tmid })
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start,
              tape := Tape.move handoffMove Tmid } =
          { state := B.halt, tape := Tout }) :
    exists n : Nat,
      (seqSubroutine A B handoffMove).runConfig n
          { state := (seqSubroutine A B handoffMove).start,
            tape := Tin } =
        { state := (seqSubroutine A B handoffMove).halt,
          tape := Tout } := by
  rcases firstReaches_halt_of_runConfig_eq hA.right hArun with
    ⟨m, _hmle, hmrun, hmfirst⟩
  exact seqSubroutine_reaches hA hB
    ⟨m, hmrun, hmfirst⟩ hBReach

theorem seqSubroutine_haltsWithTape_of_haltsWithTape
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input : Word Bool} {Tmid Tout : Tape Bool}
    (hAhalt : A.HaltsWithTape input Tmid)
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start,
              tape := Tape.move handoffMove Tmid } =
          { state := B.halt, tape := Tout }) :
    (seqSubroutine A B handoffMove).HaltsWithTape input Tout := by
  rcases MachineDescription.runConfig_eq_halt_of_haltsWithTape hAhalt with
    ⟨nA, hArun⟩
  rcases seqSubroutine_reaches_of_runConfig_eq
      (A := A) (B := B) (handoffMove := handoffMove)
      hA hB hArun hBReach with
    ⟨n, hn⟩
  exact ⟨n, by
    constructor
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.state hn
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.tape hn⟩

theorem seqSubroutine_haltsWithTape_inv
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input : Word Bool} {Tout : Tape Bool}
    (hseq :
      (seqSubroutine A B handoffMove).HaltsWithTape input Tout) :
    exists Tmid : Tape Bool,
      A.HaltsWithTape input Tmid ∧
        exists nB : Nat,
          B.runConfig nB
              { state := B.start,
                tape := Tape.move handoffMove Tmid } =
            { state := B.halt, tape := Tout } := by
  rcases runConfig_eq_halt_of_haltsWithTape hseq with ⟨n, hn⟩
  have hseqFrag :
      exists n : Nat,
        (Fragment.seq A.asFragment B.asFragment handoffMove).toDescription.runConfig n
            { state := (Fragment.seq A.asFragment B.asFragment handoffMove).entry,
              tape := Tape.input input } =
          { state := (Fragment.seq A.asFragment B.asFragment handoffMove).exit,
            tape := Tout } := by
    exact ⟨n, by
      simpa [seqSubroutine, asFragment, Fragment.seq] using hn⟩
  rcases Fragment.seq_reaches_inv
      (A := A.asFragment) (B := B.asFragment)
      (handoffMove := handoffMove)
      (asFragment_wellFormed hA)
      (asFragment_wellFormed hB)
      hseqFrag with
    ⟨Tmid, hAReach, hBReach⟩
  rcases hAReach with ⟨nA, hArunA, _hAfirst⟩
  rcases hBReach with ⟨nB, hBrunB⟩
  exact ⟨Tmid,
    ⟨⟨nA, by
        constructor
        · simpa [HaltsWithTapeIn, asFragment] using
            congrArg Configuration.state hArunA
        · simpa [HaltsWithTapeIn, asFragment] using
            congrArg Configuration.tape hArunA⟩,
      ⟨nB, by simpa [asFragment] using hBrunB⟩⟩⟩

theorem seqSubroutine_haltsWithOutput_of_haltsWithTape
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input : Word Bool} {Tmid Tout : Tape Bool}
    (hAhalt : A.HaltsWithTape input Tmid)
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start,
              tape := Tape.move handoffMove Tmid } =
          { state := B.halt, tape := Tout }) :
    (seqSubroutine A B handoffMove).HaltsWithOutput input
      (Tape.normalizedOutput Tout) := by
  rcases hAhalt with ⟨nA, hAhalt⟩
  have hArun :
      A.runConfig nA { state := A.start, tape := Tape.input input } =
        { state := A.halt, tape := Tmid } := by
    cases hfinal : A.runConfig nA (A.initial input) with
    | mk state tape =>
        rcases hAhalt with ⟨hstate, htape⟩
        simp [hfinal] at hstate htape
        change A.runConfig nA (A.initial input) =
          { state := A.halt, tape := Tmid }
        rw [hfinal, hstate, htape]
  rcases seqSubroutine_reaches_of_runConfig_eq
      (A := A) (B := B) (handoffMove := handoffMove)
      hA hB hArun hBReach with
    ⟨n, hn⟩
  exact ⟨n, by
    constructor
    · simpa [MachineDescription.HaltsWithOutputIn] using
        congrArg MachineDescription.Configuration.state hn
    · simpa [MachineDescription.HaltsWithOutputIn] using
        congrArg (fun c => Tape.normalizedOutput c.tape) hn⟩

end MachineDescription

end Computability
end FoC
