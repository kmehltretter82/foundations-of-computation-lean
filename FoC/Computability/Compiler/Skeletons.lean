import FoC.Computability.Compiler.Core

set_option doc.verso true

/-!
# Fixed-simulator skeleton compiler bridges
-/

namespace FoC
namespace Computability

open Languages

structure FixedDescriptionBoundedSimulatorPhaseTargets
    (D : MachineDescription) where
  decodeLayout :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  simulateStep :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  repeatControl :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  emitLayout :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  pipeline_correct :
    forall L : MachineDescription.SimulatorLayout,
      emitLayout (repeatControl (simulateStep (decodeLayout L))) =
        MachineDescription.SimulatorLayout.run D L.stage L

namespace FixedDescriptionBoundedSimulatorPhaseTargets

def canonical (D : MachineDescription) :
    FixedDescriptionBoundedSimulatorPhaseTargets D where
  decodeLayout := id
  simulateStep := fun L =>
    MachineDescription.SimulatorLayout.run D L.stage L
  repeatControl := id
  emitLayout := id
  pipeline_correct := by
    intro L
    rfl

theorem canonical_pipeline_correct
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (canonical D).emitLayout
        ((canonical D).repeatControl
          ((canonical D).simulateStep ((canonical D).decodeLayout L))) =
      MachineDescription.SimulatorLayout.run D L.stage L :=
  (canonical D).pipeline_correct L

end FixedDescriptionBoundedSimulatorPhaseTargets

def FixedDescriptionBoundedSimulatorLayoutTape
    (L : MachineDescription.SimulatorLayout) : Tape Bool :=
  MachineDescription.SimulatorLayout.tape L

def FixedDescriptionBoundedSimulatorHandoffTape
    (handoffMove : Direction)
    (L : MachineDescription.SimulatorLayout) : Tape Bool :=
  Tape.move handoffMove (FixedDescriptionBoundedSimulatorLayoutTape L)

def FixedDescriptionBoundedSimulatorFragmentReaches
    (entryTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool)
    (phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout)
    (fragment : MachineDescription.Fragment)
    (L : MachineDescription.SimulatorLayout) : Prop :=
  exists n : Nat,
    fragment.toDescription.runConfig n
        { state := fragment.entry, tape := entryTape L } =
      { state := fragment.exit, tape := exitTape (phase L) } ∧
      forall k : Nat,
        k < n ->
          (fragment.toDescription.runConfig k
            { state := fragment.entry, tape := entryTape L }).state ≠
            fragment.exit

def FixedDescriptionBoundedSimulatorFragmentRealizes
    (entryTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool)
    (phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout)
    (fragment : MachineDescription.Fragment) : Prop :=
  fragment.WellFormed ∧
    forall L : MachineDescription.SimulatorLayout,
      FixedDescriptionBoundedSimulatorFragmentReaches
        entryTape exitTape phase fragment L

abbrev FixedDescriptionBoundedSimulatorPhaseRealizes :=
  FixedDescriptionBoundedSimulatorFragmentRealizes

theorem fixedDescriptionBoundedSimulatorPhaseRealizes_standard_output
    {phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout}
    {fragment : MachineDescription.Fragment}
    (h :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        phase fragment) :
    fragment.WellFormed ∧
      forall L : MachineDescription.SimulatorLayout,
        fragment.toDescription.HaltsWithOutput
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorInput (phase L)) := by
  constructor
  · exact h.left
  · intro L
    rcases h.right L with ⟨n, hn, _hminimal⟩
    exists n
    have hstate :
        (fragment.toDescription.runConfig n
          (fragment.toDescription.initial
            (FixedDescriptionBoundedSimulatorInput L))).state =
          fragment.exit := by
      simpa [MachineDescription.Fragment.toDescription,
        FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorLayoutTape,
        MachineDescription.SimulatorLayout.tape] using congrArg
          (fun c : MachineDescription.Configuration => c.state) hn
    have htape :
        (fragment.toDescription.runConfig n
          (fragment.toDescription.initial
            (FixedDescriptionBoundedSimulatorInput L))).tape =
          FixedDescriptionBoundedSimulatorLayoutTape (phase L) := by
      simpa [MachineDescription.Fragment.toDescription,
        FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorLayoutTape,
        MachineDescription.SimulatorLayout.tape] using congrArg
          (fun c : MachineDescription.Configuration => c.tape) hn
    constructor
    · simpa [MachineDescription.Fragment.toDescription] using hstate
    · rw [htape]
      exact MachineDescription.SimulatorLayout.tape_normalizedOutput
        (phase L)

theorem fixedDescriptionBoundedSimulatorHandoffPhaseRealizes
    (move : Direction) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      FixedDescriptionBoundedSimulatorLayoutTape
      (FixedDescriptionBoundedSimulatorHandoffTape move)
      id
      (MachineDescription.Fragment.handoff move) := by
  constructor
  · exact MachineDescription.Fragment.handoff_wellFormed move
  · intro L
    simpa [FixedDescriptionBoundedSimulatorLayoutTape,
      FixedDescriptionBoundedSimulatorHandoffTape] using
      MachineDescription.Fragment.handoff_firstReaches move
        (FixedDescriptionBoundedSimulatorLayoutTape L)

theorem fixedDescriptionBoundedSimulatorHaltPhaseRealizes
    (tape : MachineDescription.SimulatorLayout -> Tape Bool) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      tape tape id MachineDescription.Fragment.halt := by
  constructor
  · exact MachineDescription.Fragment.halt_wellFormed
  · intro L
    exists 0
    constructor
    · rfl
    · intro k hk
      omega

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

end MachineDescription

theorem fixedDescriptionBoundedSimulatorPhaseRealizes_seq
    {entryTape midTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool}
    {phaseA phaseB :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout}
    {A B : MachineDescription.Fragment} {handoffMove : Direction}
    (hA :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        entryTape midTape phaseA A)
    (hB :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (fun L => Tape.move handoffMove (midTape L))
        exitTape phaseB B) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      entryTape exitTape (fun L => phaseB (phaseA L))
      (MachineDescription.Fragment.seq A B handoffMove) := by
  constructor
  · exact MachineDescription.Fragment.seq_wellFormed hA.left hB.left
  · intro L
    simpa [FixedDescriptionBoundedSimulatorFragmentReaches] using
      MachineDescription.Fragment.seq_firstReaches
        (A := A) (B := B) (handoffMove := handoffMove)
        hA.left hB.left
        (Tin := entryTape L)
        (Tmid := midTape (phaseA L))
        (Tout := exitTape (phaseB (phaseA L)))
        (hA.right L)
        (hB.right (phaseA L))

structure FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction)
    (targets : FixedDescriptionBoundedSimulatorPhaseTargets D) :
    Prop where
  decodeLayout :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      FixedDescriptionBoundedSimulatorLayoutTape
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.decodeLayout S.decodeLayout
  simulateStep :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.simulateStep S.simulateStep
  repeatControl :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.repeatControl S.repeatControl
  emitLayout :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.emitLayout S.emitLayout

def FixedDescriptionBoundedSimulatorSkeletonRealizes
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    (S.toDescription handoffMove).HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L)

def FixedDescriptionBoundedSimulatorSkeletonRealizesExact
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    (S.toDescription handoffMove).HaltsWithExactOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L)

theorem fixedDescriptionBoundedSimulatorSkeletonRealizes_of_exact
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizesExact
      D S handoffMove) :
    FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove := by
  intro L
  exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
    (h L)

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizes
      D S handoffMove) :
    FixedDescriptionBoundedSimulatorTableRealizes
      D (S.toDescription handoffMove) := by
  constructor
  · exact
      MachineDescription.FixedSimulatorTableSkeleton.toDescription_wellFormed
        S handoffMove
  · exact h

theorem fixedDescriptionBoundedSimulatorSkeletonRealizes_output
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizes
      D S handoffMove)
    (L : MachineDescription.SimulatorLayout) :
    (S.toDescription handoffMove).HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L) :=
  h L

def FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists S : MachineDescription.FixedSimulatorTableSkeleton,
      exists handoffMove : Direction,
        FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨S, handoffMove, hS⟩
  exact ⟨S.toDescription handoffMove,
    fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes hS⟩

def FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction : Prop :=
  forall D : MachineDescription,
    exists S : MachineDescription.FixedSimulatorTableSkeleton,
      exists handoffMove : Direction,
      exists targets : FixedDescriptionBoundedSimulatorPhaseTargets D,
        FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
          D S handoffMove targets

def FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness : Prop :=
  forall D : MachineDescription,
    forall S : MachineDescription.FixedSimulatorTableSkeleton,
    forall handoffMove : Direction,
    forall targets : FixedDescriptionBoundedSimulatorPhaseTargets D,
      FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
        D S handoffMove targets ->
      FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseSoundness :
    FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness := by
  intro D S handoffMove targets htargets
  have hDecodeSim :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => targets.simulateStep (targets.decodeLayout L))
        (MachineDescription.Fragment.seq
          S.decodeLayout S.simulateStep handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := targets.decodeLayout)
      (phaseB := targets.simulateStep)
      (A := S.decodeLayout)
      (B := S.simulateStep)
      (handoffMove := handoffMove)
      htargets.decodeLayout htargets.simulateStep
  have hDecodeSimRepeat :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L =>
          targets.repeatControl
            (targets.simulateStep (targets.decodeLayout L)))
        (MachineDescription.Fragment.seq
          (MachineDescription.Fragment.seq
            S.decodeLayout S.simulateStep handoffMove)
          S.repeatControl handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := fun L =>
        targets.simulateStep (targets.decodeLayout L))
      (phaseB := targets.repeatControl)
      (A := MachineDescription.Fragment.seq
        S.decodeLayout S.simulateStep handoffMove)
      (B := S.repeatControl)
      (handoffMove := handoffMove)
      hDecodeSim htargets.repeatControl
  have hAllPhases :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L =>
          targets.emitLayout
            (targets.repeatControl
              (targets.simulateStep (targets.decodeLayout L))))
        (MachineDescription.Fragment.seq
          (MachineDescription.Fragment.seq
            (MachineDescription.Fragment.seq
              S.decodeLayout S.simulateStep handoffMove)
            S.repeatControl handoffMove)
          S.emitLayout handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := fun L =>
        targets.repeatControl
          (targets.simulateStep (targets.decodeLayout L)))
      (phaseB := targets.emitLayout)
      (A := MachineDescription.Fragment.seq
        (MachineDescription.Fragment.seq
          S.decodeLayout S.simulateStep handoffMove)
        S.repeatControl handoffMove)
      (B := S.emitLayout)
      (handoffMove := handoffMove)
      hDecodeSimRepeat htargets.emitLayout
  intro L
  have hOutput :=
    (fixedDescriptionBoundedSimulatorPhaseRealizes_standard_output
      hAllPhases).right L
  have hpipeline :
      targets.emitLayout
          (targets.repeatControl
            (targets.simulateStep (targets.decodeLayout L))) =
        MachineDescription.SimulatorLayout.run D L.stage L :=
    targets.pipeline_correct L
  simpa [MachineDescription.FixedSimulatorTableSkeleton.toDescription,
    MachineDescription.FixedSimulatorTableSkeleton.toFragment,
    FixedDescriptionBoundedSimulatorOutput, hpipeline] using hOutput

theorem fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨S, handoffMove, targets, htargets⟩
  exact ⟨S, handoffMove,
    hsound D S handoffMove targets htargets⟩

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
      hsound hcompile)

theorem pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile
    (fun w n => accept.HaltsIn n w)
    (fun w n => reject.HaltsIn n w)

theorem pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (hcompile :
      PairedRecognizerBoundedDovetailTableCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  cases hcompile accept reject with
  | intro decider hdecider =>
      exists decider
      constructor
      · exact hdecider.left
      · intro w b
        constructor
        · intro hhalt
          cases (hdecider.right w b).mp hhalt with
          | intro limit hlimit =>
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
                at hlimit
        · intro hprog
          cases hprog with
          | intro limit hlimit =>
              apply (hdecider.right w b).mpr
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]

theorem pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler
    (hcompile : PairedRecognizerDovetailDescriptionCompilerPrinciple) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdecider.right w b).mp hhalt with ⟨limit, hlimit⟩
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using hlimit⟩
    · intro hlimit
      rcases hlimit with ⟨limit, hlimit⟩
      apply (hdecider.right w b).mpr
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using hlimit⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_iff_pairedRecognizerDovetailDescriptionCompiler :
    PairedRecognizerBoundedDovetailTableCompilerConstruction <->
      PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  ⟨pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler,
    pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler⟩

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputRealizer_and_searchDriver
      hrunner hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    (hattempt :
      PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
      hattempt hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_tapeCodeOutputCompiler_and_descriptionBoolDeciderCompiler
    (htape : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (hbool : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    (pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
      htape)
    (pairedRecognizerDovetailStageAttemptSearchDriverCompiler_of_descriptionBoolDeciderCompiler
      hbool)

theorem pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputSubroutineRealizer_and_totalStageAttemptSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputSubroutineRealizer_and_totalStageAttemptSearchDriver
      hattempt hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
      hattempt hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_descriptionBoolDeciderCompiler
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hbool : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
    hattempt
    (pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_descriptionBoolDeciderCompiler
      hbool)

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
      hrunner hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
      hrunner hdriver)

theorem dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    DovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile (DovetailProgram accept reject)

theorem pairedRecognizerDovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler hcompile)

theorem programAcceptorCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    ProgramAcceptorCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programAcceptableByDescription_turingAcceptable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem programBoolDeciderCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    ProgramBoolDeciderCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programBoolDecidableByDescription_turingDecidable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    {accept reject : Word Bool -> Nat -> Prop}
    (htraces : ComplementaryAcceptanceTraces accept reject L) :
    TuringDecidable L := by
  cases hcompile accept reject with
  | intro D hD =>
      exact programBoolDecidableByDescription_turingDecidable
        (Exists.intro (DovetailProgram accept reject)
          (Exists.intro D (And.intro (dovetailProgram_decides htraces) hD)))

theorem reCoRe_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerableWithComplement L) :
    TuringDecidable L := by
  cases recursivelyEnumerable_with_complement_has_complementaryTraces h with
  | intro accept haccept =>
      cases haccept with
      | intro reject htraces =>
          exact complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
            hcompile htraces

theorem reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    ReCoReToDecidablePrinciple Bool := by
  intro L h
  exact reCoRe_turingDecidable_of_dovetailDescriptionCompiler hcompile h

end Computability
end FoC
