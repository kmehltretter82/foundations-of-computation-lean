import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.DispatcherAssembly.Basic

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace StaticDispatcherReaderAssembly

theorem boundedRemainderIndex_eq_of_eq
    {slots state₀ state₁ code₀ code₁ : Nat}
    (hcode₀ : code₀ < slots) (hcode₁ : code₁ < slots)
    (heq : slots * state₀ + code₀ = slots * state₁ + code₁) :
    state₀ = state₁ ∧ code₀ = code₁ := by
  by_cases hstate : state₀ = state₁
  · subst state₁
    constructor
    · rfl
    · exact Nat.add_left_cancel heq
  · rcases Nat.lt_or_gt_of_ne hstate with hlt | hgt
    · have hleftLt :
          slots * state₀ + code₀ < slots * (state₀ + 1) := by
        simpa [Nat.mul_succ] using
          Nat.add_lt_add_left hcode₀ (slots * state₀)
      have hstep :
          slots * (state₀ + 1) ≤ slots * state₁ :=
        Nat.mul_le_mul_left slots (Nat.succ_le_of_lt hlt)
      have hrightGe :
          slots * state₁ ≤ slots * state₁ + code₁ :=
        Nat.le_add_right _ _
      have hneq :
          slots * state₀ + code₀ ≠ slots * state₁ + code₁ :=
        Nat.ne_of_lt (Nat.lt_of_lt_of_le hleftLt
          (Nat.le_trans hstep hrightGe))
      exact False.elim (hneq heq)
    · have hrightLt :
          slots * state₁ + code₁ < slots * (state₁ + 1) := by
        simpa [Nat.mul_succ] using
          Nat.add_lt_add_left hcode₁ (slots * state₁)
      have hstep :
          slots * (state₁ + 1) ≤ slots * state₀ :=
        Nat.mul_le_mul_left slots (Nat.succ_le_of_lt hgt)
      have hleftGe :
          slots * state₀ ≤ slots * state₀ + code₀ :=
        Nat.le_add_right _ _
      have hneq :
          slots * state₁ + code₁ ≠ slots * state₀ + code₀ :=
        Nat.ne_of_lt (Nat.lt_of_lt_of_le hrightLt
          (Nat.le_trans hstep hleftGe))
      exact False.elim (hneq heq.symm)

theorem readCode_injective :
    Function.Injective ReadTuple3.readCode := by
  intro read₀ read₁ hcode
  cases read₀ with
  | none =>
      cases read₁ with
      | none => rfl
      | some bit =>
          cases bit <;> simp [ReadTuple3.readCode] at hcode ⊢
  | some bit₀ =>
      cases bit₀ <;>
        cases read₁ with
        | none => simp [ReadTuple3.readCode] at hcode ⊢
        | some bit₁ =>
            cases bit₁ <;> simp [ReadTuple3.readCode] at hcode ⊢

theorem code01_injective
    {read₀ read₁ read₀' read₁' : Option Bool}
    (hcode :
      ReadTuple3.code01 read₀ read₁ =
        ReadTuple3.code01 read₀' read₁') :
    read₀ = read₀' ∧ read₁ = read₁' := by
  have hidx :=
    boundedRemainderIndex_eq_of_eq
      (slots := 3)
      (state₀ := ReadTuple3.readCode read₁)
      (state₁ := ReadTuple3.readCode read₁')
      (code₀ := ReadTuple3.readCode read₀)
      (code₁ := ReadTuple3.readCode read₀')
      (ReadTuple3.readCode_lt_three read₀)
      (ReadTuple3.readCode_lt_three read₀')
      (by
        unfold ReadTuple3.code01 at hcode
        lia)
  exact
    ⟨readCode_injective hidx.right,
      readCode_injective hidx.left⟩

theorem afterRead0JumpTape1ReaderTransitions_sourceDisjoint_of_ne
    (D : Description) {state₀ state₁ : Nat}
    (read₀ read₁ : Option Bool)
    (hstate₀ : state₀ < D.stateCount)
    (hstate₁ : state₁ < D.stateCount)
    (hne : (state₀, read₀) ≠ (state₁, read₁)) :
    TransitionSourceDisjoint
      (afterRead0JumpTape1ReaderTransitions D state₀ read₀)
      (afterRead0JumpTape1ReaderTransitions D state₁ read₁) := by
  intro t u ht hu hsource
  have hpair :
      state₀ = state₁ -> read₀ = read₁ -> False := by
    intro hstate hread
    exact hne (by cases hstate; cases hread; rfl)
  have hleftCases :=
    afterRead0JumpTape1ReaderTransitions_source_cases D read₀ ht
  have hrightCases :=
    afterRead0JumpTape1ReaderTransitions_source_cases D read₁ hu
  rcases hleftCases with hleftSource | hleftCases
  · rcases hrightCases with hrightSource | hrightCases
    · have hinner :
          3 * state₀ + ReadTuple3.readCode read₀ =
            3 * state₁ + ReadTuple3.readCode read₁ := by
        rw [hleftSource, hrightSource] at hsource
        unfold StaticDispatcherState.afterRead0 at hsource
        lia
      have hidx :=
        boundedRemainderIndex_eq_of_eq
          (slots := 3)
          (state₀ := state₀)
          (state₁ := state₁)
          (code₀ := ReadTuple3.readCode read₀)
          (code₁ := ReadTuple3.readCode read₁)
          (ReadTuple3.readCode_lt_three read₀)
          (ReadTuple3.readCode_lt_three read₁)
          hinner
      exact hpair hidx.left (readCode_injective hidx.right)
    · rcases hrightCases with hrightScratch | hrightReader
      · have hleftLt :
            StaticDispatcherState.afterRead0 D state₀ read₀ <
              StaticDispatcherState.readerStateLimit D :=
          Nat.lt_of_lt_of_le
            (StaticDispatcherState.afterRead0_lt_afterRead1Base
              D read₀ hstate₀)
            (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
        have hrightGe :
            StaticDispatcherState.readerStateLimit D ≤
              afterRead0JumpScratch D state₁ read₁ := by
          unfold afterRead0JumpScratch afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase
          lia
        rw [hleftSource, hrightScratch] at hsource
        lia
      · have hleftLt :
            StaticDispatcherState.afterRead0 D state₀ read₀ <
              StaticDispatcherState.readerStateLimit D :=
          Nat.lt_of_lt_of_le
            (StaticDispatcherState.afterRead0_lt_afterRead1Base
              D read₀ hstate₀)
            (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
        have hrightGe :
            StaticDispatcherState.readerStateLimit D ≤ u.source :=
          Nat.le_trans
            (readerStateLimit_le_tape1ReaderOffset D state₁ read₁)
            hrightReader.left
        rw [hleftSource] at hsource
        lia
  · rcases hleftCases with hleftScratch | hleftReader
    · rcases hrightCases with hrightSource | hrightCases
      · have hleftGe :
            StaticDispatcherState.readerStateLimit D ≤
              afterRead0JumpScratch D state₀ read₀ := by
          unfold afterRead0JumpScratch afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase
          lia
        have hrightLt :
            StaticDispatcherState.afterRead0 D state₁ read₁ <
              StaticDispatcherState.readerStateLimit D :=
          Nat.lt_of_lt_of_le
            (StaticDispatcherState.afterRead0_lt_afterRead1Base
              D read₁ hstate₁)
            (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
        rw [hleftScratch, hrightSource] at hsource
        lia
      · rcases hrightCases with hrightScratch | hrightReader
        · have hinner :
              3 * state₀ + ReadTuple3.readCode read₀ =
                3 * state₁ + ReadTuple3.readCode read₁ := by
            rw [hleftScratch, hrightScratch] at hsource
            unfold afterRead0JumpScratch at hsource
            lia
          have hidx :=
            boundedRemainderIndex_eq_of_eq
              (slots := 3)
              (state₀ := state₀)
              (state₁ := state₁)
              (code₀ := ReadTuple3.readCode read₀)
              (code₁ := ReadTuple3.readCode read₁)
              (ReadTuple3.readCode_lt_three read₀)
              (ReadTuple3.readCode_lt_three read₁)
              hinner
          exact hpair hidx.left (readCode_injective hidx.right)
        · have hscratchLt :=
            afterRead0JumpScratch_lt_afterRead0JumpLimit
              D read₀ hstate₀
          have hreaderGe : afterRead0JumpLimit D ≤ u.source := by
            exact Nat.le_trans
              (by
                unfold tape1ReaderOffset tape1ReaderBlockBase
                exact Nat.le_add_right _ _)
              hrightReader.left
          rw [hleftScratch] at hsource
          lia
    · rcases hrightCases with hrightSource | hrightCases
      · have hleftGe :
            StaticDispatcherState.readerStateLimit D ≤ t.source :=
          Nat.le_trans
            (readerStateLimit_le_tape1ReaderOffset D state₀ read₀)
            hleftReader.left
        have hrightLt :
            StaticDispatcherState.afterRead0 D state₁ read₁ <
              StaticDispatcherState.readerStateLimit D :=
          Nat.lt_of_lt_of_le
            (StaticDispatcherState.afterRead0_lt_afterRead1Base
              D read₁ hstate₁)
            (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
        rw [hrightSource] at hsource
        lia
      · rcases hrightCases with hrightScratch | hrightReader
        · have hleftGe : afterRead0JumpLimit D ≤ t.source := by
            exact Nat.le_trans
              (by
                unfold tape1ReaderOffset tape1ReaderBlockBase
                exact Nat.le_add_right _ _)
              hleftReader.left
          have hscratchLt :=
            afterRead0JumpScratch_lt_afterRead0JumpLimit
              D read₁ hstate₁
          rw [hrightScratch] at hsource
          lia
        · have hrightReader' := hrightReader
          rw [← hsource] at hrightReader'
          unfold tape1ReaderOffset tape1ReaderBlockBase
            at hleftReader hrightReader'
          have hidxNe :
              ReadTuple3.readCode read₀ * D.stateCount + state₀ ≠
                ReadTuple3.readCode read₁ * D.stateCount + state₁ := by
            intro hidx
            have hparts :=
              boundedRemainderIndex_eq_of_eq
                (slots := D.stateCount)
                (state₀ := ReadTuple3.readCode read₀)
                (state₁ := ReadTuple3.readCode read₁)
                (code₀ := state₀)
                (code₁ := state₁)
                hstate₀ hstate₁
                (by simpa [Nat.mul_comm] using hidx)
            exact hpair hparts.right
              (readCode_injective hparts.left)
          exact
            indexedReaderBlocks_source_ne_of_state_ne
              (base := afterRead0JumpLimit D)
              (blockCount :=
                branchingTape1ReadHeadCellAndReturnToSeparatorDescription.stateCount)
              (source := t.source)
              hidxNe hleftReader hrightReader'

theorem afterRead1JumpTape2ReaderTransitions_sourceDisjoint_of_ne
    (D : Description) {state₀ state₁ : Nat}
    (read₀ read₁ read₀' read₁' : Option Bool)
    (hstate₀ : state₀ < D.stateCount)
    (hstate₁ : state₁ < D.stateCount)
    (hne : ((state₀, read₀), read₁) ≠ ((state₁, read₀'), read₁')) :
    TransitionSourceDisjoint
      (afterRead1JumpTape2ReaderTransitions D state₀ read₀ read₁)
      (afterRead1JumpTape2ReaderTransitions D state₁ read₀' read₁') := by
  intro t u ht hu hsource
  have htuple :
      state₀ = state₁ -> read₀ = read₀' -> read₁ = read₁' -> False := by
    intro hstate hread₀ hread₁
    exact hne (by cases hstate; cases hread₀; cases hread₁; rfl)
  have hleftCases :=
    afterRead1JumpTape2ReaderTransitions_source_cases D read₀ read₁ ht
  have hrightCases :=
    afterRead1JumpTape2ReaderTransitions_source_cases D read₀' read₁' hu
  rcases hleftCases with hleftSource | hleftCases
  · rcases hrightCases with hrightSource | hrightCases
    · have hinner :
          9 * state₀ + ReadTuple3.code01 read₀ read₁ =
            9 * state₁ + ReadTuple3.code01 read₀' read₁' := by
        rw [hleftSource, hrightSource] at hsource
        unfold StaticDispatcherState.afterRead1 at hsource
        lia
      have hidx :=
        boundedRemainderIndex_eq_of_eq
          (slots := 9)
          (state₀ := state₀)
          (state₁ := state₁)
          (code₀ := ReadTuple3.code01 read₀ read₁)
          (code₁ := ReadTuple3.code01 read₀' read₁')
          (ReadTuple3.code01_lt_nine read₀ read₁)
          (ReadTuple3.code01_lt_nine read₀' read₁')
          hinner
      have hreads := code01_injective hidx.right
      exact htuple hidx.left hreads.left hreads.right
    · rcases hrightCases with hrightScratch | hrightReader
      · have hleftLt :=
          StaticDispatcherState.afterRead1_lt_readerStateLimit
            D read₀ read₁ hstate₀
        have hrightGe :
            StaticDispatcherState.readerStateLimit D ≤
              afterRead1JumpScratch D state₁ read₀' read₁' := by
          unfold afterRead1JumpScratch afterRead1JumpScratchBase
            tape1ReaderLimit tape1ReaderBlockBase
            afterRead0JumpLimit afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase
          lia
        rw [hleftSource, hrightScratch] at hsource
        lia
      · have hleftLt :=
          StaticDispatcherState.afterRead1_lt_readerStateLimit
            D read₀ read₁ hstate₀
        have hrightGe :
            StaticDispatcherState.readerStateLimit D ≤ u.source :=
          Nat.le_trans
            (readerStateLimit_le_tape2ReaderOffset
              D state₁ read₀' read₁')
            hrightReader.left
        rw [hleftSource] at hsource
        lia
  · rcases hleftCases with hleftScratch | hleftReader
    · rcases hrightCases with hrightSource | hrightCases
      · have hleftGe :
            StaticDispatcherState.readerStateLimit D ≤
              afterRead1JumpScratch D state₀ read₀ read₁ := by
          unfold afterRead1JumpScratch afterRead1JumpScratchBase
            tape1ReaderLimit tape1ReaderBlockBase
            afterRead0JumpLimit afterRead0JumpScratchBase
            tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
            readyJumpScratchBase
          lia
        have hrightLt :=
          StaticDispatcherState.afterRead1_lt_readerStateLimit
            D read₀' read₁' hstate₁
        rw [hleftScratch, hrightSource] at hsource
        lia
      · rcases hrightCases with hrightScratch | hrightReader
        · have hinner :
              9 * state₀ + ReadTuple3.code01 read₀ read₁ =
                9 * state₁ + ReadTuple3.code01 read₀' read₁' := by
            rw [hleftScratch, hrightScratch] at hsource
            unfold afterRead1JumpScratch at hsource
            lia
          have hidx :=
            boundedRemainderIndex_eq_of_eq
              (slots := 9)
              (state₀ := state₀)
              (state₁ := state₁)
              (code₀ := ReadTuple3.code01 read₀ read₁)
              (code₁ := ReadTuple3.code01 read₀' read₁')
              (ReadTuple3.code01_lt_nine read₀ read₁)
              (ReadTuple3.code01_lt_nine read₀' read₁')
              hinner
          have hreads := code01_injective hidx.right
          exact htuple hidx.left hreads.left hreads.right
        · have hscratchLt :=
            afterRead1JumpScratch_lt_afterRead1JumpLimit
              D read₀ read₁ hstate₀
          have hreaderGe : afterRead1JumpLimit D ≤ u.source := by
            exact Nat.le_trans
              (by
                unfold tape2ReaderOffset tape2ReaderBlockBase
                exact Nat.le_add_right _ _)
              hrightReader.left
          rw [hleftScratch] at hsource
          lia
    · rcases hrightCases with hrightSource | hrightCases
      · have hleftGe :
            StaticDispatcherState.readerStateLimit D ≤ t.source :=
          Nat.le_trans
            (readerStateLimit_le_tape2ReaderOffset
              D state₀ read₀ read₁)
            hleftReader.left
        have hrightLt :=
          StaticDispatcherState.afterRead1_lt_readerStateLimit
            D read₀' read₁' hstate₁
        rw [hrightSource] at hsource
        lia
      · rcases hrightCases with hrightScratch | hrightReader
        · have hleftGe : afterRead1JumpLimit D ≤ t.source := by
            exact Nat.le_trans
              (by
                unfold tape2ReaderOffset tape2ReaderBlockBase
                exact Nat.le_add_right _ _)
              hleftReader.left
          have hscratchLt :=
            afterRead1JumpScratch_lt_afterRead1JumpLimit
              D read₀' read₁' hstate₁
          rw [hrightScratch] at hsource
          lia
        · have hrightReader' := hrightReader
          rw [← hsource] at hrightReader'
          unfold tape2ReaderOffset tape2ReaderBlockBase
            at hleftReader hrightReader'
          have hidxNe :
              ReadTuple3.code01 read₀ read₁ * D.stateCount + state₀ ≠
                ReadTuple3.code01 read₀' read₁' * D.stateCount + state₁ := by
            intro hidx
            have hparts :=
              boundedRemainderIndex_eq_of_eq
                (slots := D.stateCount)
                (state₀ := ReadTuple3.code01 read₀ read₁)
                (state₁ := ReadTuple3.code01 read₀' read₁')
                (code₀ := state₀)
                (code₁ := state₁)
                hstate₀ hstate₁
                (by simpa [Nat.mul_comm] using hidx)
            have hreads := code01_injective hparts.left
            exact htuple hparts.right hreads.left hreads.right
          exact
            indexedReaderBlocks_source_ne_of_state_ne
              (base := afterRead1JumpLimit D)
              (blockCount :=
                branchingTape2ReadHeadCellAndReturnToSeparatorDescription.stateCount)
              (source := t.source)
              hidxNe hleftReader hrightReader'

theorem afterRead0JumpTape1ReaderAllTransitions_deterministic
    (D : Description) :
    TransitionListDeterministic
      (afterRead0JumpTape1ReaderAllTransitions D) := by
  unfold afterRead0JumpTape1ReaderAllTransitions
  apply transitionListDeterministic_flatMap
  · intro read₀ _hread₀
    apply transitionListDeterministic_flatMap
    · intro state hstate
      exact
        afterRead0JumpTape1ReaderTransitions_deterministic
          D read₀ (activeStateValues_mem_lt hstate)
    · intro state₀ hstate₀ state₁ hstate₁ hne
      exact
        afterRead0JumpTape1ReaderTransitions_sourceDisjoint_of_ne
          D read₀ read₀
          (activeStateValues_mem_lt hstate₀)
          (activeStateValues_mem_lt hstate₁)
          (by
            intro hpair
            exact hne (congrArg Prod.fst hpair))
  · intro read₀ _hread₀ read₁ _hread₁ hne
    apply transitionSourceDisjoint_flatMap_left
    intro state₀ hstate₀
    apply transitionSourceDisjoint_flatMap_right
    intro state₁ hstate₁
    exact
      afterRead0JumpTape1ReaderTransitions_sourceDisjoint_of_ne
        D read₀ read₁
        (activeStateValues_mem_lt hstate₀)
        (activeStateValues_mem_lt hstate₁)
        (by
          intro hpair
          exact hne (congrArg Prod.snd hpair))

theorem afterRead1JumpTape2ReaderAllTransitions_deterministic
    (D : Description) :
    TransitionListDeterministic
      (afterRead1JumpTape2ReaderAllTransitions D) := by
  unfold afterRead1JumpTape2ReaderAllTransitions
  apply transitionListDeterministic_flatMap
  · intro read₀ _hread₀
    apply transitionListDeterministic_flatMap
    · intro read₁ _hread₁
      apply transitionListDeterministic_flatMap
      · intro state hstate
        exact
          afterRead1JumpTape2ReaderTransitions_deterministic
            D read₀ read₁ (activeStateValues_mem_lt hstate)
      · intro state₀ hstate₀ state₁ hstate₁ hne
        exact
          afterRead1JumpTape2ReaderTransitions_sourceDisjoint_of_ne
            D read₀ read₁ read₀ read₁
            (activeStateValues_mem_lt hstate₀)
            (activeStateValues_mem_lt hstate₁)
            (by
              intro htuple
              exact hne
                (congrArg Prod.fst (congrArg Prod.fst htuple)))
    · intro read₁ _hread₁ read₁' _hread₁' hne
      apply transitionSourceDisjoint_flatMap_left
      intro state₀ hstate₀
      apply transitionSourceDisjoint_flatMap_right
      intro state₁ hstate₁
      exact
        afterRead1JumpTape2ReaderTransitions_sourceDisjoint_of_ne
          D read₀ read₁ read₀ read₁'
          (activeStateValues_mem_lt hstate₀)
          (activeStateValues_mem_lt hstate₁)
          (by
            intro htuple
            exact hne (congrArg Prod.snd htuple))
  · intro read₀ _hread₀ read₀' _hread₀' hne
    apply transitionSourceDisjoint_flatMap_left
    intro read₁ _hread₁
    apply transitionSourceDisjoint_flatMap_left
    intro state₀ hstate₀
    apply transitionSourceDisjoint_flatMap_right
    intro read₁' _hread₁'
    apply transitionSourceDisjoint_flatMap_right
    intro state₁ hstate₁
    exact
      afterRead1JumpTape2ReaderTransitions_sourceDisjoint_of_ne
        D read₀ read₁ read₀' read₁'
        (activeStateValues_mem_lt hstate₀)
        (activeStateValues_mem_lt hstate₁)
        (by
          intro htuple
          exact hne
            (congrArg Prod.snd (congrArg Prod.fst htuple)))

theorem threeHeadReaderTransitions_deterministic
    (D : Description) :
    TransitionListDeterministic (threeHeadReaderTransitions D) := by
  simpa [threeHeadReaderTransitions] using
    transitionListDeterministic_append_of_sourceDisjoint
      (transitionListDeterministic_append_of_sourceDisjoint
        (readyJumpTape0ReaderAllTransitions_deterministic D)
        (afterRead0JumpTape1ReaderAllTransitions_deterministic D)
        (readyJumpTape0ReaderAll_afterRead0JumpTape1ReaderAll_sourceDisjoint
          D))
      (afterRead1JumpTape2ReaderAllTransitions_deterministic D)
      (readyAndAfterRead0All_afterRead1JumpTape2ReaderAll_sourceDisjoint
        D)

theorem threeHeadReaderDescription_wellFormed
    (D : Description) (hD : D.WellFormed) :
    (threeHeadReaderDescription D).WellFormed := by
  refine
    ⟨threeHeadReaderDescription_stateCount_pos D hD,
      threeHeadReaderDescription_start_lt D hD,
      threeHeadReaderDescription_halt_lt D hD,
      threeHeadReaderDescription_transitions_wellFormed D,
      ?_⟩
  simpa [threeHeadReaderDescription, MachineDescription.Deterministic,
    TransitionListDeterministic] using
    threeHeadReaderTransitions_deterministic D

theorem threeHeadReaderDescription_subroutineReady
    (D : Description) (hD : D.WellFormed) :
    (threeHeadReaderDescription D).SubroutineReady :=
  ⟨threeHeadReaderDescription_wellFormed D hD,
    threeHeadReaderDescription_haltTransitionFree
      D hD.right.right.right.left⟩

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
