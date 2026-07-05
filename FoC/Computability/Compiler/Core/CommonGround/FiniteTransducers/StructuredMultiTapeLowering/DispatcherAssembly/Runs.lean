import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.DispatcherAssembly.Determinism

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace StaticDispatcherReaderAssembly

def tableMachine (stateCount start halt : Nat)
    (transitions : List TransitionDescription) : MachineDescription where
  stateCount := stateCount
  start := start
  halt := halt
  transitions := transitions

theorem find?_matches_none_of_sources_below
    {bound state : Nat} {cell : Option Bool}
    {transitions : List TransitionDescription}
    (hbelow : TransitionSourcesBelow bound transitions)
    (hstate : bound ≤ state) :
    transitions.find? (MachineDescription.Matches state cell) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have hmatchPair : t.source = state ∧ t.read = cell := by
    simpa [MachineDescription.Matches] using hmatch
  have hsource : t.source = state := by
    exact hmatchPair.left
  exact Nat.not_lt_of_ge hstate (by simpa [hsource] using hbelow t ht)

theorem find?_matches_none_of_sources_atLeast
    {bound state : Nat} {cell : Option Bool}
    {transitions : List TransitionDescription}
    (hatLeast : TransitionSourcesAtLeast bound transitions)
    (hstate : state < bound) :
    transitions.find? (MachineDescription.Matches state cell) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have hmatchPair : t.source = state ∧ t.read = cell := by
    simpa [MachineDescription.Matches] using hmatch
  have hsource : t.source = state := by
    exact hmatchPair.left
  exact Nat.not_le_of_gt hstate (by simpa [hsource] using hatLeast t ht)

theorem find?_append_right_of_left_sources_below
    {bound state : Nat} {cell : Option Bool}
    {left right : List TransitionDescription}
    (hleft : TransitionSourcesBelow bound left)
    (hstate : bound ≤ state) :
    (left ++ right).find? (MachineDescription.Matches state cell) =
      right.find? (MachineDescription.Matches state cell) := by
  rw [List.find?_append,
    find?_matches_none_of_sources_below hleft hstate]
  simp

theorem find?_append_left_of_right_sources_atLeast
    {bound state : Nat} {cell : Option Bool}
    {left right : List TransitionDescription}
    (hright : TransitionSourcesAtLeast bound right)
    (hstate : state < bound) :
    (left ++ right).find? (MachineDescription.Matches state cell) =
      left.find? (MachineDescription.Matches state cell) := by
  rw [List.find?_append,
    find?_matches_none_of_sources_atLeast hright hstate]
  cases left.find? (MachineDescription.Matches state cell) <;> simp

theorem tableMachine_stepConfig_append_right_of_left_sources_below
    {stateCount start halt bound : Nat}
    {left right : List TransitionDescription}
    {c : MachineDescription.Configuration}
    (hleft : TransitionSourcesBelow bound left)
    (hstate : bound ≤ c.state) :
    (tableMachine stateCount start halt (left ++ right)).stepConfig c =
      (tableMachine stateCount start halt right).stepConfig c := by
  simp [tableMachine, MachineDescription.stepConfig,
    MachineDescription.lookupTransition,
    find?_append_right_of_left_sources_below hleft hstate]

theorem tableMachine_stepConfig_append_left_of_right_sources_atLeast
    {stateCount start halt bound : Nat}
    {left right : List TransitionDescription}
    {c : MachineDescription.Configuration}
    (hright : TransitionSourcesAtLeast bound right)
    (hstate : c.state < bound) :
    (tableMachine stateCount start halt (left ++ right)).stepConfig c =
      (tableMachine stateCount start halt left).stepConfig c := by
  simp [tableMachine, MachineDescription.stepConfig,
    MachineDescription.lookupTransition,
    find?_append_left_of_right_sources_atLeast hright hstate]

theorem tableMachine_runConfig_append_right_of_left_sources_below
    {stateCount start halt bound n : Nat}
    {left right : List TransitionDescription}
    {c : MachineDescription.Configuration}
    (hleft : TransitionSourcesBelow bound left)
    (hstates :
      forall k : Nat, k < n ->
        bound ≤
          ((tableMachine stateCount start halt right).runConfig k c).state) :
    (tableMachine stateCount start halt (left ++ right)).runConfig n c =
      (tableMachine stateCount start halt right).runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hstate : bound ≤ c.state := by
        simpa [MachineDescription.runConfig] using hstates 0 (Nat.succ_pos n)
      have hstep :=
        tableMachine_stepConfig_append_right_of_left_sources_below
          (stateCount := stateCount) (start := start) (halt := halt)
          (bound := bound) (left := left) (right := right)
          (c := c) hleft hstate
      cases hrightStep :
          (tableMachine stateCount start halt right).stepConfig c with
      | none =>
          have hwholeStep :
              (tableMachine stateCount start halt (left ++ right)).stepConfig c =
                none := by
            simpa [hstep] using hrightStep
          simp [MachineDescription.runConfig, hwholeStep, hrightStep]
      | some next =>
          have hwholeStep :
              (tableMachine stateCount start halt (left ++ right)).stepConfig c =
                some next := by
            simpa [hstep] using hrightStep
          simp [MachineDescription.runConfig, hwholeStep, hrightStep]
          apply ih
          intro k hk
          have hk' : k + 1 < Nat.succ n := Nat.succ_lt_succ hk
          have h := hstates (k + 1) hk'
          simpa [MachineDescription.runConfig, hrightStep] using h

theorem tableMachine_runConfig_append_left_of_right_sources_atLeast
    {stateCount start halt bound n : Nat}
    {left right : List TransitionDescription}
    {c : MachineDescription.Configuration}
    (hright : TransitionSourcesAtLeast bound right)
    (hstates :
      forall k : Nat, k < n ->
        ((tableMachine stateCount start halt left).runConfig k c).state <
          bound) :
    (tableMachine stateCount start halt (left ++ right)).runConfig n c =
      (tableMachine stateCount start halt left).runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hstate : c.state < bound := by
        simpa [MachineDescription.runConfig] using hstates 0 (Nat.succ_pos n)
      have hstep :=
        tableMachine_stepConfig_append_left_of_right_sources_atLeast
          (stateCount := stateCount) (start := start) (halt := halt)
          (bound := bound) (left := left) (right := right)
          (c := c) hright hstate
      cases hleftStep :
          (tableMachine stateCount start halt left).stepConfig c with
      | none =>
          have hwholeStep :
              (tableMachine stateCount start halt (left ++ right)).stepConfig c =
                none := by
            simpa [hstep] using hleftStep
          simp [MachineDescription.runConfig, hwholeStep, hleftStep]
      | some next =>
          have hwholeStep :
              (tableMachine stateCount start halt (left ++ right)).stepConfig c =
                some next := by
            simpa [hstep] using hleftStep
          simp [MachineDescription.runConfig, hwholeStep, hleftStep]
          apply ih
          intro k hk
          have hk' : k + 1 < Nat.succ n := Nat.succ_lt_succ hk
          have h := hstates (k + 1) hk'
          simpa [MachineDescription.runConfig, hleftStep] using h

theorem runsFromStateTapeEquiv_tableMachine_append_right_of_left_sources_below_of_run
    {stateCount start halt bound : Nat}
    {left right : List TransitionDescription}
    {sourceState targetState n : Nat}
    {Tin Tout : Tape Bool}
    {actual : Tape Bool}
    (hleft : TransitionSourcesBelow bound left)
    (hrun :
      (tableMachine stateCount start halt right).runConfig n
          { state := sourceState, tape := Tin } =
        { state := targetState, tape := actual })
    (hequiv : Tape.Equiv actual Tout)
    (hstates :
      forall k : Nat, k < n ->
        bound ≤
          ((tableMachine stateCount start halt right).runConfig k
            { state := sourceState, tape := Tin }).state) :
    RunsFromStateTapeEquiv
      (tableMachine stateCount start halt (left ++ right))
      sourceState targetState Tin Tout := by
  exact
    ⟨n, actual, by
      rw [tableMachine_runConfig_append_right_of_left_sources_below
        hleft hstates]
      exact hrun,
      hequiv⟩

theorem runsFromStateTapeEquiv_tableMachine_append_left_of_right_sources_atLeast_of_run
    {stateCount start halt bound : Nat}
    {left right : List TransitionDescription}
    {sourceState targetState n : Nat}
    {Tin Tout : Tape Bool}
    {actual : Tape Bool}
    (hright : TransitionSourcesAtLeast bound right)
    (hrun :
      (tableMachine stateCount start halt left).runConfig n
          { state := sourceState, tape := Tin } =
        { state := targetState, tape := actual })
    (hequiv : Tape.Equiv actual Tout)
    (hstates :
      forall k : Nat, k < n ->
        ((tableMachine stateCount start halt left).runConfig k
          { state := sourceState, tape := Tin }).state < bound) :
    RunsFromStateTapeEquiv
      (tableMachine stateCount start halt (left ++ right))
      sourceState targetState Tin Tout := by
  exact
    ⟨n, actual, by
      rw [tableMachine_runConfig_append_left_of_right_sources_atLeast
        hright hstates]
      exact hrun,
      hequiv⟩

theorem guardedDropOne_exists_of_length_three
    {logical : List (Tape Bool)} (hlength : logical.length = 3) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      (guardLogicalTapes logical).drop 1 = T :: rest := by
  cases logical with
  | nil =>
      simp at hlength
  | cons _ rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons T rest =>
          exact
            ⟨guardLogicalTape T, guardLogicalTapes rest,
              by simp [guardLogicalTapes]⟩

theorem guardedHasAtLeastThreeTapes_of_length_three
    {logical : List (Tape Bool)} (hlength : logical.length = 3) :
    HasAtLeastThreeTapes (guardLogicalTapes logical) := by
  cases logical with
  | nil =>
      simp at hlength
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons U rest =>
          cases rest with
          | nil =>
              simp at hlength
          | cons V rest =>
              exact
                ⟨guardLogicalTape T, guardLogicalTape U,
                  guardLogicalTape V, guardLogicalTapes rest,
                  by simp [guardLogicalTapes]⟩

theorem tape1ReaderDescription_runsFromExistingBlockStart
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hlength : logical.length = 3)
    (hstart :
      AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 1
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tape1ReaderDescription D state read0)
          (tape1ReaderStart D state read0)
          (StaticDispatcherState.afterRead1 D state read0
            (Tape.read (Description.tapeAt logical 1)))
          physical
          separatorPhysical := by
  rcases
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
        (logical := guardLogicalTapes logical)
        (physical := physical)
        hstart
        (guardedDropOne_exists_of_length_three hlength) with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetReadExitRetargetDescription
      (offset := tape1ReaderOffset D state read0)
      (localTarget :=
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget)
      (target := StaticDispatcherState.tape1ReaderTargets D state read0)
      (tape1ReaderTargets_lt_tape1ReaderOffset D read0 hstate)
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
      (observed := Tape.read (Description.tapeAt logical 1))
      (by
        simpa [tapeAt_guardLogicalTapes_read] using hrun)
  exact
    ⟨separatorPhysical, hseparator, by
      cases hread : Tape.read (Description.tapeAt logical 1) with
      | none =>
          simpa
            [tape1ReaderDescription, tape1ReaderStart,
              retargetedBranchingTape1ReadHeadCellAllExitsDescription,
              MachineDescription.offsetReadExitRetargetDescription,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape1ReaderTargets,
              StaticDispatcherState.tape1ReaderTarget,
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopy
      | some bit =>
          cases bit with
          | false =>
              simpa
                [tape1ReaderDescription, tape1ReaderStart,
                  retargetedBranchingTape1ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  StaticDispatcherState.tape1ReaderTargets,
                  StaticDispatcherState.tape1ReaderTarget,
                  branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using hcopy
          | true =>
              simpa
                [tape1ReaderDescription, tape1ReaderStart,
                  retargetedBranchingTape1ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  StaticDispatcherState.tape1ReaderTargets,
                  StaticDispatcherState.tape1ReaderTarget,
                  branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using hcopy⟩

theorem tape2ReaderDescription_runsFromExistingBlockStart
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hlength : logical.length = 3)
    (hstart :
      AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tape2ReaderDescription D state read0 read1)
          (tape2ReaderStart D state read0 read1)
          (StaticDispatcherState.afterRead D state
            { read0 := read0,
              read1 := read1,
              read2 := Tape.read (Description.tapeAt logical 2) })
          physical
          separatorPhysical := by
  rcases
      branchingTape2ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
        (logical := guardLogicalTapes logical)
        (physical := physical)
        hstart
        (guardedHasAtLeastThreeTapes_of_length_three hlength) with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetReadExitRetargetDescription
      (offset := tape2ReaderOffset D state read0 read1)
      (localTarget :=
        branchingTape2ReadHeadCellAndReturnToSeparatorTarget)
      (target :=
        StaticDispatcherState.tape2ReaderTargets D state read0 read1)
      (tape2ReaderTargets_lt_tape2ReaderOffset D read0 read1 hstate)
      branchingTape2ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
      (observed := Tape.read (Description.tapeAt logical 2))
      (by
        simpa [tapeAt_guardLogicalTapes_read] using hrun)
  exact
    ⟨separatorPhysical, hseparator, by
      cases hread : Tape.read (Description.tapeAt logical 2) with
      | none =>
          simpa
            [tape2ReaderDescription, tape2ReaderStart,
              retargetedBranchingTape2ReadHeadCellAllExitsDescription,
              MachineDescription.offsetReadExitRetargetDescription,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape2ReaderTargets,
              StaticDispatcherState.tape2ReaderTarget,
              branchingTape2ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopy
      | some bit =>
          cases bit with
          | false =>
              simpa
                [tape2ReaderDescription, tape2ReaderStart,
                  retargetedBranchingTape2ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  StaticDispatcherState.tape2ReaderTargets,
                  StaticDispatcherState.tape2ReaderTarget,
                  branchingTape2ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using hcopy
          | true =>
              simpa
                [tape2ReaderDescription, tape2ReaderStart,
                  retargetedBranchingTape2ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  StaticDispatcherState.tape2ReaderTargets,
                  StaticDispatcherState.tape2ReaderTarget,
                  branchingTape2ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using hcopy⟩

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
