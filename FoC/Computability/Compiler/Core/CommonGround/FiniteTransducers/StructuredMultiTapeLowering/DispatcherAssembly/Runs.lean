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
