import FoC.Computability.Compiler.Core.EncodedRewriters

set_option doc.verso true

/-!
# Controller stage-input projection machine
-/

namespace FoC
namespace Computability

open Languages

def dovetailControllerProjectionKeep
    (source : Nat) (cell : Bool) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source (some cell) (some cell)
    Direction.right target

def dovetailControllerProjectionErase
    (source : Nat) (cell : Option Bool) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source cell none Direction.right target

def DovetailControllerStageInputProjectionDescription :
    MachineDescription where
  stateCount := 92
  start := 0
  halt := 91
  transitions :=
    [ dovetailControllerProjectionErase 0 (some false) 1
    , dovetailControllerProjectionErase 1 (some false) 2
    , dovetailControllerProjectionErase 2 (some false) 3
    , dovetailControllerProjectionErase 3 (some false) 10
    , dovetailControllerProjectionKeep 10 false 11
    , dovetailControllerProjectionKeep 11 false 12
    , dovetailControllerProjectionKeep 12 true 13
    , dovetailControllerProjectionKeep 13 false 10
    , dovetailControllerProjectionKeep 13 true 20
    , dovetailControllerProjectionKeep 20 false 21
    , dovetailControllerProjectionKeep 21 false 22
    , dovetailControllerProjectionKeep 21 true 25
    , dovetailControllerProjectionKeep 22 true 23
    , dovetailControllerProjectionKeep 23 false 30
    , dovetailControllerProjectionKeep 23 true 90
    , dovetailControllerProjectionKeep 25 false 26
    , dovetailControllerProjectionKeep 25 true 27
    , dovetailControllerProjectionKeep 26 true 20
    , dovetailControllerProjectionKeep 27 false 20
    , dovetailControllerProjectionKeep 30 false 31
    , dovetailControllerProjectionKeep 31 false 32
    , dovetailControllerProjectionKeep 32 true 33
    , dovetailControllerProjectionKeep 33 false 30
    , dovetailControllerProjectionKeep 33 true 90
    , dovetailControllerProjectionErase 90 (some false) 90
    , dovetailControllerProjectionErase 90 (some true) 90
    , dovetailControllerProjectionErase 90 none 91 ]

theorem dovetailControllerStageInputProjectionDescription_wellFormed :
    DovetailControllerStageInputProjectionDescription.WellFormed := by
  sorry

theorem dovetailControllerStageInputProjectionDescription_haltTransitionFree :
    DovetailControllerStageInputProjectionDescription.HaltTransitionFree := by
  simp [DovetailControllerStageInputProjectionDescription,
    MachineDescription.HaltTransitionFree, dovetailControllerProjectionKeep,
    dovetailControllerProjectionErase, MachineDescription.transition]

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_of_transform_eq_some
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
          code = some out) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) := by
  sorry

theorem dovetailControllerStageInputProjectionDescription_transform_eq_some_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (h :
      DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
  sorry

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff
    (code out : Word MachineCodeSymbol) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
  constructor
  · exact
      dovetailControllerStageInputProjectionDescription_transform_eq_some_of_haltsWithOutput
  · exact
      dovetailControllerStageInputProjectionDescription_haltsWithOutput_of_transform_eq_some

theorem dovetailControllerStageInputProjectionDescription_outputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      DovetailControllerStageInputProjectionDescription :=
  ⟨⟨dovetailControllerStageInputProjectionDescription_wellFormed,
      dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff⟩,
    dovetailControllerStageInputProjectionDescription_haltTransitionFree⟩

theorem encodedControllerStageInputProjectionCodeWordSubroutineConstruction_scaffold :
    EncodedControllerStageInputProjectionCodeWordSubroutineConstruction := by
  exact
    ⟨DovetailControllerStageInputProjectionDescription,
      dovetailControllerStageInputProjectionDescription_outputCompiledSubroutine⟩

end Computability
end FoC
