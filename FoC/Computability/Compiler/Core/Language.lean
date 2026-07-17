import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Description-backed compiler boundaries
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
## Description-backed language recognition and decision
-/

def MachineDescriptionAcceptsLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.WellFormed ∧ forall w : Word Bool, D.HaltsOnInput w <-> w ∈ L

def MachineDescriptionDecidesLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool,
      (w ∈ L -> D.HaltsWithOutput w [true]) ∧
        (¬ w ∈ L -> D.HaltsWithOutput w [false])

/-!
The stopped contract additionally requires the designated halt state to have
no outgoing description transition. Since the two result symbols are the
distinct Boolean values, it compiles to an honest stopped Turing decider.
-/

def StoppedMachineDescriptionDecidesLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.HaltTransitionFree ∧ MachineDescriptionDecidesLanguage D L

theorem stoppedMachineDescriptionDecidesLanguage_decides
    {D : MachineDescription} {L : Language Bool}
    (h : StoppedMachineDescriptionDecidesLanguage D L) :
    MachineDescriptionDecidesLanguage D L :=
  h.right

namespace StoppedMachineDescriptionDecidesLanguage

theorem output_eq_of_haltsWithOutput
    {D : MachineDescription} {L : Language Bool}
    (h : StoppedMachineDescriptionDecidesLanguage D L)
    {w out : Word Bool}
    (hout : D.HaltsWithOutput w out) :
    (w ∈ L -> out = [true]) ∧ (¬ w ∈ L -> out = [false]) := by
  constructor
  · intro hw
    exact haltsWithOutput_functional_of_haltTransitionFree
      h.left hout ((h.right.right w).left hw)
  · intro hw
    exact haltsWithOutput_functional_of_haltTransitionFree
      h.left hout ((h.right.right w).right hw)

end StoppedMachineDescriptionDecidesLanguage

theorem machineDescriptionAcceptsLanguage_turingAcceptable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionAcceptsLanguage D L) :
    TuringAcceptable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  intro w
  rw [encodeWord_id]
  exact Iff.trans (toTuringMachine_haltsOnInput_iff
    h.left w) (h.right w)

theorem machineDescriptionDecidesLanguage_turingDecidable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionDecidesLanguage D L) :
    TuringDecidable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  exists false
  exists true
  intro w
  constructor
  · intro hw
    rw [encodeWord_id]
    exact (toTuringMachine_haltsWithOutput_iff
      h.left w [true]).mpr ((h.right w).left hw)
  · intro hw
    rw [encodeWord_id]
    exact (toTuringMachine_haltsWithOutput_iff
      h.left w [false]).mpr ((h.right w).right hw)

theorem stoppedMachineDescriptionDecidesLanguage_stoppedTuringDecidable
    {D : MachineDescription} {L : Language Bool}
    (h : StoppedMachineDescriptionDecidesLanguage D L) :
    StoppedTuringDecidable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  exists false
  exists true
  constructor
  · exact toTuringMachine_haltingTransitionsDisabled h.right.left h.left
  · constructor
    · decide
    · intro w
      constructor
      · intro hw
        rw [encodeWord_id]
        exact (toTuringMachine_haltsWithOutput_iff
          h.right.left w [true]).mpr ((h.right.right w).left hw)
      · intro hw
        rw [encodeWord_id]
        exact (toTuringMachine_haltsWithOutput_iff
          h.right.left w [false]).mpr ((h.right.right w).right hw)

/-!
## Staged-program compiler predicates
-/

def ProgramCompiledByDescription
    (P : StagedProgram Bool Unit) (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool,
      D.HaltsOnInput w <-> ProgramHaltsWithOutput P w []

theorem programCompiledByDescription_of_same_accepted_language
    {P Q : StagedProgram Bool Unit} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramAcceptsLanguage P L)
    (hQ : ProgramAcceptsLanguage Q L)
    (hcompile : ProgramCompiledByDescription P D) :
    ProgramCompiledByDescription Q D :=
  ⟨hcompile.left, fun w =>
    Iff.trans (hcompile.right w)
      (Iff.trans (hP w) (Iff.symm (hQ w)))⟩

def BoolProgramCompiledByDescription
    (P : StagedProgram Bool Bool) (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      D.HaltsWithOutput w [b] <-> ProgramHaltsWithOutput P w [b]

def ProgramAcceptableByDescription (L : Language Bool) : Prop :=
  exists P : StagedProgram Bool Unit, exists D : MachineDescription,
    ProgramAcceptsLanguage P L ∧ ProgramCompiledByDescription P D

def ProgramBoolDecidableByDescription (L : Language Bool) : Prop :=
  exists P : StagedProgram Bool Bool, exists D : MachineDescription,
    ProgramBoolDecides P L ∧ BoolProgramCompiledByDescription P D

theorem programCompiledByDescription_acceptsLanguage
    {P : StagedProgram Bool Unit} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramAcceptsLanguage P L)
    (hcompile : ProgramCompiledByDescription P D) :
    MachineDescriptionAcceptsLanguage D L :=
  ⟨hcompile.left, fun w => Iff.trans (hcompile.right w) (hP w)⟩

theorem boolProgramCompiledByDescription_decidesLanguage
    {P : StagedProgram Bool Bool} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramBoolDecides P L)
    (hcompile : BoolProgramCompiledByDescription P D) :
    MachineDescriptionDecidesLanguage D L :=
  ⟨hcompile.left, fun w => by
    constructor
    · intro hw
      exact (hcompile.right w true).mpr ((hP.left w).mpr hw)
    · intro hw
      exact (hcompile.right w false).mpr ((hP.right w).mpr hw)⟩

theorem programAcceptableByDescription_turingAcceptable
    {L : Language Bool}
    (h : ProgramAcceptableByDescription L) :
    TuringAcceptable L := by
  cases h with
  | intro P hP =>
      cases hP with
      | intro D hD =>
          exact machineDescriptionAcceptsLanguage_turingAcceptable
            (programCompiledByDescription_acceptsLanguage hD.left hD.right)

theorem programBoolDecidableByDescription_turingDecidable
    {L : Language Bool}
    (h : ProgramBoolDecidableByDescription L) :
    TuringDecidable L := by
  cases h with
  | intro P hP =>
      cases hP with
      | intro D hD =>
          exact machineDescriptionDecidesLanguage_turingDecidable
            (boolProgramCompiledByDescription_decidesLanguage hD.left hD.right)

def DescriptionProgramAcceptorCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Unit,
    exists D : MachineDescription, ProgramCompiledByDescription P D

theorem programAcceptableByDescription_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple)
    {L : Language Bool}
    (h : ProgramAcceptable L) :
    ProgramAcceptableByDescription L := by
  rcases h with ⟨P, hP⟩
  rcases hcompile P with ⟨D, hD⟩
  exact ⟨P, D, hP, hD⟩

theorem turingAcceptable_programAcceptableByDescription_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple)
    {L : Language Bool}
    (h : TuringAcceptable L) :
    ProgramAcceptableByDescription L :=
  programAcceptableByDescription_of_descriptionCompiler hcompile
    (turingAcceptable_programAcceptable h)

def DescriptionProgramBoolDeciderCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Bool,
    exists D : MachineDescription, BoolProgramCompiledByDescription P D

def DovetailDescriptionCompilerPrinciple : Prop :=
  forall (accept reject : Word Bool -> Nat -> Prop)
    [∀ w n, Decidable (accept w n)]
    [∀ w n, Decidable (reject w n)],
    exists D : MachineDescription,
      BoolProgramCompiledByDescription (DovetailProgram accept reject) D

end Computability
end FoC
