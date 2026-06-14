import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Description-backed compiler boundaries
-/

namespace FoC
namespace Computability

open Languages

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
  exact Iff.trans (MachineDescription.toTuringMachine_haltsOnInput_iff
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
    exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
      h.left w [true]).mpr ((h.right w).left hw)
  · intro hw
    rw [encodeWord_id]
    exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
      h.left w [false]).mpr ((h.right w).right hw)

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
    ProgramCompiledByDescription Q D := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w)
      (Iff.trans (hP w) (Iff.symm (hQ w)))

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
    MachineDescriptionAcceptsLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w) (hP w)

theorem boolProgramCompiledByDescription_decidesLanguage
    {P : StagedProgram Bool Bool} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramBoolDecides P L)
    (hcompile : BoolProgramCompiledByDescription P D) :
    MachineDescriptionDecidesLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    constructor
    · intro hw
      exact (hcompile.right w true).mpr ((hP.left w).mpr hw)
    · intro hw
      exact (hcompile.right w false).mpr ((hP.right w).mpr hw)

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

/-
The next aliases separate semantic compiler assumptions from finite-source
compiler targets.  A semantic assumption quantifies over arbitrary Lean staged
programs or traces.  A finite-source construction has concrete finite data as
input, such as a supplied {name}`MachineDescription`.
-/

def SemanticDescriptionAcceptorCompilerAssumption : Prop :=
  DescriptionProgramAcceptorCompilationPrinciple

theorem programAcceptableByDescription_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple)
    {L : Language Bool}
    (h : ProgramAcceptable L) :
    ProgramAcceptableByDescription L := by
  rcases h with ⟨P, hP⟩
  rcases hcompile P with ⟨D, hD⟩
  exact ⟨P, D, hP, hD⟩

theorem recursivelyEnumerable_programAcceptableByDescription_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerable L) :
    ProgramAcceptableByDescription L :=
  programAcceptableByDescription_of_descriptionCompiler hcompile
    (recursivelyEnumerable_programAcceptable h)

def DescriptionProgramBoolDeciderCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Bool,
    exists D : MachineDescription, BoolProgramCompiledByDescription P D

def SemanticDescriptionBoolDeciderCompilerAssumption : Prop :=
  DescriptionProgramBoolDeciderCompilationPrinciple

def DovetailDescriptionCompilerPrinciple : Prop :=
  forall accept reject : Word Bool -> Nat -> Prop,
    exists D : MachineDescription,
      BoolProgramCompiledByDescription (DovetailProgram accept reject) D

def SemanticDovetailDescriptionCompilerAssumption : Prop :=
  DovetailDescriptionCompilerPrinciple


end Computability
end FoC
