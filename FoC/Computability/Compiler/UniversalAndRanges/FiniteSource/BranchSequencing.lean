import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.BranchEmitters.Spec

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

def CodePrefixParserBranchTaggedMachineSpec
    (branch : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens out : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput branch tokens out <->
      (MachineDescription.decodeDescriptionPrefix tokens = none ∧
        out = MachineDescription.encodeBoolWord [false]) ∨
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix tokens =
            some (D, input) ∧
          out =
            MachineDescription.encodeBoolWordAppend [true] tokens

def CodePrefixParserBranchTaggedMachineConstruction : Prop :=
  exists state : Type,
  exists branch : TuringMachine MachineCodeSymbol state,
    CodePrefixParserBranchTaggedMachineSpec branch

theorem codePrefixParserBranchCodeMachineConstruction_of_taggedMachine
    (htagged : CodePrefixParserBranchTaggedMachineConstruction) :
    CodePrefixParserBranchCodeMachineConstruction := by
  rcases htagged with ⟨state, branch, hbranch⟩
  refine ⟨state, branch, ?_⟩
  intro tokens out
  rw [hbranch tokens out]
  constructor
  · intro h
    rcases h with hfailure | hsuccess
    · exact
        (codePrefixParserBranchCode_transform_eq_some_iff
          tokens out).mpr (Or.inl hfailure)
    · rcases hsuccess with ⟨D, input, hdecode, hout⟩
      have htokens :
          tokens = List.append (MachineDescription.encodeDescription D)
            input :=
        MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
          hdecode
      exact
        (codePrefixParserBranchCode_transform_eq_some_iff
          tokens out).mpr
          (Or.inr
            ⟨D, input, hdecode, by simpa [htokens] using hout⟩)
  · intro h
    rcases
        (codePrefixParserBranchCode_transform_eq_some_iff
          tokens out).mp h with
      hfailure | hsuccess
    · exact Or.inl hfailure
    · rcases hsuccess with ⟨D, input, hdecode, hout⟩
      have htokens :
          tokens = List.append (MachineDescription.encodeDescription D)
            input :=
        MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
          hdecode
      exact Or.inr
        ⟨D, input, hdecode, by simpa [htokens] using hout⟩

theorem codePrefixParserBranchTaggedMachineConstruction_finite :
    CodePrefixParserBranchTaggedMachineConstruction := by
  refine ⟨CodePrefixParserBranchState, codePrefixParserBranchMachine, ?_⟩
  exact codePrefixParserBranchMachine_haltsWithOutput_iff

theorem codePrefixParserBranchCodeMachineConstruction_scaffold :
    CodePrefixParserBranchCodeMachineConstruction :=
  codePrefixParserBranchCodeMachineConstruction_of_taggedMachine
    codePrefixParserBranchTaggedMachineConstruction_finite

theorem codePrefixParserBranchMachineConstruction_scaffold :
    CodePrefixParserBranchMachineConstruction :=
  codePrefixParserBranchMachineConstruction_of_codeMachine
    codePrefixParserBranchCodeMachineConstruction_scaffold

end Computability
end FoC
