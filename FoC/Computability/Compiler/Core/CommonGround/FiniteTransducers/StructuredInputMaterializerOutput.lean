import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer

set_option doc.verso true

/-!
# Structured input materializer output contracts

This module records normalized-output views of the reusable three-logical-tape
input materializer contracts.  The exact {lit}`HaltsFromTapeEquiv`
contracts remain the primary executable boundary; these output contracts are
for downstream routes that only inspect the emitted word and do not depend on
the final cursor position.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

/--
Output-level view of a materializer whose target is the canonical structured
three-tape target.
-/
def Structured3InputMaterializerOutputSpec {ι : Type}
    (source output : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall input : ι,
      materializer.HaltsFromTapeWithOutput
        (source input)
        (Tape.normalizedOutput
          (structured3InputMaterializerTargetTape
            (source input) (output input)))

def Structured3InputMaterializerOutputConstruction {ι : Type}
    (source output : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    Structured3InputMaterializerOutputSpec source output materializer

/--
Output-level view of a materializer with an already-named target family.
-/
def Structured3InputTargetFamilyOutputSpec {ι : Type}
    (source target : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall input : ι,
      materializer.HaltsFromTapeWithOutput
        (source input) (Tape.normalizedOutput (target input))

def Structured3InputTargetFamilyOutputConstruction {ι : Type}
    (source target : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    Structured3InputTargetFamilyOutputSpec source target materializer

theorem structured3InputMaterializerOutputSpec_subroutineReady {ι : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerOutputSpec source output materializer) :
    materializer.SubroutineReady :=
  hmaterializer.left

theorem structured3InputMaterializerOutputSpec_haltsFromTapeWithOutput
    {ι : Type} {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerOutputSpec source output materializer)
    (input : ι) :
    materializer.HaltsFromTapeWithOutput
      (source input)
      (Tape.normalizedOutput
        (structured3InputMaterializerTargetTape
          (source input) (output input))) :=
  hmaterializer.right input

theorem structured3InputTargetFamilyOutputSpec_subroutineReady {ι : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilyOutputSpec source target materializer) :
    materializer.SubroutineReady :=
  hmaterializer.left

theorem structured3InputTargetFamilyOutputSpec_haltsFromTapeWithOutput
    {ι : Type} {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilyOutputSpec source target materializer)
    (input : ι) :
    materializer.HaltsFromTapeWithOutput
      (source input) (Tape.normalizedOutput (target input)) :=
  hmaterializer.right input

theorem structured3InputMaterializerOutputSpec_of_exact {ι : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerSpec source output materializer) :
    Structured3InputMaterializerOutputSpec source output materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun input)

theorem structured3InputMaterializerOutputConstruction_of_exact {ι : Type}
    {source output : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerConstruction source output) :
    Structured3InputMaterializerOutputConstruction source output := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputMaterializerOutputSpec_of_exact hspec⟩

theorem structured3InputTargetFamilyOutputSpec_of_exact {ι : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilySpec source target materializer) :
    Structured3InputTargetFamilyOutputSpec source target materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun input)

theorem structured3InputTargetFamilyOutputConstruction_of_exact {ι : Type}
    {source target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyConstruction source target) :
    Structured3InputTargetFamilyOutputConstruction source target := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputTargetFamilyOutputSpec_of_exact hspec⟩

theorem structured3InputTargetFamilyOutputSpec_of_materializerOutputSpec
    {ι : Type} {source output target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerOutputSpec source output materializer)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputTargetFamilyOutputSpec source target materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [htarget input] using hrun input

theorem structured3InputMaterializerOutputSpec_of_targetFamilyOutputSpec
    {ι : Type} {source output target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilyOutputSpec source target materializer)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputMaterializerOutputSpec source output materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [htarget input] using hrun input

theorem structured3InputMaterializerOutputSpec_iff_targetFamilyOutputSpec
    {ι : Type} {source output target : ι -> Tape Bool}
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input))
    (materializer : MachineDescription) :
    Structured3InputMaterializerOutputSpec source output materializer ↔
      Structured3InputTargetFamilyOutputSpec source target materializer := by
  constructor
  · intro hmaterializer
    exact
      structured3InputTargetFamilyOutputSpec_of_materializerOutputSpec
        hmaterializer htarget
  · intro hmaterializer
    exact
      structured3InputMaterializerOutputSpec_of_targetFamilyOutputSpec
        hmaterializer htarget

theorem structured3InputTargetFamilyOutputConstruction_of_materializerOutputConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerOutputConstruction source output)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputTargetFamilyOutputConstruction source target := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputTargetFamilyOutputSpec_of_materializerOutputSpec
        hspec htarget⟩

theorem structured3InputMaterializerOutputConstruction_of_targetFamilyOutputConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyOutputConstruction source target)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputMaterializerOutputConstruction source output := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputMaterializerOutputSpec_of_targetFamilyOutputSpec
        hspec htarget⟩

theorem structured3InputMaterializerOutputConstruction_iff_targetFamilyOutputConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputMaterializerOutputConstruction source output ↔
      Structured3InputTargetFamilyOutputConstruction source target := by
  constructor
  · intro hmaterializer
    exact
      structured3InputTargetFamilyOutputConstruction_of_materializerOutputConstruction
        hmaterializer htarget
  · intro hmaterializer
    exact
      structured3InputMaterializerOutputConstruction_of_targetFamilyOutputConstruction
        hmaterializer htarget

theorem structured3InputTargetFamilyOutputSpec_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilyOutputSpec source target materializer)
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input) :
    Structured3InputTargetFamilyOutputSpec source' target' materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [hsource input, htarget input] using hrun input

theorem structured3InputTargetFamilyOutputSpec_iff_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input)
    (materializer : MachineDescription) :
    Structured3InputTargetFamilyOutputSpec source' target' materializer ↔
      Structured3InputTargetFamilyOutputSpec source target materializer := by
  constructor
  · intro hmaterializer
    exact
      structured3InputTargetFamilyOutputSpec_of_eq hmaterializer
        (fun input => (hsource input).symm)
        (fun input => (htarget input).symm)
  · intro hmaterializer
    exact
      structured3InputTargetFamilyOutputSpec_of_eq hmaterializer
        hsource htarget

theorem structured3InputTargetFamilyOutputConstruction_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyOutputConstruction source target)
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input) :
    Structured3InputTargetFamilyOutputConstruction source' target' := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputTargetFamilyOutputSpec_of_eq hspec
        hsource htarget⟩

theorem structured3InputTargetFamilyOutputConstruction_iff_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input) :
    Structured3InputTargetFamilyOutputConstruction source' target' ↔
      Structured3InputTargetFamilyOutputConstruction source target := by
  constructor
  · intro hmaterializer
    exact
      structured3InputTargetFamilyOutputConstruction_of_eq hmaterializer
        (fun input => (hsource input).symm)
        (fun input => (htarget input).symm)
  · intro hmaterializer
    exact
      structured3InputTargetFamilyOutputConstruction_of_eq hmaterializer
        hsource htarget

theorem structured3InputTargetFamilyOutputSpec_reindex {ι κ : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilyOutputSpec source target materializer)
    (index : κ -> ι) :
    Structured3InputTargetFamilyOutputSpec
      (fun input : κ => source (index input))
      (fun input : κ => target (index input))
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  exact ⟨hready, fun input => hrun (index input)⟩

theorem structured3InputTargetFamilyOutputConstruction_reindex
    {ι κ : Type} {source target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyOutputConstruction source target)
    (index : κ -> ι) :
    Structured3InputTargetFamilyOutputConstruction
      (fun input : κ => source (index input))
      (fun input : κ => target (index input)) := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputTargetFamilyOutputSpec_reindex hspec index⟩

theorem structured3InputMaterializerOutputSpec_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerOutputSpec source output materializer)
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input) :
    Structured3InputMaterializerOutputSpec source' output' materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [hsource input, houtput input] using hrun input

theorem structured3InputMaterializerOutputSpec_iff_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input)
    (materializer : MachineDescription) :
    Structured3InputMaterializerOutputSpec source' output' materializer ↔
      Structured3InputMaterializerOutputSpec source output materializer := by
  constructor
  · intro hmaterializer
    exact
      structured3InputMaterializerOutputSpec_of_eq hmaterializer
        (fun input => (hsource input).symm)
        (fun input => (houtput input).symm)
  · intro hmaterializer
    exact
      structured3InputMaterializerOutputSpec_of_eq hmaterializer
        hsource houtput

theorem structured3InputMaterializerOutputConstruction_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerOutputConstruction source output)
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input) :
    Structured3InputMaterializerOutputConstruction source' output' := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputMaterializerOutputSpec_of_eq hspec hsource houtput⟩

theorem structured3InputMaterializerOutputConstruction_iff_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input) :
    Structured3InputMaterializerOutputConstruction source' output' ↔
      Structured3InputMaterializerOutputConstruction source output := by
  constructor
  · intro hmaterializer
    exact
      structured3InputMaterializerOutputConstruction_of_eq hmaterializer
        (fun input => (hsource input).symm)
        (fun input => (houtput input).symm)
  · intro hmaterializer
    exact
      structured3InputMaterializerOutputConstruction_of_eq hmaterializer
        hsource houtput

theorem structured3InputMaterializerOutputSpec_reindex {ι κ : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerOutputSpec source output materializer)
    (index : κ -> ι) :
    Structured3InputMaterializerOutputSpec
      (fun input : κ => source (index input))
      (fun input : κ => output (index input))
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  exact ⟨hready, fun input => hrun (index input)⟩

theorem structured3InputMaterializerOutputConstruction_reindex
    {ι κ : Type} {source output : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerOutputConstruction source output)
    (index : κ -> ι) :
    Structured3InputMaterializerOutputConstruction
      (fun input : κ => source (index input))
      (fun input : κ => output (index input)) := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputMaterializerOutputSpec_reindex hspec index⟩

end FiniteTransducers
end CommonGround
end Computability
end FoC
