import FoC.Computability.Compiler.Structured.Lowering.Layout

set_option doc.verso true

/-!
# Structured input materializer contract

This module names the reusable boundary contract for entering a lowered
three-logical-tape computation from a public one-tape source.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

/--
Physical target shape for a three-logical-tape input materializer.

Tape 0 is the public source tape, tape 1 is the blank scratch/counter tape, and
tape 2 is a caller-provided output-buffer tape determined by the same input
index as the source.
-/
def structured3InputMaterializerTargetTape
    (source output : Tape Bool) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
    source Tape.blank output

theorem structured3InputMaterializerTargetTape_eq_encodedGuardedStructuredTapes
    (source output : Tape Bool) :
    structured3InputMaterializerTargetTape source output =
      Structured.MultiTapeLowering.encodedGuardedStructuredTapes
        [source, Tape.blank, output] := by
  rfl

theorem structured3InputMaterializerTargetTape_read
    (source output : Tape Bool) :
    Tape.read (structured3InputMaterializerTargetTape source output) =
      none := by
  rfl

theorem structured3InputMaterializerTargetTape_cells
    (source output : Tape Bool) :
    Tape.cells (structured3InputMaterializerTargetTape source output) =
      List.append Structured.MultiTapeLowering.tapeSeparatorCells
        (List.append
          (Structured.MultiTapeLowering.logicalTapeCode
            (Structured.MultiTapeLowering.guardLogicalTape source))
          (List.append Structured.MultiTapeLowering.tapeSeparatorCells
            (List.append
              (Structured.MultiTapeLowering.logicalTapeCode
                (Structured.MultiTapeLowering.guardLogicalTape Tape.blank))
              (List.append Structured.MultiTapeLowering.tapeSeparatorCells
                (List.append
                  (Structured.MultiTapeLowering.logicalTapeCode
                    (Structured.MultiTapeLowering.guardLogicalTape output))
                  Structured.MultiTapeLowering.tapeSeparatorCells))))) := by
  exact
    Structured.MultiTapeLowering.encodedGuardedStructuredTapes_three_cells
      source Tape.blank output

theorem structured3InputMaterializerTargetTape_normalizedOutput
    (source output : Tape Bool) :
    Tape.normalizedOutput
        (structured3InputMaterializerTargetTape source output) =
      List.append
        (Structured.MultiTapeLowering.logicalTapeBits
          (Structured.MultiTapeLowering.guardLogicalTape source))
        (List.append
          (Structured.MultiTapeLowering.logicalTapeBits
            (Structured.MultiTapeLowering.guardLogicalTape Tape.blank))
          (Structured.MultiTapeLowering.logicalTapeBits
            (Structured.MultiTapeLowering.guardLogicalTape output))) := by
  rw [Tape.normalizedOutput, structured3InputMaterializerTargetTape_cells]
  simp [Structured.MultiTapeLowering.logicalTapeCode_eq_map_some,
    Structured.MultiTapeLowering.tapeSeparatorCells,
    List.filterMap_append, Function.comp_def]

/--
Reusable materializer contract for entering a three-logical-tape structured
subroutine.

The index fixes both the public source tape and the tape-2 output buffer.  This
keeps the target functional for each source family and avoids the impossible
legacy contracts that quantified over arbitrary output padding.
-/
def Structured3InputMaterializerSpec {ι : Type}
    (source output : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall input : ι,
      materializer.HaltsFromTapeEquiv
        (source input)
        (structured3InputMaterializerTargetTape
          (source input) (output input))

def Structured3InputMaterializerConstruction {ι : Type}
    (source output : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    Structured3InputMaterializerSpec source output materializer

/--
Generic target-family view of a public one-tape materializer.

This is useful when a caller already has a named structured target tape and
wants to defer the proof that it is the canonical
{name}`structured3InputMaterializerTargetTape`.
-/
def Structured3InputTargetFamilySpec {ι : Type}
    (source target : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall input : ι,
      materializer.HaltsFromTapeEquiv
        (source input) (target input)

def Structured3InputTargetFamilyConstruction {ι : Type}
    (source target : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    Structured3InputTargetFamilySpec source target materializer

theorem structured3InputMaterializerSpec_subroutineReady {ι : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerSpec source output materializer) :
    materializer.SubroutineReady :=
  hmaterializer.left

theorem structured3InputMaterializerSpec_haltsFromTapeEquiv {ι : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerSpec source output materializer)
    (input : ι) :
    materializer.HaltsFromTapeEquiv
      (source input)
      (structured3InputMaterializerTargetTape
        (source input) (output input)) :=
  hmaterializer.right input

theorem structured3InputTargetFamilySpec_subroutineReady {ι : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilySpec source target materializer) :
    materializer.SubroutineReady :=
  hmaterializer.left

theorem structured3InputTargetFamilySpec_haltsFromTapeEquiv {ι : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilySpec source target materializer)
    (input : ι) :
    materializer.HaltsFromTapeEquiv
      (source input) (target input) :=
  hmaterializer.right input

theorem structured3InputTargetFamilySpec_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilySpec source target materializer)
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input) :
    Structured3InputTargetFamilySpec source' target' materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [hsource input, htarget input] using hrun input

theorem structured3InputTargetFamilySpec_iff_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input)
    (materializer : MachineDescription) :
    Structured3InputTargetFamilySpec source' target' materializer ↔
      Structured3InputTargetFamilySpec source target materializer := by
  constructor
  · intro hmaterializer
    exact
      structured3InputTargetFamilySpec_of_eq hmaterializer
        (fun input => (hsource input).symm)
        (fun input => (htarget input).symm)
  · intro hmaterializer
    exact
      structured3InputTargetFamilySpec_of_eq hmaterializer
        hsource htarget

theorem structured3InputTargetFamilyConstruction_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyConstruction source target)
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input) :
    Structured3InputTargetFamilyConstruction source' target' := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputTargetFamilySpec_of_eq hspec hsource htarget⟩

theorem structured3InputTargetFamilyConstruction_iff_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input) :
    Structured3InputTargetFamilyConstruction source' target' ↔
      Structured3InputTargetFamilyConstruction source target := by
  constructor
  · intro hmaterializer
    exact
      structured3InputTargetFamilyConstruction_of_eq hmaterializer
        (fun input => (hsource input).symm)
        (fun input => (htarget input).symm)
  · intro hmaterializer
    exact
      structured3InputTargetFamilyConstruction_of_eq hmaterializer
        hsource htarget

theorem structured3InputTargetFamilySpec_reindex {ι κ : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilySpec source target materializer)
    (index : κ -> ι) :
    Structured3InputTargetFamilySpec
      (fun input : κ => source (index input))
      (fun input : κ => target (index input))
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  exact ⟨hready, fun input => hrun (index input)⟩

theorem structured3InputTargetFamilyConstruction_reindex {ι κ : Type}
    {source target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyConstruction source target)
    (index : κ -> ι) :
    Structured3InputTargetFamilyConstruction
      (fun input : κ => source (index input))
      (fun input : κ => target (index input)) := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputTargetFamilySpec_reindex hspec index⟩

theorem structured3InputTargetFamilySpec_of_materializerSpec {ι : Type}
    {source output target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerSpec source output materializer)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputTargetFamilySpec source target materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [htarget input] using hrun input

theorem structured3InputMaterializerSpec_of_targetFamilySpec {ι : Type}
    {source output target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilySpec source target materializer)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputMaterializerSpec source output materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [htarget input] using hrun input

theorem structured3InputMaterializerSpec_iff_targetFamilySpec {ι : Type}
    {source output target : ι -> Tape Bool}
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input))
    (materializer : MachineDescription) :
    Structured3InputMaterializerSpec source output materializer ↔
      Structured3InputTargetFamilySpec source target materializer := by
  constructor
  · intro hmaterializer
    exact
      structured3InputTargetFamilySpec_of_materializerSpec
        hmaterializer htarget
  · intro hmaterializer
    exact
      structured3InputMaterializerSpec_of_targetFamilySpec
        hmaterializer htarget

theorem structured3InputTargetFamilyConstruction_of_materializerConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerConstruction source output)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputTargetFamilyConstruction source target := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputTargetFamilySpec_of_materializerSpec
        hspec htarget⟩

theorem structured3InputMaterializerConstruction_of_targetFamilyConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyConstruction source target)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputMaterializerConstruction source output := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputMaterializerSpec_of_targetFamilySpec
        hspec htarget⟩

theorem structured3InputMaterializerConstruction_iff_targetFamilyConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    Structured3InputMaterializerConstruction source output ↔
      Structured3InputTargetFamilyConstruction source target := by
  constructor
  · intro hmaterializer
    exact
      structured3InputTargetFamilyConstruction_of_materializerConstruction
        hmaterializer htarget
  · intro hmaterializer
    exact
      structured3InputMaterializerConstruction_of_targetFamilyConstruction
        hmaterializer htarget

theorem structured3InputMaterializerSpec_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerSpec source output materializer)
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input) :
    Structured3InputMaterializerSpec source' output' materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro input
  simpa [hsource input, houtput input] using hrun input

theorem structured3InputMaterializerSpec_iff_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input)
    (materializer : MachineDescription) :
    Structured3InputMaterializerSpec source' output' materializer ↔
      Structured3InputMaterializerSpec source output materializer := by
  constructor
  · intro hmaterializer
    exact
      structured3InputMaterializerSpec_of_eq hmaterializer
        (fun input => (hsource input).symm)
        (fun input => (houtput input).symm)
  · intro hmaterializer
    exact
      structured3InputMaterializerSpec_of_eq hmaterializer
        hsource houtput

theorem structured3InputMaterializerConstruction_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerConstruction source output)
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input) :
    Structured3InputMaterializerConstruction source' output' := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputMaterializerSpec_of_eq hspec hsource houtput⟩

theorem structured3InputMaterializerConstruction_iff_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input) :
    Structured3InputMaterializerConstruction source' output' ↔
      Structured3InputMaterializerConstruction source output := by
  constructor
  · intro hmaterializer
    exact
      structured3InputMaterializerConstruction_of_eq hmaterializer
        (fun input => (hsource input).symm)
        (fun input => (houtput input).symm)
  · intro hmaterializer
    exact
      structured3InputMaterializerConstruction_of_eq hmaterializer
        hsource houtput

theorem structured3InputMaterializerSpec_reindex {ι κ : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerSpec source output materializer)
    (index : κ -> ι) :
    Structured3InputMaterializerSpec
      (fun input : κ => source (index input))
      (fun input : κ => output (index input))
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  exact ⟨hready, fun input => hrun (index input)⟩

theorem structured3InputMaterializerConstruction_reindex {ι κ : Type}
    {source output : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerConstruction source output)
    (index : κ -> ι) :
    Structured3InputMaterializerConstruction
      (fun input : κ => source (index input))
      (fun input : κ => output (index input)) := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      structured3InputMaterializerSpec_reindex hspec index⟩

end FiniteTransducers
end CommonGround
end Computability
end FoC
