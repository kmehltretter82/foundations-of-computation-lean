import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress

set_option doc.verso true

/-!
# Finite realization frontier for guarded #18 egress

The parent module proves an executable exact decoder for the guarded tape-0
payload, an executable metadata/scratch/witness decoder for tape 2, and exact
semantic assembly of the required right-scratch target.  This module isolates
the one remaining implementation question: realize that checked transform by
a finite one-tape description while accepting every far-edge-padded
representative of the guarded source and retaining its harmless outer padding.

Tape 0 is handled directly from the outer separator by
{lit}`GuardedEgress.RawPairQuoter`, which carries the untouched tape-1/tape-2
suffix forward for the later metadata assembly.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress
namespace FiniteRealization

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-!
## Realization contract for the checked transform
-/

/-- A finite normalizer realizes every successful result of the checked
parse-and-assemble transform on every equivalent physical representative, up
to far-edge blank padding. -/
def Spec (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (i : Index) (actual target : Tape Bool),
      Tape.Equiv actual i.source ->
        SemanticAssembly.assembleTarget
            (SemanticAssembly.tape0Payload i) i.doneWitnessTape =
          some target ->
        normalizer.HaltsFromTapeEquiv actual target

def Construction : Prop :=
  exists normalizer : MachineDescription, Spec normalizer

/-- It is enough to realize the checked transform from each canonical guarded
source.  Run equivalence transports the resulting execution to every
far-edge-padded representative, and output equivalence composes with the
canonical result. -/
def CanonicalSpec (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall i : Index,
      normalizer.HaltsFromTapeEquiv i.source i.target

def CanonicalConstruction : Prop :=
  exists normalizer : MachineDescription, CanonicalSpec normalizer

theorem spec_of_canonicalSpec
    {normalizer : MachineDescription}
    (hcanonical : CanonicalSpec normalizer) : Spec normalizer := by
  constructor
  · exact hcanonical.left
  · intro i actual target hequiv htarget
    rw [SemanticAssembly.assembleTarget_index] at htarget
    cases htarget
    rcases hcanonical.right i with
      ⟨canonicalOutput, hcanonicalRun, hcanonicalOutput⟩
    rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm hequiv) hcanonicalRun with
      ⟨actualOutput, hactualRun, hactualOutput⟩
    exact
      ⟨actualOutput, hactualRun,
        Tape.Equiv.trans hactualOutput hcanonicalOutput⟩

theorem construction_of_canonicalConstruction
    (hcanonical : CanonicalConstruction) : Construction := by
  rcases hcanonical with ⟨normalizer, hnormalizer⟩
  exact ⟨normalizer, spec_of_canonicalSpec hnormalizer⟩

theorem guardedEgressSpec_of_spec
    {normalizer : MachineDescription} (hspec : Spec normalizer) :
    GuardedEgress.Spec normalizer := by
  constructor
  · exact hspec.left
  · intro i actual hequiv
    exact hspec.right i actual i.target hequiv
      (SemanticAssembly.assembleTarget_index i)

theorem spec_of_guardedEgressSpec
    {normalizer : MachineDescription}
    (hspec : GuardedEgress.Spec normalizer) : Spec normalizer := by
  constructor
  · exact hspec.left
  · intro i actual target hequiv htarget
    rw [SemanticAssembly.assembleTarget_index] at htarget
    cases htarget
    exact hspec.right i actual hequiv

theorem guardedEgressConstruction_of_construction
    (hconstruction : Construction) : GuardedEgress.Construction := by
  rcases hconstruction with ⟨normalizer, hnormalizer⟩
  exact ⟨normalizer, guardedEgressSpec_of_spec hnormalizer⟩

theorem construction_of_guardedEgressConstruction
    (hconstruction : GuardedEgress.Construction) : Construction := by
  rcases hconstruction with ⟨normalizer, hnormalizer⟩
  exact ⟨normalizer, spec_of_guardedEgressSpec hnormalizer⟩

/-!
## Exact raw-segment ingress
-/

/-- Physical cells following the tape-0 closing separator. -/
def tape0PayloadPadding (i : Index) : List (Option Bool) :=
  List.append
    (logicalTapeCode (guardLogicalTape i.consumedStageTape))
    (List.append tapeSeparatorCells
      (List.append
        (logicalTapeCode (guardLogicalTape i.doneWitnessTape))
        tapeSeparatorCells))

/-!
## Narrow remaining machine leaf
-/

/-- Machine-level parser/assembler after the clean raw-segment ingress.  The
implementation must retain exact pair alignment and head-marker position,
decode tape-2 metadata and witness fields, and normalize all outer padding to
the exact target. -/
def RawGuardedParserAssemblerConstruction : Prop := Construction

theorem construction_of_rawGuardedParserAssembler
    (hparser : RawGuardedParserAssemblerConstruction) : Construction :=
  hparser

end FiniteRealization
end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
