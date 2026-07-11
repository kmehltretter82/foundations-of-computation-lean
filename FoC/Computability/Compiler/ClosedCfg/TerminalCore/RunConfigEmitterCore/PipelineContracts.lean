import FoC.Computability.Compiler.Core.CommonGround.SeqComposition

set_option doc.verso true

/-!
# Exact-output pipeline contracts

The #18 input materializer, structured lowering, and physical handoffs may
retain harmless far-edge blank padding.  The last serializer nevertheless has
an exact public target.  Its honest contract must therefore accept every tape
equivalent to the canonical guarded endpoint and normalize all of them to the
same exact output.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace PipelineContracts

/-- A final phase that normalizes every equivalent representative of an
indexed source to one exact indexed output. -/
def EquivInputExactOutputSpec {ι : Type}
    (source target : ι -> Tape Bool)
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (i : ι) (actual : Tape Bool),
      Tape.Equiv actual (source i) ->
        normalizer.HaltsFromTape actual (target i)

def EquivInputExactOutputConstruction {ι : Type}
    (source target : ι -> Tape Bool) : Prop :=
  exists normalizer : MachineDescription,
    EquivInputExactOutputSpec source target normalizer

theorem EquivInputExactOutputSpec.canonical {ι : Type}
    {source target : ι -> Tape Bool}
    {normalizer : MachineDescription}
    (hspec : EquivInputExactOutputSpec source target normalizer)
    (i : ι) :
    normalizer.HaltsFromTape (source i) (target i) := by
  exact hspec.right i (source i) (Tape.Equiv.refl _)

/-- Determinism guardrail: equivalent indexed sources may not demand distinct
exact targets under an equivalence-input exact-output contract. -/
theorem EquivInputExactOutputSpec.target_eq_of_source_equiv {ι : Type}
    {source target : ι -> Tape Bool}
    {normalizer : MachineDescription}
    (hspec : EquivInputExactOutputSpec source target normalizer)
    {i j : ι}
    (hsource : Tape.Equiv (source i) (source j)) :
    target i = target j := by
  have hi := hspec.canonical i
  have hjFromI := hspec.right j (source i) hsource
  exact
    haltsFromTape_functional_of_haltTransitionFree
      hspec.left.right hi hjFromI

/-- Compose an ordinary first phase that reaches its indexed midpoint only up
to tape equivalence with a final exact normalizer.  The sequential handoff move
is included in the final phase's canonical source family. -/
theorem seqSubroutine_haltsFromTape_of_firstEquiv_secondExact
    {ι : Type}
    {first normalizer : MachineDescription}
    {handoffMove : Direction}
    {input midpoint target : ι -> Tape Bool}
    (hfirstReady : first.SubroutineReady)
    (hnormalizer :
      EquivInputExactOutputSpec
        (fun i => Tape.move handoffMove (midpoint i))
        target normalizer)
    (i : ι)
    (hfirst :
      first.HaltsFromTapeEquiv (input i) (midpoint i)) :
    (seqSubroutine first normalizer handoffMove).HaltsFromTape
      (input i) (target i) := by
  rcases hfirst with ⟨actual, hactual, hactualEquiv⟩
  have hnextEquiv :
      Tape.Equiv
        (Tape.move handoffMove actual)
        (Tape.move handoffMove (midpoint i)) :=
    Tape.Equiv.move hactualEquiv handoffMove
  have hnormalizerRun :=
    hnormalizer.right i (Tape.move handoffMove actual) hnextEquiv
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      hfirstReady hnormalizer.left hactual rfl hnormalizerRun

/-- Family-level construction form of the previous composition. -/
theorem seqSubroutine_exactFamily_of_firstEquiv_secondExact
    {ι : Type}
    {first normalizer : MachineDescription}
    {handoffMove : Direction}
    {input midpoint target : ι -> Tape Bool}
    (hfirstReady : first.SubroutineReady)
    (hfirst : forall i : ι,
      first.HaltsFromTapeEquiv (input i) (midpoint i))
    (hnormalizer :
      EquivInputExactOutputSpec
        (fun i => Tape.move handoffMove (midpoint i))
        target normalizer) :
    (seqSubroutine first normalizer handoffMove).SubroutineReady ∧
      forall i : ι,
        (seqSubroutine first normalizer handoffMove).HaltsFromTape
          (input i) (target i) := by
  constructor
  · exact seqSubroutine_subroutineReady hfirstReady hnormalizer.left
  · intro i
    exact seqSubroutine_haltsFromTape_of_firstEquiv_secondExact
      hfirstReady hnormalizer i (hfirst i)

end PipelineContracts
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
