import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.TapeLemmas

set_option doc.verso true

/-!
# Guarded-egress pipeline contracts

The #18 input materializer, structured lowering, and physical handoffs may
retain harmless far-edge blank padding.  The former attempt to normalize every
such representative to one exact physical tape is impossible by context-length
monotonicity.  The viable contract retains the padding up to tape equivalence,
which still fixes the exact normalized output word and head-relative layout.
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

/-- Add invisible far-right blank padding to a represented tape. -/
def rightPaddedRepresentative (T : Tape Bool) (padding : Nat) : Tape Bool :=
  { T with right := T.right ++ List.replicate padding none }

theorem rightPaddedRepresentative_equiv
    (T : Tape Bool) (padding : Nat) :
    Tape.Equiv (rightPaddedRepresentative T padding) T := by
  constructor
  · rfl
  · constructor
    · rfl
    · exact FoC.Computability.dropTrailingNone_append_replicate_none
        T.right padding

theorem rightPaddedRepresentative_contextLength
    (T : Tape Bool) (padding : Nat) :
    Tape.contextLength (rightPaddedRepresentative T padding) =
      Tape.contextLength T + padding := by
  simp [rightPaddedRepresentative, Tape.contextLength]
  lia

/-- No exact target can be reached uniformly from every padding-equivalent
representative: the input representative can always be padded beyond the
target's context length. -/
theorem equivInputExactOutputConstruction_impossible
    {ι : Type} (i : ι) (source target : ι -> Tape Bool) :
    ¬ EquivInputExactOutputConstruction source target := by
  intro hconstruction
  rcases hconstruction with ⟨normalizer, hnormalizer⟩
  let actual :=
    rightPaddedRepresentative
      (source i) (Tape.contextLength (target i) + 1)
  have hequiv : Tape.Equiv actual (source i) := by
    exact rightPaddedRepresentative_equiv _ _
  have hrun := hnormalizer.right i actual hequiv
  have hgt :
      Tape.contextLength (target i) < Tape.contextLength actual := by
    rw [show Tape.contextLength actual =
        Tape.contextLength (source i) +
          (Tape.contextLength (target i) + 1) by
      exact rightPaddedRepresentative_contextLength _ _]
    lia
  exact MachineDescription.not_haltsFromTape_of_contextLength_gt hgt hrun

/-- A viable final phase accepts every equivalent source representative and
halts on a tape equivalent to the indexed target.  This preserves exact
normalized output and head-relative layout without demanding an impossible
context-length shrink. -/
def EquivInputEquivOutputSpec {ι : Type}
    (source target : ι -> Tape Bool)
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (i : ι) (actual : Tape Bool),
      Tape.Equiv actual (source i) ->
        normalizer.HaltsFromTapeEquiv actual (target i)

def EquivInputEquivOutputConstruction {ι : Type}
    (source target : ι -> Tape Bool) : Prop :=
  exists normalizer : MachineDescription,
    EquivInputEquivOutputSpec source target normalizer

theorem EquivInputEquivOutputSpec.canonical {ι : Type}
    {source target : ι -> Tape Bool}
    {normalizer : MachineDescription}
    (hspec : EquivInputEquivOutputSpec source target normalizer)
    (i : ι) :
    normalizer.HaltsFromTapeEquiv (source i) (target i) := by
  exact hspec.right i (source i) (Tape.Equiv.refl _)

/-- Compose an equivalence-producing first phase with the viable
equivalence-input/equivalence-output final phase. -/
theorem seqSubroutine_haltsFromTapeEquiv_of_firstEquiv_secondEquiv
    {ι : Type}
    {first normalizer : MachineDescription}
    {handoffMove : Direction}
    {input midpoint target : ι -> Tape Bool}
    (hfirstReady : first.SubroutineReady)
    (hnormalizer :
      EquivInputEquivOutputSpec
        (fun i => Tape.move handoffMove (midpoint i))
        target normalizer)
    (i : ι)
    (hfirst :
      first.HaltsFromTapeEquiv (input i) (midpoint i)) :
    (seqSubroutine first normalizer handoffMove).HaltsFromTapeEquiv
      (input i) (target i) := by
  rcases hfirst with ⟨actual, hactual, hactualEquiv⟩
  have hnextEquiv :
      Tape.Equiv
        (Tape.move handoffMove actual)
        (Tape.move handoffMove (midpoint i)) :=
    Tape.Equiv.move hactualEquiv handoffMove
  rcases hnormalizer.right i (Tape.move handoffMove actual) hnextEquiv with
    ⟨output, houtput, houtputEquiv⟩
  refine ⟨output, ?_, houtputEquiv⟩
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      hfirstReady hnormalizer.left hactual rfl houtput

end PipelineContracts
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
