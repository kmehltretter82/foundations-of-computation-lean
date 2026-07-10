import FoC.Computability.Compiler.ClosedCfg.PostTrans.BranchHandoffShape

set_option doc.verso true

/-!
# Padded merge post-transition construction specs

This module contains only the construction-family contracts for the padded
merge post-transition phase.  The source-field/nested-layout tape facts live
below this module, and the composition adapters live in the downstream adapter
module.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

/-!
The branch-parametric specs below are stated in the honest tape-equivalence
currency ({name}`MachineDescription.HaltsFromTapeEquiv`): every downstream
consumer weakens to equivalence before reaching the public
{name}`SelectedMergeEquivEmitterSpec` contract, so exact window accounting is
not demanded of the finite-machine leaves.  The nested-layout parser uses the
same currency because its first contextual materializer cannot shrink the
represented tape window exactly.
-/

def SelectedMergePaddedEmitterAfterTransitionPaddedSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTapeEquiv
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterAfterTransitionPaddedConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergePaddedEmitterAfterTransitionPaddedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterTransitionPaddedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterHitPaddedSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTapeEquiv
        (SelectedMergePaddedEmitterAfterHitPaddedTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterHitPaddedDecodedSpec
    (useAccept : Bool) (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTapeEquiv
        (SelectedMergePaddedEmitterAfterHitPaddedTape p)
        (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p)

def SelectedMergePaddedEmitterAfterHitPaddedDecodedConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedDecodedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsSpec
    (useAccept : Bool) (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTapeEquiv
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p)

def SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsSpec
      useAccept emitter

def SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec
    (parser : MachineDescription) : Prop :=
  parser.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      parser.HaltsFromTapeEquiv
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)

def SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction :
    Prop :=
  exists parser : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec parser

def SelectedMergePaddedEmitterAfterHitPaddedParsedInnerSpec
    (useAccept : Bool) (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTapeEquiv
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
        (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p)

def SelectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerSpec useAccept emitter

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
