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

def SelectedMergePaddedEmitterAfterTransitionPaddedSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
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
      emitter.HaltsFromTape
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
      emitter.HaltsFromTape
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
      emitter.HaltsFromTape
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
      parser.HaltsFromTape
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
      emitter.HaltsFromTape
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
