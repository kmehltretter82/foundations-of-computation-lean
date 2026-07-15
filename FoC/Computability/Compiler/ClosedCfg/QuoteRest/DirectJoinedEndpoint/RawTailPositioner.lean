import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerOutput
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingPrefixScanner
import FoC.Computability.Compiler.Core.CommonGround.Identity

set_option doc.verso true

/-!
# Joined-output raw-tail positioner

The direct closeout emits the normalized joined word at its first bit.  This
positioner validates the canonical header and quoted Boolean-word field, then
uses the scanner handoff move to halt at the first bit of the live raw tail.
It preserves the word exactly and supplies the physical head position required
by the retained selected-projection consumer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CanonicalLayouts.DovetailLayoutScanner
open SelectedProjectionPaddedTailCleanup

def joinedOutputRawTailPositionerDescription : MachineDescription :=
  seqSubroutine
    postPaddingOutputPrefixScannerDescription
    ExactIdentityDescription
    Direction.right

theorem joinedOutputRawTailPositionerDescription_subroutineReady :
    joinedOutputRawTailPositionerDescription.SubroutineReady := by
  exact
    seqSubroutine_subroutineReady
      postPaddingOutputPrefixScannerDescription_subroutineReady
      CommonGround.Identity.exactIdentityDescription_subroutineReady

theorem assemblySourceRestFinishTargetPrefixBits_eq_scannerFields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (encodeCodeWordAsInput
          (encodeBoolWordAppend
            (assemblySourceRestFinishSourceBits w sourceRestBits stage)
            [])) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_encodeBoolWordAppend]
  rfl

theorem postPaddingOutputPrefixStageHandoffBase_eq_targetPrefixRev
    (w sourceRestBits : Word Bool) (stage : Nat) :
    postPaddingOutputPrefixStageHandoffBase
        (assemblySourceRestFinishSourceBits w sourceRestBits stage) [] =
      (assemblySourceRestFinishTargetPrefixBits
        w sourceRestBits stage).reverse.map some := by
  rw [postPaddingOutputPrefixStageHandoffBase_eq_bits_reverse,
    assemblySourceRestFinishTargetPrefixBits_eq_scannerFields]
  simp [postPaddingOutputPrefixHeaderBase, List.reverse_append,
    List.map_append]

theorem joinedOutputScannerTarget_move_right_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.right
        (boolWordCanonicalHandoffConfigWithBase
          (assemblySourceRestFinishSourceBits w sourceRestBits stage)
          (postPaddingOutputPrefixHeaderBase [])
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)).tape =
      assemblySourceRestFinishTargetTape w sourceRestBits stage := by
  rw [boolWordCanonicalHandoffConfigWithBase_move_right_all]
  change
    tapeAtCells
        (postPaddingOutputPrefixStageHandoffBase
          (assemblySourceRestFinishSourceBits w sourceRestBits stage) [])
        ((assemblySourceRestFinishRawTailBits sourceRestBits stage).map some) =
      assemblySourceRestFinishTargetTape w sourceRestBits stage
  rw [postPaddingOutputPrefixStageHandoffBase_eq_targetPrefixRev]
  rfl

theorem joinedOutputInput_eq_scannerSource
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.input
        (List.append
          (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)) =
      tapeAtCells []
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend
                (assemblySourceRestFinishSourceBits w sourceRestBits stage)
                [])).map some)
            ((assemblySourceRestFinishRawTailBits sourceRestBits stage).map
              some))) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_scannerFields]
  simp [Tape.input, tapeAtCells, encodeCodeSymbolAsInput]

theorem postPaddingOutputPrefixScannerDescription_haltsFrom_joinedOutputInput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    postPaddingOutputPrefixScannerDescription.HaltsFromTape
      (Tape.input
        (List.append
          (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)))
      (boolWordCanonicalHandoffConfigWithBase
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (postPaddingOutputPrefixHeaderBase [])
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)).tape := by
  rcases stageNatBits_cons_false stage with ⟨stageTail, hstage⟩
  rw [joinedOutputInput_eq_scannerSource]
  rw [assemblySourceRestFinishRawTailBits, hstage]
  simpa [List.map_append, List.append_assoc] using
    postPaddingOutputPrefixScannerDescription_haltsFrom
      (assemblySourceRestFinishSourceBits w sourceRestBits stage)
      (List.append stageTail sourceRestBits) []

theorem joinedOutputRawTailPositionerDescription_haltsFrom_namedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    joinedOutputRawTailPositionerDescription.HaltsFromTape
      (Tape.input
        (List.append
          (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)))
      (assemblySourceRestFinishTargetTape w sourceRestBits stage) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      postPaddingOutputPrefixScannerDescription_subroutineReady
      CommonGround.Identity.exactIdentityDescription_subroutineReady
      (postPaddingOutputPrefixScannerDescription_haltsFrom_joinedOutputInput
        w sourceRestBits stage)
      (joinedOutputScannerTarget_move_right_eq_targetTape
        w sourceRestBits stage)
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (assemblySourceRestFinishTargetTape w sourceRestBits stage))

theorem joinedOutputRawTailPositionerDescription_haltsFrom_joinedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    joinedOutputRawTailPositionerDescription.HaltsFromTape
      (Tape.input
        (assemblySourceRestFinishJoinedOutput w sourceRestBits stage))
      (assemblySourceRestFinishTargetTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishJoinedOutput_eq_targetTape_namedOutput]
  exact
    joinedOutputRawTailPositionerDescription_haltsFrom_namedOutput
      w sourceRestBits stage

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
