import FoC.Computability.Compiler.Core.ControllerResultContinue.GuardProjection

set_option doc.verso true

/-!
# Controller result continuation stage-input leaf

This module isolates the final stage-input continuation leaf.  The pure
encoding lemmas here name the exact target word produced after the stage input
projection has removed the controller header and result suffix.
-/

namespace FoC
namespace Computability

open Languages

namespace ControllerResultContinueConstruction

def stageInputContinueNatTail : Nat -> Word MachineCodeSymbol
  | 0 => [MachineCodeSymbol.tick, MachineCodeSymbol.done, MachineCodeSymbol.done]
  | n + 1 => MachineCodeSymbol.tick :: stageInputContinueNatTail n

theorem encodeNatAppend_succ
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend (n + 1) suffix =
      MachineCodeSymbol.tick ::
        MachineDescription.encodeNatAppend n suffix := by
  rfl

theorem encodeBoolWordAppend_nil_nil :
    MachineDescription.encodeBoolWordAppend ([] : Word Bool) [] =
      [MachineCodeSymbol.done] := by
  rfl

theorem stageInputContinueNatTail_eq_encode
    (stage : Nat) :
    stageInputContinueNatTail stage =
      MachineDescription.encodeNatAppend (stage + 1)
        (MachineDescription.encodeBoolWordAppend ([] : Word Bool) []) := by
  induction stage with
  | zero =>
      rfl
  | succ stage ih =>
      change
        MachineCodeSymbol.tick :: stageInputContinueNatTail stage =
          MachineDescription.encodeNatAppend (stage + 1 + 1)
            (MachineDescription.encodeBoolWordAppend ([] : Word Bool) [])
      rw [ih]
      rfl

theorem stageInputContinue_output_eq_header_input_tail
    (input : Word Bool) (stage : Nat) :
    MachineDescription.DovetailControllerLayout.encode
        { input := input, stage := stage + 1, result := [] } =
      MachineCodeSymbol.header ::
        MachineDescription.encodeBoolWordAppend input
          (stageInputContinueNatTail stage) := by
  rw [stageInputContinueNatTail_eq_encode]
  rfl

theorem stageInputContinue_nextStage_eq_header_input_tail
    (C : MachineDescription.DovetailControllerLayout) :
    MachineDescription.DovetailControllerLayout.encode
        (MachineDescription.DovetailControllerLayout.nextStage C) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeBoolWordAppend C.input
          (stageInputContinueNatTail C.stage) := by
  cases C
  exact stageInputContinue_output_eq_header_input_tail _ _

theorem stageInputContinue_stageInputCode_eq_input_stage
    (input : Word Bool) (stage : Nat) :
    MachineDescription.DovetailLayout.stageInputCode input stage =
      MachineDescription.encodeBoolWordAppend input
        (MachineDescription.encodeNatAppend stage []) := by
  rfl

end ControllerResultContinueConstruction

end Computability
end FoC
