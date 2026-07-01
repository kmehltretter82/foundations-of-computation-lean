import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.NestedLayoutShape

set_option doc.verso true

/-!
# Merge post-transition branch handoff shape

This module names the accepting and rejecting decoded handoff target tapes used
by the padded merge post-transition inner leaves.  It stays below the branch
construction contracts so the finite emitters can rewrite their exact target
shapes without importing downstream cleanup or final modules.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergePaddedEmitterAcceptDecodedHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append
      ((encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.S.config
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.S.hit
                    (encodeBoolAppend p.L.rejectHit []))))))).map some)
      (List.replicate (SimulatorLayout.asBoolInput p.S).length none))

def SelectedMergePaddedEmitterRejectDecodedHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append
      ((encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.S.config
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.S.hit []))))))).map some)
      (List.replicate (SimulatorLayout.asBoolInput p.S).length none))

theorem SelectedMergePaddedEmitterAcceptDecodedHandoffTape_eq_outputTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAcceptDecodedHandoffTape p =
      SelectedMergeEquivEmitterPaddedOutputTape true p := by
  rw [SelectedMergePaddedEmitterAcceptDecodedHandoffTape,
    SelectedMergeEquivEmitterPaddedOutputTape_true_eq_tapeAtCells_fields]

theorem SelectedMergePaddedEmitterRejectDecodedHandoffTape_eq_outputTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterRejectDecodedHandoffTape p =
      SelectedMergeEquivEmitterPaddedOutputTape false p := by
  rw [SelectedMergePaddedEmitterRejectDecodedHandoffTape,
    SelectedMergeEquivEmitterPaddedOutputTape_false_eq_tapeAtCells_fields]

def SelectedMergePaddedEmitterDecodedHandoffTape
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Tape Bool :=
  if useAccept then
    SelectedMergePaddedEmitterAcceptDecodedHandoffTape p
  else
    SelectedMergePaddedEmitterRejectDecodedHandoffTape p

theorem SelectedMergePaddedEmitterDecodedHandoffTape_eq_outputTape
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffTape useAccept p =
      SelectedMergeEquivEmitterPaddedOutputTape useAccept p := by
  cases useAccept
  · exact SelectedMergePaddedEmitterRejectDecodedHandoffTape_eq_outputTape p
  · exact SelectedMergePaddedEmitterAcceptDecodedHandoffTape_eq_outputTape p

theorem SelectedMergePaddedEmitterAcceptDecodedHandoffTape_cells_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAcceptDecodedHandoffTape p) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.transition ::
            encodeBoolWordAppend p.L.input
              (encodeNatAppend p.L.stage
                (encodeConfigurationAppend p.S.config
                  (encodeConfigurationAppend p.L.rejectConfig
                    (encodeBoolAppend p.S.hit
                      (encodeBoolAppend p.L.rejectHit []))))))).map some)
        (List.replicate (SimulatorLayout.asBoolInput p.S).length none) := by
  rw [SelectedMergePaddedEmitterAcceptDecodedHandoffTape_eq_outputTape]
  exact SelectedMergeEquivEmitterPaddedOutputTape_true_cells_eq_fields p

theorem SelectedMergePaddedEmitterRejectDecodedHandoffTape_cells_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterRejectDecodedHandoffTape p) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.transition ::
            encodeBoolWordAppend p.L.input
              (encodeNatAppend p.L.stage
                (encodeConfigurationAppend p.L.acceptConfig
                  (encodeConfigurationAppend p.S.config
                    (encodeBoolAppend p.L.acceptHit
                      (encodeBoolAppend p.S.hit []))))))).map some)
        (List.replicate (SimulatorLayout.asBoolInput p.S).length none) := by
  rw [SelectedMergePaddedEmitterRejectDecodedHandoffTape_eq_outputTape]
  exact SelectedMergeEquivEmitterPaddedOutputTape_false_cells_eq_fields p

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
