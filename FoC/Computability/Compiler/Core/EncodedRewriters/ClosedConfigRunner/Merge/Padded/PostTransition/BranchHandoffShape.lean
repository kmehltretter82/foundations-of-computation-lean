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

def SelectedMergePaddedEmitterDecodedHandoffBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Word Bool :=
  SelectedMergePaddedEmitterTargetBits useAccept p

def SelectedMergePaddedEmitterParsedInnerTargetTailBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Word Bool :=
  SelectedMergePaddedEmitterOutputTailBits useAccept p

theorem SelectedMergePaddedEmitterDecodedHandoffTape_eq_outputTape
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffTape useAccept p =
      SelectedMergeEquivEmitterPaddedOutputTape useAccept p := by
  cases useAccept
  · exact SelectedMergePaddedEmitterRejectDecodedHandoffTape_eq_outputTape p
  · exact SelectedMergePaddedEmitterAcceptDecodedHandoffTape_eq_outputTape p

theorem SelectedMergePaddedEmitterDecodedHandoffBits_eq_outputCode
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L) := by
  rw [SelectedMergePaddedEmitterDecodedHandoffBits,
    SelectedMergePaddedEmitterTargetBits_eq_outputCode]

theorem SelectedMergePaddedEmitterDecodedHandoffBits_eq_transition_targetTail
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      List.append (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (SelectedMergePaddedEmitterParsedInnerTargetTailBits
          useAccept p) := by
  rw [SelectedMergePaddedEmitterDecodedHandoffBits,
    SelectedMergePaddedEmitterTargetBits_eq_transition_outputTail]
  rfl

theorem SelectedMergePaddedEmitterParsedInnerTargetTailBits_true
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetTailBits true p =
      encodeCodeWordAsInput
        (encodeBoolWordAppend p.L.input
          (encodeNatAppend p.L.stage
            (encodeConfigurationAppend p.S.config
              (encodeConfigurationAppend p.L.rejectConfig
                (encodeBoolAppend p.S.hit
                  (encodeBoolAppend p.L.rejectHit [])))))) := by
  rw [SelectedMergePaddedEmitterParsedInnerTargetTailBits,
    SelectedMergePaddedEmitterOutputTailBits_true]

theorem SelectedMergePaddedEmitterParsedInnerTargetTailBits_false
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetTailBits false p =
      encodeCodeWordAsInput
        (encodeBoolWordAppend p.L.input
          (encodeNatAppend p.L.stage
            (encodeConfigurationAppend p.L.acceptConfig
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.L.acceptHit
                  (encodeBoolAppend p.S.hit [])))))) := by
  rw [SelectedMergePaddedEmitterParsedInnerTargetTailBits,
    SelectedMergePaddedEmitterOutputTailBits_false]

theorem SelectedMergePaddedEmitterDecodedHandoffBits_true_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffBits true p =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.S.config
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.S.hit
                    (encodeBoolAppend p.L.rejectHit [])))))) := by
  rw [SelectedMergePaddedEmitterDecodedHandoffBits,
    SelectedMergePaddedEmitterTargetBits_true_eq_fields]

theorem SelectedMergePaddedEmitterDecodedHandoffBits_false_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffBits false p =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.S.config
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.S.hit [])))))) := by
  rw [SelectedMergePaddedEmitterDecodedHandoffBits,
    SelectedMergePaddedEmitterTargetBits_false_eq_fields]

theorem SelectedMergePaddedEmitterDecodedHandoffTape_eq_tapeAtCells_bits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffTape useAccept p =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((SelectedMergePaddedEmitterDecodedHandoffBits
            useAccept p).map some)
          (List.replicate (SimulatorLayout.asBoolInput p.S).length none)) := by
  rw [SelectedMergePaddedEmitterDecodedHandoffTape_eq_outputTape,
    SelectedMergeEquivEmitterPaddedOutputTape_eq_tapeAtCells_targetBits]
  rfl

theorem SelectedMergePaddedEmitterDecodedHandoffTape_normalizedOutput_eq_bits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      SelectedMergePaddedEmitterDecodedHandoffBits useAccept p := by
  rw [SelectedMergePaddedEmitterDecodedHandoffTape_eq_outputTape,
    SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_targetBits]
  rfl

theorem SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_bits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      List.append
        ((SelectedMergePaddedEmitterDecodedHandoffBits useAccept p).map some)
        (List.replicate (SimulatorLayout.asBoolInput p.S).length none) := by
  rw [SelectedMergePaddedEmitterDecodedHandoffTape_eq_outputTape,
    SelectedMergeEquivEmitterPaddedOutputTape_cells_eq_targetBits]
  rfl

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
