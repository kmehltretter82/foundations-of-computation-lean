import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.BranchHandoffShape

set_option doc.verso true

/-!
# Merge post-transition parsed-inner windows

The parsed-inner emitter does not merely copy an encoded transition word.  Its
source is the checked scanner shape: after the outer transition symbol, the
nested layout body still begins with the scanner-local transition remainder.
The target is the ordinary emitted transition code word, so the finite-machine
leaf must delete that marked-body remainder while it replaces the selected
inner config/hit fields with the outer simulator config/hit fields.

This module names those source and target windows without choosing the concrete
finite-machine route.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (List.append
      CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits
      (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
        p.L.input
        (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.L.stage)))

def SelectedMergePaddedEmitterParsedInnerOutputPrefixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
      p.L.input
      (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        p.L.stage))

def SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    p.L.acceptConfig
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      p.L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        p.L.acceptHit
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.L.rejectHit
          (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p))))

def SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      (SelectedMergeOutputRejectConfig useAccept p.S p.L)
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        (SelectedMergeOutputAcceptHit useAccept p.S p.L)
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          (SelectedMergeOutputRejectHit useAccept p.S p.L)
          [])))

def SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    p.S.config
    (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.S.hit [])

theorem
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits_eq_stage_outerConfigHit
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p =
      List.append
        (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage)
        (SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits p) := by
  simp [SelectedMergePaddedEmitterParsedInnerOuterSuffixBits,
    SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits]

theorem
    SelectedMergePaddedEmitterParsedInnerSourceBits_eq_markedPrefix_fieldTail
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerSourceBits p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p) := by
  rw [SelectedMergePaddedEmitterParsedInnerSourceBits_eq_nestedFields]
  simp [SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits,
    SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    List.append_assoc]

theorem
    SelectedMergePaddedEmitterParsedInnerSourceTailBits_eq_markedBody_outerSuffix
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerSourceTailBits p =
      List.append
        CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
            p.L.input
            (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.L.stage))
          (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p)) := by
  have h :=
    SelectedMergePaddedEmitterParsedInnerSourceBits_eq_markedPrefix_fieldTail
      p
  rw [SelectedMergePaddedEmitterParsedInnerSourceBits_eq_transition_tail] at h
  simp [SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits,
    SelectedMergePaddedEmitterParsedInnerSourceTailBits,
    SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits,
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    List.append_assoc] at h ⊢

theorem
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits_true
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits true p =
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        p.S.config
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.L.rejectConfig
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.S.hit
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              p.L.rejectHit []))) := by
  rfl

theorem
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits_false
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits false p =
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        p.L.acceptConfig
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.S.config
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.acceptHit
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              p.S.hit []))) := by
  rfl

theorem
    SelectedMergePaddedEmitterDecodedHandoffBits_eq_outputPrefix_fieldTail
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
          useAccept p) := by
  cases useAccept
  · rw [SelectedMergePaddedEmitterDecodedHandoffBits_false_eq_fields]
    simp only [encodeCodeWordAsInput]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
    rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    simp [SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits,
      SelectedMergeOutputAcceptConfig, SelectedMergeOutputRejectConfig,
      SelectedMergeOutputAcceptHit, SelectedMergeOutputRejectHit,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      encodeCodeWordAsInput,
      List.append_assoc]
  · rw [SelectedMergePaddedEmitterDecodedHandoffBits_true_eq_fields]
    simp only [encodeCodeWordAsInput]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
    rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    simp [SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits,
      SelectedMergeOutputAcceptConfig, SelectedMergeOutputRejectConfig,
      SelectedMergeOutputAcceptHit, SelectedMergeOutputRejectHit,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      encodeCodeWordAsInput,
      List.append_assoc]

theorem
    SelectedMergePaddedEmitterParsedInnerTargetTailBits_eq_outputPrefixTail
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetTailBits useAccept p =
      List.append
        (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
          p.L.input
          (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.L.stage))
        (SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
          useAccept p) := by
  cases useAccept
  · rw [SelectedMergePaddedEmitterParsedInnerTargetTailBits_false]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
    rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    simp [SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits,
      SelectedMergeOutputAcceptConfig, SelectedMergeOutputRejectConfig,
      SelectedMergeOutputAcceptHit, SelectedMergeOutputRejectHit,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      encodeCodeWordAsInput, List.append_assoc]
  · rw [SelectedMergePaddedEmitterParsedInnerTargetTailBits_true]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
    rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    simp [SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits,
      SelectedMergeOutputAcceptConfig, SelectedMergeOutputRejectConfig,
      SelectedMergeOutputAcceptHit, SelectedMergeOutputRejectHit,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      encodeCodeWordAsInput, List.append_assoc]

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
