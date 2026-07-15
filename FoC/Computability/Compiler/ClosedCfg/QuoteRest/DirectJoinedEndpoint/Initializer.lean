import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpointCore

/-! Exact mixed-source initialization for the direct joined-output endpoint. -/

set_option maxRecDepth 10000

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

open Structured.MultiTapeLowering

def directJoinedSourcePrefixRev : Word Bool :=
  [false, false, true, false, false, false]

theorem directJoinedSourcePrefixRev_reverse :
    directJoinedSourcePrefixRev.reverse = DirectJoinedCloseout.fixedSourcePrefix := by
  rfl

theorem structuredLiveTailEmitterAssemblySourceTape_eq_canonicalizerSource
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblySourceTape p =
      mixedSourceCanonicalizerSourceTape
        directJoinedSourcePrefixRev
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteScan p)
          (assemblySourceRestLiveTailEmitterRawTail p))
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  cases p
  simp [structuredLiveTailEmitterAssemblySourceTape,
    assemblySourceRestLiveTailEmitterLeftRev,
    assemblySourceRestFinishParserMarkerLeftCells,
    transitionPrefixLeftTail,
    mixedOptionCellQuoteLiveTailEmitterSplitSourceTape,
    mixedSourceCanonicalizerSourceTape, directJoinedSourcePrefixRev,
    DovetailInitialLayoutInitializer.tapeAtCells,
    CommonGround.FiniteTransducers.tapeAtCells,
    List.map_append, List.append_assoc]
  rfl

theorem directJoinedAssemblySourceBits_eq_segments
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyInputBits p =
      List.append DirectJoinedCloseout.fixedSourcePrefix
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteScan p)
          (assemblySourceRestLiveTailEmitterRawTail p)) := by
  cases p with
  | mk w sourceRestBits stage =>
      unfold structuredLiveTailEmitterAssemblyInputBits
        assemblySourceRestLiveTailEmitterQuoteScan
        assemblySourceRestLiveTailEmitterRawTail
      rw [assemblySourceRestFinishSourceBits,
        DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_eq_prefix_stageNat,
        assemblySourceRestFinishRawTailBits]
      cases w with
      | nil =>
          simp [DirectJoinedCloseout.fixedSourcePrefix,
            assemblySourceRestFinishParserMarkerRightBits,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
            encodeCodeSymbolAsInput]
      | cons bit rest =>
          simp [DirectJoinedCloseout.fixedSourcePrefix,
            assemblySourceRestFinishParserMarkerRightBits,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
            encodeCodeSymbolAsInput, List.append_assoc]

theorem directJoinedAssemblySourceBits_eq_cons
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyInputBits p =
      false :: List.append ([false, false, true, false, false] : Word Bool)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteScan p)
          (assemblySourceRestLiveTailEmitterRawTail p)) := by
  rw [directJoinedAssemblySourceBits_eq_segments]
  rfl

theorem directJoinedAssemblySourceBits_lastSplit
    (p : AssemblySourceRestLiveTailEmitterParam) :
    exists sourceInit : Word Bool, exists last : Bool,
      structuredLiveTailEmitterAssemblyInputBits p =
        List.append sourceInit [last] := by
  rcases assemblySourceRestFinishRawTailBits_lastSplit_exists
      p.sourceRestBits p.stage with ⟨rawInit, last, hraw⟩
  refine
    ⟨List.append DirectJoinedCloseout.fixedSourcePrefix
      (List.append
        (assemblySourceRestLiveTailEmitterQuoteScan p) rawInit),
      last, ?_⟩
  rw [directJoinedAssemblySourceBits_eq_segments]
  have hraw' : assemblySourceRestLiveTailEmitterRawTail p =
      List.append rawInit [last] := hraw
  rw [hraw']
  simp [List.append_assoc]

theorem mixedSourceCanonicalizerDescription_haltsFrom_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    mixedSourceCanonicalizerDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblySourceTape p)
      (Tape.input (structuredLiveTailEmitterAssemblyInputBits p)) := by
  rcases directJoinedAssemblySourceBits_lastSplit p with
    ⟨sourceInit, last, hlast⟩
  rw [structuredLiveTailEmitterAssemblySourceTape_eq_canonicalizerSource]
  rw [hlast]
  apply mixedSourceCanonicalizerDescription_haltsFrom_layout
  rw [directJoinedSourcePrefixRev_reverse]
  rw [directJoinedAssemblySourceBits_eq_segments] at hlast
  exact hlast

theorem optionCellExpandAppendDescription_haltsFrom_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    StructuredConstructionTargets.optionCellExpandAppendDescription.HaltsFromTape
      (Tape.input (structuredLiveTailEmitterAssemblyInputBits p))
      (encodedGuardedStructured3Tapes
        (Tape.input (structuredLiveTailEmitterAssemblyInputBits p))
        Tape.blank Tape.blank) := by
  rw [← CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape]
  rw [← StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget]
  unfold StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape
  rw [← StructuredConstructionTargets.optionCellExpandAppendTargetCells_eq_structured3]
  exact
    StructuredConstructionTargets.optionCellExpandAppendDescription_runSpec.forward
      (structuredLiveTailEmitterAssemblyInputBits p)

theorem guardLogicalTape_input_cons_eq_cellPassSourceTape
    (first : Bool) (rest : Word Bool) :
    guardLogicalTape (Tape.input (first :: rest)) =
      structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
        [] (first :: rest) := by
  cases rest <;> rfl

def loweredDirectJoinedInnerGuardDescription : MachineDescription :=
  lowerStructured3Description DirectJoinedInnerGuard.description

theorem loweredDirectJoinedInnerGuardDescription_subroutineReady :
    loweredDirectJoinedInnerGuardDescription.SubroutineReady := by
  exact lowerStructured3Description_subroutineReady
    DirectJoinedInnerGuard.description_wellFormed
    DirectJoinedInnerGuard.description_supported

theorem directJoinedInnerGuardDescription_haltsWithTapes_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    DirectJoinedInnerGuard.description.HaltsWithTapes
      (Structured.MultiTapeLowering.ThreeTape.config 0
        (Tape.input (structuredLiveTailEmitterAssemblyInputBits p))
        Tape.blank Tape.blank)
      [guardLogicalTape
          (Tape.input (structuredLiveTailEmitterAssemblyInputBits p)),
        Tape.blank, Tape.blank] := by
  let rest := List.append ([false, false, true, false, false] : Word Bool)
    (List.append
      (assemblySourceRestLiveTailEmitterQuoteScan p)
      (assemblySourceRestLiveTailEmitterRawTail p))
  refine ⟨DirectJoinedInnerGuard.fuel (false :: rest), ?_⟩
  rw [directJoinedAssemblySourceBits_eq_cons]
  exact DirectJoinedInnerGuard.run_nonempty false rest Tape.blank Tape.blank

theorem directJoinedInnerGuardEncodedTarget_eq_emitterInitial
    (p : AssemblySourceRestLiveTailEmitterParam) :
    encodedGuardedStructured3Tapes
        (guardLogicalTape
          (Tape.input (structuredLiveTailEmitterAssemblyInputBits p)))
        Tape.blank Tape.blank =
      structuredLiveTailEmitterAssemblyEncodedInitialTape p := by
  rw [structuredLiveTailEmitterAssemblyEncodedInitialTape_eq_encoded3]
  rw [directJoinedAssemblySourceBits_eq_cons]
  rw [guardLogicalTape_input_cons_eq_cellPassSourceTape]
  rfl

theorem loweredDirectJoinedInnerGuardDescription_haltsFrom_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    loweredDirectJoinedInnerGuardDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (Tape.input (structuredLiveTailEmitterAssemblyInputBits p))
        Tape.blank Tape.blank)
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p) := by
  rw [← directJoinedInnerGuardEncodedTarget_eq_emitterInitial]
  exact lowerStructured3Description_haltsFromConfigWithTapes
    DirectJoinedInnerGuard.description_wellFormed
    DirectJoinedInnerGuard.description_haltTransitionFree
    DirectJoinedInnerGuard.description_supported
    (c := Structured.MultiTapeLowering.ThreeTape.config 0
      (Tape.input (structuredLiveTailEmitterAssemblyInputBits p))
      Tape.blank Tape.blank)
    (tapes :=
      [guardLogicalTape
          (Tape.input (structuredLiveTailEmitterAssemblyInputBits p)),
        Tape.blank, Tape.blank])
    rfl rfl
    (directJoinedInnerGuardDescription_haltsWithTapes_assembly p)

def directJoinedInitializerDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription mixedSourceCanonicalizerDescription
    (canonicalPrimitiveSeqDescription
      StructuredConstructionTargets.optionCellExpandAppendDescription
      loweredDirectJoinedInnerGuardDescription)

theorem directJoinedInitializerDescription_subroutineReady :
    directJoinedInitializerDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    mixedSourceCanonicalizerDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      StructuredConstructionTargets.optionCellExpandAppendDescription_subroutineReady
      loweredDirectJoinedInnerGuardDescription_subroutineReady)

theorem directJoinedInitializerDescription_haltsFrom_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    directJoinedInitializerDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblySourceTape p)
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p) := by
  apply canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    mixedSourceCanonicalizerDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      StructuredConstructionTargets.optionCellExpandAppendDescription_subroutineReady
      loweredDirectJoinedInnerGuardDescription_subroutineReady)
    (mixedSourceCanonicalizerDescription_haltsFrom_assembly p)
  exact canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    StructuredConstructionTargets.optionCellExpandAppendDescription_subroutineReady
    loweredDirectJoinedInnerGuardDescription_subroutineReady
    (optionCellExpandAppendDescription_haltsFrom_assembly p).toEquiv
    (loweredDirectJoinedInnerGuardDescription_haltsFrom_assembly p)

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
