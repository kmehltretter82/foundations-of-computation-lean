import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.PrefixPipeline

/-!
# Accept-config insertion shapes

Exact list decompositions used by the accept-branch output-buffer inserter.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat

open CanonicalLayouts.DovetailLayoutScanner

def acceptPrefix (L : DovetailLayout) : Word Bool :=
  List.append transitionPrefixBits
    (boolWordFieldBits L.input
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage))

def acceptOldTail (L : DovetailLayout) : Word Bool :=
  List.append (configurationFieldBits L.rejectConfig [])
    (selectedProjectionPaddedTailCleanupSelectedHitBits true L)

def acceptInsertedTail (L : DovetailLayout) : Word Bool :=
  List.append (configurationFieldBits L.acceptConfig []) (acceptOldTail L)

theorem parsedLayoutBits_accept_decomp (L : DovetailLayout) :
    ParsedLayoutBits L =
      List.append (acceptPrefix L)
        (List.append (acceptInsertedTail L)
          (boolFieldBits L.rejectHit [])) := by
  rw [parsedLayoutBits_fieldDecomp]
  unfold acceptPrefix acceptInsertedTail acceptOldTail
  simp [selectedProjectionPaddedTailCleanupSelectedHitBits,
    boolWordFieldBits, cellListFieldBits, List.append_assoc]
  done

theorem copiedDataWord_accept_eq_preInsertion (L : DovetailLayout) :
    copiedDataWord true L =
      List.append (ParsedLayoutBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (acceptOldTail L)) := by
  simpa [acceptOldTail] using copiedDataWord_accept_decomp L
  done

theorem acceptConfigFieldBits_length_pos (L : DovetailLayout) :
    0 < (configurationFieldBits L.acceptConfig []).length := by
  rw [configurationFieldBits_nil_length]
  lia
  done

theorem acceptOldTail_length_lt_acceptInsertedTail (L : DovetailLayout) :
    (acceptOldTail L).length < (acceptInsertedTail L).length := by
  have hlength := acceptConfigFieldBits_length_pos L
  simp [acceptInsertedTail]
  exact hlength
  done

end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
