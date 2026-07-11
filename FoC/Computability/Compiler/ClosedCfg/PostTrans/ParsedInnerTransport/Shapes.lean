import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerWindows
import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.DeletePass
import FoC.Computability.Compiler.Dovetail.Scanner.Composition.Definitions

set_option doc.verso true

/-!
# Parsed-inner transport shapes

Field-ending and restored-stack identities used by both branch schedules of
the parsed-inner post-prefix transport.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncRewriters
namespace BoundedLayoutRunner
namespace ParsedInnerTransport

open CanonicalLayouts.DovetailLayoutScanner

theorem stageNatBits_eq_prefix_done (n : Nat) :
    exists pre : Word Bool,
      stageNatBits n =
        List.append pre [false, false, true, true] := by
  induction n with
  | zero =>
      exact ⟨[], by simp [stageNatBits_zero]⟩
  | succ n ih =>
      rcases ih with ⟨pre, hpre⟩
      refine ⟨List.append [false, false, true, false] pre, ?_⟩
      simp [stageNatBits_succ, hpre]

theorem stageNatBits_reverse_cons_cons (n : Nat) :
    exists rest : Word Bool,
      (stageNatBits n).reverse = true :: true :: rest := by
  rcases stageNatBits_eq_prefix_done n with ⟨pre, hpre⟩
  refine ⟨false :: false :: pre.reverse, ?_⟩
  rw [hpre]
  simp

theorem cellListCanonicalRestoredLeftWithBase_eq_fieldBits_reverse_append
    (cells baseLeft : List (Option Bool)) :
    cellListCanonicalRestoredLeftWithBase cells baseLeft =
      List.append ((cellListFieldBits cells []).reverse.map some)
        baseLeft := by
  rw [← cellListCanonicalRestoredBitsRev_map_some_withBase]
  rw [← cellListCanonicalRestoredBitsRev_reverse]
  simp

theorem boolFieldBits_eq_four (b : Bool) :
    boolFieldBits b [] = [false, true, b, !b] := by
  cases b <;>
    simp [boolFieldBits, cellFieldBits, cellCodeBits, encodeCell,
      encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem cellCodeBits_ends_valid (cell : Option Bool) :
    exists c2 c3 c4 : Bool,
      cellCodeBits cell = [false, c2, c3, c4] ∧
        SentinelTokenValid c2 c3 c4 := by
  cases cell with
  | none =>
      exact ⟨true, false, false, by
        simp [cellCodeBits, encodeCell, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, SentinelTokenValid]⟩
  | some b =>
      cases b with
      | false =>
          exact ⟨true, false, true, by
            simp [cellCodeBits, encodeCell, encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, SentinelTokenValid]⟩
      | true =>
          exact ⟨true, true, false, by
            simp [cellCodeBits, encodeCell, encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, SentinelTokenValid]⟩

theorem cellsCodeBits_ends_valid
    (cells : List (Option Bool)) (h : cells ≠ []) :
    exists pre : Word Bool,
    exists c2 c3 c4 : Bool,
      cellsCodeBits cells =
          List.append pre [false, c2, c3, c4] ∧
        SentinelTokenValid c2 c3 c4 := by
  induction cells with
  | nil =>
      exact (h rfl).elim
  | cons cell rest ih =>
      cases rest with
      | nil =>
          rcases cellCodeBits_ends_valid cell with
            ⟨c2, c3, c4, hcell, hvalid⟩
          exact ⟨[], c2, c3, c4, by
            simpa [cellsCodeBits] using hcell, hvalid⟩
      | cons next tail =>
          rcases ih (by simp) with ⟨pre, c2, c3, c4, hrest, hvalid⟩
          unfold Word at *
          refine
            ⟨List.append (cellCodeBits cell) pre,
              c2, c3, c4, ?_, hvalid⟩
          simp [cellsCodeBits, List.append_assoc]
          exact hrest

theorem cellListFieldBits_ends_valid
    (cells : List (Option Bool)) :
    exists pre : Word Bool,
    exists c2 c3 c4 : Bool,
      cellListFieldBits cells [] =
          List.append pre [false, c2, c3, c4] ∧
        SentinelTokenValid c2 c3 c4 := by
  cases cells with
  | nil =>
      exact ⟨[], false, true, true, by
        simp [cellListFieldBits, cellsCodeBits, stageNatBits_zero,
          SentinelTokenValid]⟩
  | cons cell rest =>
      rcases cellsCodeBits_ends_valid (cell :: rest) (by simp) with
        ⟨pre, c2, c3, c4, hcells, hvalid⟩
      unfold Word at *
      refine
        ⟨List.append (stageNatBits (cell :: rest).length) pre,
          c2, c3, c4, ?_, hvalid⟩
      simp [cellListFieldBits, List.append_assoc]
      exact hcells

theorem configurationFieldBits_ends_valid
    (cfg : Configuration) :
    exists pre : Word Bool,
    exists c2 c3 c4 : Bool,
      configurationFieldBits cfg [] =
          List.append pre [false, c2, c3, c4] ∧
        SentinelTokenValid c2 c3 c4 := by
  rcases cellListFieldBits_ends_valid cfg.tape.right with
    ⟨tail, c2, c3, c4, htail, hvalid⟩
  unfold Word at *
  refine
    ⟨List.append (stageNatBits cfg.state)
        (List.append (stageNatBits cfg.tape.left.length)
          (List.append (cellsCodeBits cfg.tape.left)
            (List.append (cellCodeBits cfg.tape.head) tail))),
      c2, c3, c4, ?_, hvalid⟩
  have hright :
      List.append (stageNatBits cfg.tape.right.length)
          (cellsCodeBits cfg.tape.right) =
        List.append tail [false, c2, c3, c4] := by
    simpa [cellListFieldBits] using htail
  simp [configurationFieldBits, tapeFieldBits, cellListFieldBits,
    cellFieldBits, List.append_assoc]
  exact hright

theorem configurationFieldBits_false_false_tail
    (cfg : Configuration) (suffix : Word Bool) :
    exists tail : Word Bool,
      configurationFieldBits cfg suffix = false :: false :: tail := by
  rcases stageNatBits_false_false_tail cfg.state with
    ⟨stateTail, hstate⟩
  refine ⟨List.append stateTail (tapeFieldBits cfg.tape suffix), ?_⟩
  rw [configurationFieldBits, hstate]
  simp

theorem configurationFieldBits_eq_reverse_cons_cons
    (cfg : Configuration) :
    exists x y : Bool,
    exists rest : Word Bool,
      configurationFieldBits cfg [] = (x :: y :: rest).reverse := by
  rcases configurationFieldBits_ends_valid cfg with
    ⟨pre, c2, c3, c4, hfield, _hvalid⟩
  refine ⟨c4, c3, c2 :: false :: pre.reverse, ?_⟩
  rw [hfield]
  simp

theorem outputPrefixBits_cons
    (p : SelectedMergeEmitterPayload) :
    exists rest : Word Bool,
      SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p =
        false :: rest := by
  refine
    ⟨List.append [false, false, true]
        (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
          p.L.input (stageNatBits p.L.stage)), ?_⟩
  simp [SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
    encodeCodeSymbolAsInput]

theorem outputPrefixBits_eq_prefix_done
    (p : SelectedMergeEmitterPayload) :
    exists pre : Word Bool,
      SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p =
        List.append pre [false, false, true, true] := by
  rcases stageNatBits_eq_prefix_done p.L.stage with ⟨stagePre, hstage⟩
  refine
    ⟨List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (List.append
          (stageNatBits (p.L.input.map some).length)
          (List.append (cellsCodeBits (p.L.input.map some)) stagePre)),
      ?_⟩
  unfold Word at *
  simp [SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
    boolWordFieldBits, cellListFieldBits, hstage, List.append_assoc]

theorem outputPrefixBits_eq_reverse_cons_cons
    (p : SelectedMergeEmitterPayload) :
    exists x y : Bool,
    exists rest : Word Bool,
      SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p =
        (x :: y :: rest).reverse := by
  let beforeStage : List Bool :=
    List.append
      (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
      (List.append
        (stageNatBits (p.L.input.map some).length)
        (cellsCodeBits (p.L.input.map some)))
  let stageBits : List Bool := stageNatBits p.L.stage
  have hprefix :
      SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p =
        List.append beforeStage stageBits := by
    simp [SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      cellListFieldBits, beforeStage, stageBits, List.append_assoc]
  rcases stageNatBits_reverse_cons_cons p.L.stage with
    ⟨stageRest, hstage⟩
  let stageRestList : List Bool := stageRest
  have hstageList :
      stageBits.reverse = true :: true :: stageRestList := by
    simpa [stageBits, stageRestList] using hstage
  have hreverse :
      (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse =
        true :: true :: List.append stageRestList beforeStage.reverse := by
    calc
      (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse =
          List.append stageBits.reverse beforeStage.reverse := by
            rw [hprefix]
            exact
              (List.reverse_append :
                (List.append beforeStage stageBits).reverse =
                  List.append stageBits.reverse beforeStage.reverse)
      _ = true :: true :: List.append stageRestList beforeStage.reverse := by
            rw [hstageList]
            rfl
  refine
    ⟨true, true, List.append stageRestList beforeStage.reverse, ?_⟩
  unfold Word
  simpa using congrArg List.reverse hreverse

theorem outputPrefixAcceptConfigBits_eq_reverse_cons_cons
    (p : SelectedMergeEmitterPayload) :
    exists x y : Bool,
    exists rest : Word Bool,
      List.append
          (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
          (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p) =
        (x :: y :: rest).reverse := by
  rcases configurationFieldBits_eq_reverse_cons_cons p.L.acceptConfig with
    ⟨x, y, rest, hcfg⟩
  refine
    ⟨x, y,
      List.append rest
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse,
      ?_⟩
  rw [SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits, hcfg]
  simp [List.reverse_append, List.append_assoc]

theorem postPrefixSourceBits_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerPostPrefixSourceBits p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (List.append
          (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p)
          (List.append
            (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
            (List.append
              (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p)
              (List.append
                (SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p)
                (List.append
                  (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p)
                  (List.append
                    (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
                    (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits
                      p))))))) := by
  simp [SelectedMergePaddedEmitterParsedInnerPostPrefixSourceBits,
    SelectedMergePaddedEmitterParsedInnerSourceFieldTailExpandedBits]

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
