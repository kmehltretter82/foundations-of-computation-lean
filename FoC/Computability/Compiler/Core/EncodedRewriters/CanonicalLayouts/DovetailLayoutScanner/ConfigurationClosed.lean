import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed.CellSuffix

set_option doc.verso true

/-!
# Configuration-suffix scanner closed facts

This module owns code-origin contracts for the composed configuration suffix
scanner.  Parser proofs should consume these contracts through CommonGround
instead of unpacking the nat- and tape-suffix subroutines locally.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

theorem configurationSuffixScannerDescription_runConfig_code_handoff
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      ConfigurationSuffixScannerDescription.runConfig n
          (config ConfigurationSuffixScannerDescription.start baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state := ConfigurationSuffixScannerDescription.halt
          tape := Tout }) :
    exists cfg : Configuration,
    exists suffix : Word MachineCodeSymbol,
    exists baseAfter : List (Option Bool),
      code = encodeConfigurationAppend cfg suffix ∧
        Tape.move Direction.right Tout =
          tapeAtCells baseAfter
            ((encodeCodeWordAsInput suffix).map
              some) := by
  have hseq :
      (seqSubroutine
        DovetailStagePrefix.NonemptyNatSuffixScannerDescription
        TapeSuffixScannerDescription
        Direction.right).runConfig n
          { state :=
              (seqSubroutine
                DovetailStagePrefix.NonemptyNatSuffixScannerDescription
                TapeSuffixScannerDescription
                Direction.right).start
            tape :=
              tapeAtCells baseLeft
                ((encodeCodeWordAsInput code).map
                  some) } =
        { state :=
            (seqSubroutine
              DovetailStagePrefix.NonemptyNatSuffixScannerDescription
              TapeSuffixScannerDescription
              Direction.right).halt
          tape := Tout } := by
    simpa [ConfigurationSuffixScannerDescription, config] using h
  rcases
      seqSubroutine_runConfig_inv
        (A := DovetailStagePrefix.NonemptyNatSuffixScannerDescription)
        (B := TapeSuffixScannerDescription)
        (handoffMove := Direction.right)
        DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        tapeSuffixScannerDescription_subroutineReady
        hseq with
    ⟨Tstage, hstage, htape⟩
  rcases hstage with ⟨nStage, hstageRun, _hstageFirst⟩
  rcases
      DovetailStagePrefix.nonemptyNatSuffixScannerDescription_runConfig_code_inv
        baseLeft code (by simpa [config] using hstageRun) with
    ⟨state, tapeSymbol, tapeRest, hcodeState⟩
  rcases encodeCodeWordAsInput_cons_bits tapeSymbol tapeRest with
    ⟨tapeBit, tapeTail, htapeBits⟩
  rcases
      DovetailStagePrefix.nonemptyNatSuffixScannerDescription_runConfig_encodeNatAppend_handoff
        baseLeft state (tapeSymbol :: tapeRest) tapeBit tapeTail
        htapeBits
        (by simpa [config, hcodeState] using hstageRun) with
    ⟨baseAfterState, hstageMove⟩
  rcases htape with ⟨nTape, htapeRun⟩
  have htapeCodeRun :
      TapeSuffixScannerDescription.runConfig nTape
          (config TapeSuffixScannerDescription.start baseAfterState
            ((encodeCodeWordAsInput
              (tapeSymbol :: tapeRest)).map some)) =
        { state := TapeSuffixScannerDescription.halt
          tape := Tout } := by
    simpa [config, hstageMove] using htapeRun
  rcases
      tapeSuffixScannerDescription_runConfig_code_handoff
        baseAfterState (tapeSymbol :: tapeRest) htapeCodeRun with
    ⟨tape, suffix, baseAfter, htapeCode, hmove⟩
  refine
    ⟨{ state := state, tape := tape }, suffix, baseAfter, ?_, hmove⟩
  simp [encodeConfigurationAppend, hcodeState,
    htapeCode]

theorem configurationSuffixScannerDescription_runConfig_encodeNat_empty_ne_halt
    (state : Nat) (baseLeft : List (Option Bool)) (n : Nat) :
    (ConfigurationSuffixScannerDescription.runConfig n
        (config ConfigurationSuffixScannerDescription.start baseLeft
          ((encodeCodeWordAsInput
            (encodeNatAppend state [])).map some))).state ≠
      ConfigurationSuffixScannerDescription.halt := by
  intro hhalt
  have hcfg :
      ConfigurationSuffixScannerDescription.runConfig n
          (config ConfigurationSuffixScannerDescription.start baseLeft
            ((encodeCodeWordAsInput
              (encodeNatAppend state [])).map some)) =
        { state := ConfigurationSuffixScannerDescription.halt
          tape :=
            (ConfigurationSuffixScannerDescription.runConfig n
              (config ConfigurationSuffixScannerDescription.start baseLeft
                ((encodeCodeWordAsInput
                  (encodeNatAppend state [])).map
                  some))).tape } := by
    cases hrun :
        ConfigurationSuffixScannerDescription.runConfig n
          (config ConfigurationSuffixScannerDescription.start baseLeft
            ((encodeCodeWordAsInput
              (encodeNatAppend state [])).map some)) with
    | mk q T =>
        simp [hrun] at hhalt
        simp [hhalt]
  have hseq :
      (seqSubroutine
        DovetailStagePrefix.NonemptyNatSuffixScannerDescription
        TapeSuffixScannerDescription
        Direction.right).runConfig n
          { state :=
              (seqSubroutine
                DovetailStagePrefix.NonemptyNatSuffixScannerDescription
                TapeSuffixScannerDescription
                Direction.right).start
            tape :=
              tapeAtCells baseLeft
                ((encodeCodeWordAsInput
                  (encodeNatAppend state [])).map
                  some) } =
        { state :=
            (seqSubroutine
              DovetailStagePrefix.NonemptyNatSuffixScannerDescription
              TapeSuffixScannerDescription
              Direction.right).halt
          tape :=
            (ConfigurationSuffixScannerDescription.runConfig n
              (config ConfigurationSuffixScannerDescription.start baseLeft
                ((encodeCodeWordAsInput
                  (encodeNatAppend state [])).map
                  some))).tape } := by
    simpa [ConfigurationSuffixScannerDescription, config] using hcfg
  rcases
      seqSubroutine_runConfig_inv
        (A := DovetailStagePrefix.NonemptyNatSuffixScannerDescription)
        (B := TapeSuffixScannerDescription)
        (handoffMove := Direction.right)
        DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        tapeSuffixScannerDescription_subroutineReady
        hseq with
    ⟨_Tstage, hstage, _htape⟩
  rcases hstage with ⟨nStage, hstageRun, _hstageFirst⟩
  have hstageState :
      (DovetailStagePrefix.NonemptyNatSuffixScannerDescription.runConfig
        nStage
        (config DovetailStagePrefix.NonemptyNatSuffixScannerDescription.start
          baseLeft
          ((encodeCodeWordAsInput
            (encodeNatAppend state [])).map some))).state =
        DovetailStagePrefix.NonemptyNatSuffixScannerDescription.halt := by
    simpa [config] using
      congrArg Configuration.state hstageRun
  exact
    DovetailStagePrefix.nonemptyNatSuffixScannerDescription_runConfig_encodeNat_empty_ne_halt
      state baseLeft nStage hstageState

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
