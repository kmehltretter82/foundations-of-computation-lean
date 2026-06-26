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
            ((MachineDescription.encodeCodeWordAsInput code).map some)) =
        { state := ConfigurationSuffixScannerDescription.halt
          tape := Tout }) :
    exists cfg : MachineDescription.Configuration,
    exists suffix : Word MachineCodeSymbol,
    exists baseAfter : List (Option Bool),
      code = MachineDescription.encodeConfigurationAppend cfg suffix ∧
        Tape.move Direction.right Tout =
          tapeAtCells baseAfter
            ((MachineDescription.encodeCodeWordAsInput suffix).map
              some) := by
  have hseq :
      (MachineDescription.seqSubroutine
        DovetailStagePrefix.NatSuffixScannerDescription
        TapeSuffixScannerDescription
        Direction.right).runConfig n
          { state :=
              (MachineDescription.seqSubroutine
                DovetailStagePrefix.NatSuffixScannerDescription
                TapeSuffixScannerDescription
                Direction.right).start
            tape :=
              tapeAtCells baseLeft
                ((MachineDescription.encodeCodeWordAsInput code).map
                  some) } =
        { state :=
            (MachineDescription.seqSubroutine
              DovetailStagePrefix.NatSuffixScannerDescription
              TapeSuffixScannerDescription
              Direction.right).halt
          tape := Tout } := by
    simpa [ConfigurationSuffixScannerDescription, config] using h
  rcases
      MachineDescription.seqSubroutine_runConfig_inv
        (A := DovetailStagePrefix.NatSuffixScannerDescription)
        (B := TapeSuffixScannerDescription)
        (handoffMove := Direction.right)
        DovetailStagePrefix.natSuffixScannerDescription_subroutineReady
        tapeSuffixScannerDescription_subroutineReady
        hseq with
    ⟨Tstage, hstage, htape⟩
  rcases hstage with ⟨nStage, hstageRun, _hstageFirst⟩
  rcases
      DovetailStagePrefix.natSuffixScannerDescription_runConfig_code_inv
        baseLeft code (by simpa [config] using hstageRun) with
    ⟨state, tapeCode, hcodeState⟩
  cases tapeCode with
  | nil =>
      -- Remaining finite-machine obligation: the nat scanner can halt on the
      -- empty suffix by rewinding, so this branch must rule out a following
      -- tape-suffix halt from that rewound handoff tape.
      sorry
  | cons tapeSymbol tapeRest =>
      rcases encodeCodeWordAsInput_cons_bits tapeSymbol tapeRest with
        ⟨tapeBit, tapeTail, htapeBits⟩
      rcases
          natSuffixScannerDescription_runConfig_encodeNatAppend_handoff
            baseLeft state (tapeSymbol :: tapeRest) tapeBit tapeTail
            htapeBits
            (by simpa [config, hcodeState] using hstageRun) with
        ⟨baseAfterState, hstageMove⟩
      rcases htape with ⟨nTape, htapeRun⟩
      have htapeCodeRun :
          TapeSuffixScannerDescription.runConfig nTape
              (config TapeSuffixScannerDescription.start baseAfterState
                ((MachineDescription.encodeCodeWordAsInput
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
      simp [MachineDescription.encodeConfigurationAppend, hcodeState,
        htapeCode]

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
