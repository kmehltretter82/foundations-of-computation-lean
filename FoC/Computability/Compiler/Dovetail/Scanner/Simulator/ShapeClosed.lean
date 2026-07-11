import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Closed
import FoC.Computability.Compiler.Dovetail.Scanner.BoolWordClosed
import FoC.Computability.Compiler.Dovetail.Scanner.ConfigurationClosed
import FoC.Computability.Compiler.Core.EncRewriters.BoundedLayoutRunner.Parser.Closed

set_option doc.verso true

/-!
# Shape facts for closed simulator-layout scanner runs

A halting run of the checked simulator-layout scanner from a code-word start
forces the code word to decode as a complete simulator layout.  This is the
simulator-family analogue of the dovetail decode inversion, assembled from the
shared component scanner inversions.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace CanonicalLayouts
namespace SimulatorLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.SeqComposition
open DovetailLayoutScanner

private abbrev CFS := ConfigurationSuffixScannerDescription
private abbrev BFS := BoolFinalScannerDescription
private abbrev NNSS := DovetailStagePrefix.NonemptyNatSuffixScannerDescription
private abbrev BWSS := BoolWordSuffixScannerDescription
private abbrev CSL := CheckedSimulatorLayoutScannerDescription

theorem encodeCodeWordAsInput_header_prefix_inv
    {code : Word MachineCodeSymbol} {tail : Word Bool}
    (h :
      encodeCodeWordAsInput code =
        false :: false :: false :: false :: tail) :
    exists rest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.header :: rest ∧
        encodeCodeWordAsInput rest = tail := by
  cases code with
  | nil =>
      simp [encodeCodeWordAsInput] at h
  | cons symbol rest =>
      cases symbol with
      | header =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
          exact ⟨rest, rfl, rfl⟩
      | transition =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | tick =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | done =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | blank =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | zero =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | one =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | moveLeft =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | moveRight =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h

/--
Decode inversion for the checked simulator-layout scanner: a halting run from
a code-word start forces a complete simulator-layout parse.
-/
theorem checkedSimulatorLayoutScannerDescription_haltsWithTape_decodeComplete_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    (h :
      CSL.HaltsWithTape (encodeCodeWordAsInput code) Tout) :
    exists L : SimulatorLayout,
      SimulatorLayout.decodeComplete code = some L := by
  rcases
      checkedSimulatorLayoutScannerDescription_haltsWithTape_fields_inv
        h with
    ⟨b, suffixTail, Tinput, Tstage, Tconfig, Tbody,
      nInput, nStage, nConfig, nFlag, _nReturn,
      hbits, hinputRun, hstageRun, hconfigRun, hflagRun, _hreturnRun⟩
  rcases encodeCodeWordAsInput_header_prefix_inv hbits with
    ⟨rest, hcode, hrestBits⟩
  -- Input bool-word field.
  have hinputRunCode :
      BWSS.runConfig nInput
          (config BWSS.start
            (List.append (headerRemainderBits.reverse.map some) [none])
            ((encodeCodeWordAsInput rest).map some)) =
        { state := BWSS.halt
          tape := Tinput } := by
    rw [hrestBits]
    exact hinputRun
  rcases
      boolWordSuffixScannerDescription_runConfig_code_inv
        (List.append (headerRemainderBits.reverse.map some) [none])
        rest hinputRunCode with
    ⟨inputWord, inputRest, hrest⟩
  rw [hrest] at hinputRunCode
  rcases
      BoundedLayoutRunner.boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_stage_handoff
        (List.append (headerRemainderBits.reverse.map some) [none])
        inputWord inputRest
        hinputRunCode
        (by exact hstageRun) with
    ⟨baseAfterInput, hinputMove⟩
  -- Stage nat field.
  have hstageRunCode :
      NNSS.runConfig nStage
          (config NNSS.start baseAfterInput
            ((encodeCodeWordAsInput inputRest).map some)) =
        { state := NNSS.halt
          tape := Tstage } := by
    have h' := hstageRun
    rw [hinputMove] at h'
    exact h'
  rcases
      DovetailStagePrefix.nonemptyNatSuffixScannerDescription_runConfig_code_inv
        baseAfterInput inputRest hstageRunCode with
    ⟨stage, configFirst, configSuffix, hinputRest⟩
  rcases
      DovetailLayoutScanner.encodeCodeWordAsInput_cons_bits
        configFirst configSuffix with
    ⟨configBit, configBitsTail, hconfigBits⟩
  have hconfigBits' :
      encodeCodeWordAsInput
          (configFirst :: configSuffix) =
        configBit :: configBitsTail := hconfigBits
  rw [hinputRest] at hstageRunCode
  rcases
      DovetailStagePrefix.nonemptyNatSuffixScannerDescription_runConfig_encodeNatAppend_handoff
        baseAfterInput stage (configFirst :: configSuffix)
        configBit configBitsTail hconfigBits' hstageRunCode with
    ⟨baseAfterStage, hstageMove⟩
  -- Configuration field.
  have hconfigRunCode :
      CFS.runConfig nConfig
          (config CFS.start baseAfterStage
            ((encodeCodeWordAsInput
              (configFirst :: configSuffix)).map some)) =
        { state := CFS.halt
          tape := Tconfig } := by
    have h' := hconfigRun
    rw [hstageMove] at h'
    exact h'
  rcases
      DovetailLayoutScanner.configurationSuffixScannerDescription_runConfig_code_handoff
        baseAfterStage (configFirst :: configSuffix)
        hconfigRunCode with
    ⟨cfg, flagRest, baseAfterConfig, hconfigCode, hconfigMove⟩
  -- Final hit flag.
  have hflagRunCode :
      BFS.runConfig nFlag
          (config BFS.start baseAfterConfig
            ((encodeCodeWordAsInput flagRest).map some)) =
        { state := BFS.halt
          tape := Tbody } := by
    have h' := hflagRun
    rw [hconfigMove] at h'
    exact h'
  rcases
      DovetailLayoutScanner.boolFinalScannerDescription_runConfig_code_terminal_inv
        baseAfterConfig flagRest hflagRunCode with
    ⟨hit, hflagCode, _hbodyMove⟩
  -- Assemble the complete layout.
  refine
    ⟨{ input := inputWord
       stage := stage
       config := cfg
       hit := hit }, ?_⟩
  have hcodeEq :
      code =
        SimulatorLayout.encode
          { input := inputWord
            stage := stage
            config := cfg
            hit := hit } := by
    rw [hcode, hrest, hinputRest, hconfigCode, hflagCode]
    rfl
  rw [hcodeEq]
  exact
    SimulatorLayout.decodeComplete_encode
      { input := inputWord
        stage := stage
        config := cfg
        hit := hit }

end SimulatorLayoutScanner
end CanonicalLayouts
end EncRewriters

end Computability
end FoC
