import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner.TailBits

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace DovetailInitialLayoutInitializer
namespace StageInputMarkedScanner

theorem stageInputBits_nil_eq_done_nat
    (stage : Nat) :
    stageInputBits ([] : Word Bool) stage =
      false :: false :: true :: true ::
        encodeCodeWordAsInput
          (encodeNat stage) := by
  rw [stageInputBits_eq_false_false_tail]
  rw [stageInputSecondBitTail_nil]
  rfl

theorem scanner_marked_done_tail_decodeNat_none_ne_halt
    (rest : Word MachineCodeSymbol)
    (hdecode : decodeNat rest = none)
    (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (markedTailStartConfig
        (true :: true ::
          encodeCodeWordAsInput rest))).state ≠
      StageInputMarkedScannerDescription.halt := by
  cases rest with
  | nil =>
      exact
        scanner_ne_halt_of_reaches_stepConfig_none
          (k := 6) (by
            rfl)
          (by
            change (150 : Nat) ≠ 999
            omega)
  | cons symbol suffix =>
      cases symbol with
      | header =>
          apply
            scanner_ne_halt_of_reaches_ne_halt_region
              (k := 18)
              (mid :=
                config 200 [some true, some true, none, some false]
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: suffix)).map some))
          · simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              run_marked_tail_done_false_false_to_state200
                (false :: false ::
                  encodeCodeWordAsInput suffix)
          · intro m
            exact
              run_state200_decodeNat_none_ne_halt
                (MachineCodeSymbol.header :: suffix)
                [some true, some true, none, some false]
                hdecode m
      | transition =>
          apply
            scanner_ne_halt_of_reaches_ne_halt_region
              (k := 18)
              (mid :=
                config 200 [some true, some true, none, some false]
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: suffix)).map some))
          · simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              run_marked_tail_done_false_false_to_state200
                (false :: true ::
                  encodeCodeWordAsInput suffix)
          · intro m
            exact
              run_state200_decodeNat_none_ne_halt
                (MachineCodeSymbol.transition :: suffix)
                [some true, some true, none, some false]
                hdecode m
      | tick =>
          apply
            scanner_ne_halt_of_reaches_ne_halt_region
              (k := 18)
              (mid :=
                config 200 [some true, some true, none, some false]
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.tick :: suffix)).map some))
          · simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              run_marked_tail_done_false_false_to_state200
                (true :: false ::
                  encodeCodeWordAsInput suffix)
          · intro m
            exact
              run_state200_decodeNat_none_ne_halt
                (MachineCodeSymbol.tick :: suffix)
                [some true, some true, none, some false]
                hdecode m
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (151 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (151 : Nat) ≠ 999
                omega)
      | one =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (151 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (151 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            scanner_ne_halt_of_reaches_stepConfig_none
              (k := 18) (by
                cases suffix <;>
                simp [markedTailStartConfig,
                  StageInputMarkedScannerDescription,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                change (152 : Nat) ≠ 999
                omega)

theorem scanner_marked_done_tail_decodeNat_inv
    {rest : Word MachineCodeSymbol} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig
              (true :: true ::
                encodeCodeWordAsInput rest)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists stage : Nat,
    exists suffix : Word MachineCodeSymbol,
      decodeNat rest = some (stage, suffix) := by
  rcases hscanner with ⟨steps, hsteps⟩
  cases hdecode : decodeNat rest with
  | none =>
      have hne :=
        scanner_marked_done_tail_decodeNat_none_ne_halt
          rest hdecode steps
      have hstate :
          (StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig
              (true :: true ::
                encodeCodeWordAsInput rest))).state =
            StageInputMarkedScannerDescription.halt := by
        simpa using
          congrArg Configuration.state hsteps
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨stage, suffix⟩
      exact ⟨stage, suffix, rfl⟩

theorem scanner_marked_done_tail_nat_inv
    {rest : Word MachineCodeSymbol} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig
              (true :: true ::
                encodeCodeWordAsInput rest)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists stage : Nat,
      rest = encodeNat stage := by
  rcases scanner_marked_done_tail_decodeNat_inv hscanner with
    ⟨stagePrefix, suffix, hdecode⟩
  have hrest :
      rest =
        encodeNatAppend stagePrefix suffix :=
    decodeNat_eq_some_encodeNatAppend hdecode
  have hprefix :
      StageInputMarkedScannerDescription.runConfig 18
          (markedTailStartConfig
            (true :: true ::
              encodeCodeWordAsInput rest)) =
        config 200 [some true, some true, none, some false]
          ((encodeCodeWordAsInput rest).map some) := by
    rw [hrest]
    change
      StageInputMarkedScannerDescription.runConfig 18
          (markedTailStartConfig
            (true :: true ::
              encodeCodeWordAsInput
                (List.append (encodeNat stagePrefix)
                  suffix))) =
        config 200 [some true, some true, none, some false]
          (List.map some
            (encodeCodeWordAsInput
              (List.append (encodeNat stagePrefix)
                suffix)))
    rw [encodeCodeWordAsInput_append]
    have hrun :=
      run_marked_tail_done_stageNat_to_state200
        stagePrefix (encodeCodeWordAsInput suffix)
    simpa [stageNatBits, List.map_append] using hrun
  have hmid :
      (config 200 [some true, some true, none, some false]
        ((encodeCodeWordAsInput rest).map some)).state ≠
        StageInputMarkedScannerDescription.halt := by
    simp [config, StageInputMarkedScannerDescription]
  rcases
      runConfig_halt_after_prefix
        stageInputMarkedScannerDescription_haltTransitionFree
        hprefix hmid hscanner with
    ⟨rem, hrem⟩
  exact state200_code_tail_nat_inv ⟨rem, hrem⟩

theorem scanner_marked_done_tail_bits_shape_inv
    {rest : Word MachineCodeSymbol} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig
              (true :: true ::
                encodeCodeWordAsInput rest)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists stage : Nat,
      stageInputBits ([] : Word Bool) stage =
        false :: false :: true :: true ::
          encodeCodeWordAsInput rest := by
  rcases scanner_marked_done_tail_nat_inv hscanner with
    ⟨stage, hrest⟩
  subst rest
  exact ⟨stage, stageInputBits_nil_eq_done_nat stage⟩

theorem scanner_marked_code_tail_bits_shape_inv
    {code : Word MachineCodeSymbol} {tail : Word Bool} {T : Tape Bool}
    (hbits :
      encodeCodeWordAsInput code =
        false :: false :: tail)
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      stageInputBits w stage = false :: false :: tail := by
  rcases scanner_marked_code_tail_first_symbol_inv hbits hscanner with
    ⟨rest, _hcode, htail⟩ | ⟨rest, _hcode, htail⟩
  · subst tail
    exact scanner_marked_tick_tail_bits_shape_inv hscanner
  · subst tail
    rcases scanner_marked_done_tail_bits_shape_inv hscanner with
      ⟨stage, hshape⟩
    exact ⟨([] : Word Bool), stage, hshape⟩

theorem stageInputBits_false_false_tail_bridge
    {code : Word MachineCodeSymbol} {tail w : Word Bool}
    {stage : Nat}
    (hbits :
      encodeCodeWordAsInput code =
        false :: false :: tail)
    (hshape :
      stageInputBits w stage = false :: false :: tail) :
    code = PairedRecognizerDovetailStageInputCode w stage ∧
      tail = stageInputSecondBitTail w stage := by
  constructor
  · apply encodeCodeWordAsInput_injective
    rw [hbits, ← hshape]
    rfl
  · have hcanon := stageInputBits_eq_false_false_tail w stage
    rw [hshape] at hcanon
    injection hcanon with _ htailWithPrefix
    injection htailWithPrefix

theorem scanner_marked_code_tail_shape_inv
    {code : Word MachineCodeSymbol} {tail : Word Bool} {T : Tape Bool}
    (hbits :
      encodeCodeWordAsInput code =
        false :: false :: tail)
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      code = PairedRecognizerDovetailStageInputCode w stage ∧
        tail = stageInputSecondBitTail w stage := by
  rcases scanner_marked_code_tail_bits_shape_inv hbits hscanner with
    ⟨w, stage, hshape⟩
  rcases stageInputBits_false_false_tail_bridge hbits hshape with
    ⟨hcode, htail⟩
  exact ⟨w, stage, hcode, htail⟩

theorem scanner_marked_tail_tape_inv
    {tail : Word Bool} {T : Tape Bool}
    {w : Word Bool} {stage : Nat}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T })
    (htail : tail = stageInputSecondBitTail w stage) :
    T = stageInputSecondBitMarkedCheckedHandoffTape w stage := by
  subst tail
  rcases hscanner with ⟨scannerSteps, hscanner⟩
  rcases run_start_forward w stage with ⟨forwardSteps, hforward⟩
  exact
    runConfig_halt_tape_functional_from_config
      stageInputMarkedScannerDescription_haltTransitionFree
      hscanner
      (by
        simpa [markedTailStartConfig, markedStartConfig] using
          hforward)

theorem scanner_marked_code_tail_inv
    {code : Word MachineCodeSymbol} {tail : Word Bool} {T : Tape Bool}
    (hbits :
      encodeCodeWordAsInput code =
        false :: false :: tail)
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      code = PairedRecognizerDovetailStageInputCode w stage ∧
        tail = stageInputSecondBitTail w stage ∧
        T = stageInputSecondBitMarkedCheckedHandoffTape w stage := by
  rcases scanner_marked_code_tail_shape_inv hbits hscanner with
    ⟨w, stage, hcode, htail⟩
  exact
    ⟨w, stage, hcode, htail,
      scanner_marked_tail_tape_inv hscanner htail⟩

/-!
**Encoding inversion bridge.**  Once the finite scanner has recovered a
canonical {lean}`stageInputBits` suffix, the code-level conclusion is delegated
to {name}`DovetailLayout.decodeStageInputComplete`.
-/

theorem stageInputBits_code_decode
    {code : Word MachineCodeSymbol} {w : Word Bool}
    {stage : Nat}
    (hbits :
      encodeCodeWordAsInput code =
        stageInputBits w stage) :
    DovetailLayout.decodeStageInputComplete code =
      some (w, stage) := by
  have hcode :
      code = PairedRecognizerDovetailStageInputCode w stage :=
    encodeCodeWordAsInput_injective
      (by simpa [stageInputBits] using hbits)
  rw [hcode]
  simp [PairedRecognizerDovetailStageInputCode,
    DovetailLayout.decodeStageInputComplete_stageInputCode]

theorem stageInputBits_code_inv
    {code : Word MachineCodeSymbol} {w : Word Bool}
    {stage : Nat}
    (hbits :
      encodeCodeWordAsInput code =
        stageInputBits w stage) :
    code = PairedRecognizerDovetailStageInputCode w stage := by
  exact
    DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
      (stageInputBits_code_decode hbits)

theorem stageInputMarkedScannerDescription_closed
    (code : Word MachineCodeSymbol) (Tmark T : Tape Bool)
    (hmark :
      MarkStageInputSecondBitDescription.HaltsWithTape
        (encodeCodeWordAsInput code) Tmark)
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            { state := StageInputMarkedScannerDescription.start
              tape := Tape.move Direction.right Tmark } =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      code = PairedRecognizerDovetailStageInputCode w stage ∧
        T = stageInputSecondBitMarkedCheckedHandoffTape w stage := by
  rcases markStageInputSecondBitDescription_haltsWithTape_inv hmark with
    ⟨tail, hbits, hTmark⟩
  have hscannerTail :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T } := by
    rcases hscanner with ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    simpa [markedTailStartConfig, hTmark] using hsteps
  rcases scanner_marked_code_tail_inv hbits hscannerTail with
    ⟨w, stage, hcode, _htail, hT⟩
  exact ⟨w, stage, hcode, hT⟩

/-!
The exported construction theorem packages the subroutine readiness, forward
run, and closed-run inversion required by {name}`StageInputMarkedScannerSpec`.
At this point the theorem itself is only glue; every remaining proof obligation
has a phase-specific name.
-/

theorem stageInputMarkedScannerDescription_spec :
    StageInputMarkedScannerSpec StageInputMarkedScannerDescription := by
  constructor
  · exact stageInputMarkedScannerDescription_subroutineReady
  constructor
  · intro w stage
    simpa [markedStartConfig, checkedHaltConfig] using
      run_start_forward w stage
  · intro code Tmark T hmark hscanner
    exact
      stageInputMarkedScannerDescription_closed
        code Tmark T hmark hscanner

end StageInputMarkedScanner
end DovetailInitialLayoutInitializer
end Computability
end FoC
