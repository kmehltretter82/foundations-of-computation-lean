import FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutScanner
import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Runs
namespace FoC
namespace Computability
open Languages
open MachineDescription
namespace EncRewriters
namespace BoundedLayoutRunner
def nestedLayoutPaddingRewindDescription : MachineDescription where
  stateCount := 7
  start := 0
  halt := 6
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.right 1
    , transition 1 none none Direction.left 2
    , transition 2 none none Direction.left 3
    , transition 3 (some false) (some false) Direction.left 3
    , transition 3 (some true) (some true) Direction.left 3
    , transition 3 none none Direction.left 4
    , transition 4 none none Direction.right 5
    , transition 5 none none Direction.right 6 ]
theorem nestedLayoutPaddingRewindDescription_subroutineReady :
    nestedLayoutPaddingRewindDescription.SubroutineReady := by
  constructor
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · exact transition_wellFormed_of_all (by decide)
    · exact transition_deterministic_of_all (by decide)
  · exact transition_notFrom_of_all (by decide)
private theorem nestedLayoutPaddingRewindDescription_run_scan
    (bits : List Bool) (left : List (Option Bool)) :
    nestedLayoutPaddingRewindDescription.runConfig bits.length
        { state := 0
          tape := DovetailInitialLayoutInitializer.tapeAtCells left
            (bits.map some) } =
      { state := 0
        tape := DovetailInitialLayoutInitializer.tapeAtCells
          (List.append (bits.reverse.map some) left) [] } := by
  have hstep : forall (bit : Bool) (left : List (Option Bool))
      (right : List (Option Bool)),
      nestedLayoutPaddingRewindDescription.runConfig 1
          { state := 0
            tape := DovetailInitialLayoutInitializer.tapeAtCells left
              (some bit :: right) } =
        { state := 0
          tape := DovetailInitialLayoutInitializer.tapeAtCells
            (some bit :: left) right } := by
    intro bit left right
    cases bit <;> cases right <;>
      simp [nestedLayoutPaddingRewindDescription,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveRight]
  induction bits generalizing left with
  | nil => rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [runConfig_add]
      simp only [List.map_cons]
      rw [hstep bit left (rest.map some)]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)
private theorem nestedLayoutPaddingRewindDescription_run_turn
    (current : Bool) (left : List (Option Bool)) :
    nestedLayoutPaddingRewindDescription.runConfig 3
        { state := 0
          tape := DovetailInitialLayoutInitializer.tapeAtCells
            (some current :: left) [] } =
      { state := 3
        tape := DovetailInitialLayoutInitializer.tapeAtCells left
          [some current, none, none] } := by
  cases current <;> cases left <;>
    simp [nestedLayoutPaddingRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
private theorem nestedLayoutPaddingRewindDescription_run_left
    (leftBits : List Bool) (current : Bool)
    (right : List (Option Bool)) :
    nestedLayoutPaddingRewindDescription.runConfig
        (leftBits.length + 4)
        { state := 3
          tape := DovetailInitialLayoutInitializer.tapeAtCells
            (leftBits.map some)
            (some current :: right) } =
      { state := 6
        tape := DovetailInitialLayoutInitializer.tapeAtCells [none, none]
          (List.append
            ((List.append leftBits.reverse [current]).map some) right) } := by
  have hstep : forall (bit : Bool) (left : List (Option Bool))
      (current : Bool) (right : List (Option Bool)),
      nestedLayoutPaddingRewindDescription.runConfig 1
          { state := 3
            tape := DovetailInitialLayoutInitializer.tapeAtCells
              (some bit :: left) (some current :: right) } =
        { state := 3
          tape := DovetailInitialLayoutInitializer.tapeAtCells left
            (some bit :: some current :: right) } := by
    intro bit left current right
    cases bit <;> cases current <;> cases left <;> cases right <;>
          simp [nestedLayoutPaddingRewindDescription,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft]
  induction leftBits generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        simp [nestedLayoutPaddingRewindDescription,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 4 = 1 + (rest.length + 4) by
        simp
        lia]
      rw [runConfig_add]
      simp only [List.map_cons]
      change
        nestedLayoutPaddingRewindDescription.runConfig
            (rest.length + 4)
            (nestedLayoutPaddingRewindDescription.runConfig 1
              { state := 3
                tape := DovetailInitialLayoutInitializer.tapeAtCells
                  (some bit :: rest.map some)
                  (some current :: right) }) = _
      rw [hstep bit
        (rest.map some) current right]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih bit (some current :: right)
private theorem nestedLayoutPaddingRewindDescription_run_from_rightEnd
    (current : Bool) (leftBits : List Bool) :
    nestedLayoutPaddingRewindDescription.runConfig
        (3 + (leftBits.length + 4))
        { state := 0
          tape := DovetailInitialLayoutInitializer.tapeAtCells
            ((current :: leftBits).map some) [] } =
      { state := 6
        tape := DovetailInitialLayoutInitializer.tapeAtCells [none, none]
          (List.append ((current :: leftBits).reverse.map some)
            [none, none]) } := by
  rw [runConfig_add]
  simp only [List.map_cons]
  rw [nestedLayoutPaddingRewindDescription_run_turn current
    (leftBits.map some)]
  simpa [List.reverse_cons, List.map_append, List.append_assoc] using
    nestedLayoutPaddingRewindDescription_run_left
      leftBits current [none, none]
theorem nestedLayoutPaddingRewindDescription_haltsFromTape
    (first : Bool) (rest : List Bool) :
    nestedLayoutPaddingRewindDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells []
        ((first :: rest).map some))
      (DovetailInitialLayoutInitializer.tapeAtCells [none, none]
        (List.append ((first :: rest).map some) [none, none])) := by
  let leftStack : List Bool := (first :: rest).reverse
  have hleftStack : leftStack ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [leftStack] at this
  rcases List.exists_cons_of_ne_nil hleftStack with
    ⟨current, leftBits, hleftStackEq⟩
  refine ⟨(first :: rest).length + (3 + (leftBits.length + 4)), ?_⟩
  have hscan :=
    nestedLayoutPaddingRewindDescription_run_scan
      (first :: rest) []
  have hrightEnd :=
    nestedLayoutPaddingRewindDescription_run_from_rightEnd
      current leftBits
  have hrun :
      nestedLayoutPaddingRewindDescription.runConfig
          ((first :: rest).length + (3 + (leftBits.length + 4)))
          { state := nestedLayoutPaddingRewindDescription.start
            tape := DovetailInitialLayoutInitializer.tapeAtCells []
              ((first :: rest).map some) } =
        { state := nestedLayoutPaddingRewindDescription.halt
          tape := DovetailInitialLayoutInitializer.tapeAtCells [none, none]
            (List.append ((first :: rest).map some)
              [none, none]) } := by
    rw [runConfig_add]
    change
      nestedLayoutPaddingRewindDescription.runConfig
          (3 + (leftBits.length + 4))
          (nestedLayoutPaddingRewindDescription.runConfig
            (first :: rest).length
            { state := 0
              tape := DovetailInitialLayoutInitializer.tapeAtCells []
                ((first :: rest).map some) }) = _
    rw [hscan]
    have hsource :
        DovetailInitialLayoutInitializer.tapeAtCells
            (List.append ((first :: rest).reverse.map some) []) [] =
          DovetailInitialLayoutInitializer.tapeAtCells
            ((current :: leftBits).map some) [] := by
      rw [← hleftStackEq]
      simp [leftStack]
    rw [hsource, hrightEnd]
    have hout : (current :: leftBits).reverse = first :: rest := by
      rw [← hleftStackEq]
      simp [leftStack]
    rw [hout]
    rfl
  constructor <;> rw [hrun] <;>
    rfl
def nestedLayoutOuterTransitionShaperDescription :
    MachineDescription where
  stateCount := 8
  start := 0
  halt := 7
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 1 none (some false) Direction.right 2
    , transition 2 (some false) (some false) Direction.right 3
    , transition 3 (some false) (some false) Direction.right 4
    , transition 4 (some false) (some true) Direction.right 5
    , transition 5 (some true) none Direction.left 6
    , transition 6 (some true) (some true) Direction.right 7 ]
theorem nestedLayoutOuterTransitionShaperDescription_subroutineReady :
    nestedLayoutOuterTransitionShaperDescription.SubroutineReady := by
  constructor
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · exact transition_wellFormed_of_all (by decide)
    · exact transition_deterministic_of_all (by decide)
  · exact transition_notFrom_of_all (by decide)
theorem nestedLayoutOuterTransitionShaperDescription_haltsFromTape
    (tail : List (Option Bool)) :
    nestedLayoutOuterTransitionShaperDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells [none, none]
        (some false :: some false :: some false :: some true :: tail))
      (DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ([false, false, false, true].reverse.map some) [none])
        (none :: tail)) := by
  refine ⟨7, ?_⟩
  have hrun :
      nestedLayoutOuterTransitionShaperDescription.runConfig 7
          { state := nestedLayoutOuterTransitionShaperDescription.start
            tape := DovetailInitialLayoutInitializer.tapeAtCells [none, none]
              (some false :: some false :: some false :: some true :: tail) } =
        { state := nestedLayoutOuterTransitionShaperDescription.halt
          tape := DovetailInitialLayoutInitializer.tapeAtCells
            (List.append
              ([false, false, false, true].reverse.map some) [none])
            (none :: tail) } := by
    cases tail <;>
      simp [nestedLayoutOuterTransitionShaperDescription,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  constructor <;> rw [hrun]
theorem nestedLayoutOuterTransitionShaperDescription_target_move_right
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append
            ([false, false, false, true].reverse.map some) [none])
          (none :: tail)) =
      DovetailInitialLayoutInitializer.tapeAtCells
        SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft tail := by
  cases tail <;>
    simp [SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft,
      SelectedMergePaddedEmitterOuterTransitionBaseLeft,
      encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells, Tape.move,
      Tape.moveRight]
private abbrev NLBSS :=
  CanonicalLayouts.DovetailLayoutScanner.BoolSuffixScannerDescription
private abbrev NLCFS :=
  CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription
private abbrev NLNNSS :=
  CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription
private abbrev NLCLSS :=
  CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription
private abbrev NLTRP :=
  CanonicalLayouts.DovetailLayoutScanner.TransitionRemainderPrefixScannerDescription
private abbrev NLSCFF :=
  CanonicalLayouts.SimulatorLayoutScanner.StageConfigurationAndFinalFlagScannerDescription
def nestedLayoutContextFinalFlagsDescription : MachineDescription :=
  seqSubroutine NLBSS NLBSS Direction.right
def nestedLayoutContextRejectAndFlagsDescription : MachineDescription :=
  seqSubroutine NLCFS nestedLayoutContextFinalFlagsDescription
    Direction.right
def nestedLayoutContextConfigurationsAndFlagsDescription :
    MachineDescription :=
  seqSubroutine NLCFS nestedLayoutContextRejectAndFlagsDescription
    Direction.right
def nestedLayoutContextStageAndFieldsDescription : MachineDescription :=
  seqSubroutine NLNNSS
    nestedLayoutContextConfigurationsAndFlagsDescription
    Direction.right
def nestedLayoutContextInputAndFieldsDescription : MachineDescription :=
  seqSubroutine NLCLSS nestedLayoutContextStageAndFieldsDescription
    Direction.right
def nestedLayoutContextBodyDescription : MachineDescription :=
  seqSubroutine NLTRP nestedLayoutContextInputAndFieldsDescription
    Direction.right
def nestedLayoutOuterFinishDescription : MachineDescription :=
  seqSubroutine NLSCFF ExactIdentityDescription Direction.right
def nestedLayoutBodyAndOuterFinishDescription : MachineDescription :=
  seqSubroutine nestedLayoutContextBodyDescription
    nestedLayoutOuterFinishDescription Direction.right
def nestedLayoutRestorerCoreDescription : MachineDescription :=
  seqSubroutine nestedLayoutOuterTransitionShaperDescription
    nestedLayoutBodyAndOuterFinishDescription Direction.right
def nestedLayoutRestorerDescription : MachineDescription :=
  CommonGround.FiniteTransducers.canonicalSeqDescription
    nestedLayoutPaddingRewindDescription
    nestedLayoutRestorerCoreDescription
theorem nestedLayoutContextFinalFlagsDescription_subroutineReady :
    nestedLayoutContextFinalFlagsDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    CanonicalLayouts.DovetailLayoutScanner.boolSuffixScannerDescription_subroutineReady
    CanonicalLayouts.DovetailLayoutScanner.boolSuffixScannerDescription_subroutineReady
theorem nestedLayoutContextRejectAndFlagsDescription_subroutineReady :
    nestedLayoutContextRejectAndFlagsDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    CanonicalLayouts.DovetailLayoutScanner.configurationSuffixScannerDescription_subroutineReady
    nestedLayoutContextFinalFlagsDescription_subroutineReady
theorem nestedLayoutContextConfigurationsAndFlagsDescription_subroutineReady :
    nestedLayoutContextConfigurationsAndFlagsDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    CanonicalLayouts.DovetailLayoutScanner.configurationSuffixScannerDescription_subroutineReady
    nestedLayoutContextRejectAndFlagsDescription_subroutineReady
theorem nestedLayoutContextStageAndFieldsDescription_subroutineReady :
    nestedLayoutContextStageAndFieldsDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
    nestedLayoutContextConfigurationsAndFlagsDescription_subroutineReady
theorem nestedLayoutContextInputAndFieldsDescription_subroutineReady :
    nestedLayoutContextInputAndFieldsDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    CanonicalLayouts.DovetailLayoutScanner.boolWordSuffixScannerDescription_subroutineReady
    nestedLayoutContextStageAndFieldsDescription_subroutineReady
theorem nestedLayoutContextBodyDescription_subroutineReady :
    nestedLayoutContextBodyDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    CanonicalLayouts.DovetailLayoutScanner.transitionRemainderPrefixScannerDescription_subroutineReady
    nestedLayoutContextInputAndFieldsDescription_subroutineReady
theorem nestedLayoutOuterFinishDescription_subroutineReady :
    nestedLayoutOuterFinishDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    CanonicalLayouts.SimulatorLayoutScanner.stageConfigurationAndFinalFlagScannerDescription_subroutineReady
    CommonGround.Identity.exactIdentityDescription_subroutineReady
theorem nestedLayoutBodyAndOuterFinishDescription_subroutineReady :
    nestedLayoutBodyAndOuterFinishDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    nestedLayoutContextBodyDescription_subroutineReady
    nestedLayoutOuterFinishDescription_subroutineReady
theorem nestedLayoutRestorerCoreDescription_subroutineReady :
    nestedLayoutRestorerCoreDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    nestedLayoutOuterTransitionShaperDescription_subroutineReady
    nestedLayoutBodyAndOuterFinishDescription_subroutineReady
theorem nestedLayoutRestorerDescription_subroutineReady :
    nestedLayoutRestorerDescription.SubroutineReady := by
  exact CommonGround.FiniteTransducers.canonicalSeqDescription_subroutineReady
    nestedLayoutPaddingRewindDescription_subroutineReady
    nestedLayoutRestorerCoreDescription_subroutineReady
private theorem nestedLayoutRestorerHaltsFromTape_of_runConfig_exists
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : exists steps : Nat,
      D.runConfig steps { state := D.start, tape := Tin } =
        { state := D.halt, tape := Tout }) :
    D.HaltsFromTape Tin Tout := by
  rcases h with ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg Configuration.tape hsteps
def nestedLayoutRestorerContextTape
    (baseLeft : List (Option Bool)) (remaining : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells baseLeft
    (List.append (remaining.map some) [none, none])
private theorem nestedLayoutRestorerTransitionRemainderPrefixScanner_haltsFrom_context
    (baseLeft : List (Option Bool)) (b : Bool) (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    CanonicalLayouts.DovetailLayoutScanner.TransitionRemainderPrefixScannerDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells baseLeft
        (List.append
          ((List.append
            CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits
            (b :: suffixTail)).map some)
          rightPadding))
      (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderHandoffConfigWithBaseAndRight
        baseLeft (b :: suffixTail) rightPadding).tape := by
  apply nestedLayoutRestorerHaltsFromTape_of_runConfig_exists
  simpa [DovetailInitialLayoutInitializer.config,
    CanonicalLayouts.DovetailLayoutScanner.TransitionRemainderPrefixScannerDescription,
    CanonicalLayouts.DovetailLayoutScanner.transitionRemainderHandoffConfigWithBaseAndRight,
    CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits,
    List.map_append, List.append_assoc] using
      (CanonicalLayouts.DovetailLayoutScanner.run_transitionRemainderPrefix_raw_to_handoff_withBaseAndRight
        baseLeft b suffixTail rightPadding)
private theorem nestedLayoutRestorerBoolWordSuffixScanner_haltsFrom_context
    (w : Word Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells baseLeft
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits w
            (false :: suffixTail)).map some)
          rightPadding))
      (CanonicalLayouts.DovetailLayoutScanner.boolWordCanonicalHandoffConfigWithBaseAndRight
        w baseLeft (false :: suffixTail) rightPadding).tape := by
  apply nestedLayoutRestorerHaltsFromTape_of_runConfig_exists
  simpa [DovetailInitialLayoutInitializer.config,
    CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription,
    CanonicalLayouts.DovetailLayoutScanner.boolWordCanonicalHandoffConfigWithBaseAndRight,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    List.map_append, List.append_assoc] using
      (CanonicalLayouts.DovetailLayoutScanner.run_boolWordSuffix_raw_to_canonical_handoff_withBaseAndRight
        w baseLeft suffixTail rightPadding)
private theorem nestedLayoutRestorerNonemptyNatSuffixScanner_haltsFrom_context
    (n : Nat) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells baseLeft
        (List.append
          ((List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
            (false :: suffixTail)).map some)
          rightPadding))
      (CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight
        n baseLeft (false :: suffixTail) rightPadding).tape := by
  apply nestedLayoutRestorerHaltsFromTape_of_runConfig_exists
  simpa [DovetailInitialLayoutInitializer.config,
    CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription,
    CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight,
    List.map_append, List.append_assoc] using
      (CanonicalLayouts.DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBaseAndRight
        n baseLeft false suffixTail rightPadding)
private theorem nestedLayoutRestorerConfigurationSuffixScanner_haltsFrom_context
    (cfg : Configuration) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells baseLeft
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits cfg
            (false :: suffixTail)).map some)
          rightPadding))
      (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight
        cfg.tape.right
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
            cfg.tape.head).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            cfg.tape.left
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                cfg.state).reverse.map some)
              baseLeft)))
        (false :: suffixTail) rightPadding).tape := by
  apply nestedLayoutRestorerHaltsFromTape_of_runConfig_exists
  simpa [DovetailInitialLayoutInitializer.config,
    CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription,
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight]
    using
      (CanonicalLayouts.DovetailLayoutScanner.run_configurationSuffix_raw_to_handoff_withBaseAndRight
        cfg baseLeft suffixTail rightPadding)
private theorem nestedLayoutRestorerBoolSuffixScanner_haltsFrom_context
    (flag : Bool) (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    CanonicalLayouts.DovetailLayoutScanner.BoolSuffixScannerDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells baseLeft
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits flag
            (b :: suffixTail)).map some)
          rightPadding))
      (CanonicalLayouts.DovetailLayoutScanner.boolOnlySuffixHandoffConfigWithBaseAndRight
        flag baseLeft (b :: suffixTail) rightPadding).tape := by
  apply nestedLayoutRestorerHaltsFromTape_of_runConfig_exists
  simpa [DovetailInitialLayoutInitializer.config,
    CanonicalLayouts.DovetailLayoutScanner.BoolSuffixScannerDescription,
    CanonicalLayouts.DovetailLayoutScanner.boolOnlySuffixHandoffConfigWithBaseAndRight,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.map_append, List.append_assoc] using
      (CanonicalLayouts.DovetailLayoutScanner.run_boolOnlySuffix_raw_to_handoff_withBaseAndRight
        flag baseLeft b suffixTail rightPadding)
private theorem nestedLayoutOuterFinishDescription_haltsFrom_context
    (stage : Nat) (cfg : Configuration) (hit : Bool)
    (baseLeft : List (Option Bool)) :
    nestedLayoutOuterFinishDescription.HaltsFromTape
      (nestedLayoutRestorerContextTape baseLeft
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits cfg
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits hit []))))
      (DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
            (some hit)).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
            cfg
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).reverse.map some)
              baseLeft)))
        [none, none]) := by
  let Tmid : Tape Bool :=
    (CanonicalLayouts.DovetailLayoutScanner.boolFinalHandoffConfigWithBaseAndRight
      hit
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
        cfg
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          baseLeft))
      [none, none]).tape
  have hscan : NLSCFF.HaltsFromTape
      (nestedLayoutRestorerContextTape baseLeft
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits cfg
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits hit []))))
      Tmid := by
    apply nestedLayoutRestorerHaltsFromTape_of_runConfig_exists
    simpa [nestedLayoutRestorerContextTape, Tmid,
      CanonicalLayouts.SimulatorLayoutScanner.StageConfigurationAndFinalFlagScannerDescription,
      CanonicalLayouts.DovetailLayoutScanner.boolFinalHandoffConfigWithBaseAndRight,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc] using
        (CanonicalLayouts.SimulatorLayoutScanner.run_stageConfigurationAndFinalFlag_raw_to_handoff_withBaseAndRight
          stage cfg hit baseLeft [none])
  apply CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
    CanonicalLayouts.SimulatorLayoutScanner.stageConfigurationAndFinalFlagScannerDescription_subroutineReady
    CommonGround.Identity.exactIdentityDescription_subroutineReady
    hscan
  · simpa [Tmid] using
      (CanonicalLayouts.SimulatorLayoutScanner.boolFinalHandoffConfigWithBaseAndRight_move_right
        hit
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          cfg
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            baseLeft))
        [none, none])
  · simpa [List.map_reverse] using
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
              (some hit)).reverse.map some)
            (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
              cfg
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage).reverse.map some)
                baseLeft)))
          [none, none]))
private theorem nestedLayoutBodyAndOuterFinishDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    nestedLayoutBodyAndOuterFinishDescription.HaltsFromTape
      (nestedLayoutRestorerContextTape
        SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
            p.L)
          (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)))
      (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) := by
  let outer : Word Bool :=
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p
  let afterAcceptHit : Word Bool :=
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.L.rejectHit outer
  let afterRejectConfig : Word Bool :=
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.L.acceptHit
      afterAcceptHit
  let afterAcceptConfig : Word Bool :=
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      p.L.rejectConfig afterRejectConfig
  let afterStage : Word Bool :=
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      p.L.acceptConfig afterAcceptConfig
  let afterInput : Word Bool :=
    List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        p.L.stage)
      afterStage
  have hbody :
      List.append
          (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
            p.L)
          outer =
        List.append
          CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits
          (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
            p.L.input afterInput) := by
    simp [outer, afterInput, afterStage, afterAcceptConfig,
      afterRejectConfig, afterAcceptHit,
      CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      List.append_assoc]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits_cons_false
        (p.L.input.map some) afterInput with
    ⟨inputFieldTail, hinputField⟩
  have hinputField' :
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
          p.L.input afterInput = false :: inputFieldTail := by
    exact hinputField
  rcases
      CanonicalLayouts.DovetailLayoutScanner.stageNatBits_cons_false p.L.stage with
    ⟨inputSuffixHead, hinputSuffixHead⟩
  let inputSuffixTail : Word Bool :=
    List.append inputSuffixHead afterStage
  have hafterInput : afterInput = false :: inputSuffixTail := by
    simp [afterInput, inputSuffixTail, hinputSuffixHead]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        p.L.acceptConfig afterAcceptConfig with
    ⟨acceptFieldTail, hacceptField⟩
  have hafterStage : afterStage = false :: acceptFieldTail := by
    exact hacceptField
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        p.L.rejectConfig afterRejectConfig with
    ⟨rejectFieldTail, hrejectField⟩
  have hafterAcceptConfig :
      afterAcceptConfig = false :: rejectFieldTail := by
    exact hrejectField
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_cons_false
        (some p.L.acceptHit) afterAcceptHit with
    ⟨acceptHitTail, hacceptHit⟩
  have hafterRejectConfig :
      afterRejectConfig = false :: acceptHitTail := by
    exact hacceptHit
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_cons_false
        (some p.L.rejectHit) outer with
    ⟨rejectHitTail, hrejectHit⟩
  have hafterAcceptHit : afterAcceptHit = false :: rejectHitTail := by
    exact hrejectHit
  rcases
      CanonicalLayouts.DovetailLayoutScanner.stageNatBits_cons_false p.S.stage with
    ⟨outerStageTail, houterStage⟩
  let outerTail : Word Bool :=
    List.append outerStageTail
      (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        p.S.config
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.S.hit []))
  have houter : outer = false :: outerTail := by
    simp [outer, outerTail,
      SelectedMergePaddedEmitterParsedInnerOuterSuffixBits, houterStage]
  let b0 : List (Option Bool) :=
    SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft
  let b1 : List (Option Bool) :=
    List.append
      (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits.reverse.map
        some)
      b0
  let b2 : List (Option Bool) :=
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
      (p.L.input.map some) b1
  let b3 : List (Option Bool) :=
    List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        p.L.stage).reverse.map some)
      b2
  let b4 : List (Option Bool) :=
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
      p.L.acceptConfig b3
  let b5 : List (Option Bool) :=
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
      p.L.rejectConfig b4
  let b6 : List (Option Bool) :=
    List.append
      ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
        (some p.L.acceptHit)).reverse.map some)
      b5
  let b7 : List (Option Bool) :=
    List.append
      ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
        (some p.L.rejectHit)).reverse.map some)
      b6
  let Ttransition : Tape Bool :=
    (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderHandoffConfigWithBaseAndRight
      b0 (false :: inputFieldTail) [none, none]).tape
  have htransition :
      CanonicalLayouts.DovetailLayoutScanner.TransitionRemainderPrefixScannerDescription.HaltsFromTape
        (nestedLayoutRestorerContextTape b0
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
              p.L)
            outer))
        Ttransition := by
    rw [nestedLayoutRestorerContextTape, hbody, hinputField']
    simpa [Ttransition, List.map_append, List.append_assoc] using
        (nestedLayoutRestorerTransitionRemainderPrefixScanner_haltsFrom_context
          b0 false inputFieldTail [none, none])
  have htransitionMove :
      Tape.move Direction.right Ttransition =
        DovetailInitialLayoutInitializer.tapeAtCells b1
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
              p.L.input afterInput).map some)
            [none, none]) := by
    simpa [Ttransition, b1, hinputField'] using
      (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderHandoffConfigWithBaseAndRight_move_right
        b0 false inputFieldTail [none, none])
  let Tinput : Tape Bool :=
    (CanonicalLayouts.DovetailLayoutScanner.boolWordCanonicalHandoffConfigWithBaseAndRight
      p.L.input b1 (false :: inputSuffixTail) [none, none]).tape
  have hinput :
      CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b1
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
              p.L.input afterInput).map some)
            [none, none]))
        Tinput := by
    simpa [Tinput, hafterInput] using
      (nestedLayoutRestorerBoolWordSuffixScanner_haltsFrom_context
        p.L.input b1 inputSuffixTail [none, none])
  have hinputMove :
      Tape.move Direction.right Tinput =
        DovetailInitialLayoutInitializer.tapeAtCells b2
          (List.append (afterInput.map some) [none, none]) := by
    simpa [Tinput, b2, hafterInput,
      CanonicalLayouts.DovetailLayoutScanner.boolWordCanonicalHandoffConfigWithBaseAndRight]
      using
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight_move_right
          (p.L.input.map some) b1 false inputSuffixTail [none, none])
  let Tstage : Tape Bool :=
    (CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight
      p.L.stage b2 (false :: acceptFieldTail) [none, none]).tape
  have hstage :
      CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b2
          (List.append (afterInput.map some) [none, none]))
        Tstage := by
    simpa [Tstage, afterInput, hafterStage] using
      (nestedLayoutRestorerNonemptyNatSuffixScanner_haltsFrom_context
        p.L.stage b2 acceptFieldTail [none, none])
  have hstageMove :
      Tape.move Direction.right Tstage =
        DovetailInitialLayoutInitializer.tapeAtCells b3
          (List.append (afterStage.map some) [none, none]) := by
    simpa [Tstage, b3, hafterStage] using
      (CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight_move_right
        p.L.stage b2 false acceptFieldTail [none, none])
  let TacceptConfig : Tape Bool :=
    (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight
      p.L.acceptConfig.tape.right
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
          p.L.acceptConfig.tape.head).reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          p.L.acceptConfig.tape.left
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.L.acceptConfig.state).reverse.map some)
            b3)))
      (false :: rejectFieldTail) [none, none]).tape
  have hacceptConfig :
      CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b3
          (List.append (afterStage.map some) [none, none]))
        TacceptConfig := by
    simpa [TacceptConfig, afterStage, hafterAcceptConfig] using
      (nestedLayoutRestorerConfigurationSuffixScanner_haltsFrom_context
        p.L.acceptConfig b3 rejectFieldTail [none, none])
  have hacceptConfigMove :
      Tape.move Direction.right TacceptConfig =
        DovetailInitialLayoutInitializer.tapeAtCells b4
          (List.append (afterAcceptConfig.map some) [none, none]) := by
    simpa [TacceptConfig, b4, hafterAcceptConfig,
      CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase]
      using
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight_move_right
          p.L.acceptConfig.tape.right
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
              p.L.acceptConfig.tape.head).reverse.map some)
            (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
              p.L.acceptConfig.tape.left
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  p.L.acceptConfig.state).reverse.map some)
                b3)))
          false rejectFieldTail [none, none])
  let TrejectConfig : Tape Bool :=
    (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight
      p.L.rejectConfig.tape.right
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
          p.L.rejectConfig.tape.head).reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          p.L.rejectConfig.tape.left
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.L.rejectConfig.state).reverse.map some)
            b4)))
      (false :: acceptHitTail) [none, none]).tape
  have hrejectConfig :
      CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b4
          (List.append (afterAcceptConfig.map some) [none, none]))
        TrejectConfig := by
    simpa [TrejectConfig, afterAcceptConfig, hafterRejectConfig] using
      (nestedLayoutRestorerConfigurationSuffixScanner_haltsFrom_context
        p.L.rejectConfig b4 acceptHitTail [none, none])
  have hrejectConfigMove :
      Tape.move Direction.right TrejectConfig =
        DovetailInitialLayoutInitializer.tapeAtCells b5
          (List.append (afterRejectConfig.map some) [none, none]) := by
    simpa [TrejectConfig, b5, hafterRejectConfig,
      CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase]
      using
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight_move_right
          p.L.rejectConfig.tape.right
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
              p.L.rejectConfig.tape.head).reverse.map some)
            (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
              p.L.rejectConfig.tape.left
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  p.L.rejectConfig.state).reverse.map some)
                b4)))
          false acceptHitTail [none, none])
  let TacceptHit : Tape Bool :=
    (CanonicalLayouts.DovetailLayoutScanner.boolOnlySuffixHandoffConfigWithBaseAndRight
      p.L.acceptHit b5 (false :: rejectHitTail) [none, none]).tape
  have hacceptHit :
      CanonicalLayouts.DovetailLayoutScanner.BoolSuffixScannerDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b5
          (List.append (afterRejectConfig.map some) [none, none]))
        TacceptHit := by
    simpa [TacceptHit, afterRejectConfig, hafterAcceptHit] using
      (nestedLayoutRestorerBoolSuffixScanner_haltsFrom_context
        p.L.acceptHit b5 false rejectHitTail [none, none])
  have hacceptHitMove :
      Tape.move Direction.right TacceptHit =
        DovetailInitialLayoutInitializer.tapeAtCells b6
          (List.append (afterAcceptHit.map some) [none, none]) := by
    simpa [TacceptHit, b6, hafterAcceptHit] using
      (CanonicalLayouts.DovetailLayoutScanner.boolOnlySuffixHandoffConfigWithBaseAndRight_move_right
        p.L.acceptHit b5 false rejectHitTail [none, none])
  let TrejectHit : Tape Bool :=
    (CanonicalLayouts.DovetailLayoutScanner.boolOnlySuffixHandoffConfigWithBaseAndRight
      p.L.rejectHit b6 (false :: outerTail) [none, none]).tape
  have hrejectHit :
      CanonicalLayouts.DovetailLayoutScanner.BoolSuffixScannerDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b6
          (List.append (afterAcceptHit.map some) [none, none]))
        TrejectHit := by
    simpa [TrejectHit, afterAcceptHit, houter] using
      (nestedLayoutRestorerBoolSuffixScanner_haltsFrom_context
        p.L.rejectHit b6 false outerTail [none, none])
  have hrejectHitMove :
      Tape.move Direction.right TrejectHit =
        nestedLayoutRestorerContextTape b7 outer := by
    simpa [TrejectHit, b7, houter,
      nestedLayoutRestorerContextTape] using
      (CanonicalLayouts.DovetailLayoutScanner.boolOnlySuffixHandoffConfigWithBaseAndRight_move_right
        p.L.rejectHit b6 false outerTail [none, none])
  let Tfinal : Tape Bool :=
    DovetailInitialLayoutInitializer.tapeAtCells
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
          (some p.S.hit)).reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          p.S.config
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.S.stage).reverse.map some)
            b7)))
      [none, none]
  have houterFinish :
      nestedLayoutOuterFinishDescription.HaltsFromTape
        (nestedLayoutRestorerContextTape b7 outer)
        Tfinal := by
    simpa [outer, Tfinal,
      SelectedMergePaddedEmitterParsedInnerOuterSuffixBits] using
      (nestedLayoutOuterFinishDescription_haltsFrom_context
        p.S.stage p.S.config p.S.hit b7)
  have hfinal :
      Tfinal =
        SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p := by
    simp [Tfinal, b7, b6, b5, b4, b3, b2, b1, b0,
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape,
      SelectedMergePaddedEmitterNestedLayoutParsedLeft,
      CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase,
      SelectedMergePaddedEmitterOuterHitSuffixBits,
      SelectedMergePaddedEmitterOuterHitSuffixCode,
      CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
      CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase,
      encodeCodeWordAsInput, List.map_reverse]
  have hflagsRun :
      nestedLayoutContextFinalFlagsDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b5
          (List.append (afterRejectConfig.map some) [none, none]))
        TrejectHit := by
    unfold nestedLayoutContextFinalFlagsDescription
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CanonicalLayouts.DovetailLayoutScanner.boolSuffixScannerDescription_subroutineReady
        CanonicalLayouts.DovetailLayoutScanner.boolSuffixScannerDescription_subroutineReady
        hacceptHit hacceptHitMove hrejectHit
  have hrejectAndFlagsRun :
      nestedLayoutContextRejectAndFlagsDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b4
          (List.append (afterAcceptConfig.map some) [none, none]))
        TrejectHit := by
    unfold nestedLayoutContextRejectAndFlagsDescription
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CanonicalLayouts.DovetailLayoutScanner.configurationSuffixScannerDescription_subroutineReady
        nestedLayoutContextFinalFlagsDescription_subroutineReady
        hrejectConfig hrejectConfigMove hflagsRun
  have hconfigurationsRun :
      nestedLayoutContextConfigurationsAndFlagsDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b3
          (List.append (afterStage.map some) [none, none]))
        TrejectHit := by
    unfold nestedLayoutContextConfigurationsAndFlagsDescription
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CanonicalLayouts.DovetailLayoutScanner.configurationSuffixScannerDescription_subroutineReady
        nestedLayoutContextRejectAndFlagsDescription_subroutineReady
        hacceptConfig hacceptConfigMove hrejectAndFlagsRun
  have hstageAndFieldsRun :
      nestedLayoutContextStageAndFieldsDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b2
          (List.append (afterInput.map some) [none, none]))
        TrejectHit := by
    unfold nestedLayoutContextStageAndFieldsDescription
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        nestedLayoutContextConfigurationsAndFlagsDescription_subroutineReady
        hstage hstageMove hconfigurationsRun
  have hinputAndFieldsRun :
      nestedLayoutContextInputAndFieldsDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells b1
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
              p.L.input afterInput).map some)
            [none, none]))
        TrejectHit := by
    unfold nestedLayoutContextInputAndFieldsDescription
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CanonicalLayouts.DovetailLayoutScanner.boolWordSuffixScannerDescription_subroutineReady
        nestedLayoutContextStageAndFieldsDescription_subroutineReady
        hinput hinputMove hstageAndFieldsRun
  have hbodyRun :
      nestedLayoutContextBodyDescription.HaltsFromTape
        (nestedLayoutRestorerContextTape b0
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
              p.L)
            outer))
        TrejectHit := by
    unfold nestedLayoutContextBodyDescription
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CanonicalLayouts.DovetailLayoutScanner.transitionRemainderPrefixScannerDescription_subroutineReady
        nestedLayoutContextInputAndFieldsDescription_subroutineReady
        htransition htransitionMove hinputAndFieldsRun
  have hrun :
      nestedLayoutBodyAndOuterFinishDescription.HaltsFromTape
        (nestedLayoutRestorerContextTape b0
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
              p.L)
            outer))
        Tfinal := by
    unfold nestedLayoutBodyAndOuterFinishDescription
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        nestedLayoutContextBodyDescription_subroutineReady
        nestedLayoutOuterFinishDescription_subroutineReady
        hbodyRun hrejectHitMove houterFinish
  rw [hfinal] at hrun
  simpa [b0, outer] using hrun
theorem nestedLayoutRestorerDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    nestedLayoutRestorerDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells []
        ((SelectedMergePaddedEmitterParsedInnerSourceBits p).map some))
      (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) := by
  have hsourceBits :
      SelectedMergePaddedEmitterParsedInnerSourceBits p =
        false :: false :: false :: true ::
          SelectedMergePaddedEmitterParsedInnerSourceTailBits p := by
    simp [SelectedMergePaddedEmitterParsedInnerSourceBits,
      encodeCodeSymbolAsInput]
  let Tpadded : Tape Bool :=
    DovetailInitialLayoutInitializer.tapeAtCells [none, none]
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerSourceBits p).map some)
        [none, none])
  have hpadding :
      nestedLayoutPaddingRewindDescription.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells []
          ((SelectedMergePaddedEmitterParsedInnerSourceBits p).map some))
        Tpadded := by
    simpa [Tpadded, hsourceBits] using
        (nestedLayoutPaddingRewindDescription_haltsFromTape
          false
          (false :: false :: true ::
            SelectedMergePaddedEmitterParsedInnerSourceTailBits p))
  let tailCells : List (Option Bool) :=
    List.append
      ((SelectedMergePaddedEmitterParsedInnerSourceTailBits p).map some)
      [none, none]
  let Tshaped : Tape Bool :=
    DovetailInitialLayoutInitializer.tapeAtCells
      (List.append ([false, false, false, true].reverse.map some) [none])
      (none :: tailCells)
  have hshaper :
      nestedLayoutOuterTransitionShaperDescription.HaltsFromTape
        Tpadded Tshaped := by
    simpa [Tpadded, Tshaped, tailCells, hsourceBits] using
      (nestedLayoutOuterTransitionShaperDescription_haltsFromTape
        tailCells)
  have hshaperMove :
      Tape.move Direction.right Tshaped =
        nestedLayoutRestorerContextTape
          SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
              p.L)
            (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)) := by
    simpa [Tshaped, tailCells, nestedLayoutRestorerContextTape,
      SelectedMergePaddedEmitterParsedInnerSourceTailBits,
      List.map_append, List.append_assoc] using
        (nestedLayoutOuterTransitionShaperDescription_target_move_right
          tailCells)
  have hbody :=
    nestedLayoutBodyAndOuterFinishDescription_haltsFrom p
  have hcore :
      nestedLayoutRestorerCoreDescription.HaltsFromTape
        Tpadded
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) := by
    unfold nestedLayoutRestorerCoreDescription
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        nestedLayoutOuterTransitionShaperDescription_subroutineReady
        nestedLayoutBodyAndOuterFinishDescription_subroutineReady
        hshaper hshaperMove hbody
  have hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tpadded) =
        Tpadded := by
    simp [Tpadded, hsourceBits,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  unfold nestedLayoutRestorerDescription
  exact
    CommonGround.FiniteTransducers.canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      nestedLayoutPaddingRewindDescription_subroutineReady
      nestedLayoutRestorerCoreDescription_subroutineReady
      hpadding hbridge hcore
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
