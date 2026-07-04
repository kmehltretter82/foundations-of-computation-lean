import FoC.Computability.MachineDescriptionDebug
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips

set_option doc.verso true

/-!
# Machine-description debugger examples

This module regression-tests the opt-in debugger against
{name (full := FoC.Computability.CommonGround.FiniteTransducers.rightMoveAcrossFourBitsDescription)}`rightMoveAcrossFourBitsDescription`,
a small finite transducer whose exact run theorem is already proved in
{module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

private abbrev DebugTestMachine : MachineDescription :=
  rightMoveAcrossFourBitsDescription

private def debugTestSourceTape : Tape Bool :=
  tapeAtCells [none]
    ([some false, some true, some false, some true, none] :
      List (Option Bool))

private def debugTestSourceConfig : Configuration where
  state := DebugTestMachine.start
  tape := debugTestSourceTape

private def debugTestStuckConfig : Configuration where
  state := DebugTestMachine.start
  tape := tapeAtCells [none] [none]

private def debugTestTargetTape : Tape Bool :=
  tapeAtCells
    ([some true, some false, some true, some false, none] :
      List (Option Bool))
    [none]

private def debugTestTargetConfig : Configuration where
  state := DebugTestMachine.halt
  tape := debugTestTargetTape

private theorem debugTest_machine_run_matches_proven_target :
    DebugTestMachine.runConfig 4 debugTestSourceConfig =
      debugTestTargetConfig := by
  simpa [DebugTestMachine, debugTestSourceConfig, debugTestSourceTape,
    debugTestTargetConfig, debugTestTargetTape] using
    rightMoveAcrossFourBitsDescription_run
      false true false true [none] [none]

private theorem debugTrace_rightMoveAcrossFourBits :
    DebugTestMachine.debugTrace 10 debugTestSourceConfig =
      [ { step := 0
          before :=
            { state := 0
              tape :=
                { left := [none]
                  head := some false
                  right := [some true, some false, some true, none] } }
          read := some false
          transition :=
            some
              { source := 0
                read := some false
                write := some false
                move := DirectionDebugView.right
                target := 1 }
          after :=
            { state := 1
              tape :=
                { left := [some false, none]
                  head := some true
                  right := [some false, some true, none] } } }
      , { step := 1
          before :=
            { state := 1
              tape :=
                { left := [some false, none]
                  head := some true
                  right := [some false, some true, none] } }
          read := some true
          transition :=
            some
              { source := 1
                read := some true
                write := some true
                move := DirectionDebugView.right
                target := 2 }
          after :=
            { state := 2
              tape :=
                { left := [some true, some false, none]
                  head := some false
                  right := [some true, none] } } }
      , { step := 2
          before :=
            { state := 2
              tape :=
                { left := [some true, some false, none]
                  head := some false
                  right := [some true, none] } }
          read := some false
          transition :=
            some
              { source := 2
                read := some false
                write := some false
                move := DirectionDebugView.right
                target := 3 }
          after :=
            { state := 3
              tape :=
                { left := [some false, some true, some false, none]
                  head := some true
                  right := [none] } } }
      , { step := 3
          before :=
            { state := 3
              tape :=
                { left := [some false, some true, some false, none]
                  head := some true
                  right := [none] } }
          read := some true
          transition :=
            some
              { source := 3
                read := some true
                write := some true
                move := DirectionDebugView.right
                target := 4 }
          after :=
            { state := 4
              tape :=
                { left :=
                    [some true, some false, some true, some false,
                      none]
                  head := none
                  right := [] } } } ] := by
  decide

private theorem debugRunFinal_rightMoveAcrossFourBits :
    DebugTestMachine.debugRunFinal 4 debugTestSourceConfig =
      debugTestTargetConfig.debugView := by
  decide

private theorem compareConfigExact_accepts_proven_target :
    compareConfigExact
        (DebugTestMachine.runConfig 4 debugTestSourceConfig)
        debugTestTargetConfig =
      none := by
  rw [debugTest_machine_run_matches_proven_target]
  decide

private theorem compareTapeExact_reports_left_mismatch :
    compareTapeExact
        { left := [some true, none]
          head := some false
          right := [none] }
        { left := [some true]
          head := some false
          right := [none] } =
      some
        (TapeMismatch.leftMismatch [some true, none] [some true]) := by
  decide

private theorem compareTapeExact_reports_head_mismatch :
    compareTapeExact
        { left := [some true]
          head := some false
          right := [none] }
        { left := [some true]
          head := some true
          right := [none] } =
      some
        (TapeMismatch.headMismatch (some false) (some true)) := by
  decide

private theorem compareTapeExact_reports_right_mismatch :
    compareTapeExact
        { left := [some true]
          head := some false
          right := [none, some true] }
        { left := [some true]
          head := some false
          right := [none] } =
      some
        (TapeMismatch.rightMismatch [none, some true] [none]) := by
  decide

private theorem compareTapeEquiv_ignores_trailing_blanks :
    compareTapeEquiv
        { left := [some true, none, none]
          head := some false
          right := [some true, none, none] }
        { left := [some true]
          head := some false
          right := [some true] } =
      none := by
  decide

private theorem compareTapeEquiv_keeps_real_content_mismatch :
    compareTapeEquiv
        { left := [some true, none]
          head := some false
          right := [some true, none] }
        { left := [some false]
          head := some false
          right := [some true] } =
      some
        (TapeMismatch.leftMismatch [some true] [some false]) := by
  decide

private theorem debugTrace_stuck_row :
    DebugTestMachine.debugTrace 10 debugTestStuckConfig =
      [ { step := 0
          before :=
            { state := 0
              tape :=
                { left := [none]
                  head := none
                  right := [] } }
          read := none
          transition := none
          after :=
            { state := 0
              tape :=
                { left := [none]
                  head := none
                  right := [] } } } ] := by
  decide

private theorem debugTraceRange_selects_middle_steps :
    (DebugTestMachine.debugTraceRange 10 debugTestSourceConfig 1 3).map
        (fun row => row.step) =
      [1, 2] := by
  decide

private theorem debugTraceFrom_selects_suffix_steps :
    (DebugTestMachine.debugTraceFrom 10 debugTestSourceConfig 2).map
        (fun row => row.step) =
      [2, 3] := by
  decide

private theorem debugFirstBreakpoint_state :
    (DebugTestMachine.debugFirstBreakpoint 10 debugTestSourceConfig
        (breakOnState 2)).map
        (fun hit => (hit.step, hit.config.state)) =
      some (2, 2) := by
  decide

private theorem debugTraceUntilBreakpoint_state :
    (DebugTestMachine.debugTraceUntilBreakpoint 10 debugTestSourceConfig
        (breakOnState 2)).map
        (fun row => row.step) =
      [0, 1, 2] := by
  decide

private theorem debugTraceAroundBreakpoint_state :
    (DebugTestMachine.debugTraceAroundBreakpoint 10 debugTestSourceConfig
        (breakOnState 2) 1).map
        (fun row => row.step) =
      [1, 2, 3] := by
  decide

private theorem debugFirstBreakpoint_read :
    (DebugTestMachine.debugFirstBreakpoint 10 debugTestSourceConfig
        (breakOnRead (some false))).map
        (fun hit => (hit.step, hit.config.state)) =
      some (0, 0) := by
  decide

private theorem debugFirstBreakpoint_transition_key :
    (DebugTestMachine.debugFirstBreakpoint 10 debugTestSourceConfig
        (breakOnTransitionKey 1 (some true))).map
        (fun hit => (hit.step, hit.config.state)) =
      some (1, 1) := by
  decide

private theorem debugFirstBreakpoint_halt :
    (DebugTestMachine.debugFirstBreakpoint 10 debugTestSourceConfig
        (breakOnHalt DebugTestMachine)).map
        (fun hit => (hit.step, hit.config.state)) =
      some (4, DebugTestMachine.halt) := by
  decide

private theorem debugTraceUntilBreakpoint_halt_stops_at_last_row :
    (DebugTestMachine.debugTraceUntilBreakpoint 10 debugTestSourceConfig
        (breakOnHalt DebugTestMachine)).map
        (fun row => row.step) =
      [0, 1, 2, 3] := by
  decide

private theorem debugFirstBreakpoint_stuck :
    (DebugTestMachine.debugFirstBreakpoint 10 debugTestStuckConfig
        (breakOnStuck DebugTestMachine)).map
        (fun hit => (hit.step, hit.config.state)) =
      some (0, DebugTestMachine.start) := by
  decide

private theorem debugFirstExpectationFailure_accepts_target_step :
    DebugTestMachine.debugFirstExpectationFailure 4 debugTestSourceConfig
        [ { step := 4
            expectedState? := some DebugTestMachine.halt
            expectedTape? := some debugTestTargetTape } ] =
      none := by
  rw [show
      DebugTestMachine.debugFirstExpectationFailure 4 debugTestSourceConfig
          [ { step := 4
              expectedState? := some DebugTestMachine.halt
              expectedTape? := some debugTestTargetTape } ] =
        DebugTestMachine.debugFirstFailure 4 debugTestSourceConfig
          (checkStepExpectations
            [ { step := 4
                expectedState? := some DebugTestMachine.halt
                expectedTape? := some debugTestTargetTape } ]) by
    rfl]
  decide

private theorem debugFirstExpectationFailure_reports_first_bad_step :
    (DebugTestMachine.debugFirstExpectationFailure 4 debugTestSourceConfig
        [ { step := 2
            expectedState? := some 99
            expectedTape? := none } ]).map
        (fun failure => (failure.step, failure.config)) =
      some
        (2,
          { state := 2
            tape :=
              { left := [some true, some false, none]
                head := some false
                right := [some true, none] } }) := by
  decide

private theorem debugTraceAroundFirstExpectationFailure_bad_state :
    (DebugTestMachine.debugTraceAroundFirstExpectationFailure 4
        debugTestSourceConfig
        [ { step := 2
            expectedState? := some 99
            expectedTape? := none } ]
        1).map
        (fun row => row.step) =
      [1, 2, 3] := by
  decide

private theorem debugWatchpointHits_state_changed :
    (DebugTestMachine.debugWatchpointHits 10 debugTestSourceConfig
        watchStateChanged).map
        (fun hit => hit.step) =
      [0, 1, 2, 3] := by
  decide

private theorem debugWatchpointHits_head_changed :
    (DebugTestMachine.debugWatchpointHits 10 debugTestSourceConfig
        watchHeadChanged).map
        (fun hit => hit.step) =
      [0, 1, 2, 3] := by
  decide

private theorem debugWatchpointHits_left_nonblank_changed :
    (DebugTestMachine.debugWatchpointHits 10 debugTestSourceConfig
        watchLeftNonblankChanged).map
        (fun hit => hit.step) =
      [0, 1, 2, 3] := by
  decide

private theorem debugWatchpointHits_right_nonblank_changed :
    (DebugTestMachine.debugWatchpointHits 10 debugTestSourceConfig
        watchRightNonblankChanged).map
        (fun hit => hit.step) =
      [0, 1, 2] := by
  decide

private theorem debugWatchpointHits_normalized_output_unchanged :
    (DebugTestMachine.debugWatchpointHits 10 debugTestSourceConfig
        watchNormalizedOutputChanged).map
        (fun hit => hit.step) =
      [] := by
  decide

private theorem tapeSummary_debugTestSourceTape :
    tapeSummary 2 debugTestSourceTape =
      { leftLength := 1
        leftPrefix := [none]
        head := some false
        rightPrefix := [some true, some false]
        rightLength := 4
        outputPrefix := [false, true]
        outputLength := 4 } := by
  decide

end FiniteTransducers
end CommonGround

end Computability
end FoC
