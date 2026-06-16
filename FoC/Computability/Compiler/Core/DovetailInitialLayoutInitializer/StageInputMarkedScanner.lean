import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputValidator

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer
namespace StageInputMarkedScanner

def keep (source : Nat) (read : Bool) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source (some read) (some read)
    Direction.right target

def keepMove (source : Nat) (read : Option Bool)
    (move : Direction) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source read read move target

def writeMove (source : Nat) (read write : Option Bool)
    (move : Direction) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source read write move target

def scanLeftToSentinelRestart
    (scan checkLeft restoreMarker : Nat) :
    List TransitionDescription :=
  [ keepMove scan (some false) Direction.left scan
  , keepMove scan (some true) Direction.left scan
  , keepMove scan none Direction.left checkLeft
  , keepMove checkLeft (some true) Direction.right restoreMarker
  , writeMove restoreMarker none (some false) Direction.right 100
  ]

def scanLeftToSentinelHalt (scan : Nat) :
    List TransitionDescription :=
  [ keepMove scan (some false) Direction.left scan
  , keepMove scan (some true) Direction.left scan
  , keepMove scan none Direction.right 999
  ]

def StageInputMarkedScannerDescription :
    MachineDescription where
  stateCount := 1000
  start := 0
  halt := 999
  transitions :=
    [ keepMove 0 (some true) Direction.left 1
    , keepMove 1 none Direction.left 100

    , keep 100 false 101
    , keep 101 false 102
    , keepMove 101 none Direction.right 102
    , keep 102 true 103
    , writeMove 103 (some false) none Direction.right 120
    , keep 103 true 150
    , keepMove 103 none Direction.right 100

    , keep 120 false 121
    , keep 121 false 122
    , keep 122 true 123
    , keep 123 false 120
    , keep 123 true 130
    , keepMove 123 none Direction.right 120

    , keep 130 false 131
    , keepMove 130 (some true) Direction.right 135
    , keepMove 131 (some true) Direction.left 132
    , writeMove 132 (some false) (some true) Direction.right 133
    , keep 133 true 134
    , keep 134 false 139
    , keep 134 true 145
    , keepMove 139 (some true) Direction.left 140
    , keepMove 145 (some false) Direction.left 140
    , keep 135 true 136
    , keep 136 false 137
    , keep 136 true 138
    , keep 137 true 130
    , keep 138 false 130

    , writeMove 150 (some true) (some false) Direction.right 152
    , keep 150 false 151
    , writeMove 151 (some false) none Direction.left 160
    , keep 152 true 153
    , keep 153 false 154
    , keep 153 true 155
    , keep 154 true 150
    , keep 155 false 150

    , keepMove 160 (some false) Direction.left 160
    , keepMove 160 (some true) Direction.left 160
    , keepMove 160 none Direction.left 161
    , keepMove 161 (some true) Direction.right 164
    , keepMove 161 (some false) Direction.right 170
    , writeMove 164 none (some false) Direction.left 160
    , keepMove 170 none Direction.right 180

    , keepMove 180 (some false) Direction.right 180
    , keepMove 180 (some true) Direction.right 180
    , writeMove 180 none (some false) Direction.left 200
    , keep 200 false 201
    , keep 201 false 202
    , keep 202 true 203
    , keep 203 false 200
    , keepMove 203 (some true) Direction.right 210
    , keepMove 210 none Direction.left 220
    ]
      ++ scanLeftToSentinelRestart 140 141 142
      ++ scanLeftToSentinelHalt 220

theorem stageInputMarkedScannerDescription_wellFormed :
    StageInputMarkedScannerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := StageInputMarkedScannerDescription.transitions)
      (stateCount := StageInputMarkedScannerDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := StageInputMarkedScannerDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem stageInputMarkedScannerDescription_haltTransitionFree :
    StageInputMarkedScannerDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := StageInputMarkedScannerDescription.transitions)
    (state := StageInputMarkedScannerDescription.halt)
    (by
      native_decide) t ht

theorem stageInputMarkedScannerDescription_subroutineReady :
    StageInputMarkedScannerDescription.SubroutineReady :=
  ⟨stageInputMarkedScannerDescription_wellFormed,
    stageInputMarkedScannerDescription_haltTransitionFree⟩

theorem stageInputMarkedScannerDescription_spec :
    StageInputMarkedScannerSpec StageInputMarkedScannerDescription := by
  constructor
  · exact stageInputMarkedScannerDescription_subroutineReady
  constructor
  · intro w stage
    refine
      ⟨30 + 36 * w.length + 8 * w.length * (w.length + 1) +
        8 * stage, ?_⟩
    induction w generalizing stage with
    | nil =>
        induction stage with
        | zero =>
            native_decide
        | succ stage ih =>
            sorry
    | cons b rest ih =>
        sorry
  · intro code Tmark T hmark hscanner
    sorry

end StageInputMarkedScanner

export StageInputMarkedScanner
  (StageInputMarkedScannerDescription
   stageInputMarkedScannerDescription_subroutineReady
   stageInputMarkedScannerDescription_spec)

end DovetailInitialLayoutInitializer
end Computability
end FoC
