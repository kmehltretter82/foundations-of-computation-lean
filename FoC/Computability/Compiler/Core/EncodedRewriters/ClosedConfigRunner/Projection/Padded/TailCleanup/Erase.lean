import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.Hit

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

def eraseRightBoolFieldAfterCurrentDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 1 (some false) none Direction.right 2
    , transition 1 (some true) none Direction.right 2
    , transition 2 (some false) none Direction.right 3
    , transition 2 (some true) none Direction.right 3
    , transition 3 (some false) none Direction.right 4
    , transition 3 (some true) none Direction.right 4
    , transition 4 (some false) none Direction.right 5
    , transition 4 (some true) none Direction.right 5 ]

theorem eraseRightBoolFieldAfterCurrentDescription_wellFormed :
    eraseRightBoolFieldAfterCurrentDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := eraseRightBoolFieldAfterCurrentDescription.transitions)
      (stateCount :=
        eraseRightBoolFieldAfterCurrentDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := eraseRightBoolFieldAfterCurrentDescription.transitions)
      (by decide)

theorem eraseRightBoolFieldAfterCurrentDescription_haltTransitionFree :
    eraseRightBoolFieldAfterCurrentDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := eraseRightBoolFieldAfterCurrentDescription.transitions)
    (state := eraseRightBoolFieldAfterCurrentDescription.halt)
    (by decide)

theorem eraseRightBoolFieldAfterCurrentDescription_subroutineReady :
    eraseRightBoolFieldAfterCurrentDescription.SubroutineReady :=
  ⟨eraseRightBoolFieldAfterCurrentDescription_wellFormed,
    eraseRightBoolFieldAfterCurrentDescription_haltTransitionFree⟩

theorem eraseRightBoolFieldAfterCurrentDescription_run
    (current b0 b1 b2 b3 : Bool)
    (left right : List (Option Bool)) :
    eraseRightBoolFieldAfterCurrentDescription.runConfig 5
        { state := eraseRightBoolFieldAfterCurrentDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left
              (some current :: some b0 :: some b1 ::
                some b2 :: some b3 :: right) } =
      { state := eraseRightBoolFieldAfterCurrentDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append (List.replicate 4 (none : Option Bool))
              (some current :: left))
            right } := by
  cases current <;> cases b0 <;> cases b1 <;> cases b2 <;>
    cases b3 <;> cases right <;>
    simp [eraseRightBoolFieldAfterCurrentDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

def eraseLeftBoolFieldBeforeCurrentDescription : MachineDescription where
  stateCount := 9
  start := 0
  halt := 8
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4
    , transition 4 (some false) none Direction.left 5
    , transition 4 (some true) none Direction.left 5
    , transition 5 (some false) none Direction.left 6
    , transition 5 (some true) none Direction.left 6
    , transition 6 (some false) none Direction.left 7
    , transition 6 (some true) none Direction.left 7
    , transition 7 (some false) none Direction.left 8
    , transition 7 (some true) none Direction.left 8 ]

theorem eraseLeftBoolFieldBeforeCurrentDescription_wellFormed :
    eraseLeftBoolFieldBeforeCurrentDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := eraseLeftBoolFieldBeforeCurrentDescription.transitions)
      (stateCount :=
        eraseLeftBoolFieldBeforeCurrentDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := eraseLeftBoolFieldBeforeCurrentDescription.transitions)
      (by decide)

theorem eraseLeftBoolFieldBeforeCurrentDescription_haltTransitionFree :
    eraseLeftBoolFieldBeforeCurrentDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := eraseLeftBoolFieldBeforeCurrentDescription.transitions)
    (state := eraseLeftBoolFieldBeforeCurrentDescription.halt)
    (by decide)

theorem eraseLeftBoolFieldBeforeCurrentDescription_subroutineReady :
    eraseLeftBoolFieldBeforeCurrentDescription.SubroutineReady :=
  ⟨eraseLeftBoolFieldBeforeCurrentDescription_wellFormed,
    eraseLeftBoolFieldBeforeCurrentDescription_haltTransitionFree⟩

def skipCurrentAndFourBlankPaddingLeftDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 2 none none Direction.left 3
    , transition 3 none none Direction.left 4
    , transition 4 none none Direction.left 5 ]

theorem skipCurrentAndFourBlankPaddingLeftDescription_wellFormed :
    skipCurrentAndFourBlankPaddingLeftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := skipCurrentAndFourBlankPaddingLeftDescription.transitions)
      (stateCount :=
        skipCurrentAndFourBlankPaddingLeftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := skipCurrentAndFourBlankPaddingLeftDescription.transitions)
      (by decide)

theorem skipCurrentAndFourBlankPaddingLeftDescription_haltTransitionFree :
    skipCurrentAndFourBlankPaddingLeftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := skipCurrentAndFourBlankPaddingLeftDescription.transitions)
    (state := skipCurrentAndFourBlankPaddingLeftDescription.halt)
    (by decide)

theorem skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady :
    skipCurrentAndFourBlankPaddingLeftDescription.SubroutineReady :=
  ⟨skipCurrentAndFourBlankPaddingLeftDescription_wellFormed,
    skipCurrentAndFourBlankPaddingLeftDescription_haltTransitionFree⟩

theorem skipCurrentAndFourBlankPaddingLeftDescription_run
    (current : Bool) (left right : List (Option Bool)) :
    skipCurrentAndFourBlankPaddingLeftDescription.runConfig 5
        { state := skipCurrentAndFourBlankPaddingLeftDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (none :: none :: none :: none ::
                some current :: left)
              (none :: right) } =
      { state := skipCurrentAndFourBlankPaddingLeftDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            left
            (some current :: none :: none :: none :: none ::
              none :: right) } := by
  cases current <;>
    simp [skipCurrentAndFourBlankPaddingLeftDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem skipCurrentAndFourBlankPaddingLeftDescription_haltsFromTape
    (current : Bool) (left right : List (Option Bool)) :
    skipCurrentAndFourBlankPaddingLeftDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells
        (none :: none :: none :: none :: some current :: left)
        (none :: right))
      (DovetailInitialLayoutInitializer.tapeAtCells
        left
        (some current :: none :: none :: none :: none ::
          none :: right)) := by
  refine ⟨5, ?_⟩
  constructor <;>
    rw [skipCurrentAndFourBlankPaddingLeftDescription_run]

def skipCurrentAndFourBlankPaddingRightDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right 3
    , transition 3 none none Direction.right 4
    , transition 4 none none Direction.right 5 ]

theorem skipCurrentAndFourBlankPaddingRightDescription_wellFormed :
    skipCurrentAndFourBlankPaddingRightDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := skipCurrentAndFourBlankPaddingRightDescription.transitions)
      (stateCount :=
        skipCurrentAndFourBlankPaddingRightDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := skipCurrentAndFourBlankPaddingRightDescription.transitions)
      (by decide)

theorem skipCurrentAndFourBlankPaddingRightDescription_haltTransitionFree :
    skipCurrentAndFourBlankPaddingRightDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := skipCurrentAndFourBlankPaddingRightDescription.transitions)
    (state := skipCurrentAndFourBlankPaddingRightDescription.halt)
    (by decide)

theorem skipCurrentAndFourBlankPaddingRightDescription_subroutineReady :
    skipCurrentAndFourBlankPaddingRightDescription.SubroutineReady :=
  ⟨skipCurrentAndFourBlankPaddingRightDescription_wellFormed,
    skipCurrentAndFourBlankPaddingRightDescription_haltTransitionFree⟩

theorem skipCurrentAndFourBlankPaddingRightDescription_run
    (current target : Bool) (left right : List (Option Bool)) :
    skipCurrentAndFourBlankPaddingRightDescription.runConfig 5
        { state := skipCurrentAndFourBlankPaddingRightDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left
              (some current :: none :: none :: none :: none ::
                some target :: right) } =
      { state := skipCurrentAndFourBlankPaddingRightDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (none :: none :: none :: none :: some current :: left)
            (some target :: right) } := by
  cases current <;> cases target <;>
    simp [skipCurrentAndFourBlankPaddingRightDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem skipCurrentAndFourBlankPaddingRightDescription_haltsFromTape
    (current target : Bool) (left right : List (Option Bool)) :
    skipCurrentAndFourBlankPaddingRightDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells
        left
        (some current :: none :: none :: none :: none ::
          some target :: right))
      (DovetailInitialLayoutInitializer.tapeAtCells
        (none :: none :: none :: none :: some current :: left)
        (some target :: right)) := by
  refine ⟨5, ?_⟩
  constructor <;>
    rw [skipCurrentAndFourBlankPaddingRightDescription_run]

def selectedHitOtherFlagErasedTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    DovetailInitialLayoutInitializer.tapeAtCells
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit []).reverse.map some)
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig []).reverse.map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).reverse.map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  L.stage).reverse.map some)
                (List.append
                  ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                    some)
                  [none]))))))
      [none]
  else
    Tape.move Direction.left
      (DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig []).reverse.map some)
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig []).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage).reverse.map some)
              (List.append
                ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                  some)
                [none]))))
        (List.append (List.replicate 4 (none : Option Bool))
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit []).map some)
            [none])))

def selectedHitOtherFlagErasedAcceptLeftRev
    (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 4 (none : Option Bool))
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.acceptHit []).reverse.map some)
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig []).reverse.map some)
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig []).reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).reverse.map some)
            (List.append
              ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                some)
              [none])))))

def selectedHitOtherFlagErasedAcceptHitHead
    (hit : Bool) : Bool :=
  if hit then false else true

def selectedHitOtherFlagErasedAcceptHitRestLeftRev
    (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (if L.acceptHit then
      [some true, some true, some false]
    else
      [some false, some true, some false])
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        L.rejectConfig []).reverse.map some)
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.acceptConfig []).reverse.map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).reverse.map some)
          (List.append
            ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
              some)
            [none]))))

def selectedHitOtherFlagErasedAcceptAfterPaddingTape
    (L : DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (selectedHitOtherFlagErasedAcceptHitRestLeftRev L)
    (some (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit) ::
      none :: none :: none :: none :: none :: [none])

theorem selectedHitOtherFlagErasedAcceptLeftRev_eq_hitHead
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedAcceptLeftRev L =
      none :: none :: none :: none ::
        some (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit) ::
          selectedHitOtherFlagErasedAcceptHitRestLeftRev L := by
  by_cases haccept : L.acceptHit <;>
    simp [selectedHitOtherFlagErasedAcceptLeftRev,
      selectedHitOtherFlagErasedAcceptHitHead,
      selectedHitOtherFlagErasedAcceptHitRestLeftRev,
      haccept,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]

def selectedHitOtherFlagErasedRejectBaseLeftRev
    (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.rejectConfig []).reverse.map some)
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        L.acceptConfig []).reverse.map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).reverse.map some)
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)
          [none])))

def selectedHitOtherFlagErasedRejectBaseCells
    (L : DovetailLayout) : List (Option Bool) :=
  none :: none :: none :: none ::
    List.append
      ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.rejectHit []).map some)
      [none]

theorem selectedHitOtherFlagErasedRejectBaseLeftRev_cons
    (L : DovetailLayout) :
    exists current : Bool,
    exists rest : List (Option Bool),
      selectedHitOtherFlagErasedRejectBaseLeftRev L =
        some current :: rest := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig [] with
    ⟨tail, htail⟩
  cases hrev : tail.reverse with
  | nil =>
      refine
        ⟨false,
          List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig []).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage).reverse.map some)
              (List.append
                ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                  some)
                [none])), ?_⟩
      simp [selectedHitOtherFlagErasedRejectBaseLeftRev, htail, hrev]
  | cons bit rest =>
      refine
        ⟨bit,
          List.append (rest.map some)
            (List.append [some false]
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.acceptConfig []).reverse.map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    L.stage).reverse.map some)
                  (List.append
                    ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                      some)
                    [none])))), ?_⟩
      simp [selectedHitOtherFlagErasedRejectBaseLeftRev, htail,
        hrev, List.map_append, List.append_assoc]

theorem selectedHitOtherFlagErasedRejectBaseCells_eq_hitHead
    (L : DovetailLayout) :
    exists hitTail : Word Bool,
      selectedHitOtherFlagErasedRejectBaseCells L =
        none :: none :: none :: none ::
          some false :: List.append (hitTail.map some) [none] := by
  by_cases hreject : L.rejectHit
  · refine ⟨[true, true, false], ?_⟩
    simp [selectedHitOtherFlagErasedRejectBaseCells, hreject,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  · refine ⟨[true, false, true], ?_⟩
    simp [selectedHitOtherFlagErasedRejectBaseCells, hreject,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem selectedHitOtherFlagErasedTape_true_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput (selectedHitOtherFlagErasedTape true L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.acceptHit [])))) := by
  simp [selectedHitOtherFlagErasedTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, List.filterMap_append,
    Function.comp_def, List.reverse_append,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.append_assoc]

theorem tapeAtCells_move_left_append_none_normalizedOutput
    (leftRev right : List (Option Bool)) :
    Tape.normalizedOutput
        (Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            (List.append leftRev [none]) right)) =
      Tape.normalizedOutput
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append leftRev [none]) right) := by
  cases leftRev <;>
    cases right <;>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.normalizedOutput, Tape.cells, Tape.move, Tape.moveLeft]

theorem tapeAtCells_move_left_right_left_append_none_cons_cells
    (leftRev : List (Option Bool)) (head next : Option Bool)
    (right : List (Option Bool)) :
    Tape.cells
        (Tape.move Direction.left
          (Tape.move Direction.right
            (Tape.move Direction.left
              (DovetailInitialLayoutInitializer.tapeAtCells
                (List.append leftRev [none]) (head :: next :: right))))) =
      List.append [none]
        (List.append leftRev.reverse (head :: next :: right)) := by
  cases leftRev <;>
    simp [DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.cells, Tape.move, Tape.moveLeft, Tape.moveRight,
      List.reverse_append, List.append_assoc]

theorem tapeAtCells_move_left_right_left_cons_cons
    (leftRev : List (Option Bool)) (head next : Option Bool)
    (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells
              leftRev (head :: next :: right)))) =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          leftRev (head :: next :: right)) := by
  cases leftRev <;>
    simp [DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem selectedHitOtherFlagErasedTape_true_eq_tapeAtCells
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedTape true L =
      DovetailInitialLayoutInitializer.tapeAtCells
        (selectedHitOtherFlagErasedAcceptLeftRev L)
        [none] := by
  simp [selectedHitOtherFlagErasedTape,
    selectedHitOtherFlagErasedAcceptLeftRev]

theorem selectedHitOtherFlagErasedTape_false_eq_moveLeft_tapeAtCells
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedTape false L =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (selectedHitOtherFlagErasedRejectBaseLeftRev L)
          (selectedHitOtherFlagErasedRejectBaseCells L)) := by
  simp [selectedHitOtherFlagErasedTape,
    selectedHitOtherFlagErasedRejectBaseLeftRev,
    selectedHitOtherFlagErasedRejectBaseCells]

theorem selectedHitOtherFlagErasedTape_false_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput (selectedHitOtherFlagErasedTape false L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))) := by
  rw [show
      selectedHitOtherFlagErasedTape false L =
        Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            (List.append
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).reverse.map some)
                (List.append
                  ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                    L.acceptConfig []).reverse.map some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      L.stage).reverse.map some)
                    ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                      some))))
              [none])
            (List.append (List.replicate 4 (none : Option Bool))
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                  L.rejectHit []).map some)
                [none]))) by
    simp [selectedHitOtherFlagErasedTape, List.append_assoc]]
  rw [tapeAtCells_move_left_append_none_normalizedOutput]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, List.filterMap_append,
    Function.comp_def, List.reverse_append,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.append_assoc]

theorem selectedProjectionPaddedTarget_true_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape true L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit []))) := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput_eq_tail]
  rw [SelectedProjectionTailProjector.outputAllBits,
    SelectedProjectionTailProjector.outputBits_true_eq_fields]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil]

theorem selectedProjectionPaddedTarget_false_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape false L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit []))) := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput_eq_tail]
  rw [SelectedProjectionTailProjector.outputAllBits,
    SelectedProjectionTailProjector.outputBits_false_eq_fields]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil]

def selectedProjectionPaddedTailCleanupTargetBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit [])))
  else
    List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig [])
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.rejectHit [])))

def selectedProjectionPaddedTailCleanupPrefixBits
    (L : DovetailLayout) : Word Bool :=
  List.append (SelectedProjectionTailProjector.outputPrefixBits L)
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)

def selectedProjectionPaddedTailCleanupSelectedConfigBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.acceptConfig []
  else
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.rejectConfig []

def selectedProjectionPaddedTailCleanupUnselectedConfigBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.rejectConfig []
  else
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.acceptConfig []

def selectedProjectionPaddedTailCleanupSelectedHitBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.acceptHit []
  else
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.rejectHit []

def selectedProjectionPaddedTailCleanupKeptPrefixBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
      (selectedProjectionPaddedTailCleanupSelectedConfigBits true L)
  else
    selectedProjectionPaddedTailCleanupPrefixBits L

def selectedProjectionPaddedTailCleanupKeptSuffixBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupSelectedHitBits true L
  else
    List.append
      (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
      (selectedProjectionPaddedTailCleanupSelectedHitBits false L)

def selectedProjectionPaddedTailCleanupPostPaddingSourceBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
      (List.append
        (selectedProjectionPaddedTailCleanupSelectedConfigBits true L)
        (List.append
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits true L)))
  else
    List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
      (List.append
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L)
        (List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits false L)))

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true_eq_selected_unselected
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits true L)
          (List.append
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits true L))) := by
  rfl

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false_eq_unselected_selected
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L)
          (List.append
            (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits false L))) := by
  rfl

theorem selectedProjectionPaddedTailCleanupTargetBits_eq_kept
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupTargetBits useAccept L =
      List.append
        (selectedProjectionPaddedTailCleanupKeptPrefixBits useAccept L)
        (selectedProjectionPaddedTailCleanupKeptSuffixBits useAccept L) := by
  cases useAccept <;>
    simp [selectedProjectionPaddedTailCleanupTargetBits,
      selectedProjectionPaddedTailCleanupKeptPrefixBits,
      selectedProjectionPaddedTailCleanupKeptSuffixBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      List.append_assoc]

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_eq_deleteBlock
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits useAccept L =
      List.append
        (selectedProjectionPaddedTailCleanupKeptPrefixBits useAccept L)
        (List.append
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            useAccept L)
          (selectedProjectionPaddedTailCleanupKeptSuffixBits
            useAccept L)) := by
  cases useAccept <;>
    simp [selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
      selectedProjectionPaddedTailCleanupKeptPrefixBits,
      selectedProjectionPaddedTailCleanupKeptSuffixBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      List.append_assoc]

theorem selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupTargetBits useAccept L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits useAccept L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits useAccept L)) := by
  cases useAccept <;>
    simp [selectedProjectionPaddedTailCleanupTargetBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      List.append_assoc]

theorem selectedProjectionPaddedTailCleanupTargetBits_eq_outputCode
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupTargetBits useAccept L =
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L) := by
  rw [selectedProjectionOutputBits_eq_tailProjector_outputAllBits]
  cases useAccept <;>
    simp [selectedProjectionPaddedTailCleanupTargetBits,
      SelectedProjectionTailProjector.outputAllBits,
      SelectedProjectionTailProjector.outputBits_true_eq_fields,
      SelectedProjectionTailProjector.outputBits_false_eq_fields]
  all_goals
    conv =>
      rhs
      rw [← CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil]
    rfl

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit []))) := by
  simp [selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
    selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit []))) := by
  simp [selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
    selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupTargetBits_eq_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      selectedProjectionPaddedTailCleanupTargetBits useAccept L := by
  cases useAccept
  · simpa [selectedProjectionPaddedTailCleanupTargetBits] using
      selectedProjectionPaddedTarget_false_normalizedOutput L
  · simpa [selectedProjectionPaddedTailCleanupTargetBits] using
      selectedProjectionPaddedTarget_true_normalizedOutput L

theorem selectedProjectionPaddedTailCleanupTargetTape_normalizedOutput_eq_selectedFields
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits
            useAccept L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits
            useAccept L)) := by
  rw [selectedProjectionPaddedTailCleanupTargetBits_eq_normalizedOutput]
  rw [selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields]

theorem selectedProjectionPaddedTailCleanupTargetTape_normalizedOutput_eq_kept
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      List.append
        (selectedProjectionPaddedTailCleanupKeptPrefixBits useAccept L)
        (selectedProjectionPaddedTailCleanupKeptSuffixBits useAccept L) := by
  rw [selectedProjectionPaddedTailCleanupTargetBits_eq_normalizedOutput]
  rw [selectedProjectionPaddedTailCleanupTargetBits_eq_kept]

theorem selectedProjectionPaddedTailCleanupTargetTape_normalizedOutput_eq_outputCode
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L) := by
  rw [selectedProjectionPaddedTailCleanupTargetBits_eq_normalizedOutput,
    selectedProjectionPaddedTailCleanupTargetBits_eq_outputCode]

theorem selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      List.append
        ((selectedProjectionPaddedTailCleanupTargetBits useAccept L).map
          some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  cases useAccept
  · simpa [selectedProjectionPaddedTailCleanupTargetBits,
      List.map_append, List.append_assoc] using
      SelectedProjectionEquivEmitterPaddedOutputTape_false_cells L
  · simpa [selectedProjectionPaddedTailCleanupTargetBits,
      List.map_append, List.append_assoc] using
      SelectedProjectionEquivEmitterPaddedOutputTape_true_cells L

theorem selectedProjectionPaddedTailCleanupTargetTape_cells_eq_selectedFields
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      List.append
        ((List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
          (List.append
            (selectedProjectionPaddedTailCleanupSelectedConfigBits
              useAccept L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits
              useAccept L))).map some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  rw [selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits,
    selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields]

theorem selectedProjectionPaddedTailCleanupTargetTape_cells_eq_kept
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      List.append
        ((List.append
          (selectedProjectionPaddedTailCleanupKeptPrefixBits useAccept L)
          (selectedProjectionPaddedTailCleanupKeptSuffixBits useAccept L)).map
          some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  rw [selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits,
    selectedProjectionPaddedTailCleanupTargetBits_eq_kept]

theorem selectedProjectionPaddedTailCleanupTargetTape_cells_eq_outputCode
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      List.append
        ((encodeCodeWordAsInput
          (SelectedProjectionOutputCode useAccept L)).map some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  rw [selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits,
    selectedProjectionPaddedTailCleanupTargetBits_eq_outputCode]

theorem selectedProjectionPaddedTailCleanupTargetTape_true_cells_eq_fields
    (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape true L) =
      List.append
        ((List.append (SelectedProjectionTailProjector.outputPrefixBits L)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage)
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.acceptHit [])))).map some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  simpa [selectedProjectionPaddedTailCleanupTargetBits,
    List.map_append, List.append_assoc] using
    selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits true L

theorem selectedProjectionPaddedTailCleanupTargetTape_false_cells_eq_fields
    (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape false L) =
      List.append
        ((List.append (SelectedProjectionTailProjector.outputPrefixBits L)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage)
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))).map some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  simpa [selectedProjectionPaddedTailCleanupTargetBits,
    List.map_append, List.append_assoc] using
    selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits false L


end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
