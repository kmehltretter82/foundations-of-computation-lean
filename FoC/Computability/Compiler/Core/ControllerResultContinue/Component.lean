import FoC.Computability.Compiler.Core.ControllerResultContinue.StageInputContinue

set_option doc.verso true

/-!
# Controller Result Continue Component

This module packages the guard/projection prefix with the physical continuation
that runs from the projection machine's final tape shape.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace ControllerResultContinueConstruction

def ProjectionTailRewindDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition
        0 none none Direction.left 0
    , transition
        0 (some false) (some false) Direction.left 1
    , transition
        0 (some true) (some true) Direction.left 1
    , transition
        1 (some false) (some false) Direction.left 1
    , transition
        1 (some true) (some true) Direction.left 1
    , transition
        1 none none Direction.right 2
    ]

theorem projectionTailRewindDescription_wellFormed :
    ProjectionTailRewindDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ProjectionTailRewindDescription.transitions)
      (stateCount := ProjectionTailRewindDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ProjectionTailRewindDescription.transitions)
      (by native_decide)

theorem projectionTailRewindDescription_haltTransitionFree :
    ProjectionTailRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ProjectionTailRewindDescription.transitions)
    (state := ProjectionTailRewindDescription.halt)
    (by native_decide)

theorem projectionTailRewindDescription_subroutineReady :
    ProjectionTailRewindDescription.SubroutineReady :=
  ⟨projectionTailRewindDescription_wellFormed,
    projectionTailRewindDescription_haltTransitionFree⟩

def StageInputContinueBoundaryRewriterDescription : MachineDescription :=
  { StageInputContinueCheckedRewriterDescription with start := 1 }

theorem stageInputContinueBoundaryRewriterDescription_wellFormed :
    StageInputContinueBoundaryRewriterDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := StageInputContinueBoundaryRewriterDescription.transitions)
      (stateCount := StageInputContinueBoundaryRewriterDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := StageInputContinueBoundaryRewriterDescription.transitions)
      (by native_decide)

theorem stageInputContinueBoundaryRewriterDescription_haltTransitionFree :
    StageInputContinueBoundaryRewriterDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := StageInputContinueBoundaryRewriterDescription.transitions)
    (state := StageInputContinueBoundaryRewriterDescription.halt)
    (by native_decide)

theorem stageInputContinueBoundaryRewriterDescription_subroutineReady :
    StageInputContinueBoundaryRewriterDescription.SubroutineReady :=
  ⟨stageInputContinueBoundaryRewriterDescription_wellFormed,
    stageInputContinueBoundaryRewriterDescription_haltTransitionFree⟩

def ProjectedStageInputContinueDescription : MachineDescription :=
  seqSubroutine
    ProjectionTailRewindDescription
    StageInputContinueBoundaryRewriterDescription
    Direction.left

theorem projectedStageInputContinueDescription_subroutineReady :
    ProjectedStageInputContinueDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    projectionTailRewindDescription_subroutineReady
    stageInputContinueBoundaryRewriterDescription_subroutineReady

theorem stageInputContinueBoundaryRewriterDescription_run_header
    (right : List (Option Bool)) :
    StageInputContinueBoundaryRewriterDescription.runConfig 4
        { state := StageInputContinueBoundaryRewriterDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (none :: right) } =
      { state := 5
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [some false]
            (List.append
              [some false, some false, some false] right) } := by
  simp [StageInputContinueBoundaryRewriterDescription,
    StageInputContinueCheckedRewriterDescription,
    DovetailInitialLayoutInitializer.tapeAtCells,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem stageInputContinueBoundaryRewriterDescription_run_scan_nonempty
    (leftRev : List (Option Bool)) (b : Bool)
    (rest : List (Option Bool)) :
    StageInputContinueBoundaryRewriterDescription.runConfig 1
        { state := 5
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev
              (some b :: rest) } =
      { state := 5
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (some b :: leftRev) rest } := by
  cases b <;> cases rest <;>
    simp [StageInputContinueBoundaryRewriterDescription,
      StageInputContinueCheckedRewriterDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem stageInputContinueBoundaryRewriterDescription_run_scan
    (leftRev : List (Option Bool)) (bits : Word Bool) :
    StageInputContinueBoundaryRewriterDescription.runConfig bits.length
        { state := 5
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev
              (List.append (bits.map some) [none]) } =
      { state := 5
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append (bits.reverse.map some) leftRev) [none] } := by
  induction bits generalizing leftRev with
  | nil =>
      simp [runConfig]
  | cons b rest ih =>
      rw [show (b :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        StageInputContinueBoundaryRewriterDescription.runConfig rest.length
            (StageInputContinueBoundaryRewriterDescription.runConfig 1
              { state := 5
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells leftRev
                    (some b :: List.append (rest.map some) [none]) }) =
          { state := 5
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (List.append ((b :: rest).reverse.map some) leftRev)
                [none] }
      rw [stageInputContinueBoundaryRewriterDescription_run_scan_nonempty]
      rw [ih]
      simp [List.append_assoc]

theorem stageInputContinueBoundaryRewriterDescription_run_to_last_bit
    (leftRev : List (Option Bool)) (lastBit : Bool) :
    StageInputContinueBoundaryRewriterDescription.runConfig 1
        { state := 5
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (some lastBit :: leftRev) [none] } =
      { state := 6
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells leftRev
            [some lastBit, none] } := by
  cases lastBit <;>
    simp [StageInputContinueBoundaryRewriterDescription,
      StageInputContinueCheckedRewriterDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem stageInputContinueBoundaryRewriterDescription_run_rewrite_last
    (leftRev : List (Option Bool)) (lastBit : Bool) :
    StageInputContinueBoundaryRewriterDescription.runConfig 1
        { state := 6
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev
              [some lastBit, none] } =
      { state := 7
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (some false :: leftRev) [none] } := by
  cases lastBit <;>
    simp [StageInputContinueBoundaryRewriterDescription,
      StageInputContinueCheckedRewriterDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem stageInputContinueBoundaryRewriterDescription_run_append_done_done
    (leftRev : List (Option Bool)) :
    StageInputContinueBoundaryRewriterDescription.runConfig 8
        { state := 7
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev [none] } =
      { state := StageInputContinueBoundaryRewriterDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append
              (stageInputContinueDoneDoneBits.reverse.map some) leftRev)
            [none] } := by
  simp [StageInputContinueBoundaryRewriterDescription,
    StageInputContinueCheckedRewriterDescription,
    stageInputContinueDoneDoneBits,
    encodeCodeWordAsInput,
    encodeCodeSymbolAsInput,
    DovetailInitialLayoutInitializer.tapeAtCells,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move,
    Tape.moveRight]

theorem stageInputContinueBoundaryRewriterDescription_haltsFromTape_prefixBits
    (prefixBits : Word Bool) :
    StageInputContinueBoundaryRewriterDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells []
        (none ::
          List.append
            ((List.append prefixBits stageInputContinueDoneBits).map some)
            [none]))
      (stageInputContinueOutputTape
        (stageInputContinueBitsOutputFromPrefix prefixBits)) := by
  let inputBits := List.append prefixBits stageInputContinueDoneBits
  let scanBits := List.append [false, false, false] inputBits
  let outputBits := stageInputContinueBitsOutputFromPrefix prefixBits
  let leftAfterLast : List (Option Bool) :=
    List.map some
      (List.append [true, false, false]
        (List.append prefixBits.reverse
          [false, false, false, false]))
  refine ⟨4 + scanBits.length + 10, ?_⟩
  have hrun :
      StageInputContinueBoundaryRewriterDescription.runConfig
          (4 + scanBits.length + 10)
          { state := StageInputContinueBoundaryRewriterDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells []
                (none ::
                  List.append
                    ((List.append prefixBits
                        stageInputContinueDoneBits).map some)
                    [none]) } =
        { state := StageInputContinueBoundaryRewriterDescription.halt
          tape := stageInputContinueOutputTape outputBits } := by
    rw [show 4 + scanBits.length + 10 =
        4 + (scanBits.length + 10) by omega]
    rw [runConfig_add]
    have hheader :
        StageInputContinueBoundaryRewriterDescription.runConfig 4
            { state := StageInputContinueBoundaryRewriterDescription.start
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells []
                  (none :: List.append (inputBits.map some) [none]) } =
          { state := 5
            tape := stageInputContinueHeaderPrefixedTape inputBits } := by
      simpa [stageInputContinueHeaderPrefixedTape, List.append_assoc]
        using
          stageInputContinueBoundaryRewriterDescription_run_header
            (List.append (inputBits.map some) [none])
    rw [hheader]
    rw [show scanBits.length + 10 =
        scanBits.length + (1 + (1 + 8)) by omega]
    rw [runConfig_add]
    have hscan :
        StageInputContinueBoundaryRewriterDescription.runConfig
            scanBits.length
            { state := 5
              tape := stageInputContinueHeaderPrefixedTape inputBits } =
          { state := 5
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (List.append (scanBits.reverse.map some) [some false])
                [none] } := by
      have htape :
          stageInputContinueHeaderPrefixedTape inputBits =
            DovetailInitialLayoutInitializer.tapeAtCells [some false]
              (List.append (scanBits.map some) [none]) := by
        simp [stageInputContinueHeaderPrefixedTape, scanBits]
      rw [htape]
      simpa [List.append_assoc] using
        stageInputContinueBoundaryRewriterDescription_run_scan
          [some false] scanBits
    rw [hscan]
    have hleft :
        List.append (scanBits.reverse.map some) [some false] =
          some true :: leftAfterLast := by
      simp [scanBits, inputBits, leftAfterLast,
        stageInputContinueDoneBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
    rw [hleft]
    rw [runConfig_add]
    have hlast :
      StageInputContinueBoundaryRewriterDescription.runConfig 1
            { state := 5
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (some true :: leftAfterLast) [none] } =
          { state := 6
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                leftAfterLast [some true, none] } := by
      exact
        stageInputContinueBoundaryRewriterDescription_run_to_last_bit
          leftAfterLast true
    rw [hlast]
    rw [runConfig_add]
    have hrewrite :
      StageInputContinueBoundaryRewriterDescription.runConfig 1
            { state := 6
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  leftAfterLast [some true, none] } =
          { state := 7
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (some false :: leftAfterLast) [none] } := by
      exact
        stageInputContinueBoundaryRewriterDescription_run_rewrite_last
          leftAfterLast true
    rw [hrewrite]
    have happend :
      StageInputContinueBoundaryRewriterDescription.runConfig 8
            { state := 7
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (some false :: leftAfterLast) [none] } =
          { state := StageInputContinueBoundaryRewriterDescription.halt
            tape := stageInputContinueOutputTape outputBits } := by
      have hbase :=
        stageInputContinueBoundaryRewriterDescription_run_append_done_done
          (some false :: leftAfterLast)
      simpa [stageInputContinueOutputTape, outputBits,
        stageInputContinueBitsOutputFromPrefix, leftAfterLast,
        stageInputContinueHeaderBits, stageInputContinueTickBits,
        stageInputContinueDoneDoneBits,
        encodeCodeSymbolAsInput,
        encodeCodeWordAsInput,
        List.reverse_append, List.map_append, List.append_assoc] using hbase
    exact happend
  constructor
  · exact
      (by
        simpa [inputBits, outputBits] using
          congrArg Configuration.state hrun)
  · exact
      (by
        simpa [inputBits, outputBits] using
          congrArg Configuration.tape hrun)

theorem dropTrailingNone_replicate_none_bool
    (n : Nat) :
    Tape.dropTrailingNone
        (List.replicate n (none : Option Bool)) = [] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate_succ, Tape.dropTrailingNone, ih]

theorem dropTrailingNone_append_replicate_none_bool
    (xs : List (Option Bool)) (n : Nat) :
    Tape.dropTrailingNone
        (List.append xs (List.replicate n none)) =
      Tape.dropTrailingNone xs := by
  induction xs with
  | nil =>
      exact dropTrailingNone_replicate_none_bool n
  | cons cell rest ih =>
      change
        Tape.dropTrailingNone
            (cell :: List.append rest (List.replicate n none)) =
          Tape.dropTrailingNone (cell :: rest)
      rw [Tape.dropTrailingNone_cons, Tape.dropTrailingNone_cons, ih]

theorem none_cons_replicate_none_append_none
    (n : Nat) :
    none ::
        List.append (List.replicate n (none : Option Bool)) [none] =
      List.replicate (n + 2) none := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        none :: none ::
            List.append (List.replicate n (none : Option Bool)) [none] =
          List.replicate (n + 1 + 2) none
      rw [show n + 1 + 2 = (n + 2) + 1 by omega]
      rw [List.replicate_succ]
      exact congrArg (fun xs => none :: xs) ih

theorem dropTrailingNone_append_boundary_blanks
    (xs : List (Option Bool)) (n : Nat) :
    Tape.dropTrailingNone
        (List.append xs
          (none ::
            List.append (List.replicate n none) [none])) =
      Tape.dropTrailingNone xs := by
  rw [none_cons_replicate_none_append_none]
  exact dropTrailingNone_append_replicate_none_bool xs (n + 2)

theorem stageInputContinueBoundaryPaddedTape_equiv
    (prefixBits : Word Bool) (trail : Nat) :
    Tape.Equiv
      (DovetailInitialLayoutInitializer.tapeAtCells
        ([none, none, none] : List (Option Bool))
        (none ::
          List.append
            ((List.append prefixBits stageInputContinueDoneBits).map some)
            (none ::
              List.append (List.replicate trail none) [none])))
      (DovetailInitialLayoutInitializer.tapeAtCells []
        (none ::
          List.append
            ((List.append prefixBits stageInputContinueDoneBits).map some)
            [none])) := by
  constructor
  · simp [DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.dropTrailingNone]
  · constructor
    · simp [DovetailInitialLayoutInitializer.tapeAtCells]
    · simp [DovetailInitialLayoutInitializer.tapeAtCells,
        List.append_assoc]
      let base : List (Option Bool) :=
        List.append (List.map some prefixBits)
          (List.map some stageInputContinueDoneBits)
      have hactual :
          Tape.dropTrailingNone
              (List.append base
                (none ::
                  List.append (List.replicate trail none) [none])) =
            Tape.dropTrailingNone base :=
        dropTrailingNone_append_boundary_blanks base trail
      have hcanon :
          Tape.dropTrailingNone (List.append base [none]) =
            Tape.dropTrailingNone base := by
        rw [show [none] = List.replicate 1 (none : Option Bool) by rfl]
        exact dropTrailingNone_append_replicate_none_bool base 1
      exact
        (by
          simpa [base, List.append_assoc] using
            hactual.trans hcanon.symm)

theorem tapeAtCells_move_left_of_cells_ne_nil
    (leftCell : Option Bool) (leftRev cells : List (Option Bool))
    (hcells : cells ≠ []) :
    Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (leftCell :: leftRev) cells) =
      DovetailInitialLayoutInitializer.tapeAtCells
        leftRev (leftCell :: cells) := by
  cases cells with
  | nil =>
      contradiction
  | cons cell rest =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft]

def stageInputContinueStagePrefixBits
    (input : Word Bool) (stage : Nat) : Word Bool :=
  encodeCodeWordAsInput
    (stageInputContinueStagePrefix input stage)

def projectionStageInputBitsLeftRev
    (input : Word Bool) (stage : Nat) : Word Bool :=
  List.append [true, false, false]
    (stageInputContinueStagePrefixBits input stage).reverse

theorem projectionStageInputBitsLeftRev_payload_cells
    (input : Word Bool) (stage : Nat) :
    List.append
        ((projectionStageInputBitsLeftRev input stage).reverse.map some)
        [some true] =
      (List.append
        (stageInputContinueStagePrefixBits input stage)
        stageInputContinueDoneBits).map some := by
  simp [projectionStageInputBitsLeftRev,
    stageInputContinueDoneBits,
    encodeCodeSymbolAsInput,
    List.map_append, List.append_assoc]

theorem projectionStageInputBitsLeftRev_payload_cells_mapped
    (input : Word Bool) (stage : Nat) :
    List.append
        ((projectionStageInputBitsLeftRev input stage).map some).reverse
        [some true] =
      (List.append
        (stageInputContinueStagePrefixBits input stage)
        stageInputContinueDoneBits).map some := by
  simpa [List.map_reverse] using
    projectionStageInputBitsLeftRev_payload_cells input stage

theorem stageInputContinueStagePrefixBits_map_reverse
    (input : Word Bool) (stage : Nat) :
    (List.map some
        (stageInputContinueStagePrefixBits input stage)).reverse =
      List.append
        (List.map some
          (encodeCodeWordAsInput
            (List.replicate stage MachineCodeSymbol.tick))).reverse
        (List.map some
          (encodeCodeWordAsInput
            (encodeBoolWord input))).reverse := by
  unfold stageInputContinueStagePrefixBits stageInputContinueStagePrefix
  rw [encodeCodeWordAsInput_encodeBoolWordAppend]
  simp [encodeBoolWord, List.map_append,
    List.reverse_append]

theorem replicate_none_succ_append
    (n : Nat) (tail : List (Option Bool)) :
    List.append (List.replicate (n + 1) none) tail =
      none :: List.append (List.replicate n none) tail := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate_succ]

theorem replicate_none_append_replicate
    (m n : Nat) (tail : List (Option Bool)) :
    List.append (List.replicate m none)
        (List.append (List.replicate n none) tail) =
      List.append (List.replicate (m + n) none) tail := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.replicate_succ]
      rw [show (m + 1) + n = (m + n) + 1 by omega]
      rw [List.replicate_succ]
      exact congrArg (fun xs => none :: xs) ih

theorem projectionFinalTape_move_left_eq_tailBlock
    (input result : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (ControllerStageInputProjection.finalTape
          { input := input, stage := stage, result := result }) =
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append (List.replicate (8 * result.length + 4) none)
          (some true ::
            List.append
              ((projectionStageInputBitsLeftRev input stage).map some)
              ([none, none, none, none] : List (Option Bool))))
        [none, none] := by
  let outputRev : List (Option Bool) :=
    some true ::
      List.append
        ((projectionStageInputBitsLeftRev input stage).map some)
        ([none, none, none, none] : List (Option Bool))
  let tail : List (Option Bool) :=
    List.append ([none, none, none, none] : List (Option Bool))
      (List.append (List.replicate (4 * result.length) none)
        outputRev)
  have hlead :
      List.append
          (List.replicate (4 * result.length + 1) none) tail =
        none :: List.append
          (List.replicate (4 * result.length) none) tail := by
    exact replicate_none_succ_append (4 * result.length) tail
  have hblank :
      List.append (List.replicate (4 * result.length) none) tail =
        List.append (List.replicate (8 * result.length + 4) none)
          outputRev := by
    unfold tail
    change
      List.append (List.replicate (4 * result.length) none)
          (List.append (List.replicate 4 none)
            (List.append (List.replicate (4 * result.length) none)
              outputRev)) =
        List.append (List.replicate (8 * result.length + 4) none)
          outputRev
    rw [replicate_none_append_replicate]
    rw [replicate_none_append_replicate]
    have hnat :
        4 * result.length + 4 + 4 * result.length =
          8 * result.length + 4 := by
      omega
    rw [hnat]
  have htape :
      ControllerStageInputProjection.finalTape
          { input := input, stage := stage, result := result } =
      ControllerStageInputProjection.projectionTapeAtCells
          (List.append (List.replicate (4 * result.length + 1) none)
            tail) [] := by
    simp [ControllerStageInputProjection.finalTape,
      ControllerStageInputProjection.finalLeftRev,
      ControllerStageInputProjection.finalInputLeftRev,
      tail, outputRev,
      projectionStageInputBitsLeftRev,
      stageInputContinueStagePrefixBits_map_reverse,
      ControllerStageInputProjection.projectionCodeCells,
      ControllerStageInputProjection.projectionDoneCodeCells,
      ControllerStageInputProjection.projectionStageTickCellsRev,
      encodeCodeSymbolAsInput]
  rw [htape]
  rw [hlead]
  simp [ControllerStageInputProjection.projectionTapeAtCells,
    Tape.move, Tape.moveLeft, DovetailInitialLayoutInitializer.tapeAtCells]
  exact hblank

theorem projectionTailRewindDescription_run_blank
    (leftRev right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig 1
        { state := ProjectionTailRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (none :: leftRev) (none :: right) } =
      { state := ProjectionTailRewindDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            leftRev (none :: none :: right) } := by
  simp [ProjectionTailRewindDescription,
    DovetailInitialLayoutInitializer.tapeAtCells,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft]

theorem projectionTailRewindDescription_run_blank_to_cell
    (leftCell : Option Bool) (leftRev right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig 1
        { state := ProjectionTailRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftCell :: leftRev) (none :: right) } =
      { state := ProjectionTailRewindDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            leftRev (leftCell :: none :: right) } := by
  cases leftCell <;>
    simp [ProjectionTailRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem projectionTailRewindDescription_run_state0_bit
    (leftCell : Option Bool) (bit : Bool)
    (leftRev right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig 1
        { state := ProjectionTailRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftCell :: leftRev) (some bit :: right) } =
      { state := 1
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            leftRev (leftCell :: some bit :: right) } := by
  cases leftCell <;> cases bit <;>
    simp [ProjectionTailRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem projectionTailRewindDescription_run_scan_bit
    (leftCell : Option Bool) (bit : Bool)
    (leftRev right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig 1
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftCell :: leftRev) (some bit :: right) } =
      { state := 1
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            leftRev (leftCell :: some bit :: right) } := by
  cases leftCell <;> cases bit <;>
    simp [ProjectionTailRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem projectionTailRewindDescription_run_finish
    (leftRev right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig 1
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              leftRev (none :: right) } =
      { state := ProjectionTailRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (none :: leftRev) right } := by
  cases right <;>
    simp [ProjectionTailRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem projectionTailRewindDescription_run_blanks
    (n : Nat) (leftRev right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig n
        { state := ProjectionTailRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (List.replicate n none) leftRev)
              (none :: right) } =
      { state := ProjectionTailRewindDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            leftRev
            (List.append (List.replicate (n + 1) none) right) } := by
  induction n generalizing right with
  | zero =>
      simp [runConfig]
  | succ n ih =>
      rw [show (n + 1) = 1 + n by omega]
      rw [runConfig_add]
      change
        ProjectionTailRewindDescription.runConfig n
            (ProjectionTailRewindDescription.runConfig 1
              { state := ProjectionTailRewindDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (List.append (List.replicate (1 + n) none) leftRev)
                    (none :: right) }) =
          { state := ProjectionTailRewindDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                leftRev
                (List.append (List.replicate (1 + n + 1) none) right) }
      have hrep :
          List.append (List.replicate (1 + n) none) leftRev =
            none :: List.append (List.replicate n none) leftRev := by
        simpa [show 1 + n = n + 1 by omega] using
          replicate_none_succ_append n leftRev
      rw [hrep]
      rw [projectionTailRewindDescription_run_blank]
      rw [ih]
      rw [show 1 + n + 1 = n + 1 + 1 by omega]
      simp [List.replicate_succ', List.append_assoc]

theorem projectionTailRewindDescription_run_scan_to_first_bit
    (bitsLeftRev : Word Bool) (headBit : Bool)
    (prefixLeft right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig
        (bitsLeftRev.length + 2)
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (bitsLeftRev.map some)
                (none :: prefixLeft))
              (some headBit :: right) } =
      { state := ProjectionTailRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (none :: prefixLeft)
            (List.append (bitsLeftRev.reverse.map some)
              (some headBit :: right)) } := by
  induction bitsLeftRev generalizing headBit right with
  | nil =>
      simp only [List.length_nil, List.map_nil, List.reverse_nil]
      rw [show 0 + 2 = 1 + 1 by omega]
      rw [runConfig_add]
      change
        ProjectionTailRewindDescription.runConfig 1
            (ProjectionTailRewindDescription.runConfig 1
              { state := 1
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (none :: prefixLeft) (some headBit :: right) }) =
          { state := ProjectionTailRewindDescription.halt
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (none :: prefixLeft) (some headBit :: right) }
      rw [projectionTailRewindDescription_run_scan_bit]
      exact projectionTailRewindDescription_run_finish
        prefixLeft (some headBit :: right)
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        omega]
      rw [runConfig_add]
      change
        ProjectionTailRewindDescription.runConfig
            (rest.length + 2)
            (ProjectionTailRewindDescription.runConfig 1
              { state := 1
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (some bit ::
                      List.append (rest.map some)
                        (none :: prefixLeft))
                    (some headBit :: right) }) =
          { state := ProjectionTailRewindDescription.halt
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (none :: prefixLeft)
                (List.append ((bit :: rest).reverse.map some)
                  (some headBit :: right)) }
      rw [projectionTailRewindDescription_run_scan_bit]
      rw [ih bit (some headBit :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem projectionTailRewindDescription_run_from_last_bit
    (bitsLeftRev : Word Bool) (lastBit : Bool)
    (prefixLeft right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig
        (bitsLeftRev.length + 2)
        { state := ProjectionTailRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (bitsLeftRev.map some)
                (none :: prefixLeft))
              (some lastBit :: right) } =
      { state := ProjectionTailRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (none :: prefixLeft)
            (List.append (bitsLeftRev.reverse.map some)
              (some lastBit :: right)) } := by
  cases bitsLeftRev with
  | nil =>
      simp only [List.length_nil, List.map_nil, List.reverse_nil]
      rw [show 0 + 2 = 1 + 1 by omega]
      rw [runConfig_add]
      change
        ProjectionTailRewindDescription.runConfig 1
            (ProjectionTailRewindDescription.runConfig 1
              { state := ProjectionTailRewindDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (none :: prefixLeft) (some lastBit :: right) }) =
          { state := ProjectionTailRewindDescription.halt
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (none :: prefixLeft) (some lastBit :: right) }
      rw [projectionTailRewindDescription_run_state0_bit]
      exact projectionTailRewindDescription_run_finish
        prefixLeft (some lastBit :: right)
  | cons bit rest =>
      rw [show (bit :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        omega]
      rw [runConfig_add]
      change
        ProjectionTailRewindDescription.runConfig
            (rest.length + 2)
            (ProjectionTailRewindDescription.runConfig 1
              { state := ProjectionTailRewindDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    (some bit ::
                      List.append (rest.map some)
                        (none :: prefixLeft))
                    (some lastBit :: right) }) =
          { state := ProjectionTailRewindDescription.halt
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (none :: prefixLeft)
                (List.append ((bit :: rest).reverse.map some)
                  (some lastBit :: right)) }
      rw [projectionTailRewindDescription_run_state0_bit]
      rw [projectionTailRewindDescription_run_scan_to_first_bit
        rest bit prefixLeft (some lastBit :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem projectionTailRewindDescription_run_tail_block
    (trail : Nat) (bitsLeftRev : Word Bool) (lastBit : Bool)
    (prefixLeft right : List (Option Bool)) :
    ProjectionTailRewindDescription.runConfig
        (trail + 1 + (bitsLeftRev.length + 2))
        { state := ProjectionTailRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (List.append (List.replicate trail none)
                (some lastBit ::
                  List.append (bitsLeftRev.map some)
                    (none :: prefixLeft)))
              (none :: right) } =
      { state := ProjectionTailRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (none :: prefixLeft)
            (List.append (bitsLeftRev.reverse.map some)
              (some lastBit ::
                none :: List.append
                  (List.replicate trail none) right)) } := by
  rw [show trail + 1 + (bitsLeftRev.length + 2) =
      trail + (1 + (bitsLeftRev.length + 2)) by omega]
  rw [runConfig_add]
  rw [projectionTailRewindDescription_run_blanks]
  rw [runConfig_add]
  have hright :
      List.append (List.replicate (trail + 1) none) right =
        none :: List.append (List.replicate trail none) right :=
    replicate_none_succ_append trail right
  rw [hright]
  rw [projectionTailRewindDescription_run_blank_to_cell]
  rw [projectionTailRewindDescription_run_from_last_bit]

theorem projectedStageInputContinueDescription_haltsFromTape_finalTape
    (input result : Word Bool) (stage : Nat) :
    ProjectedStageInputContinueDescription.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (ControllerStageInputProjection.finalTape
          { input := input, stage := stage, result := result }))
      (stageInputContinueOutputTape
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            { input := input, stage := stage + 1, result := [] }))) := by
  let prefixBits := stageInputContinueStagePrefixBits input stage
  let trail := 8 * result.length + 4
  let Tstart : Tape Bool :=
    DovetailInitialLayoutInitializer.tapeAtCells
      (List.append (List.replicate trail none)
        (some true ::
          List.append
            ((projectionStageInputBitsLeftRev input stage).map some)
            ([none, none, none, none] : List (Option Bool))))
      [none, none]
  let Tmid : Tape Bool :=
    DovetailInitialLayoutInitializer.tapeAtCells
      ([none, none, none, none] : List (Option Bool))
      (List.append
        ((projectionStageInputBitsLeftRev input stage).reverse.map some)
        (some true ::
          none :: List.append (List.replicate trail none) [none]))
  have hstart :
      Tape.move Direction.left
          (ControllerStageInputProjection.finalTape
            { input := input, stage := stage, result := result }) =
        Tstart := by
    simpa [Tstart, trail] using
      projectionFinalTape_move_left_eq_tailBlock input result stage
  have hAhalt :
      ProjectionTailRewindDescription.HaltsFromTape Tstart Tmid := by
    refine ⟨trail + 1 +
        ((projectionStageInputBitsLeftRev input stage).length + 2), ?_⟩
    have hrun :=
      projectionTailRewindDescription_run_tail_block
        trail (projectionStageInputBitsLeftRev input stage) true
        ([none, none, none] : List (Option Bool)) [none]
    change
      (ProjectionTailRewindDescription.runConfig
        (trail + 1 +
          ((projectionStageInputBitsLeftRev input stage).length + 2))
        { state := ProjectionTailRewindDescription.start
          tape := Tstart }).state =
          ProjectionTailRewindDescription.halt ∧
        (ProjectionTailRewindDescription.runConfig
          (trail + 1 +
            ((projectionStageInputBitsLeftRev input stage).length + 2))
          { state := ProjectionTailRewindDescription.start
            tape := Tstart }).tape = Tmid
    rw [show
        ProjectionTailRewindDescription.runConfig
          (trail + 1 +
            ((projectionStageInputBitsLeftRev input stage).length + 2))
          { state := ProjectionTailRewindDescription.start
            tape := Tstart } =
          { state := ProjectionTailRewindDescription.halt
            tape := Tmid } by
        simpa [Tstart, Tmid, trail, List.append_assoc] using hrun]
    exact ⟨rfl, rfl⟩
  have hAhaltStart :
      ProjectionTailRewindDescription.HaltsFromTape
        (Tape.move Direction.left
          (ControllerStageInputProjection.finalTape
            { input := input, stage := stage, result := result }))
        Tmid := by
    simpa [hstart] using hAhalt
  let Tboundary : Tape Bool :=
    DovetailInitialLayoutInitializer.tapeAtCells
      ([none, none, none] : List (Option Bool))
      (none ::
        List.append
          ((List.append prefixBits stageInputContinueDoneBits).map some)
          (none :: List.append (List.replicate trail none) [none]))
  let Tcanonical : Tape Bool :=
    DovetailInitialLayoutInitializer.tapeAtCells []
      (none ::
        List.append
          ((List.append prefixBits stageInputContinueDoneBits).map some)
          [none])
  have hboundary :
      Tape.move Direction.left Tmid = Tboundary := by
    let cells : List (Option Bool) :=
      List.append
        ((projectionStageInputBitsLeftRev input stage).reverse.map some)
        (some true ::
          none :: List.append (List.replicate trail none) [none])
    have hcells : cells ≠ [] := by
      simp [cells]
    have hmove :
        Tape.move Direction.left Tmid =
          DovetailInitialLayoutInitializer.tapeAtCells
            ([none, none, none] : List (Option Bool))
            (none :: cells) := by
      simpa [Tmid, cells] using
        tapeAtCells_move_left_of_cells_ne_nil
          (none : Option Bool)
          ([none, none, none] : List (Option Bool))
          cells hcells
    rw [hmove]
    simp [Tboundary, cells, prefixBits,
      DovetailInitialLayoutInitializer.tapeAtCells]
    have hpayload :=
      congrArg
        (fun xs : List (Option Bool) =>
          List.append xs
            (none :: List.append (List.replicate trail none) [none]))
        (projectionStageInputBitsLeftRev_payload_cells_mapped input stage)
    simpa [List.append_assoc, List.map_append] using hpayload
  have hboundaryEquiv :
      Tape.Equiv Tboundary Tcanonical := by
    simpa [Tboundary, Tcanonical, prefixBits] using
      stageInputContinueBoundaryPaddedTape_equiv prefixBits trail
  have hBclean :
      StageInputContinueBoundaryRewriterDescription.HaltsFromTape
        Tcanonical
        (stageInputContinueOutputTape
          (stageInputContinueBitsOutputFromPrefix prefixBits)) := by
    simpa [Tcanonical, prefixBits] using
      stageInputContinueBoundaryRewriterDescription_haltsFromTape_prefixBits
        prefixBits
  have hBactualEquiv :
      StageInputContinueBoundaryRewriterDescription.HaltsFromTapeEquiv
        (Tape.move Direction.left Tmid)
        (stageInputContinueOutputTape
          (stageInputContinueBitsOutputFromPrefix prefixBits)) := by
    have hfromBoundary :
        StageInputContinueBoundaryRewriterDescription.HaltsFromTapeEquiv
          Tboundary
          (stageInputContinueOutputTape
            (stageInputContinueBitsOutputFromPrefix prefixBits)) :=
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm hboundaryEquiv) hBclean
    simpa [hboundary] using hfromBoundary
  rcases hBactualEquiv with ⟨Tactual, hBactual, hTactual⟩
  rcases
      runConfig_eq_halt_of_haltsFromTape hBactual with
    ⟨nB, hBRun⟩
  have hseq :
      ProjectedStageInputContinueDescription.HaltsFromTape
        (Tape.move Direction.left
          (ControllerStageInputProjection.finalTape
            { input := input, stage := stage, result := result }))
        Tactual := by
    exact
      seqSubroutine_haltsFromTape_of_haltsFromTape
        projectionTailRewindDescription_subroutineReady
        stageInputContinueBoundaryRewriterDescription_subroutineReady
        hAhaltStart ⟨nB, hBRun⟩
  refine ⟨Tactual, hseq, ?_⟩
  have htarget :
      stageInputContinueOutputTape
          (stageInputContinueBitsOutputFromPrefix prefixBits) =
        stageInputContinueOutputTape
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              { input := input, stage := stage + 1, result := [] })) := by
    simp [prefixBits, stageInputContinueStagePrefixBits,
      stageInputContinue_outputBits_eq_prefix input stage]
  simpa [htarget] using hTactual

def ControllerResultContinueDescription : MachineDescription :=
  seqSubroutine
    ResultNoneGuardStageInputProjectionDescription
    ProjectedStageInputContinueDescription
    Direction.left

theorem controllerResultContinueDescription_subroutineReady :
    ControllerResultContinueDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    resultNoneGuardStageInputProjectionDescription_subroutineReady
    projectedStageInputContinueDescription_subroutineReady

theorem resultNoneGuardStageInputProjectionDescription_haltsWithTapeEquiv_finalTape_controllerEncode
    (C : DovetailControllerLayout)
    (hraw : PairedRecognizerDovetailControllerRawOutput C.result = none) :
    ResultNoneGuardStageInputProjectionDescription.HaltsWithTapeEquiv
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (ControllerStageInputProjection.finalTape C) := by
  let code := DovetailControllerLayout.encode C
  let inputBits := encodeCodeWordAsInput code
  have haccept : (resultNoneGuardScanBoundary code).accepts :=
    (resultNoneGuardScanBoundary_controllerEncode_accepts_iff C).mpr hraw
  rcases
      resultNoneGuardScanRewindDescription_handoff_equiv_code_of_accepts
        code haccept with
    ⟨Tguard, hguard, hguardMove⟩
  have hprojReady :
      ControllerStageInputProjection.Description.SubroutineReady :=
    ⟨ControllerStageInputProjection.wellFormed,
      ControllerStageInputProjection.haltTransitionFree⟩
  have hprojWith :
      ControllerStageInputProjection.Description.HaltsWithTape
        inputBits (ControllerStageInputProjection.finalTape C) := by
    simpa [code, inputBits] using
      ControllerStageInputProjection.haltsWithTape_encode C
  have hprojFrom :
      ControllerStageInputProjection.Description.HaltsFromTape
        (Tape.input inputBits)
        (ControllerStageInputProjection.finalTape C) := by
    rcases hprojWith with ⟨nProj, hnProj⟩
    exact ⟨nProj, by simpa [initial] using hnProj⟩
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm hguardMove) hprojFrom with
    ⟨Tactual, hprojActual, hactualEquiv⟩
  rcases
      runConfig_eq_halt_of_haltsFromTape
        hprojActual with
    ⟨nProjActual, hprojRun⟩
  have hseq :
      ResultNoneGuardStageInputProjectionDescription.HaltsWithTape
        inputBits Tactual := by
    simpa [ResultNoneGuardStageInputProjectionDescription, inputBits] using
      seqSubroutine_haltsWithTape_of_haltsWithTape
        resultNoneGuardScanRewindDescription_subroutineReady
        hprojReady hguard ⟨nProjActual, hprojRun⟩
  exact ⟨Tactual, hseq, hactualEquiv⟩

theorem resultNoneGuardStageInputProjectionDescription_haltsWithTape_inv_finalTape
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hhalt :
      ResultNoneGuardStageInputProjectionDescription.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    exists C : DovetailControllerLayout,
      code = DovetailControllerLayout.encode C ∧
        PairedRecognizerDovetailControllerRawOutput C.result = none ∧
          Tape.Equiv T (ControllerStageInputProjection.finalTape C) := by
  let inputBits := encodeCodeWordAsInput code
  have hguardReady : ResultNoneGuardScanRewindDescription.SubroutineReady :=
    resultNoneGuardScanRewindDescription_subroutineReady
  have hprojReady :
      ControllerStageInputProjection.Description.SubroutineReady :=
    ⟨ControllerStageInputProjection.wellFormed,
      ControllerStageInputProjection.haltTransitionFree⟩
  rcases
      seqSubroutine_haltsWithTape_inv
        hguardReady hprojReady
        (by simpa [ResultNoneGuardStageInputProjectionDescription,
          inputBits] using hhalt) with
    ⟨Tguard, hguard, hprojReach⟩
  have hguardEquiv :
      Tape.Equiv
        (Tape.move Direction.left Tguard)
        (Tape.input inputBits) := by
    simpa [inputBits] using
      resultNoneGuardScanRewindDescription_handoff_equiv_of_haltsWithTape_code
        hguard
  rcases hprojReach with ⟨nProj, hprojRun⟩
  have hprojActual :
      ControllerStageInputProjection.Description.HaltsFromTape
        (Tape.move Direction.left Tguard) T := by
    refine ⟨nProj, ?_⟩
    change
      (ControllerStageInputProjection.Description.runConfig nProj
        { state := ControllerStageInputProjection.Description.start
          tape := Tape.move Direction.left Tguard }).state =
          ControllerStageInputProjection.Description.halt ∧
        (ControllerStageInputProjection.Description.runConfig nProj
          { state := ControllerStageInputProjection.Description.start
            tape := Tape.move Direction.left Tguard }).tape = T
    rw [hprojRun]
    exact ⟨rfl, rfl⟩
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        hguardEquiv hprojActual with
    ⟨Tclean, hprojClean, hcleanEquiv⟩
  have hprojCleanWith :
      ControllerStageInputProjection.Description.HaltsWithTape
        inputBits Tclean := by
    rcases hprojClean with ⟨nClean, hnClean⟩
    exact ⟨nClean, by simpa [initial] using hnClean⟩
  rcases hprojClean with ⟨nClean, hnClean⟩
  rcases
      ControllerStageInputProjection.decodeComplete_of_halting_run
        (code := code) (n := nClean)
        (by simpa [initial] using hnClean.left) with
    ⟨C, hdecode⟩
  have hcode :
      code = DovetailControllerLayout.encode C :=
    DovetailControllerLayout.decodeComplete_eq_some_encode
      hdecode
  have haccept :
      (resultNoneGuardScanBoundary code).accepts :=
    resultNoneGuardScanRewindDescription_accepts_of_haltsWithTape_code
      hguard
  have hraw :
      PairedRecognizerDovetailControllerRawOutput C.result = none := by
    rw [hcode] at haccept
    exact
      (resultNoneGuardScanBoundary_controllerEncode_accepts_iff C).mp
        haccept
  have hknown :
      ControllerStageInputProjection.Description.HaltsWithTape
        inputBits (ControllerStageInputProjection.finalTape C) := by
    simpa [inputBits, hcode] using
      ControllerStageInputProjection.haltsWithTape_encode C
  have hTclean :
      Tclean = ControllerStageInputProjection.finalTape C :=
    MachineDescription.haltsWithTape_functional_of_haltTransitionFree
      ControllerStageInputProjection.haltTransitionFree
      hprojCleanWith hknown
  refine ⟨C, hcode, hraw, ?_⟩
  exact
    Tape.Equiv.trans (Tape.Equiv.symm hcleanEquiv)
      (by rw [hTclean]; exact Tape.Equiv.refl _)

theorem controllerResultContinueDescription_haltsWithOutput_controllerEncode
    (C : DovetailControllerLayout)
    (hraw : PairedRecognizerDovetailControllerRawOutput C.result = none) :
    ControllerResultContinueDescription.HaltsWithOutput
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.nextStage C))) := by
  rcases C with ⟨input, stage, result⟩
  let C : DovetailControllerLayout :=
    { input := input, stage := stage, result := result }
  let nextCode : Word MachineCodeSymbol :=
    DovetailControllerLayout.encode
      (DovetailControllerLayout.nextStage C)
  let outputTape : Tape Bool :=
    stageInputContinueOutputTape
      (encodeCodeWordAsInput nextCode)
  have hprefixEquiv :
      ResultNoneGuardStageInputProjectionDescription.HaltsWithTapeEquiv
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        (ControllerStageInputProjection.finalTape C) := by
    exact
      resultNoneGuardStageInputProjectionDescription_haltsWithTapeEquiv_finalTape_controllerEncode
        C hraw
  rcases hprefixEquiv with ⟨Tprefix, hprefix, hprefixTapeEquiv⟩
  have hcontClean :
      ProjectedStageInputContinueDescription.HaltsFromTapeEquiv
        (Tape.move Direction.left
          (ControllerStageInputProjection.finalTape C))
        outputTape := by
    simpa [C, outputTape, nextCode] using
      projectedStageInputContinueDescription_haltsFromTape_finalTape
        input result stage
  rcases hcontClean with ⟨TcleanOut, hcontCleanExact, hcleanOutEquiv⟩
  have hhandoffEquiv :
      Tape.Equiv
        (Tape.move Direction.left
          (ControllerStageInputProjection.finalTape C))
        (Tape.move Direction.left Tprefix) :=
    Tape.Equiv.move (Tape.Equiv.symm hprefixTapeEquiv) Direction.left
  have hcontActualEquiv :
      ProjectedStageInputContinueDescription.HaltsFromTapeEquiv
        (Tape.move Direction.left Tprefix) outputTape := by
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          hhandoffEquiv hcontCleanExact with
      ⟨TactualOut, hactualOut, hactualToClean⟩
    exact
      ⟨TactualOut, hactualOut,
        Tape.Equiv.trans hactualToClean hcleanOutEquiv⟩
  rcases hcontActualEquiv with ⟨Tout, hcontActual, hToutEquiv⟩
  rcases
      runConfig_eq_halt_of_haltsFromTape
        hcontActual with
    ⟨nCont, hcontRun⟩
  have hfull :
      ControllerResultContinueDescription.HaltsWithTape
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        Tout := by
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        resultNoneGuardStageInputProjectionDescription_subroutineReady
        projectedStageInputContinueDescription_subroutineReady
        hprefix ⟨nCont, hcontRun⟩
  have hfullEquiv :
      ControllerResultContinueDescription.HaltsWithTapeEquiv
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        outputTape :=
    ⟨Tout, hfull, hToutEquiv⟩
  have hout :=
    haltsWithOutput_of_haltsWithTapeEquiv hfullEquiv
  simpa [C, nextCode, outputTape,
    DovetailControllerLayout.nextStage,
    stageInputContinueOutputTape_normalizedOutput] using hout

theorem controllerResultContinueDescription_canonicalForwardSpec :
    ControllerResultContinueCanonicalForwardSpec
      ControllerResultContinueDescription := by
  intro C hraw
  exact
    controllerResultContinueDescription_haltsWithOutput_controllerEncode
      C hraw

theorem controllerResultContinueDescription_closedLayoutSpec :
    ControllerResultContinueClosedLayoutSpec
      ControllerResultContinueDescription := by
  intro code out hhalt
  rcases hhalt with ⟨n, hn⟩
  let inputBits := encodeCodeWordAsInput code
  let seq := ControllerResultContinueDescription
  let Tout : Tape Bool :=
    (seq.runConfig n (seq.initial inputBits)).tape
  have hfullTape :
      seq.HaltsWithTape inputBits Tout := by
    refine ⟨n, ?_⟩
    exact ⟨hn.left, rfl⟩
  have hToutNorm :
      Tape.normalizedOutput Tout =
        encodeCodeWordAsInput out :=
    hn.right
  have hprefixReady :
      ResultNoneGuardStageInputProjectionDescription.SubroutineReady :=
    resultNoneGuardStageInputProjectionDescription_subroutineReady
  have hcontinueReady :
      ProjectedStageInputContinueDescription.SubroutineReady :=
    projectedStageInputContinueDescription_subroutineReady
  rcases
      seqSubroutine_haltsWithTape_inv
        hprefixReady hcontinueReady
        (by simpa [seq, ControllerResultContinueDescription,
          inputBits] using hfullTape) with
    ⟨Tprefix, hprefix, hcontinueReach⟩
  rcases
      resultNoneGuardStageInputProjectionDescription_haltsWithTape_inv_finalTape
        (by simpa [inputBits] using hprefix) with
    ⟨C, hcode, hraw, hprefixEquiv⟩
  rcases hcontinueReach with ⟨nContinue, hcontinueRun⟩
  have hcontinueActual :
      ProjectedStageInputContinueDescription.HaltsFromTape
        (Tape.move Direction.left Tprefix) Tout := by
    refine ⟨nContinue, ?_⟩
    change
      (ProjectedStageInputContinueDescription.runConfig nContinue
        { state := ProjectedStageInputContinueDescription.start
          tape := Tape.move Direction.left Tprefix }).state =
          ProjectedStageInputContinueDescription.halt ∧
        (ProjectedStageInputContinueDescription.runConfig nContinue
          { state := ProjectedStageInputContinueDescription.start
            tape := Tape.move Direction.left Tprefix }).tape = Tout
    rw [hcontinueRun]
    exact ⟨rfl, rfl⟩
  let expectedTape : Tape Bool :=
    stageInputContinueOutputTape
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.nextStage C)))
  have hcleanContinue :
      ProjectedStageInputContinueDescription.HaltsFromTapeEquiv
        (Tape.move Direction.left
          (ControllerStageInputProjection.finalTape C))
        expectedTape := by
    simpa [expectedTape,
      DovetailControllerLayout.nextStage] using
      projectedStageInputContinueDescription_haltsFromTape_finalTape
        C.input C.result C.stage
  rcases hcleanContinue with
    ⟨TcleanOut, hcleanContinueExact, hcleanOutEquiv⟩
  have hinputEquiv :
      Tape.Equiv
        (Tape.move Direction.left
          (ControllerStageInputProjection.finalTape C))
        (Tape.move Direction.left Tprefix) :=
    Tape.Equiv.move (Tape.Equiv.symm hprefixEquiv) Direction.left
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        hinputEquiv hcleanContinueExact with
    ⟨TknownOut, hknownContinue, hknownToClean⟩
  have hToutEq : Tout = TknownOut :=
    haltsFromTape_functional_of_haltTransitionFree
      projectedStageInputContinueDescription_subroutineReady.right
      hcontinueActual hknownContinue
  have hToutExpectedNorm :
      Tape.normalizedOutput Tout =
        Tape.normalizedOutput expectedTape := by
    rw [hToutEq]
    exact
      Tape.Equiv.normalizedOutput_eq
        (Tape.Equiv.trans hknownToClean hcleanOutEquiv)
  have hExpectedNorm :
      Tape.normalizedOutput expectedTape =
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C)) := by
    simp [expectedTape, stageInputContinueOutputTape_normalizedOutput]
  have houtBits :
      encodeCodeWordAsInput out =
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C)) := by
    rw [← hToutNorm]
    exact hToutExpectedNorm.trans hExpectedNorm
  have hout :
      out =
        DovetailControllerLayout.encode
      (DovetailControllerLayout.nextStage C) :=
    encodeCodeWordAsInput_injective houtBits
  exact ⟨C, hcode, hraw, hout⟩

theorem controllerResultContinueComponentConstruction :
    ControllerResultContinueComponentConstruction := by
  exact
    ⟨ControllerResultContinueDescription,
      controllerResultContinueDescription_subroutineReady,
      controllerResultContinueDescription_canonicalForwardSpec,
      controllerResultContinueDescription_closedLayoutSpec⟩

end ControllerResultContinueConstruction

end Computability
end FoC
