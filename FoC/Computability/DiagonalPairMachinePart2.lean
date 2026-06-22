import FoC.Computability.DiagonalPairMachinePart1


set_option doc.verso true

/-!
# DiagonalPairMachinePart2

Supporting declarations and helper lemmas for Computability DiagonalPairMachinePart2.
-/

namespace FoC
namespace Computability
open Foundation
open Languages

def faithfulDiagonalPairMapRewindTape
    (leftRev crossed : Word ConcreteMachineCodeSymbol) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match leftRev with
  | [] =>
      { left := []
        head := none
        right :=
          crossed.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code)) ++
            [some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator)] }
  | code :: rest =>
      { left :=
          rest.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code))
        head := some (FaithfulDiagonalPairMapMachineSymbol.raw code)
        right :=
          crossed.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code)) ++
            [some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator)] }

def faithfulDiagonalPairMapAppendScanTape
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol)
    (scannedRev remaining : List FaithfulDiagonalPairMapScanCell) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match remaining with
  | [] =>
      { left :=
          faithfulDiagonalPairMapScanTapeCells scannedRev ++
            faithfulDiagonalPairMapMarkedLeftContext processed code
        head := none
        right := [] }
  | cell :: rest =>
      { left :=
          faithfulDiagonalPairMapScanTapeCells scannedRev ++
            faithfulDiagonalPairMapMarkedLeftContext processed code
        head := faithfulDiagonalPairMapScanCellEncode cell
        right := faithfulDiagonalPairMapScanTapeCells rest }

def faithfulDiagonalPairMapSeekTape
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol)
    (leftRev crossed : List FaithfulDiagonalPairMapScanCell) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match leftRev with
  | [] =>
      { left := faithfulDiagonalPairMapLeftContext processed
        head := some (FaithfulDiagonalPairMapMachineSymbol.markLeft code)
        right :=
          faithfulDiagonalPairMapScanTapeCells crossed ++
            [some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.right code))] }
  | cell :: rest =>
      { left :=
          faithfulDiagonalPairMapScanTapeCells rest ++
            faithfulDiagonalPairMapMarkedLeftContext processed code
        head := faithfulDiagonalPairMapScanCellEncode cell
        right :=
          faithfulDiagonalPairMapScanTapeCells crossed ++
            [some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.right code))] }

def faithfulDiagonalPairMapHaltTape
    (processed : Word ConcreteMachineCodeSymbol) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  Tape.move Direction.right
    (Tape.write
      (some (FaithfulDiagonalPairMapMachineSymbol.out
        PairCodeSymbol.separator))
      (faithfulDiagonalPairMapProcessTape processed []))

def faithfulDiagonalPairMapConfig
    (state : FaithfulDiagonalPairMapMachineState)
    (tape : Tape FaithfulDiagonalPairMapMachineSymbol) :
    TuringMachine.Configuration
      FaithfulDiagonalPairMapMachineSymbol
      FaithfulDiagonalPairMapMachineState :=
  { state := state, tape := tape }

def faithfulDiagonalPairMapTransition :
    FaithfulDiagonalPairMapMachineState ->
      Option FaithfulDiagonalPairMapMachineSymbol ->
        Option
          (Option FaithfulDiagonalPairMapMachineSymbol × Direction ×
            FaithfulDiagonalPairMapMachineState)
  | FaithfulDiagonalPairMapMachineState.initStart, none =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.halt)
  | FaithfulDiagonalPairMapMachineState.initStart,
      some (FaithfulDiagonalPairMapMachineSymbol.raw code) =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.raw code),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.initScan)
  | FaithfulDiagonalPairMapMachineState.initStart,
      some cell =>
      some (some cell, Direction.right,
        FaithfulDiagonalPairMapMachineState.initScan)
  | FaithfulDiagonalPairMapMachineState.initScan, none =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator),
          Direction.left,
          FaithfulDiagonalPairMapMachineState.rewind)
  | FaithfulDiagonalPairMapMachineState.initScan,
      some cell =>
      some (some cell, Direction.right,
        FaithfulDiagonalPairMapMachineState.initScan)
  | FaithfulDiagonalPairMapMachineState.rewind, none =>
      some (none, Direction.right,
        FaithfulDiagonalPairMapMachineState.process)
  | FaithfulDiagonalPairMapMachineState.rewind,
      some cell =>
      some (some cell, Direction.left,
        FaithfulDiagonalPairMapMachineState.rewind)
  | FaithfulDiagonalPairMapMachineState.process,
      some (FaithfulDiagonalPairMapMachineSymbol.raw code) =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.markLeft code),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.append code)
  | FaithfulDiagonalPairMapMachineState.process,
      some (FaithfulDiagonalPairMapMachineSymbol.out
        PairCodeSymbol.separator) =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.halt)
  | FaithfulDiagonalPairMapMachineState.process, cell =>
      some (cell, Direction.right,
        FaithfulDiagonalPairMapMachineState.process)
  | FaithfulDiagonalPairMapMachineState.append code, none =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          (PairCodeSymbol.right code)),
          Direction.left,
          FaithfulDiagonalPairMapMachineState.seekMark)
  | FaithfulDiagonalPairMapMachineState.append code,
      some cell =>
      some (some cell, Direction.right,
        FaithfulDiagonalPairMapMachineState.append code)
  | FaithfulDiagonalPairMapMachineState.seekMark,
      some (FaithfulDiagonalPairMapMachineSymbol.markLeft code) =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          (PairCodeSymbol.left code)),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.process)
  | FaithfulDiagonalPairMapMachineState.seekMark,
      some cell =>
      some (some cell, Direction.left,
        FaithfulDiagonalPairMapMachineState.seekMark)
  | FaithfulDiagonalPairMapMachineState.seekMark, none =>
      some (none, Direction.right,
        FaithfulDiagonalPairMapMachineState.process)
  | FaithfulDiagonalPairMapMachineState.halt, _ =>
      none

def FaithfulConcreteDiagonalPairMapMachine :
    TuringMachine
      FaithfulDiagonalPairMapMachineSymbol
      FaithfulDiagonalPairMapMachineState where
  start := FaithfulDiagonalPairMapMachineState.initStart
  halt := FaithfulDiagonalPairMapMachineState.halt
  transition := faithfulDiagonalPairMapTransition
  statesFinite := FaithfulDiagonalPairMapMachineState.finite

 /-- {name}`faithfulDiagonalPairMapScanTapeCells_append` characterizes a scan safety phase. -/
theorem faithfulDiagonalPairMapScanTapeCells_append
    (x y : List FaithfulDiagonalPairMapScanCell) :
    faithfulDiagonalPairMapScanTapeCells (x ++ y) =
      faithfulDiagonalPairMapScanTapeCells x ++
        faithfulDiagonalPairMapScanTapeCells y := by
  simp [faithfulDiagonalPairMapScanTapeCells]

 /-- {name}`faithfulDiagonalPairMapLeftContext_append_single` describes append/fold behavior used by later composition. -/
theorem faithfulDiagonalPairMapLeftContext_append_single
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol) :
    faithfulDiagonalPairMapLeftContext (List.append processed [code]) =
      some (FaithfulDiagonalPairMapMachineSymbol.out
        (PairCodeSymbol.left code)) ::
        faithfulDiagonalPairMapLeftContext processed := by
  simp [faithfulDiagonalPairMapLeftContext,
    faithfulDiagonalPairMapLeftCells, List.map_append]

 /-- {name}`faithfulDiagonalPairMapScanCells_append_processed` characterizes a scan safety phase. -/
theorem faithfulDiagonalPairMapScanCells_append_processed
    (remaining processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol) :
    faithfulDiagonalPairMapScanCells remaining (List.append processed [code]) =
      faithfulDiagonalPairMapScanCells remaining processed ++
        [FaithfulDiagonalPairMapScanCell.right code] := by
  simp [faithfulDiagonalPairMapScanCells, List.map_append,
    List.append_assoc]

 /-- {name}`faithfulDiagonalPairMap_filterMap_some_map` captures the core lemma for this local construction. -/
theorem faithfulDiagonalPairMap_filterMap_some_map
    {alpha beta : Type} (f : alpha -> beta) (w : List alpha) :
    List.filterMap (fun a => some (f a)) w = w.map f := by
  induction w with
  | nil =>
      rfl
  | cons a rest ih =>
      simp [ih]

 /-- {name}`faithfulDiagonalPairMap_output_left_map` captures the core lemma for this local construction. -/
theorem faithfulDiagonalPairMap_output_left_map
    (w : Word ConcreteMachineCodeSymbol) :
    List.map
        (fun code =>
          FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code)) w =
      List.map
        (fun pair => FaithfulDiagonalPairMapMachineSymbol.out pair)
        (List.map PairCodeSymbol.left w) := by
  induction w with
  | nil =>
      rfl
  | cons code rest ih =>
      change
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code) ::
          List.map
            (fun code =>
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.left code)) rest =
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code) ::
          List.map
            (fun pair => FaithfulDiagonalPairMapMachineSymbol.out pair)
            (List.map PairCodeSymbol.left rest)
      rw [ih]

 /-- {name}`faithfulDiagonalPairMap_output_right_map` captures the core lemma for this local construction. -/
theorem faithfulDiagonalPairMap_output_right_map
    (w : Word ConcreteMachineCodeSymbol) :
    List.map
        (fun code =>
          FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.right code)) w =
      List.map
        (fun pair => FaithfulDiagonalPairMapMachineSymbol.out pair)
        (List.map PairCodeSymbol.right w) := by
  induction w with
  | nil =>
      rfl
  | cons code rest ih =>
      change
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.right code) ::
          List.map
            (fun code =>
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code)) rest =
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.right code) ::
          List.map
            (fun pair => FaithfulDiagonalPairMapMachineSymbol.out pair)
            (List.map PairCodeSymbol.right rest)
      rw [ih]

 /-- {name}`faithfulDiagonalPairMap_initScan_computes` characterizes a scan safety phase. -/
theorem faithfulDiagonalPairMap_initScan_computes
    (seenRev rest : Word ConcreteMachineCodeSymbol) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.initScan
        (faithfulDiagonalPairMapInitScanTape seenRev rest))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.rewind
        (faithfulDiagonalPairMapRewindTape
          (List.append rest.reverse seenRev) [])) := by
  induction rest generalizing seenRev with
  | nil =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (faithfulDiagonalPairMapInitScanTape seenRev []))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.rewind nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (dir := Direction.left)
            (nextState := FaithfulDiagonalPairMapMachineState.rewind)
            ?_)
          ?_
      · rfl
      · cases seenRev with
        | nil =>
            exact TuringMachine.Computes.refl _
        | cons code suffix =>
            exact TuringMachine.Computes.refl _
  | cons code suffix ih =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (faithfulDiagonalPairMapInitScanTape seenRev (code :: suffix)))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.initScan nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.initScan)
            ?_)
          ?_
      · rfl
      · cases suffix with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapInitScanTape,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (code :: seenRev)
        | cons next tail =>
            simpa [nextTape, faithfulDiagonalPairMapInitScanTape,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (code :: seenRev)

 /-- {name}`faithfulDiagonalPairMap_rewind_computes` captures the core lemma for this local construction. -/
theorem faithfulDiagonalPairMap_rewind_computes
    (leftRev crossed : Word ConcreteMachineCodeSymbol) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.rewind
        (faithfulDiagonalPairMapRewindTape leftRev crossed))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.process
        (faithfulDiagonalPairMapProcessTape []
          (List.append leftRev.reverse crossed))) := by
  induction leftRev generalizing crossed with
  | nil =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write none
            (faithfulDiagonalPairMapRewindTape
              ([] : Word ConcreteMachineCodeSymbol) crossed))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.process nextTape)
          (TuringMachine.Step.mk
            (write := none)
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.process)
            ?_)
          ?_
      · rfl
      · cases crossed with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapRewindTape,
              faithfulDiagonalPairMapProcessTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanCells,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := FaithfulConcreteDiagonalPairMapMachine)
                (faithfulDiagonalPairMapConfig
                  FaithfulDiagonalPairMapMachineState.process nextTape)
        | cons code rest =>
            simpa [nextTape, faithfulDiagonalPairMapRewindTape,
              faithfulDiagonalPairMapProcessTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanCells,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := FaithfulConcreteDiagonalPairMapMachine)
                (faithfulDiagonalPairMapConfig
                  FaithfulDiagonalPairMapMachineState.process nextTape)
  | cons code rest ih =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (faithfulDiagonalPairMapRewindTape (code :: rest) crossed))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.rewind nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (dir := Direction.left)
            (nextState := FaithfulDiagonalPairMapMachineState.rewind)
            ?_)
          ?_
      · rfl
      · cases rest with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapRewindTape,
              faithfulDiagonalPairMapProcessTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanCells,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (code :: crossed)
        | cons next tail =>
            simpa [nextTape, faithfulDiagonalPairMapRewindTape,
              faithfulDiagonalPairMapProcessTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanCells,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (code :: crossed)

 /-- {name}`faithfulDiagonalPairMap_appendScan_computes` characterizes a scan safety phase. -/
theorem faithfulDiagonalPairMap_appendScan_computes
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol)
    (scannedRev remaining : List FaithfulDiagonalPairMapScanCell) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        (FaithfulDiagonalPairMapMachineState.append code)
        (faithfulDiagonalPairMapAppendScanTape
          processed code scannedRev remaining))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.seekMark
        (faithfulDiagonalPairMapSeekTape
          processed code (remaining.reverse ++ scannedRev) [])) := by
  induction remaining generalizing scannedRev with
  | nil =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.right code)))
            (faithfulDiagonalPairMapAppendScanTape
              processed code scannedRev []))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.seekMark nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.right code)))
            (dir := Direction.left)
            (nextState := FaithfulDiagonalPairMapMachineState.seekMark)
            ?_)
          ?_
      · rfl
      · cases scannedRev with
        | nil =>
            exact TuringMachine.Computes.refl _
        | cons cell rest =>
            exact TuringMachine.Computes.refl _
  | cons cell rest ih =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (faithfulDiagonalPairMapScanCellEncode cell)
            (faithfulDiagonalPairMapAppendScanTape
              processed code scannedRev (cell :: rest)))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            (FaithfulDiagonalPairMapMachineState.append code) nextTape)
          (TuringMachine.Step.mk
            (write := faithfulDiagonalPairMapScanCellEncode cell)
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.append code)
            ?_)
          ?_
      · cases cell <;> rfl
      · cases rest with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapAppendScanTape,
              faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (cell :: scannedRev)
        | cons next tail =>
            simpa [nextTape, faithfulDiagonalPairMapAppendScanTape,
              faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (cell :: scannedRev)

 /-- {name}`faithfulDiagonalPairMap_seek_computes` captures the core lemma for this local construction. -/
theorem faithfulDiagonalPairMap_seek_computes
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol)
    (leftRev crossed : List FaithfulDiagonalPairMapScanCell) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.seekMark
        (faithfulDiagonalPairMapSeekTape
          processed code leftRev crossed))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.process
        (faithfulDiagonalPairMapProcessScanTape
          (List.append processed [code])
          (leftRev.reverse ++ crossed ++
            [FaithfulDiagonalPairMapScanCell.right code]))) := by
  induction leftRev generalizing crossed with
  | nil =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.left code)))
            (faithfulDiagonalPairMapSeekTape processed code [] crossed))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.process nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.left code)))
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.process)
            ?_)
          ?_
      · rfl
      · cases crossed with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells, List.map_append,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := FaithfulConcreteDiagonalPairMapMachine)
                (faithfulDiagonalPairMapConfig
                  FaithfulDiagonalPairMapMachineState.process nextTape)
        | cons cell rest =>
            simpa [nextTape, faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells, List.map_append,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := FaithfulConcreteDiagonalPairMapMachine)
                (faithfulDiagonalPairMapConfig
                  FaithfulDiagonalPairMapMachineState.process nextTape)
  | cons cell rest ih =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (faithfulDiagonalPairMapScanCellEncode cell)
            (faithfulDiagonalPairMapSeekTape
              processed code (cell :: rest) crossed))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.seekMark nextTape)
          (TuringMachine.Step.mk
            (write := faithfulDiagonalPairMapScanCellEncode cell)
            (dir := Direction.left)
            (nextState := FaithfulDiagonalPairMapMachineState.seekMark)
            ?_)
          ?_
      · cases cell <;> rfl
      · cases rest with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (cell :: crossed)
        | cons next tail =>
            simpa [nextTape, faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (cell :: crossed)

 /-- {name}`faithfulDiagonalPairMap_process_computes` captures the core lemma for this local construction. -/
theorem faithfulDiagonalPairMap_process_computes
    (processed remaining : Word ConcreteMachineCodeSymbol) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.process
        (faithfulDiagonalPairMapProcessTape processed remaining))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.halt
        (faithfulDiagonalPairMapHaltTape
          (List.append processed remaining))) := by
  induction remaining generalizing processed with
  | nil =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (faithfulDiagonalPairMapProcessTape processed []))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.halt nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.halt)
            ?_)
          ?_
      · rfl
      · simpa [nextTape, faithfulDiagonalPairMapHaltTape]
          using TuringMachine.Computes.refl
            (M := FaithfulConcreteDiagonalPairMapMachine)
            (faithfulDiagonalPairMapConfig
              FaithfulDiagonalPairMapMachineState.halt nextTape)
  | cons code rest ih =>
      let scanRest := faithfulDiagonalPairMapScanCells rest processed
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.markLeft code))
            (faithfulDiagonalPairMapProcessTape processed
              (code :: rest)))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            (FaithfulDiagonalPairMapMachineState.append code) nextTape)
          (TuringMachine.Step.mk
            (write := some
              (FaithfulDiagonalPairMapMachineSymbol.markLeft code))
            (dir := Direction.right)
            (nextState :=
              FaithfulDiagonalPairMapMachineState.append code)
            ?_)
          ?_
      · rfl
      · have hnext :
            nextTape =
              faithfulDiagonalPairMapAppendScanTape
                processed code [] scanRest := by
          cases rest with
          | nil =>
              simp [nextTape, scanRest, faithfulDiagonalPairMapProcessTape,
                faithfulDiagonalPairMapProcessScanTape,
                faithfulDiagonalPairMapAppendScanTape,
                faithfulDiagonalPairMapScanCells,
                faithfulDiagonalPairMapScanTapeCells,
                faithfulDiagonalPairMapScanCellEncode,
                faithfulDiagonalPairMapMarkedLeftContext,
                Tape.move, Tape.moveRight, Tape.write]
          | cons next suffix =>
              simp [nextTape, scanRest, faithfulDiagonalPairMapProcessTape,
                faithfulDiagonalPairMapProcessScanTape,
                faithfulDiagonalPairMapAppendScanTape,
                faithfulDiagonalPairMapScanCells,
                faithfulDiagonalPairMapScanTapeCells,
                faithfulDiagonalPairMapScanCellEncode,
                faithfulDiagonalPairMapMarkedLeftContext,
                Tape.move, Tape.moveRight, Tape.write]
        rw [hnext]
        refine
          TuringMachine.computes_trans
            (faithfulDiagonalPairMap_appendScan_computes
              processed code [] scanRest)
            ?_
        refine
          TuringMachine.computes_trans
            (by
              simpa [scanRest, List.reverse_append,
                faithfulDiagonalPairMapScanCells,
                List.append_assoc]
                using
                  faithfulDiagonalPairMap_seek_computes
                    processed code scanRest.reverse [])
            ?_
        simpa [faithfulDiagonalPairMapProcessTape,
          faithfulDiagonalPairMapScanCells, List.map_append,
          List.append_assoc]
          using ih (List.append processed [code])

 /-- {name}`faithfulDiagonalPairMap_haltTape_normalized` establishes the halting condition in this construction. -/
theorem faithfulDiagonalPairMap_haltTape_normalized
    (w : Word ConcreteMachineCodeSymbol) :
    Tape.normalizedOutput (faithfulDiagonalPairMapHaltTape w) =
      EncodeWord faithfulDiagonalPairMapOutputEncode
        (ConcreteDiagonalPairMap w) := by
  cases w with
  | nil =>
      simp [faithfulDiagonalPairMapHaltTape,
        faithfulDiagonalPairMapProcessTape,
        faithfulDiagonalPairMapProcessScanTape,
        faithfulDiagonalPairMapScanCells,
        faithfulDiagonalPairMapScanTapeCells,
        faithfulDiagonalPairMapScanCellEncode,
        faithfulDiagonalPairMapLeftContext,
        faithfulDiagonalPairMapLeftCells,
        ConcreteDiagonalPairMap,
        PairCodeSymbol.diagonalMap,
        PairCodeSymbol.encodePair,
        EncodeWord,
        Tape.move, Tape.moveRight, Tape.write, Tape.normalizedOutput,
        Tape.cells]
      change
        [FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator] =
        [FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator]
      rfl
  | cons code rest =>
      simp [faithfulDiagonalPairMapHaltTape,
        faithfulDiagonalPairMapProcessTape,
        faithfulDiagonalPairMapProcessScanTape,
        faithfulDiagonalPairMapScanCells,
        faithfulDiagonalPairMapScanTapeCells,
        faithfulDiagonalPairMapScanCellEncode,
        faithfulDiagonalPairMapLeftContext,
        faithfulDiagonalPairMapLeftCells,
        ConcreteDiagonalPairMap,
        PairCodeSymbol.diagonalMap,
        PairCodeSymbol.encodePair,
        EncodeWord,
        Tape.move, Tape.moveRight, Tape.write, Tape.normalizedOutput,
        Tape.cells, Function.comp_def,
        faithfulDiagonalPairMap_filterMap_some_map]
      unfold faithfulDiagonalPairMapOutputEncode
      change
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code) ::
          (List.map
              (fun code =>
                FaithfulDiagonalPairMapMachineSymbol.out
                  (PairCodeSymbol.left code)) rest ++
            FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator ::
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code) ::
                List.map
                  (fun code =>
                    FaithfulDiagonalPairMapMachineSymbol.out
                      (PairCodeSymbol.right code)) rest) =
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code) ::
          List.map
            (fun pair =>
              FaithfulDiagonalPairMapMachineSymbol.out pair)
            (List.map PairCodeSymbol.left rest ++
              PairCodeSymbol.separator ::
                PairCodeSymbol.right code ::
                  List.map PairCodeSymbol.right rest)
      congr
      have hleft :=
        faithfulDiagonalPairMap_output_left_map rest
      have hright :
          FaithfulDiagonalPairMapMachineSymbol.out
                PairCodeSymbol.separator ::
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code) ::
                List.map
                  (fun code =>
                    FaithfulDiagonalPairMapMachineSymbol.out
                      (PairCodeSymbol.right code)) rest =
            List.map
              (fun pair =>
                FaithfulDiagonalPairMapMachineSymbol.out pair)
              (PairCodeSymbol.separator ::
                PairCodeSymbol.right code ::
                  List.map PairCodeSymbol.right rest) := by
        change
          FaithfulDiagonalPairMapMachineSymbol.out
                PairCodeSymbol.separator ::
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code) ::
                List.map
                  (fun code =>
                    FaithfulDiagonalPairMapMachineSymbol.out
                      (PairCodeSymbol.right code)) rest =
            FaithfulDiagonalPairMapMachineSymbol.out
                PairCodeSymbol.separator ::
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code) ::
                List.map
                  (fun pair =>
                    FaithfulDiagonalPairMapMachineSymbol.out pair)
                  (List.map PairCodeSymbol.right rest)
        rw [faithfulDiagonalPairMap_output_right_map rest]
      rw [hleft, hright]
      exact
        (List.map_append
          (f := fun pair =>
            FaithfulDiagonalPairMapMachineSymbol.out pair)
          (l₁ := List.map PairCodeSymbol.left rest)
          (l₂ :=
            PairCodeSymbol.separator ::
              PairCodeSymbol.right code ::
                List.map PairCodeSymbol.right rest)).symm

 /-- {name}`faithfulDiagonalPairMap_startRaw_moveRight` captures the core lemma for this local construction. -/
theorem faithfulDiagonalPairMap_startRaw_moveRight
    (code : ConcreteMachineCodeSymbol)
    (rest : Word ConcreteMachineCodeSymbol) :
    Tape.move Direction.right
      (Tape.write
        (some (FaithfulDiagonalPairMapMachineSymbol.raw code))
        (Tape.input
          (EncodeWord faithfulDiagonalPairMapInputEncode
            (code :: rest)))) =
      faithfulDiagonalPairMapInitScanTape [code] rest := by
  cases rest with
  | nil =>
      rfl
  | cons next suffix =>
      simp [EncodeWord, faithfulDiagonalPairMapInputEncode,
        faithfulDiagonalPairMapInitScanTape, Tape.input,
        Tape.move, Tape.moveRight, Tape.write]

 /-- {name}`faithful_concrete_diagonal_pair_map_computable` captures the core lemma for this local construction. -/
theorem faithful_concrete_diagonal_pair_map_computable :
    FaithfulConcreteDiagonalPairMapComputable := by
  unfold FaithfulConcreteDiagonalPairMapComputable
    FaithfulTuringComputable FaithfulComputesFunction ComputesFunction
  refine
    ⟨ FaithfulDiagonalPairMapMachineSymbol
    , FaithfulDiagonalPairMapMachineState
    , FaithfulConcreteDiagonalPairMapMachine
    , faithfulDiagonalPairMapInputEncode
    , faithfulDiagonalPairMapOutputEncode
    , ?_ ⟩
  refine
    ⟨ faithfulDiagonalPairMapInputEncode_injective
    , faithfulDiagonalPairMapOutputEncode_injective
    , ?_ ⟩
  intro w
  cases w with
  | nil =>
      let finalTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (Tape.input
              (EncodeWord faithfulDiagonalPairMapInputEncode
                ([] : Word ConcreteMachineCodeSymbol))))
      refine
        ⟨ faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.halt finalTape
        , ?_, rfl, ?_ ⟩
      · refine
          TuringMachine.Computes.step
            (d := faithfulDiagonalPairMapConfig
              FaithfulDiagonalPairMapMachineState.halt finalTape)
            (TuringMachine.Step.mk
              (write := some (FaithfulDiagonalPairMapMachineSymbol.out
                PairCodeSymbol.separator))
              (dir := Direction.right)
              (nextState := FaithfulDiagonalPairMapMachineState.halt)
              ?_)
            (TuringMachine.Computes.refl _)
        rfl
      · change Tape.normalizedOutput finalTape =
          EncodeWord faithfulDiagonalPairMapOutputEncode
            (ConcreteDiagonalPairMap
              ([] : Word ConcreteMachineCodeSymbol))
        simp [finalTape, ConcreteDiagonalPairMap,
          PairCodeSymbol.diagonalMap, PairCodeSymbol.encodePair,
          EncodeWord, Tape.input, Tape.blank, Tape.write, Tape.move,
          Tape.moveRight,
          Tape.normalizedOutput, Tape.cells]
        change
          [FaithfulDiagonalPairMapMachineSymbol.out
            PairCodeSymbol.separator] =
          [FaithfulDiagonalPairMapMachineSymbol.out
            PairCodeSymbol.separator]
        rfl
  | cons code rest =>
      let startNextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (Tape.input
              (EncodeWord faithfulDiagonalPairMapInputEncode
                (code :: rest))))
      let returnRev : Word ConcreteMachineCodeSymbol :=
        List.append rest.reverse [code]
      refine
        ⟨ faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.halt
            (faithfulDiagonalPairMapHaltTape (code :: rest))
        , ?_, rfl, ?_ ⟩
      · refine
          TuringMachine.Computes.step
            (d := faithfulDiagonalPairMapConfig
              FaithfulDiagonalPairMapMachineState.initScan startNextTape)
            (TuringMachine.Step.mk
              (write := some
                (FaithfulDiagonalPairMapMachineSymbol.raw code))
              (dir := Direction.right)
              (nextState := FaithfulDiagonalPairMapMachineState.initScan)
              ?_)
            ?_
        · rfl
        · have hstart :
              startNextTape =
                faithfulDiagonalPairMapInitScanTape [code] rest := by
            simpa [startNextTape]
              using faithfulDiagonalPairMap_startRaw_moveRight code rest
          rw [hstart]
          refine
            TuringMachine.computes_trans
              (faithfulDiagonalPairMap_initScan_computes [code] rest)
              ?_
          refine
            TuringMachine.computes_trans
              (by
                simpa [returnRev]
                  using
                    faithfulDiagonalPairMap_rewind_computes returnRev [])
              ?_
          simpa [returnRev, List.reverse_append, List.append_assoc]
            using
              faithfulDiagonalPairMap_process_computes
                ([] : Word ConcreteMachineCodeSymbol) (code :: rest)
      · exact faithfulDiagonalPairMap_haltTape_normalized (code :: rest)

 /-- {name}`concrete_diagonal_pair_map_computable_of_faithful` captures the core lemma for this local construction. -/
theorem concrete_diagonal_pair_map_computable_of_faithful :
    ConcreteDiagonalPairMapComputable :=
  faithfulTuringComputable_to_turingComputable
    faithful_concrete_diagonal_pair_map_computable

end Computability
end FoC
