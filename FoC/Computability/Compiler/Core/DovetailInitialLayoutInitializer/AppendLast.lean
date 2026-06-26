import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.Spec

set_option doc.verso true

/-!
# AppendLast

Supporting declarations and helper lemmas for Computability Compiler Core DovetailInitialLayoutInitializer AppendLast.
-/


namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer


def WriteTransitionPrefixDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.left 1
    , MachineDescription.transition
        0 (some true) (some true) Direction.left 1
    , MachineDescription.transition
        1 none (some true) Direction.left 2
    , MachineDescription.transition
        2 none (some false) Direction.left 3
    , MachineDescription.transition
        3 none (some false) Direction.left 4
    , MachineDescription.transition
        4 none (some false) Direction.right 5
    ]

 /-- {name}`writeTransitionPrefixDescription_wellFormed` captures the core lemma for this local construction. -/
theorem writeTransitionPrefixDescription_wellFormed :
    WriteTransitionPrefixDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := WriteTransitionPrefixDescription.transitions)
      (stateCount :=
        WriteTransitionPrefixDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := WriteTransitionPrefixDescription.transitions)
      (by
        native_decide)

 /-- {name}`writeTransitionPrefixDescription_haltTransitionFree` establishes the halting condition in this construction. -/
theorem writeTransitionPrefixDescription_haltTransitionFree :
    WriteTransitionPrefixDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := WriteTransitionPrefixDescription.transitions)
    (state := WriteTransitionPrefixDescription.halt)
    (by
      native_decide)

 /-- {name}`writeTransitionPrefixDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem writeTransitionPrefixDescription_subroutineReady :
    WriteTransitionPrefixDescription.SubroutineReady :=
  ⟨writeTransitionPrefixDescription_wellFormed,
    writeTransitionPrefixDescription_haltTransitionFree⟩

 /-- {name}`writeTransitionPrefixDescription_run` captures the core lemma for this local construction. -/
theorem writeTransitionPrefixDescription_run
    (b : Bool) (rest : List (Option Bool)) :
    WriteTransitionPrefixDescription.runConfig 5
        (config 0 [] (some b :: rest)) =
      config 5 [some false]
        (List.append [some false, some false, some true]
          (some b :: rest)) := by
  cases b <;>
    simp [WriteTransitionPrefixDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

def WriteMarkedTransitionPrefixDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.left 1
    , MachineDescription.transition
        0 (some true) (some true) Direction.left 1
    , MachineDescription.transition
        1 none (some true) Direction.left 2
    , MachineDescription.transition
        2 none (some false) Direction.left 3
    , MachineDescription.transition
        3 none none Direction.left 4
    , MachineDescription.transition
        4 none (some false) Direction.right 5
    ]

 /-- {name}`writeMarkedTransitionPrefixDescription_wellFormed` captures the core lemma for this local construction. -/
theorem writeMarkedTransitionPrefixDescription_wellFormed :
    WriteMarkedTransitionPrefixDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := WriteMarkedTransitionPrefixDescription.transitions)
      (stateCount :=
        WriteMarkedTransitionPrefixDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := WriteMarkedTransitionPrefixDescription.transitions)
      (by
        native_decide)

 /-- {name}`writeMarkedTransitionPrefixDescription_haltTransitionFree` establishes the halting condition in this construction. -/
theorem writeMarkedTransitionPrefixDescription_haltTransitionFree :
    WriteMarkedTransitionPrefixDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := WriteMarkedTransitionPrefixDescription.transitions)
    (state := WriteMarkedTransitionPrefixDescription.halt)
    (by
      native_decide)

 /-- {name}`writeMarkedTransitionPrefixDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem writeMarkedTransitionPrefixDescription_subroutineReady :
    WriteMarkedTransitionPrefixDescription.SubroutineReady :=
  ⟨writeMarkedTransitionPrefixDescription_wellFormed,
    writeMarkedTransitionPrefixDescription_haltTransitionFree⟩

 /-- {name}`writeMarkedTransitionPrefixDescription_run` captures the core lemma for this local construction. -/
theorem writeMarkedTransitionPrefixDescription_run
    (b : Bool) (rest : List (Option Bool)) :
    WriteMarkedTransitionPrefixDescription.runConfig 5
        (config 0 [] (some b :: rest)) =
      config 5 [some false]
        (List.append [none, some false, some true]
          (some b :: rest)) := by
  cases b <;>
    simp [WriteMarkedTransitionPrefixDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

def appendRightLastTape
    (leftRev : Word Bool) (b0 b1 b2 b3 : Bool) : Tape Bool :=
  { left := (List.append [b2, b1, b0] leftRev).map some
    head := some b3
    right := [] }

def AppendFixedFourBitsLastDescription
    (b0 b1 b2 b3 : Bool) : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.right 0
    , MachineDescription.transition
        0 (some true) (some true) Direction.right 0
    , MachineDescription.transition
        0 none (some b0) Direction.right 1
    , MachineDescription.transition
        1 none (some b1) Direction.right 2
    , MachineDescription.transition
        2 none (some b2) Direction.right 3
    , MachineDescription.transition
        3 none (some b3) Direction.left 4
    , MachineDescription.transition
        4 (some false) (some false) Direction.right 5
    , MachineDescription.transition
        4 (some true) (some true) Direction.right 5
    ]

 /-- {name}`appendFixedFourBitsLastDescription_wellFormed` describes append/fold behavior used by later composition. -/
theorem appendFixedFourBitsLastDescription_wellFormed
    (b0 b1 b2 b3 : Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).WellFormed := by
  constructor
  · cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      native_decide
  constructor
  · cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      native_decide
  constructor
  · cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l :=
        (AppendFixedFourBitsLastDescription
          b0 b1 b2 b3).transitions)
      (stateCount :=
        (AppendFixedFourBitsLastDescription
          b0 b1 b2 b3).stateCount)
      (by
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
          native_decide)
  · exact transition_deterministic_of_all
      (l :=
        (AppendFixedFourBitsLastDescription
          b0 b1 b2 b3).transitions)
      (by
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
          native_decide)

 /-- {name}`appendFixedFourBitsLastDescription_haltTransitionFree` describes append/fold behavior used by later composition. -/
theorem appendFixedFourBitsLastDescription_haltTransitionFree
    (b0 b1 b2 b3 : Bool) :
    (AppendFixedFourBitsLastDescription
      b0 b1 b2 b3).HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      (AppendFixedFourBitsLastDescription
        b0 b1 b2 b3).transitions)
    (state :=
      (AppendFixedFourBitsLastDescription
        b0 b1 b2 b3).halt)
    (by
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
        native_decide)

 /-- {name}`appendFixedFourBitsLastDescription_step_scan_nonempty` characterizes a scan safety phase. -/
theorem appendFixedFourBitsLastDescription_step_scan_nonempty
    (b0 b1 b2 b3 : Bool)
    (leftRev : Word Bool) (b : Bool) (rest : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).stepConfig
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev (b :: rest) } =
      some
        { state := 0
          tape := MachineDescription.appendRightScanTape
            (b :: leftRev) rest } := by
  cases b <;>
    cases rest <;>
      simp [AppendFixedFourBitsLastDescription,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition,
        MachineDescription.appendRightScanTape, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]

 /-- {name}`appendFixedFourBitsLastDescription_run_scan` states the corresponding theorem run form. -/
theorem appendFixedFourBitsLastDescription_run_scan
    (b0 b1 b2 b3 : Bool)
    (leftRev remaining : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        remaining.length
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev remaining } =
      { state := 0
        tape :=
          MachineDescription.appendRightScanTape
            (List.append remaining.reverse leftRev) [] } := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons b rest ih =>
      simp [MachineDescription.runConfig,
        appendFixedFourBitsLastDescription_step_scan_nonempty,
        ih, List.append_assoc]

 /-- {name}`appendFixedFourBitsLastDescription_run_write` states the corresponding theorem run form. -/
theorem appendFixedFourBitsLastDescription_run_write
    (b0 b1 b2 b3 : Bool) (leftRev : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig 5
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev [] } =
      { state := 5
        tape := appendRightLastTape leftRev b0 b1 b2 b3 } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [AppendFixedFourBitsLastDescription,
      appendRightLastTape,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition,
      MachineDescription.appendRightScanTape, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

 /-- {name}`appendFixedFourBitsLastDescription_run_halt` states the corresponding theorem run form. -/
theorem appendFixedFourBitsLastDescription_run_halt
    (b0 b1 b2 b3 : Bool) (w : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        (w.length + 5)
        ((AppendFixedFourBitsLastDescription b0 b1 b2 b3).initial w) =
      { state := 5
        tape := appendRightLastTape w.reverse b0 b1 b2 b3 } := by
  rw [MachineDescription.runConfig_add]
  have hscan :
      (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
          w.length
          ((AppendFixedFourBitsLastDescription
            b0 b1 b2 b3).initial w) =
        { state := 0
          tape := MachineDescription.appendRightScanTape w.reverse [] } := by
    simpa [MachineDescription.initial,
      AppendFixedFourBitsLastDescription,
      MachineDescription.appendRightScanTape_nil_eq_input] using
      appendFixedFourBitsLastDescription_run_scan
        b0 b1 b2 b3 [] w
  rw [hscan]
  exact appendFixedFourBitsLastDescription_run_write
    b0 b1 b2 b3 w.reverse

def appendScanTapeAtCells
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    Tape Bool :=
  match remaining with
  | [] => { left := leftRev, head := none, right := [] }
  | b :: rest => { left := leftRev, head := some b, right := rest.map some }

def appendScanTapeAtCellsChecked
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    Tape Bool :=
  match remaining with
  | [] => { left := leftRev, head := none, right := [] }
  | b :: rest =>
      { left := leftRev, head := some b,
        right := List.append (rest.map some) [none] }

def appendRightLastTapeAtCells
    (leftRev : List (Option Bool)) (b0 b1 b2 b3 : Bool) :
    Tape Bool :=
  { left :=
      List.append [some b2, some b1, some b0] leftRev
    head := some b3
    right := [] }

 /-- {name}`appendScanTapeAtCells_of_bits` characterizes a scan safety phase. -/
theorem appendScanTapeAtCells_of_bits
    (leftRev remaining : Word Bool) :
    appendScanTapeAtCells (leftRev.map some) remaining =
      MachineDescription.appendRightScanTape leftRev remaining := by
  cases remaining <;> rfl

 /-- {name}`appendRightLastTapeAtCells_of_bits` describes append/fold behavior used by later composition. -/
theorem appendRightLastTapeAtCells_of_bits
    (leftRev : Word Bool) (b0 b1 b2 b3 : Bool) :
    appendRightLastTapeAtCells
        (leftRev.map some) b0 b1 b2 b3 =
      appendRightLastTape leftRev b0 b1 b2 b3 := by
  simp [appendRightLastTapeAtCells,
    appendRightLastTape]

 /-- {name}`appendFixedFourBitsLastDescription_step_scan_nonempty_atCells` characterizes a scan safety phase. -/
theorem appendFixedFourBitsLastDescription_step_scan_nonempty_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (b : Bool) (rest : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).stepConfig
        { state := 0
          tape := appendScanTapeAtCells leftRev (b :: rest) } =
      some
        { state := 0
          tape := appendScanTapeAtCells
            (some b :: leftRev) rest } := by
  cases b <;>
    cases rest <;>
      simp [AppendFixedFourBitsLastDescription,
        appendScanTapeAtCells,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]

 /-- {name}`appendFixedFourBitsLastDescription_step_scan_nonempty_atCellsChecked` characterizes a scan safety phase. -/
theorem appendFixedFourBitsLastDescription_step_scan_nonempty_atCellsChecked
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (b : Bool) (rest : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).stepConfig
        { state := 0
          tape := appendScanTapeAtCellsChecked leftRev (b :: rest) } =
      some
        { state := 0
          tape := appendScanTapeAtCellsChecked
            (some b :: leftRev) rest } := by
  cases b <;>
    cases rest <;>
      simp [AppendFixedFourBitsLastDescription,
        appendScanTapeAtCellsChecked,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]

 /-- {name}`appendFixedFourBitsLastDescription_run_scan_atCells` states the corresponding theorem run form. -/
theorem appendFixedFourBitsLastDescription_run_scan_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        remaining.length
        { state := 0
          tape := appendScanTapeAtCells leftRev remaining } =
      { state := 0
        tape :=
          appendScanTapeAtCells
            (List.append (remaining.reverse.map some) leftRev) [] } := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons b rest ih =>
      simp [MachineDescription.runConfig,
        appendFixedFourBitsLastDescription_step_scan_nonempty_atCells,
        ih, List.append_assoc]

 /-- {name}`appendFixedFourBitsLastDescription_run_scan_atCellsChecked` states the corresponding theorem run form. -/
theorem appendFixedFourBitsLastDescription_run_scan_atCellsChecked
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        remaining.length
        { state := 0
          tape := appendScanTapeAtCellsChecked leftRev remaining } =
      { state := 0
        tape :=
          appendScanTapeAtCells
            (List.append (remaining.reverse.map some) leftRev) [] } := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig, appendScanTapeAtCellsChecked,
        appendScanTapeAtCells]
  | cons b rest ih =>
      simp [MachineDescription.runConfig,
        appendFixedFourBitsLastDescription_step_scan_nonempty_atCellsChecked,
        ih, List.append_assoc]

 /-- {name}`appendFixedFourBitsLastDescription_run_write_atCells` states the corresponding theorem run form. -/
theorem appendFixedFourBitsLastDescription_run_write_atCells
    (b0 b1 b2 b3 : Bool) (leftRev : List (Option Bool)) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig 5
        { state := 0
          tape := appendScanTapeAtCells leftRev [] } =
      { state := 5
        tape :=
          appendRightLastTapeAtCells
            leftRev b0 b1 b2 b3 } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [AppendFixedFourBitsLastDescription,
      appendScanTapeAtCells,
      appendRightLastTapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

 /-- {name}`appendFixedFourBitsLastDescription_run_from_scan_atCells` states the corresponding theorem run form. -/
theorem appendFixedFourBitsLastDescription_run_from_scan_atCells
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        (remaining.length + 5)
        { state := 0
          tape := appendScanTapeAtCells leftRev remaining } =
      { state := 5
        tape :=
          appendRightLastTapeAtCells
            (List.append (remaining.reverse.map some) leftRev)
            b0 b1 b2 b3 } := by
  rw [MachineDescription.runConfig_add]
  rw [appendFixedFourBitsLastDescription_run_scan_atCells]
  exact appendFixedFourBitsLastDescription_run_write_atCells
    b0 b1 b2 b3 _

 /-- {name}`appendFixedFourBitsLastDescription_run_from_scan_atCellsChecked` states the corresponding theorem run form. -/
theorem appendFixedFourBitsLastDescription_run_from_scan_atCellsChecked
    (b0 b1 b2 b3 : Bool)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendFixedFourBitsLastDescription b0 b1 b2 b3).runConfig
        (remaining.length + 5)
        { state := 0
          tape := appendScanTapeAtCellsChecked leftRev remaining } =
      { state := 5
        tape :=
          appendRightLastTapeAtCells
            (List.append (remaining.reverse.map some) leftRev)
            b0 b1 b2 b3 } := by
  rw [MachineDescription.runConfig_add]
  rw [appendFixedFourBitsLastDescription_run_scan_atCellsChecked]
  exact appendFixedFourBitsLastDescription_run_write_atCells
    b0 b1 b2 b3 _

 /-- {name}`writeMarkedTransitionPrefixDescription_handoff_to_append` describes append/fold behavior used by later composition. -/
theorem writeMarkedTransitionPrefixDescription_handoff_to_append
    (b : Bool) (rest : Word Bool) :
    Tape.move Direction.right
        (tapeAtCells [some false]
          (List.append [none, some false, some true]
            (some b :: rest.map some))) =
      appendScanTapeAtCells
        [none, some false] (false :: true :: b :: rest) := by
  cases b <;>
    cases rest <;>
      simp [tapeAtCells, appendScanTapeAtCells,
        Tape.move, Tape.moveRight]

 /-- {name}`writeMarkedTransitionPrefixDescription_handoff_to_append_checked` describes append/fold behavior used by later composition. -/
theorem writeMarkedTransitionPrefixDescription_handoff_to_append_checked
    (b : Bool) (rest : Word Bool) :
    Tape.move Direction.right
        (tapeAtCells [some false]
          (List.append [none, some false, some true]
            (List.append (some b :: rest.map some) [none]))) =
      appendScanTapeAtCellsChecked
        [none, some false] (false :: true :: b :: rest) := by
  cases b <;>
    cases rest <;>
      simp [tapeAtCells, appendScanTapeAtCellsChecked,
        Tape.move, Tape.moveRight]

def AppendCodeSymbolLastDescription
    (symbol : MachineCodeSymbol) : MachineDescription :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      AppendFixedFourBitsLastDescription b0 b1 b2 b3
  | _ => MachineDescription.ExactIdentityDescription

def appendCodeSymbolLastTape
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) : Tape Bool :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      appendRightLastTape leftRev b0 b1 b2 b3
  | _ => Tape.input leftRev.reverse

 /-- {name}`appendCodeSymbolLastDescription_start` describes append/fold behavior used by later composition. -/
theorem appendCodeSymbolLastDescription_start
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription symbol).start = 0 := by
  cases symbol <;> rfl

 /-- {name}`appendCodeSymbolLastDescription_halt` describes append/fold behavior used by later composition. -/
theorem appendCodeSymbolLastDescription_halt
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription symbol).halt = 5 := by
  cases symbol <;> rfl

 /-- {name}`appendCodeSymbolLastDescription_wellFormed` describes append/fold behavior used by later composition. -/
theorem appendCodeSymbolLastDescription_wellFormed
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription symbol).WellFormed := by
  cases symbol <;>
    exact appendFixedFourBitsLastDescription_wellFormed _ _ _ _

 /-- {name}`appendCodeSymbolLastDescription_haltTransitionFree` describes append/fold behavior used by later composition. -/
theorem appendCodeSymbolLastDescription_haltTransitionFree
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription
      symbol).HaltTransitionFree := by
  cases symbol <;>
    exact
      appendFixedFourBitsLastDescription_haltTransitionFree
        _ _ _ _

 /-- {name}`appendCodeSymbolLastDescription_run_from_scan` states the corresponding theorem run form. -/
theorem appendCodeSymbolLastDescription_run_from_scan
    (symbol : MachineCodeSymbol)
    (leftRev remaining : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).runConfig
        (remaining.length + 5)
        { state := 0
          tape := MachineDescription.appendRightScanTape leftRev remaining } =
      { state := 5
        tape :=
          appendCodeSymbolLastTape
            (List.append remaining.reverse leftRev) symbol } := by
  cases symbol <;>
    rw [MachineDescription.runConfig_add] <;>
    simp [AppendCodeSymbolLastDescription,
      appendCodeSymbolLastTape,
      MachineDescription.encodeCodeSymbolAsInput,
      appendFixedFourBitsLastDescription_run_scan,
      appendFixedFourBitsLastDescription_run_write]

 /-- {name}`appendCodeSymbolLastDescription_run_halt` states the corresponding theorem run form. -/
theorem appendCodeSymbolLastDescription_run_halt
    (symbol : MachineCodeSymbol) (w : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).runConfig
        (w.length + 5)
        ((AppendCodeSymbolLastDescription symbol).initial w) =
      { state := 5
        tape := appendCodeSymbolLastTape w.reverse symbol } := by
  cases symbol <;>
    simpa [AppendCodeSymbolLastDescription,
      appendCodeSymbolLastTape,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsLastDescription_run_halt
        _ _ _ _ w

 /-- {name}`appendCodeSymbolLastTape_move_right` describes append/fold behavior used by later composition. -/
theorem appendCodeSymbolLastTape_move_right
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) :
    Tape.move Direction.right
        (appendCodeSymbolLastTape leftRev symbol) =
      MachineDescription.appendRightScanTape
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          leftRev) [] := by
  cases symbol <;>
    simp [appendCodeSymbolLastTape,
      appendRightLastTape,
      MachineDescription.encodeCodeSymbolAsInput,
      MachineDescription.appendRightScanTape, Tape.move, Tape.moveRight]

 /-- {name}`appendCodeSymbolLastDescription_haltsWithTape` describes append/fold behavior used by later composition. -/
theorem appendCodeSymbolLastDescription_haltsWithTape
    (symbol : MachineCodeSymbol) (w : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).HaltsWithTape
        w (appendCodeSymbolLastTape w.reverse symbol) := by
  exists w.length + 5
  constructor
  · rw [appendCodeSymbolLastDescription_run_halt]
    cases symbol <;> rfl
  · rw [appendCodeSymbolLastDescription_run_halt]

def AppendCodeWordLastDescription :
    Word MachineCodeSymbol -> MachineDescription
  | [] => MachineDescription.ExactIdentityDescription
  | symbol :: [] => AppendCodeSymbolLastDescription symbol
  | symbol :: next :: rest =>
      MachineDescription.seqSubroutine
        (AppendCodeSymbolLastDescription symbol)
        (AppendCodeWordLastDescription (next :: rest))
        Direction.right

def appendCodeWordLastTape
    (leftRev : Word Bool) :
    Word MachineCodeSymbol -> Tape Bool
  | [] => MachineDescription.appendRightScanTape leftRev []
  | symbol :: [] => appendCodeSymbolLastTape leftRev symbol
  | symbol :: next :: rest =>
      appendCodeWordLastTape
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          leftRev)
        (next :: rest)

 /-- {name}`appendCodeSymbolLastDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem appendCodeSymbolLastDescription_subroutineReady
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolLastDescription symbol).SubroutineReady :=
  ⟨appendCodeSymbolLastDescription_wellFormed symbol,
    appendCodeSymbolLastDescription_haltTransitionFree symbol⟩

 /-- {name}`appendCodeWordLastDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem appendCodeWordLastDescription_subroutineReady :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        (AppendCodeWordLastDescription code).SubroutineReady
  | [], h => False.elim (h rfl)
  | symbol :: [], _ =>
      appendCodeSymbolLastDescription_subroutineReady symbol
  | symbol :: next :: rest, _ =>
      MachineDescription.seqSubroutine_subroutineReady
        (appendCodeSymbolLastDescription_subroutineReady symbol)
        (appendCodeWordLastDescription_subroutineReady
          (next :: rest) (by intro h; cases h))

 /-- {name}`appendCodeWordLastDescription_run_from_scan` states the corresponding theorem run form. -/
theorem appendCodeWordLastDescription_run_from_scan :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall leftRev remaining : Word Bool,
          exists n : Nat,
            (AppendCodeWordLastDescription code).runConfig n
                { state := (AppendCodeWordLastDescription code).start
                  tape :=
                    MachineDescription.appendRightScanTape
                      leftRev remaining } =
              { state := (AppendCodeWordLastDescription code).halt
                tape :=
                  appendCodeWordLastTape
                    (List.append remaining.reverse leftRev) code }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro leftRev remaining
      refine ⟨remaining.length + 5, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTape,
        appendCodeSymbolLastDescription_start,
        appendCodeSymbolLastDescription_halt] using
        appendCodeSymbolLastDescription_run_from_scan
          symbol leftRev remaining
  | symbol :: next :: rest, _ => by
      intro leftRev remaining
      let A := AppendCodeSymbolLastDescription symbol
      let B := AppendCodeWordLastDescription (next :: rest)
      let Tmid :=
        appendCodeSymbolLastTape
          (List.append remaining.reverse leftRev) symbol
      let leftAfterSymbol :=
        List.append
          (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
          (List.append remaining.reverse leftRev)
      have hAready : A.SubroutineReady := by
        exact appendCodeSymbolLastDescription_subroutineReady symbol
      have hBready : B.SubroutineReady := by
        exact
          appendCodeWordLastDescription_subroutineReady
            (next :: rest) (by intro h; cases h)
      have hArun :
          A.runConfig (remaining.length + 5)
              { state := A.start
                tape :=
                  MachineDescription.appendRightScanTape leftRev remaining } =
            { state := A.halt, tape := Tmid } := by
        simpa [A, Tmid,
          appendCodeSymbolLastDescription_start,
          appendCodeSymbolLastDescription_halt] using
          appendCodeSymbolLastDescription_run_from_scan
            symbol leftRev remaining
      have hBReach :
          exists nB : Nat,
            B.runConfig nB
                { state := B.start
                  tape := Tape.move Direction.right Tmid } =
              { state := B.halt
                tape :=
                  appendCodeWordLastTape
                    leftAfterSymbol (next :: rest) } := by
        rcases
            appendCodeWordLastDescription_run_from_scan
              (next :: rest) (by intro h; cases h)
              leftAfterSymbol ([] : Word Bool) with
          ⟨nB, hB⟩
        refine ⟨nB, ?_⟩
        simpa [B, Tmid, leftAfterSymbol,
          appendCodeSymbolLastTape_move_right] using hB
      rcases
          MachineDescription.seqSubroutine_reaches_of_runConfig_eq
            (A := A) (B := B) (handoffMove := Direction.right)
            hAready hBready hArun hBReach with
        ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTape, A, B, Tmid, leftAfterSymbol] using hn

 /-- {name}`appendCodeWordLastDescription_run_halt` states the corresponding theorem run form. -/
theorem appendCodeWordLastDescription_run_halt
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) :
    exists n : Nat,
      (AppendCodeWordLastDescription code).runConfig n
          ((AppendCodeWordLastDescription code).initial w) =
        { state := (AppendCodeWordLastDescription code).halt
          tape := appendCodeWordLastTape w.reverse code } := by
  rcases
      appendCodeWordLastDescription_run_from_scan
        code hcode ([] : Word Bool) w with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MachineDescription.initial,
    MachineDescription.appendRightScanTape_nil_eq_input] using hn

 /-- {name}`appendCodeWordLastDescription_haltsWithTape` describes append/fold behavior used by later composition. -/
theorem appendCodeWordLastDescription_haltsWithTape
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) :
    (AppendCodeWordLastDescription code).HaltsWithTape
      w (appendCodeWordLastTape w.reverse code) := by
  rcases appendCodeWordLastDescription_run_halt
      code hcode w with
    ⟨n, hn⟩
  exact ⟨n, by
    constructor
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.state hn
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.tape hn⟩

def appendCodeSymbolLastTapeAtCells
    (leftRev : List (Option Bool))
    (symbol : MachineCodeSymbol) : Tape Bool :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      appendRightLastTapeAtCells leftRev b0 b1 b2 b3
  | _ => appendScanTapeAtCells leftRev []

 /-- {name}`appendCodeSymbolLastTapeAtCells_of_bits` describes append/fold behavior used by later composition. -/
theorem appendCodeSymbolLastTapeAtCells_of_bits
    (leftRev : Word Bool) (symbol : MachineCodeSymbol) :
    appendCodeSymbolLastTapeAtCells
        (leftRev.map some) symbol =
      appendCodeSymbolLastTape leftRev symbol := by
  cases symbol <;>
    simp [appendCodeSymbolLastTapeAtCells,
      appendCodeSymbolLastTape,
      appendRightLastTapeAtCells_of_bits,
      MachineDescription.encodeCodeSymbolAsInput]

 /-- {name}`appendCodeSymbolLastDescription_run_from_scan_atCells` states the corresponding theorem run form. -/
theorem appendCodeSymbolLastDescription_run_from_scan_atCells
    (symbol : MachineCodeSymbol)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).runConfig
        (remaining.length + 5)
        { state := 0
          tape := appendScanTapeAtCells leftRev remaining } =
      { state := 5
        tape :=
          appendCodeSymbolLastTapeAtCells
            (List.append (remaining.reverse.map some) leftRev) symbol } := by
  cases symbol <;>
    simpa [AppendCodeSymbolLastDescription,
      appendCodeSymbolLastTapeAtCells,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsLastDescription_run_from_scan_atCells
        _ _ _ _ leftRev remaining

 /-- {name}`appendCodeSymbolLastDescription_run_from_scan_atCellsChecked` states the corresponding theorem run form. -/
theorem appendCodeSymbolLastDescription_run_from_scan_atCellsChecked
    (symbol : MachineCodeSymbol)
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    (AppendCodeSymbolLastDescription symbol).runConfig
        (remaining.length + 5)
        { state := 0
          tape := appendScanTapeAtCellsChecked leftRev remaining } =
      { state := 5
        tape :=
          appendCodeSymbolLastTapeAtCells
            (List.append (remaining.reverse.map some) leftRev) symbol } := by
  cases symbol <;>
    simpa [AppendCodeSymbolLastDescription,
      appendCodeSymbolLastTapeAtCells,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsLastDescription_run_from_scan_atCellsChecked
        _ _ _ _ leftRev remaining

 /-- {name}`appendCodeSymbolLastTapeAtCells_move_right` describes append/fold behavior used by later composition. -/
theorem appendCodeSymbolLastTapeAtCells_move_right
    (leftRev : List (Option Bool)) (symbol : MachineCodeSymbol) :
    Tape.move Direction.right
        (appendCodeSymbolLastTapeAtCells leftRev symbol) =
      appendScanTapeAtCells
        (List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          leftRev) [] := by
  cases symbol <;>
    simp [appendCodeSymbolLastTapeAtCells,
      appendRightLastTapeAtCells,
      appendScanTapeAtCells,
      MachineDescription.encodeCodeSymbolAsInput,
      Tape.move, Tape.moveRight]

def appendCodeWordLastTapeAtCells
    (leftRev : List (Option Bool)) :
    Word MachineCodeSymbol -> Tape Bool
  | [] => appendScanTapeAtCells leftRev []
  | symbol :: [] => appendCodeSymbolLastTapeAtCells leftRev symbol
  | symbol :: next :: rest =>
      appendCodeWordLastTapeAtCells
        (List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          leftRev)
        (next :: rest)

 /-- {name}`appendCodeWordLastTapeAtCells_of_bits` describes append/fold behavior used by later composition. -/
theorem appendCodeWordLastTapeAtCells_of_bits :
    forall code : Word MachineCodeSymbol,
    forall leftRev : Word Bool,
      appendCodeWordLastTapeAtCells
          (leftRev.map some) code =
        appendCodeWordLastTape leftRev code
  | [], leftRev => by
      simp [appendCodeWordLastTapeAtCells,
        appendCodeWordLastTape,
        appendScanTapeAtCells_of_bits]
  | symbol :: [], leftRev => by
      simp [appendCodeWordLastTapeAtCells,
        appendCodeWordLastTape,
        appendCodeSymbolLastTapeAtCells_of_bits]
  | symbol :: next :: rest, leftRev => by
      change
        appendCodeWordLastTapeAtCells
            (List.append
              ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
              (leftRev.map some))
            (next :: rest) =
          appendCodeWordLastTape
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            (next :: rest)
      have hmap :
          List.append
              ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
              (leftRev.map some) =
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
              leftRev).map some := by
        simp
      rw [hmap]
      exact
        appendCodeWordLastTapeAtCells_of_bits
          (next :: rest)
          (List.append
            (MachineDescription.encodeCodeSymbolAsInput symbol).reverse
            leftRev)

 /-- {name}`appendCodeWordLastDescription_run_from_scan_atCells` states the corresponding theorem run form. -/
theorem appendCodeWordLastDescription_run_from_scan_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall leftRev : List (Option Bool),
        forall remaining : Word Bool,
          exists n : Nat,
            (AppendCodeWordLastDescription code).runConfig n
                { state := (AppendCodeWordLastDescription code).start
                  tape :=
                    appendScanTapeAtCells
                      leftRev remaining } =
              { state := (AppendCodeWordLastDescription code).halt
                tape :=
                  appendCodeWordLastTapeAtCells
                    (List.append (remaining.reverse.map some) leftRev) code }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro leftRev remaining
      refine ⟨remaining.length + 5, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTapeAtCells,
        appendCodeSymbolLastDescription_start,
        appendCodeSymbolLastDescription_halt] using
        appendCodeSymbolLastDescription_run_from_scan_atCells
          symbol leftRev remaining
  | symbol :: next :: rest, _ => by
      intro leftRev remaining
      let A := AppendCodeSymbolLastDescription symbol
      let B := AppendCodeWordLastDescription (next :: rest)
      let Tmid :=
        appendCodeSymbolLastTapeAtCells
          (List.append (remaining.reverse.map some) leftRev) symbol
      let leftAfterSymbol :=
        List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          (List.append (remaining.reverse.map some) leftRev)
      have hAready : A.SubroutineReady := by
        exact appendCodeSymbolLastDescription_subroutineReady symbol
      have hBready : B.SubroutineReady := by
        exact
          appendCodeWordLastDescription_subroutineReady
            (next :: rest) (by intro h; cases h)
      have hArun :
          A.runConfig (remaining.length + 5)
              { state := A.start
                tape :=
                  appendScanTapeAtCells leftRev remaining } =
            { state := A.halt, tape := Tmid } := by
        simpa [A, Tmid,
          appendCodeSymbolLastDescription_start,
          appendCodeSymbolLastDescription_halt] using
          appendCodeSymbolLastDescription_run_from_scan_atCells
            symbol leftRev remaining
      have hBReach :
          exists nB : Nat,
            B.runConfig nB
                { state := B.start
                  tape := Tape.move Direction.right Tmid } =
              { state := B.halt
                tape :=
                  appendCodeWordLastTapeAtCells
                    leftAfterSymbol (next :: rest) } := by
        rcases
            appendCodeWordLastDescription_run_from_scan_atCells
              (next :: rest) (by intro h; cases h)
              leftAfterSymbol ([] : Word Bool) with
          ⟨nB, hB⟩
        refine ⟨nB, ?_⟩
        simpa [B, Tmid, leftAfterSymbol,
          appendCodeSymbolLastTapeAtCells_move_right] using hB
      rcases
          MachineDescription.seqSubroutine_reaches_of_runConfig_eq
            (A := A) (B := B) (handoffMove := Direction.right)
            hAready hBready hArun hBReach with
        ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTapeAtCells, A, B, Tmid,
        leftAfterSymbol] using hn

 /-- {name}`appendCodeWordLastDescription_run_from_scan_atCellsChecked` states the corresponding theorem run form. -/
theorem appendCodeWordLastDescription_run_from_scan_atCellsChecked :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall leftRev : List (Option Bool),
        forall remaining : Word Bool,
          exists n : Nat,
            (AppendCodeWordLastDescription code).runConfig n
                { state := (AppendCodeWordLastDescription code).start
                  tape :=
                    appendScanTapeAtCellsChecked
                      leftRev remaining } =
              { state := (AppendCodeWordLastDescription code).halt
                tape :=
                  appendCodeWordLastTapeAtCells
                    (List.append (remaining.reverse.map some) leftRev) code }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro leftRev remaining
      refine ⟨remaining.length + 5, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTapeAtCells,
        appendCodeSymbolLastDescription_start,
        appendCodeSymbolLastDescription_halt] using
        appendCodeSymbolLastDescription_run_from_scan_atCellsChecked
          symbol leftRev remaining
  | symbol :: next :: rest, _ => by
      intro leftRev remaining
      let A := AppendCodeSymbolLastDescription symbol
      let B := AppendCodeWordLastDescription (next :: rest)
      let Tmid :=
        appendCodeSymbolLastTapeAtCells
          (List.append (remaining.reverse.map some) leftRev) symbol
      let leftAfterSymbol :=
        List.append
          ((MachineDescription.encodeCodeSymbolAsInput symbol).reverse.map some)
          (List.append (remaining.reverse.map some) leftRev)
      have hAready : A.SubroutineReady := by
        exact appendCodeSymbolLastDescription_subroutineReady symbol
      have hBready : B.SubroutineReady := by
        exact
          appendCodeWordLastDescription_subroutineReady
            (next :: rest) (by intro h; cases h)
      have hArun :
          A.runConfig (remaining.length + 5)
              { state := A.start
                tape :=
                  appendScanTapeAtCellsChecked leftRev remaining } =
            { state := A.halt, tape := Tmid } := by
        simpa [A, Tmid,
          appendCodeSymbolLastDescription_start,
          appendCodeSymbolLastDescription_halt] using
          appendCodeSymbolLastDescription_run_from_scan_atCellsChecked
            symbol leftRev remaining
      have hBReach :
          exists nB : Nat,
            B.runConfig nB
                { state := B.start
                  tape := Tape.move Direction.right Tmid } =
              { state := B.halt
                tape :=
                  appendCodeWordLastTapeAtCells
                    leftAfterSymbol (next :: rest) } := by
        rcases
            appendCodeWordLastDescription_run_from_scan_atCells
              (next :: rest) (by intro h; cases h)
              leftAfterSymbol ([] : Word Bool) with
          ⟨nB, hB⟩
        refine ⟨nB, ?_⟩
        simpa [B, Tmid, leftAfterSymbol,
          appendCodeSymbolLastTapeAtCells_move_right] using hB
      rcases
          MachineDescription.seqSubroutine_reaches_of_runConfig_eq
            (A := A) (B := B) (handoffMove := Direction.right)
            hAready hBready hArun hBReach with
        ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [AppendCodeWordLastDescription,
        appendCodeWordLastTapeAtCells, A, B, Tmid,
        leftAfterSymbol] using hn

def MarkedPrefixThenAppendCodeWordLastDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    WriteMarkedTransitionPrefixDescription
    (AppendCodeWordLastDescription code)
    Direction.right

 /-- {name}`markedPrefixThenAppendCodeWordLastDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem markedPrefixThenAppendCodeWordLastDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (MarkedPrefixThenAppendCodeWordLastDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    writeMarkedTransitionPrefixDescription_subroutineReady
    (appendCodeWordLastDescription_subroutineReady code hcode)

 /-- {name}`markedPrefixThenAppendCodeWordLastDescription_run` captures the core lemma for this local construction. -/
theorem markedPrefixThenAppendCodeWordLastDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists n : Nat,
      (MarkedPrefixThenAppendCodeWordLastDescription code).runConfig n
          ((MarkedPrefixThenAppendCodeWordLastDescription
            code).initial (b :: rest)) =
        { state :=
            (MarkedPrefixThenAppendCodeWordLastDescription code).halt
          tape :=
            appendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: b :: rest).reverse.map some)
                [none, some false])
              code } := by
  let A := WriteMarkedTransitionPrefixDescription
  let B := AppendCodeWordLastDescription code
  let Tmid :=
    tapeAtCells [some false]
      (List.append [none, some false, some true]
        (some b :: rest.map some))
  have hAready : A.SubroutineReady := by
    exact writeMarkedTransitionPrefixDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact appendCodeWordLastDescription_subroutineReady code hcode
  have hArun :
      A.runConfig 5
          { state := A.start
            tape := Tape.input (b :: rest) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, MachineDescription.initial,
      config, tapeAtCells, Tape.input] using
      writeMarkedTransitionPrefixDescription_run
        b (rest.map some)
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt
            tape :=
              appendCodeWordLastTapeAtCells
                (List.append
                  ((false :: true :: b :: rest).reverse.map some)
                  [none, some false])
                code } := by
    rcases
        appendCodeWordLastDescription_run_from_scan_atCells
          code hcode [none, some false] (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid,
      writeMarkedTransitionPrefixDescription_handoff_to_append] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MarkedPrefixThenAppendCodeWordLastDescription,
    MachineDescription.initial, A, B] using hn

 /-- {name}`markedPrefixThenAppendCodeWordLastDescription_run_checked` states the corresponding theorem run form. -/
theorem markedPrefixThenAppendCodeWordLastDescription_run_checked
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists n : Nat,
      (MarkedPrefixThenAppendCodeWordLastDescription code).runConfig n
          { state := (MarkedPrefixThenAppendCodeWordLastDescription code).start
            tape :=
              tapeAtCells []
                (List.append (some b :: rest.map some) [none]) } =
        { state :=
            (MarkedPrefixThenAppendCodeWordLastDescription code).halt
          tape :=
            appendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: b :: rest).reverse.map some)
                [none, some false])
              code } := by
  let A := WriteMarkedTransitionPrefixDescription
  let B := AppendCodeWordLastDescription code
  let Tmid :=
    tapeAtCells [some false]
      (List.append [none, some false, some true]
        (List.append (some b :: rest.map some) [none]))
  have hAready : A.SubroutineReady := by
    exact writeMarkedTransitionPrefixDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact appendCodeWordLastDescription_subroutineReady code hcode
  have hArun :
      A.runConfig 5
          { state := A.start
            tape :=
              tapeAtCells []
                (List.append (some b :: rest.map some) [none]) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, config, tapeAtCells] using
      writeMarkedTransitionPrefixDescription_run
        b (List.append (rest.map some) [none])
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt
            tape :=
              appendCodeWordLastTapeAtCells
                (List.append
                  ((false :: true :: b :: rest).reverse.map some)
                  [none, some false])
                code } := by
    rcases
        appendCodeWordLastDescription_run_from_scan_atCellsChecked
          code hcode [none, some false] (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid,
      writeMarkedTransitionPrefixDescription_handoff_to_append_checked] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MarkedPrefixThenAppendCodeWordLastDescription,
    A, B] using hn

 /-- {name}`encodeNat_ne_nil` captures the core lemma for this local construction. -/
theorem encodeNat_ne_nil (n : Nat) :
    MachineDescription.encodeNat n ≠ [] := by
  cases n <;> simp [MachineDescription.encodeNat]

def AppendNatLastDescription
    (n : Nat) : MachineDescription :=
  AppendCodeWordLastDescription
    (MachineDescription.encodeNat n)

def appendNatLastTape
    (leftRev : Word Bool) (n : Nat) : Tape Bool :=
  appendCodeWordLastTape leftRev
    (MachineDescription.encodeNat n)

 /-- {name}`appendNatLastDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem appendNatLastDescription_subroutineReady
    (n : Nat) :
    (AppendNatLastDescription n).SubroutineReady :=
  appendCodeWordLastDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

 /-- {name}`appendNatLastDescription_run_from_scan` states the corresponding theorem run form. -/
theorem appendNatLastDescription_run_from_scan
    (n : Nat) (leftRev remaining : Word Bool) :
    exists steps : Nat,
      (AppendNatLastDescription n).runConfig steps
          { state := (AppendNatLastDescription n).start
            tape := MachineDescription.appendRightScanTape leftRev remaining } =
        { state := (AppendNatLastDescription n).halt
          tape :=
            appendNatLastTape
              (List.append remaining.reverse leftRev) n } := by
  simpa [AppendNatLastDescription,
    appendNatLastTape] using
    appendCodeWordLastDescription_run_from_scan
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      leftRev remaining

 /-- {name}`appendNatLastDescription_haltsWithTape` describes append/fold behavior used by later composition. -/
theorem appendNatLastDescription_haltsWithTape
    (n : Nat) (w : Word Bool) :
    (AppendNatLastDescription n).HaltsWithTape
      w (appendNatLastTape w.reverse n) := by
  simpa [AppendNatLastDescription,
    appendNatLastTape] using
    appendCodeWordLastDescription_haltsWithTape
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      w

def MarkedPrefixThenAppendNatLastDescription
    (n : Nat) : MachineDescription :=
  MarkedPrefixThenAppendCodeWordLastDescription
    (MachineDescription.encodeNat n)

 /-- {name}`markedPrefixThenAppendNatLastDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem markedPrefixThenAppendNatLastDescription_subroutineReady
    (n : Nat) :
    (MarkedPrefixThenAppendNatLastDescription
      n).SubroutineReady :=
  markedPrefixThenAppendCodeWordLastDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

 /-- {name}`markedPrefixThenAppendNatLastDescription_run` captures the core lemma for this local construction. -/
theorem markedPrefixThenAppendNatLastDescription_run
    (n : Nat) (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (MarkedPrefixThenAppendNatLastDescription n).runConfig steps
          ((MarkedPrefixThenAppendNatLastDescription
            n).initial (b :: rest)) =
        { state :=
            (MarkedPrefixThenAppendNatLastDescription n).halt
          tape :=
            appendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: b :: rest).reverse.map some)
                [none, some false])
              (MachineDescription.encodeNat n) } := by
  simpa [MarkedPrefixThenAppendNatLastDescription] using
    markedPrefixThenAppendCodeWordLastDescription_run
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      b rest


end DovetailInitialLayoutInitializer
end Computability
end FoC
