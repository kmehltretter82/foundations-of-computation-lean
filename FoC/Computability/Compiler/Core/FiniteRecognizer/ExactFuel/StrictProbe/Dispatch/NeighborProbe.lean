import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.MarkedPrefixRestorer
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Neighbor-emptiness probe

Finite left/right neighbor probes over protected exact-fuel frames, returning a
Boolean emptiness result while restoring the serialized frame.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.NeighborProbe

open Languages

open SerializedFieldComposer

/- Rewind from an interior serialized-field cursor without assuming that the
cursor is already at the blank just beyond the complete word. -/
namespace PrefixRewind

def scanTape
    (remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := crossed.map some }
  | current :: tail =>
      SerializedShift.cursorTape tail (current :: crossed)

def scanConfig
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control where
  state := .scan
  tape := scanTape remainingRev crossed

def gateTape (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.right (scanTape [] word)

def gateConfig (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control where
  state := .gate
  tape := gateTape word

theorem start_step
    (leftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    RewindWord.machine.stepConfig
        { state := RewindWord.Control.start
          tape := SerializedShift.cursorTape leftRev (first :: rest) } =
      some (scanConfig leftRev (first :: rest)) := by
  cases leftRev <;> cases rest <;> rfl

theorem scan_step
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    RewindWord.machine.stepConfig
        (scanConfig (current :: remainingRev) crossed) =
      some (scanConfig remainingRev (current :: crossed)) := by
  cases remainingRev <;> cases crossed <;> rfl

theorem scan_finish (crossed : Word MachineCodeSymbol) :
    RewindWord.machine.stepConfig (scanConfig [] crossed) =
      some (gateConfig crossed) := by
  cases crossed <;> rfl

theorem scan_run_exact
    (remainingRev crossed : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact? (remainingRev.length + 1)
        (scanConfig remainingRev crossed) =
      some (gateConfig (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact scan_finish crossed
  | cons current remainingRev ih =>
      change
        RewindWord.machine.runConfigExact? ((remainingRev.length + 1) + 1)
            (scanConfig (current :: remainingRev) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_exact
    (leftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact? (leftRev.length + 2)
        { state := RewindWord.Control.start
          tape := SerializedShift.cursorTape leftRev (first :: rest) } =
      some
        (gateConfig (List.append leftRev.reverse (first :: rest))) := by
  change
    RewindWord.machine.runConfigExact? ((leftRev.length + 1) + 1)
        { state := RewindWord.Control.start
          tape := SerializedShift.cursorTape leftRev (first :: rest) } = _
  rw [TuringMachine.runConfigExact?]
  rw [start_step]
  simp only
  simpa using scan_run_exact leftRev (first :: rest)

theorem gateTape_equiv_input (word : Word MachineCodeSymbol) :
    Tape.Equiv (gateTape word) (Tape.input word) := by
  cases word <;>
    simp [gateTape, scanTape, Tape.move, Tape.moveRight,
      Tape.input, Tape.blank, Tape.Equiv, Tape.dropTrailingNone]

end PrefixRewind

def expected {stateCount : Nat}
    (direction : Direction) (L : Layout stateCount) : Bool :=
  match direction with
  | .left =>
      match L.left with
      | [] => true
      | _ :: _ => false
  | .right =>
      match L.right with
      | [] => true
      | _ :: _ => false

theorem left_word_eq_protectedWord {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    List.append (LeftPrepend.leftCountPrefix L)
        (afterStateWord L callerData) =
      Frame.protectedWord L callerData := by
  rw [protectedWord_eq_statePrefix_stateSuffix]
  unfold LeftPrepend.leftCountPrefix statePrefix stateSuffix
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

theorem marked_right_word_eq {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    List.append
        (Dispatch.RightFirstCell.markedRightCountLeftRev L).reverse
        (HeadLocator.afterHeadWord L callerData) =
      Edits.MarkedPrefixRestorer.markedDeletedWord
        L L.right callerData := by
  have hcountBase :
      (HeadLocator.countBaseLeftRev L).reverse =
        List.append (statePrefix L)
          (MachineDescription.encodeNat L.state.val) := by
    rw [← HeadLocator.scannedStateLeft_eq_countBase L]
    simp [statePrefix, List.reverse_append]
  have hmarkedBase :
      (Dispatch.RightFieldLocator.HeadDecoder.markedCountBaseLeftRev
        L).reverse =
        List.append (statePrefix L)
          (List.append (MachineDescription.encodeNat L.state.val)
            (List.append (HeadLocator.transitionMarkers L.left.length)
              [MachineCodeSymbol.blank])) := by
    unfold Dispatch.RightFieldLocator.HeadDecoder.markedCountBaseLeftRev
    calc
      (MachineCodeSymbol.blank ::
          List.append (HeadLocator.transitionMarkers L.left.length)
            (HeadLocator.countBaseLeftRev L) :
            Word MachineCodeSymbol).reverse =
          List.append (HeadLocator.countBaseLeftRev L).reverse
            (List.append
              (HeadLocator.transitionMarkers L.left.length).reverse
              [MachineCodeSymbol.blank]) := by
            simp [List.reverse_append, List.append_assoc]
      _ = List.append (statePrefix L)
          (List.append (MachineDescription.encodeNat L.state.val)
            (List.append (HeadLocator.transitionMarkers L.left.length)
              [MachineCodeSymbol.blank])) := by
            rw [hcountBase,
              Edits.MarkedPrefixRestorer.transitionMarkers_reverse]
            simp [List.append_assoc]
  have hmarkedPrefix :
      (Dispatch.RightFirstCell.markedRightCountLeftRev L).reverse =
        Edits.MarkedPrefixRestorer.markedPrefix L := by
    unfold Dispatch.RightFirstCell.markedRightCountLeftRev
    calc
      (List.append (optionalCellWord L.head).reverse
          (List.append (HeadLocator.markedCellsWord L.left).reverse
            (Dispatch.RightFieldLocator.HeadDecoder.markedCountBaseLeftRev
              L)) : Word MachineCodeSymbol).reverse =
          List.append
            (Dispatch.RightFieldLocator.HeadDecoder.markedCountBaseLeftRev
              L).reverse
            (List.append (HeadLocator.markedCellsWord L.left)
              (optionalCellWord L.head)) := by
            simp [List.reverse_append, List.append_assoc]
      _ = Edits.MarkedPrefixRestorer.markedPrefix L := by
            rw [hmarkedBase]
            unfold Edits.MarkedPrefixRestorer.markedPrefix
            simp [List.append_assoc]
  rw [Edits.MarkedPrefixRestorer.markedDeletedWord_decomp]
  rw [Dispatch.RightFirstCell.afterHeadWord_eq_rightCountPayload]
  rw [show RightPrepend.rightPayloadSuffix L callerData =
      MoveRightNonempty.afterFirstRightCell L.right callerData by rfl]
  rw [hmarkedPrefix]

theorem restored_right_word_eq_protectedWord {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    List.append (RightPrepend.rightCountPrefix L)
        (MachineDescription.encodeNatAppend L.right.length
          (MoveRightNonempty.afterFirstRightCell L.right callerData)) =
      Frame.protectedWord L callerData := by
  rw [RightPrepend.protectedWord_decomp]
  unfold RightPrepend.rightPayloadPrefix
    RightPrepend.rightPayloadSuffix
    MoveRightNonempty.afterFirstRightCell
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

inductive Control where
  | leftLocate (inner : FieldLocator.Control)
  | leftRewind (isEmpty : Bool) (inner : RewindWord.Control)
  | rightLocate (inner : Dispatch.RightFieldLocator.OuterLocator.Control)
  | rightMarkedRewind (isEmpty : Bool) (inner : RewindWord.Control)
  | rightRestore (isEmpty : Bool)
      (inner : Edits.MarkedPrefixRestorer.Control)
  | rightCleanRewind (isEmpty : Bool) (inner : RewindWord.Control)
  | done (isEmpty : Bool)
deriving DecidableEq

namespace Control

def elems : List Control :=
  (FieldLocator.Control.elems.map Control.leftLocate) ++
  (RewindWord.Control.elems.map (Control.leftRewind false)) ++
  (RewindWord.Control.elems.map (Control.leftRewind true)) ++
  (Dispatch.RightFieldLocator.OuterLocator.Control.elems.map
    Control.rightLocate) ++
  (RewindWord.Control.elems.map (Control.rightMarkedRewind false)) ++
  (RewindWord.Control.elems.map (Control.rightMarkedRewind true)) ++
  (Edits.MarkedPrefixRestorer.Control.elems.map
    (Control.rightRestore false)) ++
  (Edits.MarkedPrefixRestorer.Control.elems.map
    (Control.rightRestore true)) ++
  (RewindWord.Control.elems.map (Control.rightCleanRewind false)) ++
  (RewindWord.Control.elems.map (Control.rightCleanRewind true)) ++
  [.done false, .done true]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | leftLocate inner =>
        have h := FieldLocator.Control.finite.complete inner
        change inner ∈ FieldLocator.Control.elems at h
        simp [elems, h]
    | leftRewind result inner =>
        have h := RewindWord.Control.finite.complete inner
        change inner ∈ RewindWord.Control.elems at h
        cases result <;> simp [elems, h]
    | rightLocate inner =>
        have h :=
          Dispatch.RightFieldLocator.OuterLocator.Control.finite.complete
            inner
        change inner ∈
          Dispatch.RightFieldLocator.OuterLocator.Control.elems at h
        simp [elems, h]
    | rightMarkedRewind result inner =>
        have h := RewindWord.Control.finite.complete inner
        change inner ∈ RewindWord.Control.elems at h
        cases result <;> simp [elems, h]
    | rightRestore result inner =>
        have h := Edits.MarkedPrefixRestorer.Control.finite.complete inner
        change inner ∈ Edits.MarkedPrefixRestorer.Control.elems at h
        cases result <;> simp [elems, h]
    | rightCleanRewind result inner =>
        have h := RewindWord.Control.finite.complete inner
        change inner ∈ RewindWord.Control.elems at h
        cases result <;> simp [elems, h]
    | done result =>
        cases result <;> simp [elems]

end Control

def leftRewindEmbed (result : Bool) : RewindWord.Control -> Control
  | .gate => .done result
  | inner => .leftRewind result inner

def rightMarkedRewindEmbed (result : Bool) :
    RewindWord.Control -> Control
  | .gate => .rightRestore result .header
  | inner => .rightMarkedRewind result inner

def rightRestoreEmbed (result : Bool) :
    Edits.MarkedPrefixRestorer.Control -> Control
  | .gate => .rightCleanRewind result .start
  | inner => .rightRestore result inner

def rightCleanRewindEmbed (result : Bool) :
    RewindWord.Control -> Control
  | .gate => .done result
  | inner => .rightCleanRewind result inner

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .leftLocate .gate, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left,
        .leftRewind false .scan)
  | .leftLocate .gate, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left,
        .leftRewind true .scan)
  | .leftLocate inner, read =>
      match FieldLocator.transition .leftCount inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .leftLocate target)
  | .leftRewind result inner, read =>
      match RewindWord.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, leftRewindEmbed result target)
  | .rightLocate (.decode (.gate _)), some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left,
        .rightMarkedRewind false .scan)
  | .rightLocate (.decode (.gate _)), some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left,
        .rightMarkedRewind true .scan)
  | .rightLocate inner, read =>
      match Dispatch.RightFieldLocator.OuterLocator.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rightLocate target)
  | .rightMarkedRewind result inner, read =>
      match RewindWord.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, rightMarkedRewindEmbed result target)
  | .rightRestore result inner, read =>
      match Edits.MarkedPrefixRestorer.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, rightRestoreEmbed result target)
  | .rightCleanRewind result inner, read =>
      match RewindWord.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, rightCleanRewindEmbed result target)
  | .done _, _ => none

def machine (direction : Direction) :
    TuringMachine MachineCodeSymbol Control where
  start :=
    match direction with
    | .left => .leftLocate (FieldLocator.machine .leftCount).start
    | .right =>
        .rightLocate
          Dispatch.RightFieldLocator.OuterLocator.machine.start
  halt := .done false
  transition := transition
  statesFinite := Control.finite

def leftLocateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      FieldLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.leftLocate c

def leftRewindConfig (result : Bool)
    (c : TuringMachine.Configuration MachineCodeSymbol RewindWord.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (leftRewindEmbed result) c

def rightLocateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.RightFieldLocator.OuterLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.rightLocate c

def rightMarkedRewindConfig (result : Bool)
    (c : TuringMachine.Configuration MachineCodeSymbol RewindWord.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (rightMarkedRewindEmbed result) c

def rightRestoreConfig (result : Bool)
    (c : TuringMachine.Configuration MachineCodeSymbol
      Edits.MarkedPrefixRestorer.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (rightRestoreEmbed result) c

def rightCleanRewindConfig (result : Bool)
    (c : TuringMachine.Configuration MachineCodeSymbol RewindWord.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (rightCleanRewindEmbed result) c

theorem leftLocate_step_of_some
    (direction : Direction)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      FieldLocator.Control)
    (hstep : (FieldLocator.machine .leftCount).stepConfig c = some d) :
    (machine direction).stepConfig (leftLocateConfig c) =
      some (leftLocateConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FieldLocator.machine] at hstep
      cases htransition :
          FieldLocator.transition .leftCount inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, move, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate =>
              simp [FieldLocator.transition] at htransition
          | header | fuel | state | leftCount =>
              simp [machine, transition, leftLocateConfig,
                TuringMachine.PhaseEmbedding.liftConfig,
                htransition]

theorem rightLocate_step_of_some
    (direction : Direction)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.RightFieldLocator.OuterLocator.Control)
    (hstep :
      Dispatch.RightFieldLocator.OuterLocator.machine.stepConfig c =
        some d) :
    (machine direction).stepConfig (rightLocateConfig c) =
      some (rightLocateConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Dispatch.RightFieldLocator.OuterLocator.machine] at hstep
      cases htransition :
          Dispatch.RightFieldLocator.OuterLocator.transition inner
            (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, move, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | locate inner | locateReturn | counter inner | counterReturn =>
              simp [machine, transition, rightLocateConfig,
                TuringMachine.PhaseEmbedding.liftConfig,
                htransition]
          | decode inner =>
              cases inner with
              | decode count =>
                  simp [machine, transition, rightLocateConfig,
                    TuringMachine.PhaseEmbedding.liftConfig,
                    htransition]
              | gate head =>
                  simp [Dispatch.RightFieldLocator.OuterLocator.transition,
                    Dispatch.RightFieldLocator.HeadDecoder.transition]
                    at htransition

theorem leftRewind_step_of_some
    (direction : Direction) (result : Bool)
    (c d : TuringMachine.Configuration MachineCodeSymbol RewindWord.Control)
    (hstep : RewindWord.machine.stepConfig c = some d) :
    (machine direction).stepConfig (leftRewindConfig result c) =
      some (leftRewindConfig result d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [RewindWord.machine] at hstep
      cases htransition : RewindWord.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, move, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate => simp [RewindWord.transition] at htransition
          | start | scan =>
              simp [machine, transition, leftRewindConfig,
                leftRewindEmbed,
                TuringMachine.PhaseEmbedding.liftConfig,
                htransition]

theorem rightMarkedRewind_step_of_some
    (direction : Direction) (result : Bool)
    (c d : TuringMachine.Configuration MachineCodeSymbol RewindWord.Control)
    (hstep : RewindWord.machine.stepConfig c = some d) :
    (machine direction).stepConfig (rightMarkedRewindConfig result c) =
      some (rightMarkedRewindConfig result d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [RewindWord.machine] at hstep
      cases htransition : RewindWord.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, move, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate => simp [RewindWord.transition] at htransition
          | start | scan =>
              simp [machine, transition, rightMarkedRewindConfig,
                rightMarkedRewindEmbed,
                TuringMachine.PhaseEmbedding.liftConfig,
                htransition]

theorem rightRestore_step_of_some
    (direction : Direction) (result : Bool)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Edits.MarkedPrefixRestorer.Control)
    (hstep : Edits.MarkedPrefixRestorer.machine.stepConfig c = some d) :
    (machine direction).stepConfig (rightRestoreConfig result c) =
      some (rightRestoreConfig result d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Edits.MarkedPrefixRestorer.machine] at hstep
      cases htransition :
          Edits.MarkedPrefixRestorer.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, move, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate =>
              simp [Edits.MarkedPrefixRestorer.transition] at htransition
          | header | fuel | state | restoreCount | restoreCells =>
              simp [machine, transition, rightRestoreConfig,
                rightRestoreEmbed,
                TuringMachine.PhaseEmbedding.liftConfig,
                htransition]

theorem rightCleanRewind_step_of_some
    (direction : Direction) (result : Bool)
    (c d : TuringMachine.Configuration MachineCodeSymbol RewindWord.Control)
    (hstep : RewindWord.machine.stepConfig c = some d) :
    (machine direction).stepConfig (rightCleanRewindConfig result c) =
      some (rightCleanRewindConfig result d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [RewindWord.machine] at hstep
      cases htransition : RewindWord.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, move, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate => simp [RewindWord.transition] at htransition
          | start | scan =>
              simp [machine, transition, rightCleanRewindConfig,
                rightCleanRewindEmbed,
                TuringMachine.PhaseEmbedding.liftConfig,
                htransition]

theorem leftLocate_run_of_some
    (direction : Direction)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FieldLocator.Control}
    (hrun : (FieldLocator.machine .leftCount).runConfigExact?
      steps source = some target) :
    (machine direction).runConfigExact? steps (leftLocateConfig source) =
      some (leftLocateConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.leftLocate
  · intro c d hstep
    simpa [leftLocateConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        leftLocate_step_of_some direction c d hstep
  · simpa [leftLocateConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem rightLocate_run_of_some
    (direction : Direction)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.RightFieldLocator.OuterLocator.Control}
    (hrun :
      Dispatch.RightFieldLocator.OuterLocator.machine.runConfigExact?
        steps source = some target) :
    (machine direction).runConfigExact? steps (rightLocateConfig source) =
      some (rightLocateConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.rightLocate
  · intro c d hstep
    simpa [rightLocateConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        rightLocate_step_of_some direction c d hstep
  · simpa [rightLocateConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem leftRewind_run_of_some
    (direction : Direction) (result : Bool)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RewindWord.Control}
    (hrun : RewindWord.machine.runConfigExact? steps source = some target) :
    (machine direction).runConfigExact? steps
        (leftRewindConfig result source) =
      some (leftRewindConfig result target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (leftRewindEmbed result)
  · intro c d hstep
    simpa [leftRewindConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        leftRewind_step_of_some direction result c d hstep
  · simpa [leftRewindConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem rightMarkedRewind_run_of_some
    (direction : Direction) (result : Bool)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RewindWord.Control}
    (hrun : RewindWord.machine.runConfigExact? steps source = some target) :
    (machine direction).runConfigExact? steps
        (rightMarkedRewindConfig result source) =
      some (rightMarkedRewindConfig result target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (rightMarkedRewindEmbed result)
  · intro c d hstep
    simpa [rightMarkedRewindConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        rightMarkedRewind_step_of_some direction result c d hstep
  · simpa [rightMarkedRewindConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem rightRestore_run_of_some
    (direction : Direction) (result : Bool)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Edits.MarkedPrefixRestorer.Control}
    (hrun : Edits.MarkedPrefixRestorer.machine.runConfigExact?
      steps source = some target) :
    (machine direction).runConfigExact? steps
        (rightRestoreConfig result source) =
      some (rightRestoreConfig result target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (rightRestoreEmbed result)
  · intro c d hstep
    simpa [rightRestoreConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        rightRestore_step_of_some direction result c d hstep
  · simpa [rightRestoreConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem rightCleanRewind_run_of_some
    (direction : Direction) (result : Bool)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RewindWord.Control}
    (hrun : RewindWord.machine.runConfigExact? steps source = some target) :
    (machine direction).runConfigExact? steps
        (rightCleanRewindConfig result source) =
      some (rightCleanRewindConfig result target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (rightCleanRewindEmbed result)
  · intro c d hstep
    simpa [rightCleanRewindConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        rightCleanRewind_step_of_some direction result c d hstep
  · simpa [rightCleanRewindConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem left_tick_handoff
    (leftRev rest : Word MachineCodeSymbol) :
    (machine .left).runConfigExact? 1
        (leftLocateConfig
          (FieldLocator.config .gate leftRev
            (MachineCodeSymbol.tick :: rest))) =
      some
        (leftRewindConfig false
          (PrefixRewind.scanConfig leftRev
            (MachineCodeSymbol.tick :: rest))) := by
  cases leftRev <;> cases rest <;> rfl

theorem left_done_handoff
    (leftRev rest : Word MachineCodeSymbol) :
    (machine .left).runConfigExact? 1
        (leftLocateConfig
          (FieldLocator.config .gate leftRev
            (MachineCodeSymbol.done :: rest))) =
      some
        (leftRewindConfig true
          (PrefixRewind.scanConfig leftRev
            (MachineCodeSymbol.done :: rest))) := by
  cases leftRev <;> cases rest <;> rfl

theorem right_tick_handoff
    (head : Option MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol) :
    (machine .right).runConfigExact? 1
        (rightLocateConfig
          (Dispatch.RightFieldLocator.OuterLocator.decodeConfig
            (Dispatch.RightFieldLocator.HeadDecoder.config (.gate head)
              leftRev (MachineCodeSymbol.tick :: rest)))) =
      some
        (rightMarkedRewindConfig false
          (PrefixRewind.scanConfig leftRev
            (MachineCodeSymbol.tick :: rest))) := by
  cases leftRev <;> cases rest <;> rfl

theorem right_done_handoff
    (head : Option MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol) :
    (machine .right).runConfigExact? 1
        (rightLocateConfig
          (Dispatch.RightFieldLocator.OuterLocator.decodeConfig
            (Dispatch.RightFieldLocator.HeadDecoder.config (.gate head)
              leftRev (MachineCodeSymbol.done :: rest)))) =
      some
        (rightMarkedRewindConfig true
          (PrefixRewind.scanConfig leftRev
            (MachineCodeSymbol.done :: rest))) := by
  cases leftRev <;> cases rest <;> rfl

theorem runConfigExact_trans
    (direction : Direction)
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol Control}
    (hab : (machine direction).runConfigExact? first a = some b)
    (hbc : (machine direction).runConfigExact? second b = some c) :
    (machine direction).runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)

def leftSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  FieldLocator.leftCountSteps L +
    (1 + ((LeftPrepend.leftCountPrefix L).reverse.length + 1))

theorem left_run_exact {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      (machine .left).runConfigExact? (leftSteps L)
          { state := (machine .left).start
            tape := Tape.input (Frame.protectedWord L callerData) } =
        some endpoint ∧
      endpoint.state = .done (expected .left L) ∧
      Tape.Equiv (Tape.input (Frame.protectedWord L callerData))
        endpoint.tape := by
  have hlocate := leftLocate_run_of_some .left
    (FieldLocator.locate_leftCount_exact L callerData)
  have hsource :
      leftLocateConfig (FieldLocator.startConfig L callerData) =
        { state := (machine .left).start
          tape := Tape.input (Frame.protectedWord L callerData) } := by
    rfl
  rw [hsource] at hlocate
  cases hleft : L.left with
  | nil =>
      have hcountShape :
          afterStateWord L callerData =
            MachineCodeSymbol.done :: headSuffix L callerData := by
        rw [HeadLocator.afterStateWord_eq_count_payload, hleft]
        rfl
      rw [hcountShape] at hlocate
      have hhandoff := left_done_handoff
        (LeftPrepend.leftCountPrefix L).reverse (headSuffix L callerData)
      have hscanInner := PrefixRewind.scan_run_exact
        (LeftPrepend.leftCountPrefix L).reverse
        (MachineCodeSymbol.done :: headSuffix L callerData)
      have hscan := leftRewind_run_of_some .left true hscanInner
      have hpref := runConfigExact_trans .left hlocate hhandoff
      have hrun := runConfigExact_trans .left hpref hscan
      have hword :
          List.append
              (LeftPrepend.leftCountPrefix L).reverse.reverse
              (MachineCodeSymbol.done :: headSuffix L callerData) =
            Frame.protectedWord L callerData := by
        rw [List.reverse_reverse, ← hcountShape]
        exact left_word_eq_protectedWord L callerData
      refine
        ⟨leftRewindConfig true
          (PrefixRewind.gateConfig
            (List.append
              (LeftPrepend.leftCountPrefix L).reverse.reverse
              (MachineCodeSymbol.done :: headSuffix L callerData))),
          ?_, ?_, ?_⟩
      · simpa [leftSteps, Nat.add_assoc] using hrun
      · simp [leftRewindConfig, leftRewindEmbed, expected, hleft,
          TuringMachine.PhaseEmbedding.liftConfig,
          PrefixRewind.gateConfig]
      · rw [hword]
        exact Tape.Equiv.symm
          (PrefixRewind.gateTape_equiv_input
            (Frame.protectedWord L callerData))
  | cons first remaining =>
      have hcountShape :
          afterStateWord L callerData =
            MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend remaining.length
                (HeadLocator.cellsPayloadAppend (first :: remaining)
                  (headSuffix L callerData)) := by
        rw [HeadLocator.afterStateWord_eq_count_payload, hleft]
        rfl
      let rest : Word MachineCodeSymbol :=
        MachineDescription.encodeNatAppend remaining.length
          (HeadLocator.cellsPayloadAppend (first :: remaining)
            (headSuffix L callerData))
      rw [hcountShape] at hlocate
      have hhandoff := left_tick_handoff
        (LeftPrepend.leftCountPrefix L).reverse rest
      have hscanInner := PrefixRewind.scan_run_exact
        (LeftPrepend.leftCountPrefix L).reverse
        (MachineCodeSymbol.tick :: rest)
      have hscan := leftRewind_run_of_some .left false hscanInner
      have hpref := runConfigExact_trans .left hlocate hhandoff
      have hrun := runConfigExact_trans .left hpref hscan
      have hword :
          List.append
              (LeftPrepend.leftCountPrefix L).reverse.reverse
              (MachineCodeSymbol.tick :: rest) =
            Frame.protectedWord L callerData := by
        have htail :
            (MachineCodeSymbol.tick :: rest : Word MachineCodeSymbol) =
              afterStateWord L callerData := by
          unfold rest
          exact hcountShape.symm
        calc
          (List.append
              (LeftPrepend.leftCountPrefix L).reverse.reverse
              (MachineCodeSymbol.tick :: rest) :
              Word MachineCodeSymbol) =
              List.append (LeftPrepend.leftCountPrefix L)
                (MachineCodeSymbol.tick :: rest) := by
                rw [List.reverse_reverse]
          _ = List.append (LeftPrepend.leftCountPrefix L)
              (afterStateWord L callerData) := by
                exact congrArg
                  (fun tail : Word MachineCodeSymbol =>
                    List.append (LeftPrepend.leftCountPrefix L) tail)
                  htail
          _ = Frame.protectedWord L callerData :=
            left_word_eq_protectedWord L callerData
      refine
        ⟨leftRewindConfig false
          (PrefixRewind.gateConfig
            (List.append
              (LeftPrepend.leftCountPrefix L).reverse.reverse
              (MachineCodeSymbol.tick :: rest))),
          ?_, ?_, ?_⟩
      · simpa [leftSteps, Nat.add_assoc] using hrun
      · simp [leftRewindConfig, leftRewindEmbed, expected, hleft,
          TuringMachine.PhaseEmbedding.liftConfig,
          PrefixRewind.gateConfig]
      · rw [hword]
        exact Tape.Equiv.symm
          (PrefixRewind.gateTape_equiv_input
            (Frame.protectedWord L callerData))

def rightSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  (((Dispatch.RightFieldLocator.OuterLocator.runSteps L + 1) +
      (Dispatch.RightFirstCell.markedRightCountLeftRev L).length + 1) +
    Edits.MarkedPrefixRestorer.runSteps L) +
  ((RightPrepend.rightCountPrefix L).reverse.length + 2)

theorem right_run_of_shape {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (result : Bool) (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (hshape : HeadLocator.afterHeadWord L callerData = first :: rest)
    (hhandoff :
      (machine .right).runConfigExact? 1
          (rightLocateConfig
            (Dispatch.RightFieldLocator.OuterLocator.decodeConfig
              (Dispatch.RightFieldLocator.HeadDecoder.config
                (.gate L.head)
                (Dispatch.RightFirstCell.markedRightCountLeftRev L)
                (first :: rest)))) =
        some
          (rightMarkedRewindConfig result
            (PrefixRewind.scanConfig
              (Dispatch.RightFirstCell.markedRightCountLeftRev L)
              (first :: rest)))) :
    exists endpoint,
      (machine .right).runConfigExact? (rightSteps L)
          { state := (machine .right).start
            tape := Tape.input (Frame.protectedWord L callerData) } =
        some endpoint ∧
      endpoint.state = .done result ∧
      Tape.Equiv (Tape.input (Frame.protectedWord L callerData))
        endpoint.tape := by
  have hlocate := rightLocate_run_of_some .right
    (Dispatch.RightFieldLocator.OuterLocator.run_exact L callerData)
  have hsource :
      rightLocateConfig
          (Dispatch.RightFieldLocator.OuterLocator.locateConfig
            (FieldLocator.startConfig L callerData)) =
        { state := (machine .right).start
          tape := Tape.input (Frame.protectedWord L callerData) } := by
    rfl
  rw [hsource] at hlocate
  have hlocateTarget :
      rightLocateConfig
          (Dispatch.RightFieldLocator.OuterLocator.decodeConfig
            (Dispatch.RightFieldLocator.HeadDecoder.rightCountConfig
              L callerData)) =
        rightLocateConfig
          (Dispatch.RightFieldLocator.OuterLocator.decodeConfig
            (Dispatch.RightFieldLocator.HeadDecoder.config
              (.gate L.head)
              (Dispatch.RightFirstCell.markedRightCountLeftRev L)
              (first :: rest))) := by
    unfold Dispatch.RightFieldLocator.HeadDecoder.rightCountConfig
      Dispatch.RightFirstCell.markedRightCountLeftRev
    rw [hshape]
  rw [hlocateTarget] at hlocate
  have hmarkedScanInner := PrefixRewind.scan_run_exact
    (Dispatch.RightFirstCell.markedRightCountLeftRev L)
    (first :: rest)
  have hmarkedScan :=
    rightMarkedRewind_run_of_some .right result hmarkedScanInner
  have hprefOne := runConfigExact_trans .right hlocate hhandoff
  have hprefTwo := runConfigExact_trans .right hprefOne hmarkedScan
  have hmarkedWord := marked_right_word_eq L callerData
  rw [hshape] at hmarkedWord
  have hmarkedGateEquiv :
      Tape.Equiv
        (Tape.input
          (Edits.MarkedPrefixRestorer.markedDeletedWord
            L L.right callerData))
        (PrefixRewind.gateConfig
          (List.append
            (Dispatch.RightFirstCell.markedRightCountLeftRev L).reverse
            (first :: rest))).tape := by
    rw [← hmarkedWord]
    exact Tape.Equiv.symm
      (PrefixRewind.gateTape_equiv_input
        (List.append
          (Dispatch.RightFirstCell.markedRightCountLeftRev L).reverse
          (first :: rest)))
  have hrestoreSourceEquiv :
      Tape.Equiv
        (Edits.MarkedPrefixRestorer.sourceConfig
          L L.right callerData).tape
        (PrefixRewind.gateConfig
          (List.append
            (Dispatch.RightFirstCell.markedRightCountLeftRev L).reverse
            (first :: rest))).tape := by
    have hsourceTape :
        (Edits.MarkedPrefixRestorer.sourceConfig
          L L.right callerData).tape =
          Tape.input
            (Edits.MarkedPrefixRestorer.markedDeletedWord
              L L.right callerData) := by
      unfold Edits.MarkedPrefixRestorer.sourceConfig
        Edits.MarkedPrefixRestorer.config
      rw [Edits.MarkedPrefixRestorer.markedDeletedWord_decomp]
      unfold Edits.MarkedPrefixRestorer.markedPrefix statePrefix
      rfl
    rw [hsourceTape]
    exact hmarkedGateEquiv
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (Edits.MarkedPrefixRestorer.run_exact L L.right callerData)
        hrestoreSourceEquiv with
    ⟨restoreEndpoint, hrestoreInner, hrestoreState, hrestoreTape⟩
  have hrestore := rightRestore_run_of_some .right result hrestoreInner
  have hmarkedTarget :
      rightMarkedRewindConfig result
          (PrefixRewind.gateConfig
            (List.append
              (Dispatch.RightFirstCell.markedRightCountLeftRev L).reverse
              (first :: rest))) =
        rightRestoreConfig result
          { state := Edits.MarkedPrefixRestorer.Control.header
            tape :=
              (PrefixRewind.gateConfig
                (List.append
                  (Dispatch.RightFirstCell.markedRightCountLeftRev
                    L).reverse
                  (first :: rest))).tape } := by
    rfl
  rw [hmarkedTarget] at hprefTwo
  have hrestoreSource :
      rightRestoreConfig result
          { state :=
              (Edits.MarkedPrefixRestorer.sourceConfig
                L L.right callerData).state
            tape :=
              (PrefixRewind.gateConfig
                (List.append
                  (Dispatch.RightFirstCell.markedRightCountLeftRev
                    L).reverse
                  (first :: rest))).tape } =
        rightRestoreConfig result
          { state := Edits.MarkedPrefixRestorer.Control.header
            tape :=
              (PrefixRewind.gateConfig
                (List.append
                  (Dispatch.RightFirstCell.markedRightCountLeftRev
                    L).reverse
                  (first :: rest))).tape } := by
    rfl
  rw [hrestoreSource] at hrestore
  have hcleanRest :
      MachineDescription.encodeNatAppend L.right.length
          (MoveRightNonempty.afterFirstRightCell L.right callerData) =
        first :: rest := by
    rw [← hshape]
    symm
    simpa [RightPrepend.rightPayloadSuffix,
      MoveRightNonempty.afterFirstRightCell] using
      Dispatch.RightFirstCell.afterHeadWord_eq_rightCountPayload
        L callerData
  have hcleanSourceEquiv :
      Tape.Equiv
        (SerializedShift.cursorTape
          (RightPrepend.rightCountPrefix L).reverse (first :: rest))
        restoreEndpoint.tape := by
    rw [← hcleanRest]
    exact hrestoreTape
  have hcleanInner := PrefixRewind.run_exact
    (RightPrepend.rightCountPrefix L).reverse first rest
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hcleanInner hcleanSourceEquiv with
    ⟨rewindEndpoint, hrewindInner, hrewindState, hrewindTape⟩
  have hclean :=
    rightCleanRewind_run_of_some .right result hrewindInner
  have hrestoreTarget :
      rightRestoreConfig result restoreEndpoint =
        rightCleanRewindConfig result
          { state := RewindWord.Control.start
            tape := restoreEndpoint.tape } := by
    cases restoreEndpoint with
    | mk actualState tape =>
        simp only at hrestoreState
        subst actualState
        rfl
  rw [hrestoreTarget] at hrestore
  have hprefThree := runConfigExact_trans .right hprefTwo hrestore
  have hrun := runConfigExact_trans .right hprefThree hclean
  have hfinalWord :
      List.append
          (RightPrepend.rightCountPrefix L).reverse.reverse
          (first :: rest) =
        Frame.protectedWord L callerData := by
    rw [List.reverse_reverse, ← hcleanRest]
    exact restored_right_word_eq_protectedWord L callerData
  refine ⟨rightCleanRewindConfig result rewindEndpoint, ?_, ?_, ?_⟩
  · simpa [rightSteps, Nat.add_assoc] using hrun
  · change rightCleanRewindEmbed result rewindEndpoint.state = .done result
    rw [hrewindState]
    rfl
  · have hgate :
        Tape.Equiv
          (Tape.input (Frame.protectedWord L callerData))
          (PrefixRewind.gateConfig
            (List.append
              (RightPrepend.rightCountPrefix L).reverse.reverse
              (first :: rest))).tape := by
        rw [hfinalWord]
        exact Tape.Equiv.symm
          (PrefixRewind.gateTape_equiv_input
            (Frame.protectedWord L callerData))
    exact Tape.Equiv.trans hgate hrewindTape

theorem right_run_exact {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      (machine .right).runConfigExact? (rightSteps L)
          { state := (machine .right).start
            tape := Tape.input (Frame.protectedWord L callerData) } =
        some endpoint ∧
      endpoint.state = .done (expected .right L) ∧
      Tape.Equiv (Tape.input (Frame.protectedWord L callerData))
        endpoint.tape := by
  cases hright : L.right with
  | nil =>
      have hshape :
          HeadLocator.afterHeadWord L callerData =
            MachineCodeSymbol.done ::
              RightPrepend.rightPayloadSuffix L callerData := by
        rw [Dispatch.RightFirstCell.afterHeadWord_eq_rightCountPayload,
          hright]
        rfl
      have hhandoff := right_done_handoff L.head
        (Dispatch.RightFirstCell.markedRightCountLeftRev L)
        (RightPrepend.rightPayloadSuffix L callerData)
      rcases right_run_of_shape L callerData true MachineCodeSymbol.done
          (RightPrepend.rightPayloadSuffix L callerData)
          hshape hhandoff with
        ⟨endpoint, hrun, hstate, htape⟩
      refine ⟨endpoint, hrun, ?_, htape⟩
      simpa [expected, hright] using hstate
  | cons first remaining =>
      let rest : Word MachineCodeSymbol :=
        MachineDescription.encodeNatAppend remaining.length
          (RightPrepend.rightPayloadSuffix L callerData)
      have hshape :
          HeadLocator.afterHeadWord L callerData =
            MachineCodeSymbol.tick :: rest := by
        rw [Dispatch.RightFirstCell.afterHeadWord_eq_rightCountPayload,
          hright]
        rfl
      have hhandoff := right_tick_handoff L.head
        (Dispatch.RightFirstCell.markedRightCountLeftRev L) rest
      rcases right_run_of_shape L callerData false MachineCodeSymbol.tick
          rest hshape hhandoff with
        ⟨endpoint, hrun, hstate, htape⟩
      refine ⟨endpoint, hrun, ?_, htape⟩
      simpa [expected, hright] using hstate

def runSteps {stateCount : Nat}
    (direction : Direction) (L : Layout stateCount) : Nat :=
  match direction with
  | .left => leftSteps L
  | .right => rightSteps L

/-- Inspect the selected neighboring-list count and return to the same
canonical protected frame, carrying the Boolean result in the terminal
control. -/
theorem run_exact {stateCount : Nat}
    (direction : Direction) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      (machine direction).runConfigExact? (runSteps direction L)
          { state := (machine direction).start
            tape := Tape.input (Frame.protectedWord L callerData) } =
        some endpoint ∧
      endpoint.state = .done (expected direction L) ∧
      Tape.Equiv (Tape.input (Frame.protectedWord L callerData))
        endpoint.tape := by
  cases direction with
  | left =>
      simpa [runSteps] using left_run_exact L callerData
  | right =>
      simpa [runSteps] using right_run_exact L callerData

/-- The same counted probe run transports across trailing-blank window
padding, which is the form consumed by the cyclic update kernel. -/
theorem run_from_equiv {stateCount : Nat}
    (direction : Direction) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (Frame.protectedWord L callerData)) T) :
    exists endpoint,
      (machine direction).runConfigExact? (runSteps direction L)
          { state := (machine direction).start, tape := T } =
        some endpoint ∧
      endpoint.state = .done (expected direction L) ∧
      Tape.Equiv (Tape.input (Frame.protectedWord L callerData))
        endpoint.tape := by
  rcases run_exact direction L callerData with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, hrun, hstate.trans hcleanState,
    Tape.Equiv.trans hcleanTape htape⟩

end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.NeighborProbe
