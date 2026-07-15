import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Tail

/-!
# Exact-fuel stage-input insertion machinery

Bounded encoded-block insertion and its one-cell composition used by the
nonempty stage-input materializer.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace InitialMaterializer

namespace VariableBlockInsert
def wordsOfLength : Nat -> List (Word MachineCodeSymbol)
  | 0 => [[]]
  | count + 1 =>
      MachineCodeSymbol.finite.elems.flatMap fun symbol =>
        (wordsOfLength count).map (fun rest => symbol :: rest)
theorem wordsOfLength_complete (word : Word MachineCodeSymbol) (count : Nat)
    (hlength : word.length = count) : word ∈ wordsOfLength count := by
  induction count generalizing word with
  | zero =>
      have hword : word = [] := List.eq_nil_of_length_eq_zero hlength
      subst word
      simp [wordsOfLength]
  | succ count ih =>
      cases word with
      | nil => simp at hlength
      | cons symbol rest =>
          simp only [List.length_cons] at hlength
          have hrest : rest.length = count := Nat.add_right_cancel hlength
          apply List.mem_flatMap.mpr
          refine ⟨symbol, MachineCodeSymbol.finite.complete symbol, ?_⟩
          exact List.mem_map.mpr ⟨rest, ih rest hrest, rfl⟩
def bufferWords (capacity : Nat) : List (Word MachineCodeSymbol) :=
  (List.range (capacity + 1)).flatMap wordsOfLength
theorem bufferWords_complete (capacity : Nat) (word : Word MachineCodeSymbol)
    (hlength : word.length ≤ capacity) : word ∈ bufferWords capacity := by
  apply List.mem_flatMap.mpr
  refine ⟨word.length, ?_, wordsOfLength_complete word word.length rfl⟩
  simp
  lia

structure Buffer (capacity : Nat) where
  word : Word MachineCodeSymbol
  length_le : word.length ≤ capacity
deriving DecidableEq
def toBuffer? (capacity : Nat) (word : Word MachineCodeSymbol) : Option (Buffer capacity) :=
  if h : word.length ≤ capacity then some ⟨word, h⟩ else none

namespace Buffer
def elems (capacity : Nat) : List (Buffer capacity) :=
  (bufferWords capacity).filterMap (toBuffer? capacity)
def finite (capacity : Nat) : Foundation.FiniteType (Buffer capacity) where
  elems := elems capacity
  complete := by
    intro buffer
    apply List.mem_filterMap.mpr
    refine ⟨buffer.word, bufferWords_complete capacity buffer.word buffer.length_le, ?_⟩
    simp [toBuffer?, buffer.length_le]
def popPush {capacity : Nat} (buffer : Buffer capacity) (current : MachineCodeSymbol) :
    Option (MachineCodeSymbol × Buffer capacity) :=
  match buffer with
  | ⟨[], _⟩ => none
  | ⟨head :: tail, hlength⟩ =>
      some (head, ⟨List.append tail [current], by
            simpa using hlength⟩)
def pop {capacity : Nat} (buffer : Buffer capacity) : Option (MachineCodeSymbol × Buffer capacity) :=
  match buffer with
  | ⟨[], _⟩ => none
  | ⟨head :: tail, hlength⟩ =>
      some (head, ⟨tail, by
            have hle : tail.length ≤ (head :: tail).length := by
              simp
            exact Nat.le_trans hle hlength⟩)
end Buffer

inductive Control (capacity : Nat) where
  | carry (buffer : Buffer capacity)
  | halt
deriving DecidableEq

namespace Control
def elems (capacity : Nat) : List (Control capacity) :=
  List.append ((Buffer.finite capacity).elems.map Control.carry) [.halt]
def finite (capacity : Nat) : Foundation.FiniteType (Control capacity) where
  elems := elems capacity
  complete := by
    intro control
    cases control with
    | carry buffer =>
        simp [elems]
        exact (Buffer.finite capacity).complete buffer
    | halt => simp [elems]
end Control
def transition {capacity : Nat} : Control capacity -> Option MachineCodeSymbol -> Option
        (Option MachineCodeSymbol × Direction × Control capacity)
  | .carry buffer, some current =>
      match buffer.popPush current with
      | none => none
      | some (written, nextBuffer) =>
          some (some written, Direction.right, .carry nextBuffer)
  | .carry buffer, none =>
      match buffer.pop with
      | none => none
      | some (written, nextBuffer) =>
          if nextBuffer.word = [] then
            some (some written, Direction.right, .halt) else
            some (some written, Direction.right, .carry nextBuffer)
  | .halt, _ => none
def machine (capacity : Nat) (initial : Buffer capacity) : TuringMachine MachineCodeSymbol (Control capacity) where
  start := .carry initial
  halt := .halt
  transition := transition
  statesFinite := Control.finite capacity
def config {capacity : Nat} (buffer : Buffer capacity) (leftRev : Word MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol)) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control capacity) where
  state := .carry buffer
  tape := InsertOneWithBoundary.cursorTape (List.append (leftRev.map some) baseCells) rest
def haltConfig {capacity : Nat} (leftRev : Word MachineCodeSymbol) (baseCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol (Control capacity) where
  state := .halt
  tape :=
    { left := List.append (leftRev.map some) baseCells
      head := none
      right := [] }
def cross {capacity : Nat} : Buffer capacity -> Word MachineCodeSymbol ->
      Word MachineCodeSymbol -> Buffer capacity × Word MachineCodeSymbol
  | buffer, leftRev, [] => (buffer, leftRev)
  | buffer, leftRev, current :: suffix =>
      match buffer.popPush current with
      | none => (buffer, leftRev)
      | some (written, nextBuffer) =>
          cross nextBuffer (written :: leftRev) suffix
theorem step_cons {capacity : Nat} (initial : Buffer capacity)
    (head current : MachineCodeSymbol) (tail leftRev suffix : Word MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (hlength : (head :: tail).length ≤ capacity) : (machine capacity initial).stepConfig
        (config ⟨head :: tail, hlength⟩ leftRev baseCells (current :: suffix)) = some
        (config ⟨List.append tail [current], by simpa using hlength⟩ (head :: leftRev) baseCells suffix) := by
  cases suffix <;> rfl
theorem cross_run_exact {capacity : Nat} (initial buffer : Buffer capacity)
    (leftRev suffix : Word MachineCodeSymbol) (baseCells : List (Option MachineCodeSymbol))
    (hnonempty : buffer.word ≠ []) : (machine capacity initial).runConfigExact? suffix.length
        (config buffer leftRev baseCells suffix) = some (config (cross buffer leftRev suffix).1
          (cross buffer leftRev suffix).2 baseCells []) := by
  induction suffix generalizing buffer leftRev with
  | nil =>
      rfl
  | cons current suffix ih =>
      cases buffer with
      | mk word hlength =>
          cases word with
          | nil => contradiction
          | cons head tail =>
              change (machine capacity initial).runConfigExact? (suffix.length + 1)
                    (config ⟨head :: tail, hlength⟩ leftRev baseCells (current :: suffix)) = _
              rw [TuringMachine.runConfigExact?]
              rw [step_cons]
              simp only
              have hnext : (List.append tail [current] : Word MachineCodeSymbol) ≠ [] := by
                simp
              rw [ih ⟨List.append tail [current], by
                  simpa using hlength⟩ (head :: leftRev) hnext]
              rfl
theorem cross_spec {capacity : Nat} (buffer : Buffer capacity)
    (leftRev suffix : Word MachineCodeSymbol) (hnonempty : buffer.word ≠ []) :
    (cross buffer leftRev suffix).1.word ≠ [] ∧ (cross buffer leftRev suffix).1.word.length = buffer.word.length ∧
      List.append (cross buffer leftRev suffix).2.reverse (cross buffer leftRev suffix).1.word =
        List.append leftRev.reverse (List.append buffer.word suffix) := by
  induction suffix generalizing buffer leftRev with
  | nil =>
      simp [cross, hnonempty]
  | cons current suffix ih =>
      cases buffer with
      | mk word hlength =>
          cases word with
          | nil => contradiction
          | cons head tail =>
              have hnext : (List.append tail [current] : Word MachineCodeSymbol) ≠ [] := by
                simp
              have hspec := ih ⟨List.append tail [current], by
                  simpa using hlength⟩ (head :: leftRev) hnext
              simpa [cross, Buffer.popPush, List.reverse_cons, List.append_assoc] using hspec
theorem flush_last {capacity : Nat} (initial : Buffer capacity) (head : MachineCodeSymbol)
    (leftRev : Word MachineCodeSymbol) (baseCells : List (Option MachineCodeSymbol))
    (hlength : ([head] : Word MachineCodeSymbol).length ≤ capacity) :
    (machine capacity initial).stepConfig (config ⟨[head], hlength⟩ leftRev baseCells []) =
      some (haltConfig (head :: leftRev) baseCells) := by
  rfl
theorem flush_more {capacity : Nat} (initial : Buffer capacity) (head next : MachineCodeSymbol)
    (rest leftRev : Word MachineCodeSymbol) (baseCells : List (Option MachineCodeSymbol))
    (hlength : (head :: next :: rest).length ≤ capacity) :
    (machine capacity initial).stepConfig (config ⟨head :: next :: rest, hlength⟩ leftRev
          baseCells []) = some (config ⟨next :: rest, by
            have hle : (next :: rest).length ≤ (head :: next :: rest).length := by simp
            exact Nat.le_trans hle hlength⟩ (head :: leftRev) baseCells []) := by
  rfl
theorem flush_run_exact {capacity : Nat} (initial : Buffer capacity)
    (head : MachineCodeSymbol) (tail leftRev : Word MachineCodeSymbol) (baseCells : List (Option MachineCodeSymbol))
    (hlength : (head :: tail).length ≤ capacity) : (machine capacity initial).runConfigExact? (head :: tail).length
        (config ⟨head :: tail, hlength⟩ leftRev baseCells []) = some (haltConfig
          (List.append (head :: tail).reverse leftRev) baseCells) := by
  induction tail generalizing head leftRev with
  | nil =>
      change (machine capacity initial).runConfigExact? 1 (config ⟨[head], hlength⟩ leftRev baseCells []) = _
      rw [TuringMachine.runConfigExact?]
      rw [flush_last]
      simp only [TuringMachine.runConfigExact?]
      rfl
  | cons next rest ih =>
      change (machine capacity initial).runConfigExact? ((next :: rest).length + 1)
            (config ⟨head :: next :: rest, hlength⟩ leftRev baseCells []) = _
      rw [TuringMachine.runConfigExact?]
      rw [flush_more]
      simp only
      have htail : (next :: rest).length ≤ capacity := by
        have hle : (next :: rest).length ≤ (head :: next :: rest).length := by simp
        exact Nat.le_trans hle hlength
      rw [ih next (head :: leftRev) htail]
      simp [List.reverse_cons, List.append_assoc]
def finalLeftRev {capacity : Nat} (buffer : Buffer capacity)
    (leftRev suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (cross buffer leftRev suffix).1.word.reverse (cross buffer leftRev suffix).2
theorem run_exact {capacity : Nat} (initial buffer : Buffer capacity)
    (leftRev suffix : Word MachineCodeSymbol) (baseCells : List (Option MachineCodeSymbol))
    (hnonempty : buffer.word ≠ []) : (machine capacity initial).runConfigExact?
        (suffix.length + buffer.word.length) (config buffer leftRev baseCells suffix) = some
        (haltConfig (finalLeftRev buffer leftRev suffix) baseCells) := by
  rw [ExactRun.append]
  rw [cross_run_exact initial buffer leftRev suffix baseCells hnonempty]
  simp only
  have hspec := cross_spec buffer leftRev suffix hnonempty
  cases hcross : cross buffer leftRev suffix with
  | mk finalBuffer finalLeftRev' =>
      simp only [hcross] at hspec
      rcases hspec with ⟨hfinalNonempty, hlength, _hinvariant⟩
      cases finalBuffer with
      | mk finalWord hfinalLength =>
          simp only at hfinalNonempty hlength
          cases finalWord with
          | nil => contradiction
          | cons head tail =>
              rw [← hlength]
              simpa [finalLeftRev, hcross] using flush_run_exact initial head tail finalLeftRev' baseCells hfinalLength
theorem finalLeftRev_reverse {capacity : Nat} (buffer : Buffer capacity)
    (leftRev suffix : Word MachineCodeSymbol) (hnonempty : buffer.word ≠ []) :
    (finalLeftRev buffer leftRev suffix).reverse = List.append leftRev.reverse (List.append buffer.word suffix) := by
  have hspec := (cross_spec buffer leftRev suffix hnonempty).2.2
  simpa [finalLeftRev, List.reverse_append] using hspec
end VariableBlockInsert

namespace BoundedBlockInsert
abbrev Buffer := VariableBlockInsert.Buffer 10
abbrev Control := VariableBlockInsert.Control 10

namespace Control
abbrev halt : Control := VariableBlockInsert.Control.halt
def finite : Foundation.FiniteType Control :=
  VariableBlockInsert.Control.finite 10
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control) :=
  VariableBlockInsert.transition
abbrev machine (initial : Buffer) : TuringMachine MachineCodeSymbol Control :=
  VariableBlockInsert.machine 10 initial
abbrev config (buffer : Buffer) (leftRev : Word MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol)) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  VariableBlockInsert.config buffer leftRev baseCells rest
abbrev haltConfig (leftRev : Word MachineCodeSymbol) (baseCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  VariableBlockInsert.haltConfig (capacity := 10) leftRev baseCells
abbrev finalLeftRev (buffer : Buffer) (leftRev suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  VariableBlockInsert.finalLeftRev buffer leftRev suffix
def cellBuffer (symbol : MachineCodeSymbol) : Buffer :=
  ⟨NonemptyRightRegion.cellWord symbol, NonemptyRightRegion.cellWord_length_le_ten symbol⟩
theorem cellBuffer_nonempty (symbol : MachineCodeSymbol) : (cellBuffer symbol).word ≠ [] :=
  NonemptyRightRegion.cellWord_ne_nil symbol
theorem insertCell_run_exact (symbol : MachineCodeSymbol)
    (leftRev payload : Word MachineCodeSymbol) (baseCells : List (Option MachineCodeSymbol)) :
    (machine (cellBuffer symbol)).runConfigExact? (payload.length + (cellBuffer symbol).word.length)
        (config (cellBuffer symbol) leftRev baseCells payload) = some (haltConfig
          (finalLeftRev (cellBuffer symbol) leftRev payload) baseCells) := by
  exact VariableBlockInsert.run_exact (cellBuffer symbol) (cellBuffer symbol) leftRev payload baseCells
    (cellBuffer_nonempty symbol)
theorem insertedCell_word (symbol : MachineCodeSymbol) (leftRev payload : Word MachineCodeSymbol) :
    (finalLeftRev (cellBuffer symbol) leftRev payload).reverse = List.append leftRev.reverse
        (List.append (NonemptyRightRegion.cellWord symbol) payload) := by
  exact VariableBlockInsert.finalLeftRev_reverse (cellBuffer symbol) leftRev payload (cellBuffer_nonempty symbol)
end BoundedBlockInsert

namespace RightCellInsert
def baseCells (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : List (Option MachineCodeSymbol) :=
  List.append ((MachineDescription.encodeNat processed.length).reverse.map some)
    (some MachineCodeSymbol.tick :: none :: deeperLeft)
def sourceConfig (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol BoundedBlockInsert.Control :=
  BoundedBlockInsert.config (BoundedBlockInsert.cellBuffer current) []
    (baseCells processed deeperLeft) (RightCellPrep.payload processed)
def endpointConfig (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol BoundedBlockInsert.Control :=
  BoundedBlockInsert.haltConfig (BoundedBlockInsert.finalLeftRev
      (BoundedBlockInsert.cellBuffer current) [] (RightCellPrep.payload processed)) (baseCells processed deeperLeft)
def runSteps (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol) : Nat :=
  (RightCellPrep.payload processed).length + (BoundedBlockInsert.cellBuffer current).word.length
theorem run_exact (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : (BoundedBlockInsert.machine
      (BoundedBlockInsert.cellBuffer current)).runConfigExact? (runSteps current processed)
        (sourceConfig current processed deeperLeft) = some (endpointConfig current processed deeperLeft) := by
  exact BoundedBlockInsert.insertCell_run_exact current [] (RightCellPrep.payload processed)
    (baseCells processed deeperLeft)
theorem finalPayloadRev_eq (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol) :
    BoundedBlockInsert.finalLeftRev (BoundedBlockInsert.cellBuffer current) []
        (RightCellPrep.payload processed) = (List.append (NonemptyRightRegion.cellWord current)
        (RightCellPrep.payload processed)).reverse := by
  have hreverse := BoundedBlockInsert.insertedCell_word current
    ([] : Word MachineCodeSymbol) (RightCellPrep.payload processed)
  have hboth := congrArg (fun word : Word MachineCodeSymbol => word.reverse) hreverse
  unfold Languages.Word at hboth ⊢
  simpa using hboth
def encodedRevAfter (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (BoundedBlockInsert.finalLeftRev (BoundedBlockInsert.cellBuffer current) []
      (RightCellPrep.payload processed)) (List.append
      (MachineDescription.encodeNat processed.length).reverse [MachineCodeSymbol.tick])
theorem encodedRevAfter_eq_region_reverse (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol) : encodedRevAfter current processed =
      (NonemptyRightRegion.region (current :: processed)).reverse := by
  rw [show encodedRevAfter current processed = List.append (List.append (NonemptyRightRegion.cellWord current)
          (RightCellPrep.payload processed)).reverse (List.append
          (MachineDescription.encodeNat processed.length).reverse [MachineCodeSymbol.tick]) by
    simp [encodedRevAfter, finalPayloadRev_eq]]
  rw [NonemptyRightRegion.region_cons]
  simp [RightCellPrep.payload, List.reverse_append, List.append_assoc]
theorem endpointTape_eq_separatorStart (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol) (deeperLeft : List (Option MachineCodeSymbol)) :
    (endpointConfig current processed deeperLeft).tape =
      SeparatorRewind.startTapeCells deeperLeft (NonemptyRightRegion.region (current :: processed)).reverse := by
  rw [← encodedRevAfter_eq_region_reverse]
  simp [endpointConfig, BoundedBlockInsert.haltConfig, VariableBlockInsert.haltConfig,
    baseCells, encodedRevAfter, SeparatorRewind.startTapeCells, List.map_append, List.append_assoc]
end RightCellInsert

namespace OneCellMachine

inductive Control where
  | prep (control : RightCellPrep.Control)
  | bridge (symbol : MachineCodeSymbol)
  | insert (symbol : MachineCodeSymbol) (control : BoundedBlockInsert.Control)
  | rewind (control : SeparatorRewind.Control)
deriving DecidableEq

namespace Control
def insertElems : List Control :=
  MachineCodeSymbol.finite.elems.flatMap fun symbol =>
    BoundedBlockInsert.Control.finite.elems.map (Control.insert symbol)
def elems : List Control :=
  List.append (RightCellPrep.Control.finite.elems.map Control.prep) (List.append
      (MachineCodeSymbol.finite.elems.map Control.bridge) (List.append insertElems
        (SeparatorRewind.Control.finite.elems.map Control.rewind)))
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | prep inner =>
        apply List.mem_append.mpr
        apply Or.inl
        apply List.mem_map.mpr
        exact ⟨inner, RightCellPrep.Control.finite.complete inner, rfl⟩
    | bridge symbol =>
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_append.mpr
        apply Or.inl
        apply List.mem_map.mpr
        exact ⟨symbol, MachineCodeSymbol.finite.complete symbol, rfl⟩
    | insert symbol inner =>
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_append.mpr
        apply Or.inl
        apply List.mem_flatMap.mpr
        refine ⟨symbol, MachineCodeSymbol.finite.complete symbol, ?_⟩
        apply List.mem_map.mpr
        exact ⟨inner, BoundedBlockInsert.Control.finite.complete inner, rfl⟩
    | rewind inner =>
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_map.mpr
        exact ⟨inner, SeparatorRewind.Control.finite.complete inner, rfl⟩
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .prep (.gate symbol), cell =>
      some (cell, Direction.left, .bridge symbol)
  | .prep inner, cell =>
      match RightCellPrep.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .prep target)
  | .bridge symbol, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .insert symbol
            (.carry (BoundedBlockInsert.cellBuffer symbol)))
  | .bridge _, _ => none
  | .insert _ .halt, cell =>
      match SeparatorRewind.transition .start cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rewind target)
  | .insert symbol inner, cell =>
      match BoundedBlockInsert.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .insert symbol target)
  | .rewind inner, cell =>
      match SeparatorRewind.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .rewind target)
def machine : TuringMachine MachineCodeSymbol Control where
  start := .prep .start
  halt := .rewind .gate
  transition := transition
  statesFinite := Control.finite
def prepConfig (c : TuringMachine.Configuration MachineCodeSymbol RightCellPrep.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .prep c.state
  tape := c.tape
def insertConfig (symbol : MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol
      BoundedBlockInsert.Control) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .insert symbol c.state
  tape := c.tape
def rewindConfig (c : TuringMachine.Configuration MachineCodeSymbol SeparatorRewind.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewind c.state
  tape := c.tape
def bridgeConfig (symbol : MachineCodeSymbol) (leftCells : List (Option MachineCodeSymbol))
    (payload : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bridge symbol
  tape :=
    { left := leftCells
      head := some MachineCodeSymbol.done
      right := payload.map some }
theorem prep_gate_bridge_step_of_cons (symbol first : MachineCodeSymbol)
    (leftCells : List (Option MachineCodeSymbol)) (payloadRest : Word MachineCodeSymbol) :
    machine.stepConfig (prepConfig (RightCellPrep.gateConfig symbol
            (some MachineCodeSymbol.done :: leftCells) (first :: payloadRest))) = some
        (bridgeConfig symbol leftCells (first :: payloadRest)) := by
  cases payloadRest <;> rfl
theorem bridge_insert_step_of_cons (symbol first : MachineCodeSymbol)
    (leftCells : List (Option MachineCodeSymbol)) (payloadRest : Word MachineCodeSymbol) :
    machine.stepConfig (bridgeConfig symbol leftCells (first :: payloadRest)) = some
        (insertConfig symbol (BoundedBlockInsert.config
            (BoundedBlockInsert.cellBuffer symbol) [] (some MachineCodeSymbol.done :: leftCells)
            (first :: payloadRest))) := by
  cases payloadRest <;> rfl
theorem prep_step_of_not_gate (c : TuringMachine.Configuration MachineCodeSymbol
      RightCellPrep.Control) (hnot : forall symbol : MachineCodeSymbol,
      c.state ≠ .gate symbol) : machine.stepConfig (prepConfig c) =
      Option.map prepConfig (RightCellPrep.machine.stepConfig c) := by
  cases c with
  | mk state tape =>
      cases state with
      | start | separator | candidate =>
          unfold TuringMachine.stepConfig
          simp only [prepConfig, machine, transition, RightCellPrep.machine]
          cases htransition : RightCellPrep.transition _ (Tape.read tape) with
          | none => rfl
          | some action =>
              rcases action with ⟨write, direction, target⟩
              rfl
      | increment symbol | locateDone symbol =>
          unfold TuringMachine.stepConfig
          simp only [prepConfig, machine, transition, RightCellPrep.machine]
          cases htransition : RightCellPrep.transition _ (Tape.read tape) with
          | none => rfl
          | some action =>
              rcases action with ⟨write, direction, target⟩
              rfl
      | gate symbol =>
          exact (hnot symbol rfl).elim
theorem prep_run_of_eq_some (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol
      RightCellPrep.Control) (hrun : RightCellPrep.machine.runConfigExact? steps c = some d) :
    machine.runConfigExact? steps (prepConfig c) = some (prepConfig d) := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : RightCellPrep.machine.stepConfig c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          have hnot : forall symbol : MachineCodeSymbol, c.state ≠ RightCellPrep.Control.gate symbol := by
            intro symbol hgate
            have hnone : RightCellPrep.machine.stepConfig c = none := by
              cases c with
              | mk state tape =>
                  simp only at hgate
                  subst state
                  rfl
            rw [hnone] at hstep
            contradiction
          rw [prep_step_of_not_gate c hnot]
          rw [hstep]
          simp only [Option.map]
          exact ih next d hrun
theorem insert_step_of_not_halt (symbol : MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol BoundedBlockInsert.Control)
    (hnot : c.state ≠ .halt) : machine.stepConfig (insertConfig symbol c) =
      Option.map (insertConfig symbol) ((BoundedBlockInsert.machine
          (BoundedBlockInsert.cellBuffer symbol)).stepConfig c) := by
  cases c with
  | mk state tape =>
      cases state with
      | carry buffer =>
          unfold TuringMachine.stepConfig
          simp only [insertConfig, machine, transition, BoundedBlockInsert.machine, BoundedBlockInsert.transition,
            VariableBlockInsert.machine]
          cases htransition : VariableBlockInsert.transition (.carry buffer) (Tape.read tape) with
          | none => rfl
          | some action =>
              rcases action with ⟨write, direction, target⟩
              rfl
      | halt => contradiction
theorem insert_run_of_eq_some (symbol : MachineCodeSymbol) (steps : Nat)
    (c d : TuringMachine.Configuration MachineCodeSymbol BoundedBlockInsert.Control) (hrun :
      (BoundedBlockInsert.machine (BoundedBlockInsert.cellBuffer symbol)).runConfigExact?
        steps c = some d) : machine.runConfigExact? steps (insertConfig symbol c) = some (insertConfig symbol d) := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : (BoundedBlockInsert.machine (BoundedBlockInsert.cellBuffer symbol)).stepConfig c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          have hnot : c.state ≠ BoundedBlockInsert.Control.halt := by
            intro hhalt
            have hnone : (BoundedBlockInsert.machine (BoundedBlockInsert.cellBuffer symbol)).stepConfig c =
                  none := by
              cases c with
              | mk state tape =>
                  simp only at hhalt
                  subst state
                  rfl
            rw [hnone] at hstep
            contradiction
          rw [insert_step_of_not_halt symbol c hnot]
          rw [hstep]
          simp only [Option.map]
          exact ih next d hrun
theorem encodeNat_eq_ticks_done (count : Nat) : MachineDescription.encodeNat count = List.append
        (List.replicate count MachineCodeSymbol.tick) [MachineCodeSymbol.done] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [MachineDescription.encodeNat, ih, List.replicate_succ]
      rfl
def bridgeLeftCells (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : List (Option MachineCodeSymbol) :=
  List.append (List.replicate processed.length (some MachineCodeSymbol.tick))
    (some MachineCodeSymbol.tick :: none :: deeperLeft)
theorem baseCells_eq_done_cons (processed : Word MachineCodeSymbol) (deeperLeft : List (Option MachineCodeSymbol)) :
    RightCellInsert.baseCells processed deeperLeft = some MachineCodeSymbol.done ::
        bridgeLeftCells processed deeperLeft := by
  simp [RightCellInsert.baseCells, bridgeLeftCells, encodeNat_eq_ticks_done]
def sourceConfig (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : TuringMachine.Configuration MachineCodeSymbol Control :=
  prepConfig (RightCellPrep.sourceConfig deeperLeft current (NonemptyRightRegion.region processed))
def prepEndpointConfig (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : TuringMachine.Configuration MachineCodeSymbol Control :=
  prepConfig (RightCellPrep.gateConfig current (RightCellInsert.baseCells processed deeperLeft)
      (RightCellPrep.payload processed))
def insertionSourceConfig (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : TuringMachine.Configuration MachineCodeSymbol Control :=
  insertConfig current (RightCellInsert.sourceConfig current processed deeperLeft)
def insertionEndpointConfig (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : TuringMachine.Configuration MachineCodeSymbol Control :=
  insertConfig current (RightCellInsert.endpointConfig current processed deeperLeft)
def endpointConfig (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : TuringMachine.Configuration MachineCodeSymbol Control :=
  rewindConfig (SeparatorRewind.gateConfigCells deeperLeft (NonemptyRightRegion.region (current :: processed)))
theorem prep_run_exact (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (processed.length + 5) (sourceConfig current processed deeperLeft) =
      some (prepEndpointConfig current processed deeperLeft) := by
  exact prep_run_of_eq_some _ _ _ (RightCellPrep.process_one_prep_exact deeperLeft current processed)
theorem payload_ne_nil (processed : Word MachineCodeSymbol) : RightCellPrep.payload processed ≠ [] := by
  induction processed with
  | nil =>
      simp [RightCellPrep.payload, encodeOptionalCodeSymbolsPayloadAppend]
  | cons symbol processed ih =>
      intro hnil
      have hparts := List.append_eq_nil_iff.mp hnil
      have hencode : MachineDescription.encodeNat (optionalCodeSymbolTag (some symbol)) ≠ [] := by
        rw [encodeNat_eq_ticks_done]
        intro hempty
        have hlength := congrArg List.length hempty
        simp at hlength
      exact hencode hparts.1
theorem bridge_run_exact (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : machine.runConfigExact? 2
        (prepEndpointConfig current processed deeperLeft) =
      some (insertionSourceConfig current processed deeperLeft) := by
  have hnonempty := payload_ne_nil processed
  cases hpayload : RightCellPrep.payload processed with
  | nil => contradiction
  | cons first payloadRest =>
      unfold prepEndpointConfig insertionSourceConfig
      unfold RightCellInsert.sourceConfig
      rw [baseCells_eq_done_cons]
      rw [hpayload]
      change machine.runConfigExact? (1 + 1) (prepConfig (RightCellPrep.gateConfig current
            (some MachineCodeSymbol.done :: bridgeLeftCells processed deeperLeft) (first :: payloadRest))) = _
      rw [TuringMachine.runConfigExact?]
      rw [prep_gate_bridge_step_of_cons]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [bridge_insert_step_of_cons]
      rfl
theorem insertion_run_exact (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : machine.runConfigExact?
        (RightCellInsert.runSteps current processed) (insertionSourceConfig current processed deeperLeft) =
      some (insertionEndpointConfig current processed deeperLeft) := by
  exact insert_run_of_eq_some current _ _ _ (RightCellInsert.run_exact current processed deeperLeft)
theorem insertion_endpoint_eq_rewind_source (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol) (deeperLeft : List (Option MachineCodeSymbol)) :
    insertionEndpointConfig current processed deeperLeft =
      { state := .insert current .halt
        tape := SeparatorRewind.startTapeCells deeperLeft (NonemptyRightRegion.region
            (current :: processed)).reverse } := by
  change (⟨Control.insert current BoundedBlockInsert.Control.halt,
      (RightCellInsert.endpointConfig current processed deeperLeft).tape⟩ :
      TuringMachine.Configuration MachineCodeSymbol Control) = _
  rw [RightCellInsert.endpointTape_eq_separatorStart]
theorem insertion_halt_retarget_step (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol) (deeperLeft : List (Option MachineCodeSymbol)) :
    machine.stepConfig (insertionEndpointConfig current processed deeperLeft) = some
        (rewindConfig (SeparatorRewind.scanConfigCells deeperLeft (NonemptyRightRegion.region
              (current :: processed)).reverse [])) := by
  rw [insertion_endpoint_eq_rewind_source]
  cases hencoded : (NonemptyRightRegion.region (current :: processed)).reverse <;> rfl
theorem rewind_scan_step (deeperLeft : List (Option MachineCodeSymbol))
    (currentToken : MachineCodeSymbol) (remainingRev crossed : Word MachineCodeSymbol) :
    machine.stepConfig (rewindConfig (SeparatorRewind.scanConfigCells deeperLeft
            (currentToken :: remainingRev) crossed)) = some (rewindConfig (SeparatorRewind.scanConfigCells deeperLeft
            remainingRev (currentToken :: crossed))) := by
  cases remainingRev <;> rfl
theorem rewind_scan_finish (deeperLeft : List (Option MachineCodeSymbol))
    (crossed : Word MachineCodeSymbol) : machine.stepConfig (rewindConfig
          (SeparatorRewind.scanConfigCells deeperLeft [] crossed)) = some (rewindConfig
          (SeparatorRewind.gateConfigCells deeperLeft crossed)) := by
  cases crossed <;> rfl
theorem rewind_scan_run_exact (deeperLeft : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) : machine.runConfigExact? (remainingRev.length + 1) (rewindConfig
          (SeparatorRewind.scanConfigCells deeperLeft remainingRev crossed)) = some
        (rewindConfig (SeparatorRewind.gateConfigCells deeperLeft (List.append remainingRev.reverse crossed))) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact rewind_scan_finish deeperLeft crossed
  | cons currentToken remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1) (rewindConfig
              (SeparatorRewind.scanConfigCells deeperLeft (currentToken :: remainingRev) crossed)) = _
      rw [TuringMachine.runConfigExact?]
      rw [rewind_scan_step]
      simp only
      rw [ih (currentToken :: crossed)]
      simp [List.reverse_cons, List.append_assoc]
theorem rewind_run_from_insertion_endpoint (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol) (deeperLeft : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? ((NonemptyRightRegion.region (current :: processed)).length + 2)
        (insertionEndpointConfig current processed deeperLeft) =
      some (endpointConfig current processed deeperLeft) := by
  rw [show (NonemptyRightRegion.region (current :: processed)).length + 2 =
        (((NonemptyRightRegion.region (current :: processed)).reverse).length + 1) + 1 by
    simp]
  rw [TuringMachine.runConfigExact?]
  rw [insertion_halt_retarget_step]
  simp only
  simpa [endpointConfig] using rewind_scan_run_exact deeperLeft (NonemptyRightRegion.region
        (current :: processed)).reverse ([] : Word MachineCodeSymbol)
def runSteps (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol) : Nat :=
  (processed.length + 5) + (2 + (RightCellInsert.runSteps current processed +
        ((NonemptyRightRegion.region (current :: processed)).length + 2)))
theorem run_exact (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) : machine.runConfigExact? (runSteps current processed)
        (sourceConfig current processed deeperLeft) = some (endpointConfig current processed deeperLeft) := by
  unfold runSteps
  rw [ExactRun.append]
  rw [prep_run_exact]
  simp only
  rw [ExactRun.append]
  rw [bridge_run_exact]
  simp only
  rw [ExactRun.append]
  rw [insertion_run_exact]
  simp only
  exact rewind_run_from_insertion_endpoint current processed deeperLeft
end OneCellMachine

namespace TuringExactEquiv
theorem runConfigExact?_some_of_equiv
    {symbol state : Type} (M : TuringMachine symbol state) (steps : Nat)
    {clean padded cleanFinal : TuringMachine.Configuration symbol state}
    (hstate : clean.state = padded.state) (htape : Tape.Equiv clean.tape padded.tape)
    (hrun : M.runConfigExact? steps clean = some cleanFinal) :
    exists paddedFinal : TuringMachine.Configuration symbol state, M.runConfigExact? steps padded = some paddedFinal ∧
        cleanFinal.state = paddedFinal.state ∧ Tape.Equiv cleanFinal.tape paddedFinal.tape := by
  rcases clean with ⟨cleanState, cleanTape⟩
  rcases padded with ⟨paddedState, paddedTape⟩
  simp only at hstate
  subst paddedState
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv hrun htape with
    ⟨paddedFinal, hpaddedRun, hpaddedState, hpaddedTape⟩
  exact ⟨paddedFinal, hpaddedRun, hpaddedState.symm, hpaddedTape⟩
end TuringExactEquiv

end InitialMaterializer
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
