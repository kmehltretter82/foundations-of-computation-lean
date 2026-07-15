import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.HeadLocatorRuns
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
open Languages
namespace HeadActionShape
def moveLeftTarget {stateCount : Nat} (fuel : Nat) (write : Option MachineCodeSymbol) (nextState : Fin stateCount) (L : Layout stateCount) : Layout stateCount := match L.left with
  | [] =>
      { fuel := fuel
        state := nextState
        left := []
        head := none
        right := write :: L.right }
  | nextHead :: remainingLeft =>
      { fuel := fuel
        state := nextState
        left := remainingLeft
        head := nextHead
        right := write :: L.right }
def moveRightTarget {stateCount : Nat} (fuel : Nat) (write : Option MachineCodeSymbol) (nextState : Fin stateCount) (L : Layout stateCount) : Layout stateCount :=
  match L.right with
  | [] =>
      { fuel := fuel
        state := nextState
        left := write :: L.left
        head := none
        right := [] }
  | nextHead :: remainingRight =>
      { fuel := fuel
        state := nextState
        left := write :: L.left
        head := nextHead
        right := remainingRight }
end HeadActionShape
namespace DeleteBlock
def pred (n : Fin 11) : Fin 11 := ⟨n.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩
inductive Control where
  | erase (remaining : Fin 11)
  | pull
  | returnLeft (carried : MachineCodeSymbol) (remaining : Fin 11)
  | advance (remaining : Fin 11)
  | halt
deriving DecidableEq
namespace Control
def elems : List Control := List.append ((List.finRange 11).map Control.erase)
    (List.append [Control.pull, Control.halt] (List.append (MachineCodeSymbol.finite.elems.flatMap fun symbol =>
          (List.finRange 11).map (Control.returnLeft symbol))
        ((List.finRange 11).map Control.advance)))
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | erase remaining =>
        simp [elems, List.mem_finRange]
    | pull =>
        simp [elems]
    | returnLeft carried remaining =>
        simp [elems, List.mem_finRange]
        exact MachineCodeSymbol.finite.complete carried
    | advance remaining =>
        simp [elems, List.mem_finRange]
    | halt =>
        simp [elems]
end Control
def transition (gap : Fin 11) : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .erase remaining, _ =>
      if remaining.val = 1 then some (none, Direction.right, .pull)
      else some (none, Direction.right, .erase (pred remaining))
  | .pull, some current =>
      some (none, Direction.left, .returnLeft current (pred gap))
  | .pull, none =>
      some (none, Direction.left, .halt)
  | .returnLeft carried remaining, none =>
      if remaining.val = 0 then some (some carried, Direction.right, .advance gap)
      else some (none, Direction.left, .returnLeft carried (pred remaining))
  | .advance remaining, cell =>
      if remaining.val = 1 then some (cell, Direction.right, .pull)
      else some (cell, Direction.right, .advance (pred remaining))
  | _, _ => none
def machine (gap : Fin 11) : TuringMachine MachineCodeSymbol Control where
  start := .erase gap
  halt := .halt
  transition := transition gap
  statesFinite := Control.finite
def optionalGap (cell : Option MachineCodeSymbol) : Fin 11 := ⟨optionalCodeSymbolTag cell + 1, by
    have h := HeadLocator.optionalCodeSymbolTag_lt_ten cell
    lia⟩
def pullTape (gap : Fin 11) (leftRev rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol := match rest with
  | [] =>
      { left :=
          List.append (List.replicate gap.val (none : Option MachineCodeSymbol)) (leftRev.map some)
        head := none
        right := [] }
  | current :: suffix =>
      { left :=
          List.append (List.replicate gap.val (none : Option MachineCodeSymbol)) (leftRev.map some)
        head := some current
        right := suffix.map some }
def pullConfig (gap : Fin 11) (leftRev rest : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .pull
  tape := pullTape gap leftRev rest
def sourceConfig (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .erase (optionalGap cell)
  tape := SerializedShift.cursorTape leftRev (List.append (optionalCellWord cell) suffix)
theorem erase_optional_run_exact (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    (machine (optionalGap cell)).runConfigExact? (optionalGap cell).val (sourceConfig cell leftRev suffix) = some (pullConfig (optionalGap cell) leftRev suffix) := by
  cases cell with
  | none =>
      cases suffix <;> rfl
  | some symbol =>
      cases symbol <;> cases suffix <;> rfl
theorem pull_symbol_run_exact (deletedCell : Option MachineCodeSymbol) (current : MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    (machine (optionalGap deletedCell)).runConfigExact? (2 * (optionalGap deletedCell).val + 1) (pullConfig (optionalGap deletedCell) leftRev (current :: suffix)) =
      some (pullConfig (optionalGap deletedCell) (current :: leftRev) suffix) := by
  cases deletedCell with
  | none =>
      cases current <;> cases suffix <;> rfl
  | some deleted =>
      cases deleted <;> cases current <;> cases suffix <;> rfl
def exitTape (cell : Option MachineCodeSymbol) (leftRev : Word MachineCodeSymbol) : Tape MachineCodeSymbol where
  left := List.append (List.replicate ((optionalGap cell).val - 1) (none : Option MachineCodeSymbol)) (leftRev.map some)
  head := none
  right := [none]
def exitConfig (cell : Option MachineCodeSymbol) (leftRev : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := exitTape cell leftRev
theorem pull_finish_exact (cell : Option MachineCodeSymbol) (leftRev : Word MachineCodeSymbol) :
    (machine (optionalGap cell)).runConfigExact? 1 (pullConfig (optionalGap cell) leftRev []) = some (exitConfig cell leftRev) := by
  cases cell with
  | none => rfl
  | some symbol => cases symbol <;> rfl
theorem runConfigExact?_add (gap : Fin 11) (first second : Nat) (c : TuringMachine.Configuration MachineCodeSymbol Control) :
    (machine gap).runConfigExact? (first + second) c = match (machine gap).runConfigExact? first c with
      | none => none
      | some middle => (machine gap).runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add, TuringMachine.runConfigExact?, TuringMachine.runConfigExact?]
      cases hstep : (machine gap).stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next
theorem pull_run_exact (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    (machine (optionalGap cell)).runConfigExact? ((2 * (optionalGap cell).val + 1) * suffix.length + 1) (pullConfig (optionalGap cell) leftRev suffix) =
      some (exitConfig cell (List.append suffix.reverse leftRev)) := by
  induction suffix generalizing leftRev with
  | nil =>
      simpa using pull_finish_exact cell leftRev
  | cons current suffix ih =>
      rw [show (2 * (optionalGap cell).val + 1) * (current :: suffix).length + 1 = (2 * (optionalGap cell).val + 1) + ((2 * (optionalGap cell).val + 1) * suffix.length + 1) by
        simp
        lia]
      rw [runConfigExact?_add, pull_symbol_run_exact]
      simp only
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]
def runSteps (cell : Option MachineCodeSymbol) (suffix : Word MachineCodeSymbol) : Nat := (optionalGap cell).val + ((2 * (optionalGap cell).val + 1) * suffix.length + 1)
theorem run_exact (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    (machine (optionalGap cell)).runConfigExact? (runSteps cell suffix) (sourceConfig cell leftRev suffix) = some (exitConfig cell (List.append suffix.reverse leftRev)) := by
  unfold runSteps
  rw [runConfigExact?_add, erase_optional_run_exact]
  simp only
  exact pull_run_exact cell leftRev suffix
def oneSourceConfig (deleted : MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .erase (optionalGap none)
  tape := SerializedShift.cursorTape leftRev (deleted :: suffix)
theorem erase_one_run_exact (deleted : MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    (machine (optionalGap none)).runConfigExact? 1 (oneSourceConfig deleted leftRev suffix) = some (pullConfig (optionalGap none) leftRev suffix) := by
  cases deleted <;> cases suffix <;> rfl
def runOneSteps (suffix : Word MachineCodeSymbol) : Nat := 1 + (3 * suffix.length + 1)
theorem run_one_exact (deleted : MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    (machine (optionalGap none)).runConfigExact? (runOneSteps suffix) (oneSourceConfig deleted leftRev suffix) = some (exitConfig none (List.append suffix.reverse leftRev)) := by
  unfold runOneSteps
  rw [show 3 * suffix.length + 1 = (2 * (optionalGap none).val + 1) * suffix.length + 1 by
    rfl]
  rw [runConfigExact?_add, erase_one_run_exact]
  simp only
  exact pull_run_exact none leftRev suffix
end DeleteBlock
namespace InsertBlock
def wordsOfLength : Nat -> List (Word MachineCodeSymbol)
  | 0 => [[]]
  | count + 1 =>
      MachineCodeSymbol.finite.elems.flatMap fun symbol =>
        (wordsOfLength count).map (fun rest => symbol :: rest)
theorem wordsOfLength_complete (word : Word MachineCodeSymbol) (count : Nat) (hlength : word.length = count) : word ∈ wordsOfLength count := by
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
          apply List.mem_map.mpr
          exact ⟨rest, ih rest hrest, rfl⟩
def bufferWords : List (Word MachineCodeSymbol) := (List.range 11).flatMap wordsOfLength
theorem bufferWords_complete (word : Word MachineCodeSymbol) (hlength : word.length ≤ 10) : word ∈ bufferWords := by
  apply List.mem_flatMap.mpr
  refine ⟨word.length, ?_, wordsOfLength_complete word word.length rfl⟩
  simp
  lia
structure Buffer where
  word : Word MachineCodeSymbol
  length_le : word.length ≤ 10
deriving DecidableEq
def toBuffer? (word : Word MachineCodeSymbol) : Option Buffer := if h : word.length ≤ 10 then some ⟨word, h⟩ else none
namespace Buffer
def elems : List Buffer := bufferWords.filterMap toBuffer?
def finite : Foundation.FiniteType Buffer where
  elems := elems
  complete := by
    intro buffer
    apply List.mem_filterMap.mpr
    refine ⟨buffer.word, bufferWords_complete buffer.word buffer.length_le, ?_⟩
    simp [toBuffer?, buffer.length_le]
def popPush (buffer : Buffer) (current : MachineCodeSymbol) : Option (MachineCodeSymbol × Buffer) := match buffer with
  | ⟨[], _⟩ => none
  | ⟨head :: tail, hlength⟩ =>
      some (head, ⟨List.append tail [current], by
            simpa using hlength⟩)
def pop (buffer : Buffer) : Option (MachineCodeSymbol × Buffer) := match buffer with
  | ⟨[], _⟩ => none
  | ⟨head :: tail, hlength⟩ =>
      some (head, ⟨tail, by
            have hle : tail.length ≤ (head :: tail).length := by simp
            exact Nat.le_trans hle hlength⟩)
end Buffer
inductive Control where
  | carry (buffer : Buffer)
  | halt
deriving DecidableEq
namespace Control
def elems : List Control := List.append (Buffer.finite.elems.map Control.carry) [Control.halt]
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | carry buffer =>
        simp [elems]
        exact Buffer.finite.complete buffer
    | halt => simp [elems]
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .carry buffer, some current =>
      match buffer.popPush current with
      | none => none
      | some (written, nextBuffer) =>
          some (some written, Direction.right, .carry nextBuffer)
  | .carry buffer, none =>
      match buffer.pop with
      | none => none
      | some (written, nextBuffer) =>
          if nextBuffer.word = [] then some (some written, Direction.right, .halt)
          else some (some written, Direction.right, .carry nextBuffer)
  | .halt, _ => none
def machine (initial : Buffer) : TuringMachine MachineCodeSymbol Control where
  start := .carry initial
  halt := .halt
  transition := transition
  statesFinite := Control.finite
def config (buffer : Buffer) (leftRev rest : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .carry buffer
  tape := SerializedShift.cursorTape leftRev rest
def haltConfig (leftRev : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := SerializedShift.cursorTape leftRev []
def cross : Buffer -> Word MachineCodeSymbol -> Word MachineCodeSymbol -> Buffer × Word MachineCodeSymbol
  | buffer, leftRev, [] => (buffer, leftRev)
  | buffer, leftRev, current :: suffix =>
      match buffer.popPush current with
      | none => (buffer, leftRev)
      | some (written, nextBuffer) =>
          cross nextBuffer (written :: leftRev) suffix
theorem step_cons (initial : Buffer) (head current : MachineCodeSymbol) (tail leftRev suffix : Word MachineCodeSymbol) (hlength : (head :: tail).length ≤ 10) :
    (machine initial).stepConfig (config ⟨head :: tail, hlength⟩ leftRev (current :: suffix)) =
      some (config ⟨List.append tail [current], by simpa using hlength⟩ (head :: leftRev) suffix) := by cases suffix <;> rfl
theorem cross_run_exact (initial buffer : Buffer) (leftRev suffix : Word MachineCodeSymbol) (hnonempty : buffer.word ≠ []) :
    (machine initial).runConfigExact? suffix.length (config buffer leftRev suffix) = some (config (cross buffer leftRev suffix).1 (cross buffer leftRev suffix).2 []) := by
  induction suffix generalizing buffer leftRev with
  | nil =>
      rfl
  | cons current suffix ih =>
      cases buffer with
      | mk word hlength =>
          cases word with
          | nil => contradiction
          | cons head tail =>
              change (machine initial).runConfigExact? (suffix.length + 1) (config ⟨head :: tail, hlength⟩ leftRev (current :: suffix)) = _
              rw [TuringMachine.runConfigExact?, step_cons]
              simp only
              have hnext : (List.append tail [current] : Word MachineCodeSymbol) ≠ [] := by
                simp
              rw [ih ⟨List.append tail [current], by
                  simpa using hlength⟩
                (head :: leftRev) hnext]
              rfl
theorem cross_spec (buffer : Buffer) (leftRev suffix : Word MachineCodeSymbol) (hnonempty : buffer.word ≠ []) :
    (cross buffer leftRev suffix).1.word ≠ [] ∧ (cross buffer leftRev suffix).1.word.length = buffer.word.length ∧
      List.append (cross buffer leftRev suffix).2.reverse (cross buffer leftRev suffix).1.word = List.append leftRev.reverse (List.append buffer.word suffix) := by
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
                  simpa using hlength⟩
                (head :: leftRev) hnext
              simpa [cross, Buffer.popPush, List.reverse_cons, List.append_assoc] using hspec
theorem flush_last (initial : Buffer) (head : MachineCodeSymbol) (leftRev : Word MachineCodeSymbol) (hlength : ([head] : Word MachineCodeSymbol).length ≤ 10) :
    (machine initial).stepConfig (config ⟨[head], hlength⟩ leftRev []) = some (haltConfig (head :: leftRev)) := by rfl
theorem flush_more (initial : Buffer) (head next : MachineCodeSymbol) (rest leftRev : Word MachineCodeSymbol) (hlength : (head :: next :: rest).length ≤ 10) :
    (machine initial).stepConfig (config ⟨head :: next :: rest, hlength⟩ leftRev []) = some (config ⟨next :: rest, by
            have hle : (next :: rest).length ≤ (head :: next :: rest).length := by simp
            exact Nat.le_trans hle hlength⟩
          (head :: leftRev) []) := by rfl
theorem flush_run_exact (initial : Buffer) (head : MachineCodeSymbol) (tail leftRev : Word MachineCodeSymbol) (hlength : (head :: tail).length ≤ 10) :
    (machine initial).runConfigExact? (head :: tail).length (config ⟨head :: tail, hlength⟩ leftRev []) = some (haltConfig (List.append (head :: tail).reverse leftRev)) := by
  induction tail generalizing head leftRev with
  | nil =>
      change (machine initial).runConfigExact? 1 (config ⟨[head], hlength⟩ leftRev []) = _
      rw [TuringMachine.runConfigExact?, flush_last]
      simp only [TuringMachine.runConfigExact?]
      rfl
  | cons next rest ih =>
      change (machine initial).runConfigExact? ((next :: rest).length + 1) (config ⟨head :: next :: rest, hlength⟩ leftRev []) = _
      rw [TuringMachine.runConfigExact?, flush_more]
      simp only
      have htail : (next :: rest).length ≤ 10 := by
        have hle : (next :: rest).length ≤ (head :: next :: rest).length := by simp
        exact Nat.le_trans hle hlength
      rw [ih next (head :: leftRev) htail]
      simp [List.reverse_cons, List.append_assoc]
theorem runConfigExact?_add (initial : Buffer) (first second : Nat) (c : TuringMachine.Configuration MachineCodeSymbol Control) :
    (machine initial).runConfigExact? (first + second) c = match (machine initial).runConfigExact? first c with
      | none => none
      | some middle =>
          (machine initial).runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add, TuringMachine.runConfigExact?, TuringMachine.runConfigExact?]
      cases hstep : (machine initial).stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next
def finalLeftRev (buffer : Buffer) (leftRev suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (cross buffer leftRev suffix).1.word.reverse (cross buffer leftRev suffix).2
theorem run_exact (initial buffer : Buffer) (leftRev suffix : Word MachineCodeSymbol) (hnonempty : buffer.word ≠ []) :
    (machine initial).runConfigExact? (suffix.length + buffer.word.length) (config buffer leftRev suffix) = some (haltConfig (finalLeftRev buffer leftRev suffix)) := by
  rw [runConfigExact?_add, cross_run_exact initial buffer leftRev suffix hnonempty]
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
              simpa [finalLeftRev, hcross] using flush_run_exact initial head tail finalLeftRev' hfinalLength
theorem finalLeftRev_reverse (buffer : Buffer) (leftRev suffix : Word MachineCodeSymbol) (hnonempty : buffer.word ≠ []) :
    (finalLeftRev buffer leftRev suffix).reverse = List.append leftRev.reverse (List.append buffer.word suffix) := by
  have hspec := (cross_spec buffer leftRev suffix hnonempty).2.2
  simpa [finalLeftRev, List.reverse_append] using hspec
theorem optionalCellWord_length (cell : Option MachineCodeSymbol) : (optionalCellWord cell).length = optionalCodeSymbolTag cell + 1 := by
  rw [HeadLocator.optionalCellWord_eq_ticks_done]
  simp [HeadLocator.ticks_length]
def optionalBuffer (cell : Option MachineCodeSymbol) : Buffer := ⟨optionalCellWord cell, by
    rw [optionalCellWord_length]
    have h := HeadLocator.optionalCodeSymbolTag_lt_ten cell
    lia⟩
theorem optionalBuffer_nonempty (cell : Option MachineCodeSymbol) : (optionalBuffer cell).word ≠ [] := by
  rw [show (optionalBuffer cell).word = optionalCellWord cell by rfl]
  rw [HeadLocator.optionalCellWord_eq_ticks_done]
  intro h
  have hlength := congrArg List.length h
  simp at hlength
def singletonBuffer (symbol : MachineCodeSymbol) : Buffer := ⟨[symbol], by simp⟩
theorem singletonBuffer_nonempty (symbol : MachineCodeSymbol) : (singletonBuffer symbol).word ≠ [] := by simp [singletonBuffer]
end InsertBlock
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
