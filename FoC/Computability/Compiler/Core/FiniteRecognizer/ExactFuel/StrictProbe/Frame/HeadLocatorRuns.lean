import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.HeadLocatorMachine
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
open Languages
namespace HeadLocator
def ticks : Nat -> Word MachineCodeSymbol
  | 0 => []
  | count + 1 => MachineCodeSymbol.tick :: ticks count
theorem ticks_succ (count : Nat) : ticks (count + 1) = MachineCodeSymbol.tick :: ticks count := by rfl
theorem encodeNat_eq_ticks_done (count : Nat) : MachineDescription.encodeNat count = List.append (ticks count) [MachineCodeSymbol.done] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [MachineDescription.encodeNat, ticks, ih]
theorem ticks_append_tick (count : Nat) (tail : Word MachineCodeSymbol) :
    List.append (ticks count) (MachineCodeSymbol.tick :: tail) = MachineCodeSymbol.tick :: List.append (ticks count) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change MachineCodeSymbol.tick :: List.append (ticks count) (MachineCodeSymbol.tick :: tail) =
          MachineCodeSymbol.tick :: MachineCodeSymbol.tick :: List.append (ticks count) tail
      congr 1
theorem header_step (suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .header [] (MachineCodeSymbol.header :: suffix)) =
      some (cursorConfig .fuel [MachineCodeSymbol.header] suffix) := by cases suffix <;> rfl
theorem fuel_tick_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .fuel leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (cursorConfig .fuel (MachineCodeSymbol.tick :: leftRev) suffix) := by cases suffix <;> rfl
theorem fuel_done_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .fuel leftRev (MachineCodeSymbol.done :: suffix)) =
      some (cursorConfig .state (MachineCodeSymbol.done :: leftRev) suffix) := by cases suffix <;> rfl
theorem fuel_run_exact (fuel : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (fuel + 1) (cursorConfig .fuel leftRev (MachineDescription.encodeNatAppend fuel suffix)) =
      some (cursorConfig .state (List.append (MachineDescription.encodeNat fuel).reverse leftRev) suffix) := by
  induction fuel generalizing leftRev with
  | zero => exact fuel_done_step leftRev suffix
  | succ fuel ih =>
      change machine.runConfigExact? ((fuel + 1) + 1) (cursorConfig .fuel leftRev (MachineCodeSymbol.tick :: MachineDescription.encodeNatAppend fuel suffix)) = _
      rw [TuringMachine.runConfigExact?, fuel_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]
theorem state_tick_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .state leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (cursorConfig .state (MachineCodeSymbol.tick :: leftRev) suffix) := by cases suffix <;> rfl
theorem state_done_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .state leftRev (MachineCodeSymbol.done :: suffix)) =
      some (cursorConfig .markCountBoundary (MachineCodeSymbol.done :: leftRev) suffix) := by cases suffix <;> rfl
theorem state_run_exact (state : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (state + 1) (cursorConfig .state leftRev (MachineDescription.encodeNatAppend state suffix)) =
      some (cursorConfig .markCountBoundary (List.append (MachineDescription.encodeNat state).reverse leftRev) suffix) := by
  induction state generalizing leftRev with
  | zero => exact state_done_step leftRev suffix
  | succ state ih =>
      change machine.runConfigExact? ((state + 1) + 1) (cursorConfig .state leftRev (MachineCodeSymbol.tick :: MachineDescription.encodeNatAppend state suffix)) = _
      rw [TuringMachine.runConfigExact?, state_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]
def returnCountStartConfig (remaining crossed suffix : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control := match remaining with
  | [] =>
      cursorConfig .returnCountStart [] (List.append crossed (MachineCodeSymbol.blank :: suffix))
  | current :: rest =>
      { state := .returnCountStart
        tape :=
          { left := rest.map some
            head := some current
            right := (List.append crossed (MachineCodeSymbol.blank :: suffix)).map some } }
theorem markCount_tick_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .markCountBoundary leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (cursorConfig .markCountBoundary (MachineCodeSymbol.tick :: leftRev) suffix) := by cases suffix <;> rfl
theorem markCount_done_step (leftHead : MachineCodeSymbol) (leftTail suffix : Word MachineCodeSymbol) :
    machine.stepConfig (cursorConfig .markCountBoundary (leftHead :: leftTail) (MachineCodeSymbol.done :: suffix)) =
      some (returnCountStartConfig (leftHead :: leftTail) [] suffix) := by rfl
theorem markCount_run_exact (count : Nat) (leftHead : MachineCodeSymbol) (leftTail suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1) (cursorConfig .markCountBoundary (leftHead :: leftTail) (MachineDescription.encodeNatAppend count suffix)) =
      some (returnCountStartConfig (List.append (ticks count) (leftHead :: leftTail)) [] suffix) := by
  induction count generalizing leftHead leftTail with
  | zero => exact markCount_done_step leftHead leftTail suffix
  | succ count ih =>
      change machine.runConfigExact? ((count + 1) + 1) (cursorConfig .markCountBoundary (leftHead :: leftTail) (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?, markCount_tick_step]
      simp only
      rw [ih MachineCodeSymbol.tick (leftHead :: leftTail)]
      have hwords : List.append (ticks count) (MachineCodeSymbol.tick :: leftHead :: leftTail) = List.append (ticks (count + 1)) (leftHead :: leftTail) := by
        calc
          List.append (ticks count) (MachineCodeSymbol.tick :: leftHead :: leftTail) = MachineCodeSymbol.tick :: List.append (ticks count) (leftHead :: leftTail) :=
            ticks_append_tick count (leftHead :: leftTail)
          _ = List.append (ticks (count + 1)) (leftHead :: leftTail) := by
            rfl
      exact congrArg (fun word => some (returnCountStartConfig word [] suffix)) hwords
theorem returnCountStart_tick_step (next : MachineCodeSymbol) (remaining crossed suffix : Word MachineCodeSymbol) :
    machine.stepConfig (returnCountStartConfig (MachineCodeSymbol.tick :: next :: remaining) crossed suffix) =
      some (returnCountStartConfig (next :: remaining) (MachineCodeSymbol.tick :: crossed) suffix) := by rfl
theorem returnCountStart_tick_step_nonempty (rest crossed suffix : Word MachineCodeSymbol) (hrest : rest ≠ []) :
    machine.stepConfig (returnCountStartConfig (MachineCodeSymbol.tick :: rest) crossed suffix) =
      some (returnCountStartConfig rest (MachineCodeSymbol.tick :: crossed) suffix) := by
  cases rest with
  | nil => contradiction
  | cons next remaining =>
      exact returnCountStart_tick_step next remaining crossed suffix
theorem returnCountStart_done_step (baseLeftRev crossed suffix : Word MachineCodeSymbol) : machine.stepConfig (returnCountStartConfig
          (MachineCodeSymbol.done :: baseLeftRev) crossed suffix) =
      some (cursorConfig .countCheck (MachineCodeSymbol.done :: baseLeftRev) (List.append crossed (MachineCodeSymbol.blank :: suffix))) := by cases crossed <;> cases suffix <;> rfl
theorem returnCountStart_run_exact (count : Nat) (baseLeftRev crossed suffix : Word MachineCodeSymbol) : machine.runConfigExact? (count + 1) (returnCountStartConfig
          (List.append (ticks count) (MachineCodeSymbol.done :: baseLeftRev)) crossed suffix) =
      some (cursorConfig .countCheck (MachineCodeSymbol.done :: baseLeftRev) (List.append (ticks count) (List.append crossed (MachineCodeSymbol.blank :: suffix)))) := by
  induction count generalizing crossed with
  | zero =>
      exact returnCountStart_done_step baseLeftRev crossed suffix
  | succ count ih =>
      change machine.runConfigExact? ((count + 1) + 1) (returnCountStartConfig (MachineCodeSymbol.tick ::
              List.append (ticks count) (MachineCodeSymbol.done :: baseLeftRev)) crossed suffix) = _
      rw [TuringMachine.runConfigExact?]
      have hrest : List.append (ticks count) (MachineCodeSymbol.done :: baseLeftRev) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      rw [returnCountStart_tick_step_nonempty _ _ _ hrest]
      simp only
      rw [ih (MachineCodeSymbol.tick :: crossed)]
      have hwords : List.append (ticks count) (List.append (MachineCodeSymbol.tick :: crossed) (MachineCodeSymbol.blank :: suffix)) =
            List.append (ticks (count + 1)) (List.append crossed (MachineCodeSymbol.blank :: suffix)) := by
        calc
          List.append (ticks count) (List.append (MachineCodeSymbol.tick :: crossed) (MachineCodeSymbol.blank :: suffix)) =
              List.append (ticks count) (MachineCodeSymbol.tick :: List.append crossed (MachineCodeSymbol.blank :: suffix)) := by
                rfl
          _ = MachineCodeSymbol.tick :: List.append (ticks count) (List.append crossed (MachineCodeSymbol.blank :: suffix)) :=
              ticks_append_tick count (List.append crossed (MachineCodeSymbol.blank :: suffix))
          _ = List.append (ticks (count + 1)) (List.append crossed (MachineCodeSymbol.blank :: suffix)) := by
              rfl
      rw [hwords]
theorem markCountBoundary_roundTrip_exact (count : Nat) (baseLeftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (2 * count + 2) (cursorConfig .markCountBoundary (MachineCodeSymbol.done :: baseLeftRev) (MachineDescription.encodeNatAppend count suffix)) =
      some (cursorConfig .countCheck (MachineCodeSymbol.done :: baseLeftRev) (List.append (ticks count) (MachineCodeSymbol.blank :: suffix))) := by
  rw [show 2 * count + 2 = (count + 1) + (count + 1) by lia, TuringMachine.runConfigExact?_add, markCount_run_exact]
  simp only
  simpa using returnCountStart_run_exact count baseLeftRev ([] : Word MachineCodeSymbol) suffix
def markedCellWord (cell : Option MachineCodeSymbol) : Word MachineCodeSymbol := List.append (ticks (optionalCodeSymbolTag cell)) [MachineCodeSymbol.header]
def markedCellsWord : List (Option MachineCodeSymbol) -> Word MachineCodeSymbol
  | [] => []
  | cell :: rest =>
      List.append (markedCellWord cell) (markedCellsWord rest)
theorem optionalCellWord_eq_ticks_done (cell : Option MachineCodeSymbol) : optionalCellWord cell = List.append (ticks (optionalCodeSymbolTag cell)) [MachineCodeSymbol.done] := by
  simp [optionalCellWord, encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend, encodeNat_eq_ticks_done]
theorem ticks_reverse (count : Nat) : (ticks count).reverse = ticks count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [ticks_succ, List.reverse_cons, ih]
      simpa using ticks_append_tick count ([] : Word MachineCodeSymbol)
theorem countCheck_tick_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .countCheck leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (cursorConfig .seekCountBoundary (MachineCodeSymbol.transition :: leftRev) suffix) := by cases suffix <;> rfl
theorem seekCountBoundary_tick_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .seekCountBoundary leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (cursorConfig .seekCountBoundary (MachineCodeSymbol.tick :: leftRev) suffix) := by cases suffix <;> rfl
theorem seekCountBoundary_blank_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .seekCountBoundary leftRev (MachineCodeSymbol.blank :: suffix)) =
      some (cursorConfig .seekCellDone (MachineCodeSymbol.blank :: leftRev) suffix) := by cases suffix <;> rfl
theorem seekCountBoundary_run_exact (remainingCount : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (remainingCount + 1) (cursorConfig .seekCountBoundary leftRev (List.append (ticks remainingCount) (MachineCodeSymbol.blank :: suffix))) =
      some (cursorConfig .seekCellDone (MachineCodeSymbol.blank :: List.append (ticks remainingCount) leftRev) suffix) := by
  induction remainingCount generalizing leftRev with
  | zero =>
      exact seekCountBoundary_blank_step leftRev suffix
  | succ remainingCount ih =>
      change machine.runConfigExact? ((remainingCount + 1) + 1) (cursorConfig .seekCountBoundary leftRev (MachineCodeSymbol.tick ::
              List.append (ticks remainingCount) (MachineCodeSymbol.blank :: suffix))) = _
      rw [TuringMachine.runConfigExact?, seekCountBoundary_tick_step]
      simp only
      rw [ih]
      have hwords : List.append (ticks remainingCount) (MachineCodeSymbol.tick :: leftRev) = List.append (ticks (remainingCount + 1)) leftRev := by
        calc
          List.append (ticks remainingCount) (MachineCodeSymbol.tick :: leftRev) = MachineCodeSymbol.tick :: List.append (ticks remainingCount) leftRev :=
            ticks_append_tick remainingCount leftRev
          _ = List.append (ticks (remainingCount + 1)) leftRev := by
            rw [ticks_succ]
            rfl
      exact congrArg (fun word => some (cursorConfig .seekCellDone (MachineCodeSymbol.blank :: word) suffix)) hwords
theorem seekCellDone_tick_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .seekCellDone leftRev (MachineCodeSymbol.tick :: suffix)) =
      some (cursorConfig .seekCellDone (MachineCodeSymbol.tick :: leftRev) suffix) := by cases suffix <;> rfl
theorem seekCellDone_header_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .seekCellDone leftRev (MachineCodeSymbol.header :: suffix)) =
      some (cursorConfig .seekCellDone (MachineCodeSymbol.header :: leftRev) suffix) := by cases suffix <;> rfl
theorem seekCellDone_ticks_run_exact (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? count (cursorConfig .seekCellDone leftRev (List.append (ticks count) suffix)) =
      some (cursorConfig .seekCellDone (List.append (ticks count) leftRev) suffix) := by
  induction count generalizing leftRev with
  | zero =>
      rfl
  | succ count ih =>
      change machine.runConfigExact? (count + 1) (cursorConfig .seekCellDone leftRev (MachineCodeSymbol.tick :: List.append (ticks count) suffix)) = _
      rw [TuringMachine.runConfigExact?, seekCellDone_tick_step]
      simp only
      rw [ih]
      have hwords : List.append (ticks count) (MachineCodeSymbol.tick :: leftRev) = List.append (ticks (count + 1)) leftRev := by
        calc
          List.append (ticks count) (MachineCodeSymbol.tick :: leftRev) = MachineCodeSymbol.tick :: List.append (ticks count) leftRev := ticks_append_tick count leftRev
          _ = List.append (ticks (count + 1)) leftRev := by
            rw [ticks_succ]
            rfl
      exact congrArg (fun word => some (cursorConfig .seekCellDone word suffix)) hwords
theorem ticks_length (count : Nat) : (ticks count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [ticks, ih]
theorem markedCellWord_length (cell : Option MachineCodeSymbol) : (markedCellWord cell).length = optionalCodeSymbolTag cell + 1 := by simp [markedCellWord, ticks_length]
theorem markedCellWord_eq (cell : Option MachineCodeSymbol) : markedCellWord cell = List.append (ticks (optionalCodeSymbolTag cell)) [MachineCodeSymbol.header] := by rfl
theorem markedCellsWord_cons (cell : Option MachineCodeSymbol) (cells : List (Option MachineCodeSymbol)) :
    markedCellsWord (cell :: cells) = List.append (markedCellWord cell) (markedCellsWord cells) := by rfl
theorem seekCellDone_markedCell_run_exact (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (markedCellWord cell).length (cursorConfig .seekCellDone leftRev (List.append (markedCellWord cell) suffix)) =
      some (cursorConfig .seekCellDone (List.append (markedCellWord cell).reverse leftRev) suffix) := by
  rw [markedCellWord_length, markedCellWord_eq]
  have hassoc : List.append (List.append (ticks (optionalCodeSymbolTag cell)) ([MachineCodeSymbol.header] : Word MachineCodeSymbol)) suffix =
        List.append (ticks (optionalCodeSymbolTag cell)) (MachineCodeSymbol.header :: suffix) :=
    List.append_assoc _ _ _
  rw [hassoc, TuringMachine.runConfigExact?_add, seekCellDone_ticks_run_exact]
  simp only
  change machine.runConfigExact? 1 (cursorConfig .seekCellDone (List.append (ticks (optionalCodeSymbolTag cell)) leftRev) (MachineCodeSymbol.header :: suffix)) = _
  rw [TuringMachine.runConfigExact?, seekCellDone_header_step]
  simp only [TuringMachine.runConfigExact?]
  simp [List.reverse_append, ticks_reverse]
theorem seekCellDone_markedCells_run_exact (cells : List (Option MachineCodeSymbol)) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (markedCellsWord cells).length (cursorConfig .seekCellDone leftRev (List.append (markedCellsWord cells) suffix)) =
      some (cursorConfig .seekCellDone (List.append (markedCellsWord cells).reverse leftRev) suffix) := by
  induction cells generalizing leftRev with
  | nil =>
      rfl
  | cons cell cells ih =>
      rw [markedCellsWord_cons]
      have hlength : (List.append (markedCellWord cell) (markedCellsWord cells) : Word MachineCodeSymbol).length = (markedCellWord cell).length + (markedCellsWord cells).length :=
        List.length_append
      rw [hlength]
      have hassoc : List.append (List.append (markedCellWord cell) (markedCellsWord cells)) suffix =
            List.append (markedCellWord cell) (List.append (markedCellsWord cells) suffix) :=
        List.append_assoc _ _ _
      rw [hassoc, TuringMachine.runConfigExact?_add, seekCellDone_markedCell_run_exact]
      simp only
      rw [ih]
      simp [List.reverse_append, List.append_assoc]
def returnCountConfig (remaining crossed rightAfter : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control := match remaining with
  | [] =>
      cursorConfig .returnCount [] (List.append crossed (MachineCodeSymbol.header :: rightAfter))
  | current :: rest =>
      { state := .returnCount
        tape :=
          { left := rest.map some
            head := some current
            right := (List.append crossed (MachineCodeSymbol.header :: rightAfter)).map some } }
theorem seekCellDone_done_step (leftHead : MachineCodeSymbol) (leftTail rightAfter : Word MachineCodeSymbol) :
    machine.stepConfig (cursorConfig .seekCellDone (leftHead :: leftTail) (MachineCodeSymbol.done :: rightAfter)) =
      some (returnCountConfig (leftHead :: leftTail) [] rightAfter) := by rfl
theorem seekCellDone_cell_run_exact (cell : Option MachineCodeSymbol) (leftHead : MachineCodeSymbol) (leftTail rightAfter : Word MachineCodeSymbol) :
    machine.runConfigExact? (optionalCodeSymbolTag cell + 1) (cursorConfig .seekCellDone (leftHead :: leftTail) (List.append (optionalCellWord cell) rightAfter)) =
      some (returnCountConfig (List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail)) [] rightAfter) := by
  rw [optionalCellWord_eq_ticks_done]
  have hassoc : List.append (List.append (ticks (optionalCodeSymbolTag cell)) ([MachineCodeSymbol.done] : Word MachineCodeSymbol)) rightAfter =
        List.append (ticks (optionalCodeSymbolTag cell)) (MachineCodeSymbol.done :: rightAfter) :=
    List.append_assoc _ _ _
  rw [hassoc, TuringMachine.runConfigExact?_add, seekCellDone_ticks_run_exact]
  simp only
  change machine.runConfigExact? 1 (cursorConfig .seekCellDone (List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail)) (MachineCodeSymbol.done :: rightAfter)) = _
  rw [TuringMachine.runConfigExact?]
  have hleft : List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  cases hshape : List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail) with
  | nil => contradiction
  | cons next rest =>
      rw [seekCellDone_done_step]
      simp only [TuringMachine.runConfigExact?]
theorem returnCount_symbol_step (current next : MachineCodeSymbol) (remaining crossed rightAfter : Word MachineCodeSymbol) (hcurrent : current ≠ MachineCodeSymbol.transition) :
    machine.stepConfig (returnCountConfig (current :: next :: remaining) crossed rightAfter) = some (returnCountConfig (next :: remaining) (current :: crossed) rightAfter) := by
  cases current <;> simp_all [machine, TuringMachine.stepConfig, transition, returnCountConfig, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
theorem returnCount_finish (baseLeftRev crossed rightAfter : Word MachineCodeSymbol) : machine.stepConfig (returnCountConfig (MachineCodeSymbol.transition :: baseLeftRev)
          crossed rightAfter) =
      some (cursorConfig .countCheck (MachineCodeSymbol.transition :: baseLeftRev) (List.append crossed (MachineCodeSymbol.header :: rightAfter))) := by
  cases crossed <;> cases rightAfter <;> rfl
theorem returnCount_run_exact (prefixRev baseLeftRev crossed rightAfter : Word MachineCodeSymbol) (hsafe : ¬ List.Mem MachineCodeSymbol.transition prefixRev) :
    machine.runConfigExact? (prefixRev.length + 1) (returnCountConfig (List.append prefixRev (MachineCodeSymbol.transition :: baseLeftRev)) crossed rightAfter) =
      some (cursorConfig .countCheck (MachineCodeSymbol.transition :: baseLeftRev)
          (List.append prefixRev.reverse (List.append crossed (MachineCodeSymbol.header :: rightAfter)))) := by
  induction prefixRev generalizing crossed with
  | nil =>
      exact returnCount_finish baseLeftRev crossed rightAfter
  | cons current prefixRev ih =>
      have hcurrent : current ≠ MachineCodeSymbol.transition := by
        intro h
        subst current
        exact hsafe (List.Mem.head _)
      have htail : ¬ List.Mem MachineCodeSymbol.transition prefixRev := by
        intro h
        exact hsafe (List.Mem.tail _ h)
      change machine.runConfigExact? ((prefixRev.length + 1) + 1) (returnCountConfig (current :: List.append prefixRev (MachineCodeSymbol.transition :: baseLeftRev))
            crossed rightAfter) = _
      rw [TuringMachine.runConfigExact?]
      have hrest : List.append prefixRev (MachineCodeSymbol.transition :: baseLeftRev) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      cases hrestShape : List.append prefixRev (MachineCodeSymbol.transition :: baseLeftRev) with
      | nil => contradiction
      | cons next remaining =>
          rw [returnCount_symbol_step current next remaining crossed rightAfter hcurrent]
          simp only
          have ih' := ih (current :: crossed) htail
          rw [hrestShape] at ih'
          rw [ih']
          simp [List.reverse_cons, List.append_assoc]
theorem ticks_no_transition (count : Nat) : ¬ List.Mem MachineCodeSymbol.transition (ticks count) := by
  induction count with
  | zero =>
      intro h
      cases h
  | succ count ih =>
      intro h
      rw [ticks_succ] at h
      cases h with
      | tail _ htail => exact ih htail
theorem markedCellWord_no_transition (cell : Option MachineCodeSymbol) : ¬ List.Mem MachineCodeSymbol.transition (markedCellWord cell) := by
  intro h
  rw [markedCellWord_eq] at h
  rcases List.mem_append.mp h with hticks | hheader
  · exact ticks_no_transition _ hticks
  · have heq :
        MachineCodeSymbol.transition = MachineCodeSymbol.header :=
      List.mem_singleton.mp hheader
    cases heq
theorem markedCellsWord_no_transition (cells : List (Option MachineCodeSymbol)) : ¬ List.Mem MachineCodeSymbol.transition (markedCellsWord cells) := by
  induction cells with
  | nil =>
      intro h
      cases h
  | cons cell cells ih =>
      intro h
      rw [markedCellsWord_cons] at h
      rcases List.mem_append.mp h with hcell | hrest
      · exact markedCellWord_no_transition cell hcell
      · exact ih hrest
def cellReturnPrefixRev (remainingCount : Nat) (processed : List (Option MachineCodeSymbol)) (cell : Option MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (ticks (optionalCodeSymbolTag cell)) (List.append (markedCellsWord processed).reverse (MachineCodeSymbol.blank :: ticks remainingCount))
theorem cellReturnPrefixRev_no_transition (remainingCount : Nat) (processed : List (Option MachineCodeSymbol)) (cell : Option MachineCodeSymbol) :
    ¬ List.Mem MachineCodeSymbol.transition (cellReturnPrefixRev remainingCount processed cell) := by
  intro h
  unfold cellReturnPrefixRev at h
  rcases List.mem_append.mp h with hcell | hrest
  · exact ticks_no_transition _ hcell
  · rcases List.mem_append.mp hrest with hprocessed | hblank
    · exact
        markedCellsWord_no_transition processed (List.mem_reverse.mp hprocessed)
    · cases hblank with
      | tail _ hticks => exact ticks_no_transition _ hticks
def cellInputBody (processed : List (Option MachineCodeSymbol)) (cell : Option MachineCodeSymbol) (rightAfter : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (markedCellsWord processed) (List.append (optionalCellWord cell) rightAfter)
def cellOutputBody (processed : List (Option MachineCodeSymbol)) (cell : Option MachineCodeSymbol) (rightAfter : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (markedCellsWord processed) (List.append (markedCellWord cell) rightAfter)
def processCellSteps (remainingCount : Nat) (processed : List (Option MachineCodeSymbol)) (cell : Option MachineCodeSymbol) : Nat :=
  1 + ((remainingCount + 1) + ((markedCellsWord processed).length + ((optionalCodeSymbolTag cell + 1) + ((cellReturnPrefixRev remainingCount processed cell).length + 1))))
theorem processCell_run_exact (remainingCount : Nat) (processed : List (Option MachineCodeSymbol)) (cell : Option MachineCodeSymbol)
    (baseLeftRev rightAfter : Word MachineCodeSymbol) :
    machine.runConfigExact? (processCellSteps remainingCount processed cell)
        (cursorConfig .countCheck baseLeftRev (MachineCodeSymbol.tick :: List.append (ticks remainingCount) (MachineCodeSymbol.blank :: cellInputBody processed cell rightAfter))) =
      some (cursorConfig .countCheck (MachineCodeSymbol.transition :: baseLeftRev)
          (List.append (ticks remainingCount) (MachineCodeSymbol.blank :: cellOutputBody processed cell rightAfter))) := by
  unfold processCellSteps
  rw [TuringMachine.runConfigExact?_add]
  have hfirst : machine.runConfigExact? 1 (cursorConfig .countCheck baseLeftRev (MachineCodeSymbol.tick ::
            List.append (ticks remainingCount) (MachineCodeSymbol.blank :: cellInputBody processed cell rightAfter))) =
      some (cursorConfig .seekCountBoundary (MachineCodeSymbol.transition :: baseLeftRev)
          (List.append (ticks remainingCount) (MachineCodeSymbol.blank :: cellInputBody processed cell rightAfter))) := by
    rw [TuringMachine.runConfigExact?, countCheck_tick_step]
    simp only [TuringMachine.runConfigExact?]
  rw [hfirst]
  simp only
  rw [TuringMachine.runConfigExact?_add, seekCountBoundary_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  unfold cellInputBody
  rw [seekCellDone_markedCells_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  have hleft : List.append (markedCellsWord processed).reverse (MachineCodeSymbol.blank :: List.append (ticks remainingCount)
              (MachineCodeSymbol.transition :: baseLeftRev)) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  cases hshape : List.append (markedCellsWord processed).reverse (MachineCodeSymbol.blank :: List.append (ticks remainingCount) (MachineCodeSymbol.transition :: baseLeftRev)) with
  | nil => contradiction
  | cons leftHead leftTail =>
      rw [seekCellDone_cell_run_exact]
      simp only
      have hremaining : (List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail) : Word MachineCodeSymbol) =
            List.append (cellReturnPrefixRev remainingCount processed cell) (MachineCodeSymbol.transition :: baseLeftRev) := by
        calc
          List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail) =
              List.append (ticks (optionalCodeSymbolTag cell)) (List.append (markedCellsWord processed).reverse
                  (MachineCodeSymbol.blank :: List.append (ticks remainingCount) (MachineCodeSymbol.transition :: baseLeftRev))) :=
            congrArg (List.append (ticks (optionalCodeSymbolTag cell))) hshape.symm
          _ = List.append (cellReturnPrefixRev remainingCount processed cell) (MachineCodeSymbol.transition :: baseLeftRev) := by
            simp [cellReturnPrefixRev, List.append_assoc]
      rw [hremaining]
      rw [returnCount_run_exact (prefixRev := cellReturnPrefixRev remainingCount processed cell) (baseLeftRev := baseLeftRev) (crossed := []) (rightAfter := rightAfter)
        (cellReturnPrefixRev_no_transition remainingCount processed cell)]
      simp [cellReturnPrefixRev, cellOutputBody, markedCellWord, List.reverse_append, ticks_reverse, List.append_assoc]
def cellsPayloadWord : List (Option MachineCodeSymbol) -> Word MachineCodeSymbol
  | [] => []
  | cell :: rest =>
      List.append (optionalCellWord cell) (cellsPayloadWord rest)
theorem cellsPayloadWord_eq_encode (cells : List (Option MachineCodeSymbol)) : cellsPayloadWord cells = encodeOptionalCodeSymbolsPayloadAppend cells [] := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [cellsPayloadWord, encodeOptionalCodeSymbolsPayloadAppend]
      rw [ih]
      simp [optionalCellWord, encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend]
def cellsPayloadAppend : List (Option MachineCodeSymbol) -> Word MachineCodeSymbol -> Word MachineCodeSymbol
  | [], suffix => suffix
  | cell :: rest, suffix =>
      List.append (optionalCellWord cell) (cellsPayloadAppend rest suffix)
theorem cellsPayloadAppend_eq_append (cells : List (Option MachineCodeSymbol)) (suffix : Word MachineCodeSymbol) :
    cellsPayloadAppend cells suffix = List.append (cellsPayloadWord cells) suffix := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [cellsPayloadAppend, cellsPayloadWord]
      rw [ih]
      exact (List.append_assoc _ _ _).symm
theorem markedCellsWord_append (first second : List (Option MachineCodeSymbol)) :
    markedCellsWord (first ++ second) = List.append (markedCellsWord first) (markedCellsWord second) := by
  induction first with
  | nil => rfl
  | cons cell first ih =>
      simp only [List.cons_append, markedCellsWord]
      rw [ih]
      exact (List.append_assoc _ _ _).symm
def transitionMarkers : Nat -> Word MachineCodeSymbol
  | 0 => []
  | count + 1 =>
      MachineCodeSymbol.transition :: transitionMarkers count
theorem transitionMarkers_append_transition (count : Nat) (tail : Word MachineCodeSymbol) : List.append (transitionMarkers count) (MachineCodeSymbol.transition :: tail) =
      MachineCodeSymbol.transition :: List.append (transitionMarkers count) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change MachineCodeSymbol.transition :: List.append (transitionMarkers count) (MachineCodeSymbol.transition :: tail) =
          MachineCodeSymbol.transition :: MachineCodeSymbol.transition :: List.append (transitionMarkers count) tail
      congr 1
def processCellsSteps (processed : List (Option MachineCodeSymbol)) : List (Option MachineCodeSymbol) -> Nat
  | [] => 0
  | cell :: rest =>
      processCellSteps rest.length processed cell + processCellsSteps (processed ++ [cell]) rest
theorem processCells_run_exact (remaining processed : List (Option MachineCodeSymbol)) (baseLeftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (processCellsSteps processed remaining) (cursorConfig .countCheck baseLeftRev (List.append (ticks remaining.length)
            (MachineCodeSymbol.blank :: List.append (markedCellsWord processed) (cellsPayloadAppend remaining suffix)))) =
      some (cursorConfig .countCheck (List.append (transitionMarkers remaining.length) baseLeftRev)
          (MachineCodeSymbol.blank :: List.append (markedCellsWord (processed ++ remaining)) suffix)) := by
  induction remaining generalizing processed baseLeftRev with
  | nil =>
      simp [processCellsSteps, ticks, transitionMarkers, cellsPayloadAppend, TuringMachine.runConfigExact?]
  | cons cell rest ih =>
      unfold processCellsSteps
      rw [TuringMachine.runConfigExact?_add]
      have hsource : List.append (ticks (cell :: rest).length) (MachineCodeSymbol.blank :: List.append (markedCellsWord processed) (cellsPayloadAppend (cell :: rest) suffix)) =
            MachineCodeSymbol.tick :: List.append (ticks rest.length) (MachineCodeSymbol.blank :: cellInputBody processed cell (cellsPayloadAppend rest suffix)) := by
        rfl
      rw [hsource]
      rw [processCell_run_exact rest.length processed cell baseLeftRev (cellsPayloadAppend rest suffix)]
      simp only
      have hbody : cellOutputBody processed cell (cellsPayloadAppend rest suffix) = List.append (markedCellsWord (processed ++ [cell])) (cellsPayloadAppend rest suffix) := by
        simp [cellOutputBody, markedCellsWord_append, markedCellsWord, List.append_assoc]
      rw [hbody]
      rw [ih (processed ++ [cell]) (MachineCodeSymbol.transition :: baseLeftRev)]
      have hleft : List.append (transitionMarkers rest.length) (MachineCodeSymbol.transition :: baseLeftRev) = List.append (transitionMarkers (cell :: rest).length)
              baseLeftRev := by
        rw [transitionMarkers_append_transition]
        rfl
      have hprocessed : (processed ++ [cell]) ++ rest = processed ++ (cell :: rest) := by
        simp [List.append_assoc]
      rw [hleft, hprocessed]
theorem processAllCells_run_exact (remaining : List (Option MachineCodeSymbol)) (baseLeftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (processCellsSteps [] remaining) (cursorConfig .countCheck baseLeftRev
          (List.append (ticks remaining.length) (MachineCodeSymbol.blank :: cellsPayloadAppend remaining suffix))) =
      some (cursorConfig .countCheck (List.append (transitionMarkers remaining.length) baseLeftRev) (MachineCodeSymbol.blank ::
            List.append (markedCellsWord remaining) suffix)) := by
  have h := processCells_run_exact remaining [] baseLeftRev suffix
  have hempty : List.append (markedCellsWord ([] : List (Option MachineCodeSymbol))) (cellsPayloadAppend remaining suffix) = cellsPayloadAppend remaining suffix := by
    rfl
  rw [hempty] at h
  exact h
theorem optionalCodeSymbolTag_lt_ten (cell : Option MachineCodeSymbol) : optionalCodeSymbolTag cell < 10 := by
  cases cell with
  | none => decide
  | some symbol => cases symbol <;> decide
def headCount (cell : Option MachineCodeSymbol) : Fin 10 := ⟨optionalCodeSymbolTag cell, optionalCodeSymbolTag_lt_ten cell⟩
theorem decodedHead_headCount (cell : Option MachineCodeSymbol) : decodedHead (headCount cell) = cell := by
  cases cell with
  | none => rfl
  | some symbol => cases symbol <;> rfl
theorem countCheck_blank_step (leftRev suffix : Word MachineCodeSymbol) : machine.stepConfig (cursorConfig .countCheck leftRev (MachineCodeSymbol.blank :: suffix)) =
      some (cursorConfig (.decodeHead ⟨0, by decide⟩) (MachineCodeSymbol.blank :: leftRev) suffix) := by cases suffix <;> rfl
theorem decodeHead_ticks_run_exact (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (optionalCodeSymbolTag cell) (cursorConfig (.decodeHead ⟨0, by decide⟩) leftRev (List.append (ticks (optionalCodeSymbolTag cell)) suffix)) =
      some (cursorConfig (.decodeHead (headCount cell)) (List.append (ticks (optionalCodeSymbolTag cell)) leftRev) suffix) := by
  cases cell with
  | none => rfl
  | some symbol =>
      cases symbol <;> cases suffix <;> rfl
theorem decodeHead_header_step (count : Fin 10) (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (cursorConfig (.decodeHead count) leftRev (MachineCodeSymbol.header :: suffix)) =
      some (cursorConfig (.decodeHead ⟨0, by decide⟩) (MachineCodeSymbol.header :: leftRev) suffix) := by cases suffix <;> rfl
theorem decodeHead_markedCell_run_exact (cell : Option MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (markedCellWord cell).length (cursorConfig (.decodeHead ⟨0, by decide⟩) leftRev (List.append (markedCellWord cell) suffix)) =
      some (cursorConfig (.decodeHead ⟨0, by decide⟩) (List.append (markedCellWord cell).reverse leftRev) suffix) := by
  rw [markedCellWord_length, markedCellWord_eq]
  have hassoc : List.append (List.append (ticks (optionalCodeSymbolTag cell)) ([MachineCodeSymbol.header] : Word MachineCodeSymbol)) suffix =
        List.append (ticks (optionalCodeSymbolTag cell)) (MachineCodeSymbol.header :: suffix) :=
    List.append_assoc _ _ _
  rw [hassoc, TuringMachine.runConfigExact?_add, decodeHead_ticks_run_exact cell]
  simp only
  change machine.runConfigExact? 1 (cursorConfig (.decodeHead (headCount cell)) (List.append (ticks (optionalCodeSymbolTag cell)) leftRev) (MachineCodeSymbol.header :: suffix)) = _
  rw [TuringMachine.runConfigExact?, decodeHead_header_step]
  simp only [TuringMachine.runConfigExact?]
  simp [List.reverse_append, ticks_reverse]
theorem decodeHead_markedCells_run_exact (cells : List (Option MachineCodeSymbol)) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (markedCellsWord cells).length (cursorConfig (.decodeHead ⟨0, by decide⟩) leftRev (List.append (markedCellsWord cells) suffix)) =
      some (cursorConfig (.decodeHead ⟨0, by decide⟩) (List.append (markedCellsWord cells).reverse leftRev) suffix) := by
  induction cells generalizing leftRev with
  | nil =>
      rfl
  | cons cell cells ih =>
      rw [markedCellsWord_cons]
      have hlength : (List.append (markedCellWord cell) (markedCellsWord cells) : Word MachineCodeSymbol).length = (markedCellWord cell).length + (markedCellsWord cells).length :=
        List.length_append
      rw [hlength]
      have hassoc : List.append (List.append (markedCellWord cell) (markedCellsWord cells)) suffix =
            List.append (markedCellWord cell) (List.append (markedCellsWord cells) suffix) :=
        List.append_assoc _ _ _
      rw [hassoc, TuringMachine.runConfigExact?_add, decodeHead_markedCell_run_exact]
      simp only
      rw [ih]
      simp [List.reverse_append, List.append_assoc]
def leftScanConfig (control : Control) (remaining rightWord : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control := match remaining with
  | [] =>
      { state := control
        tape :=
          { left := []
            head := none
            right := rightWord.map some } }
  | current :: rest =>
      { state := control
        tape :=
          { left := rest.map some
            head := some current
            right := rightWord.map some } }
theorem decodeHead_done_step (count : Fin 10) (leftHead : MachineCodeSymbol) (leftTail rightAfter : Word MachineCodeSymbol) :
    machine.stepConfig (cursorConfig (.decodeHead count) (leftHead :: leftTail) (MachineCodeSymbol.done :: rightAfter)) =
      some (leftScanConfig (.restoreCells (decodedHead count)) (leftHead :: leftTail) (MachineCodeSymbol.done :: rightAfter)) := by rfl
theorem decodeHead_cell_run_exact (cell : Option MachineCodeSymbol) (leftHead : MachineCodeSymbol) (leftTail rightAfter : Word MachineCodeSymbol) :
    machine.runConfigExact? (optionalCodeSymbolTag cell + 1) (cursorConfig (.decodeHead ⟨0, by decide⟩) (leftHead :: leftTail) (List.append (optionalCellWord cell) rightAfter)) =
      some (leftScanConfig (.restoreCells cell) (List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail)) (MachineCodeSymbol.done :: rightAfter)) := by
  rw [optionalCellWord_eq_ticks_done]
  have hassoc : List.append (List.append (ticks (optionalCodeSymbolTag cell)) ([MachineCodeSymbol.done] : Word MachineCodeSymbol)) rightAfter =
        List.append (ticks (optionalCodeSymbolTag cell)) (MachineCodeSymbol.done :: rightAfter) :=
    List.append_assoc _ _ _
  rw [hassoc, TuringMachine.runConfigExact?_add, decodeHead_ticks_run_exact]
  simp only
  change machine.runConfigExact? 1 (cursorConfig (.decodeHead (headCount cell)) (List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail))
          (MachineCodeSymbol.done :: rightAfter)) = _
  rw [TuringMachine.runConfigExact?]
  have hleft : List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  cases hshape : List.append (ticks (optionalCodeSymbolTag cell)) (leftHead :: leftTail) with
  | nil => contradiction
  | cons next rest =>
      rw [decodeHead_done_step, decodedHead_headCount]
      simp only [TuringMachine.runConfigExact?]
theorem restoreCells_tick_step (head : Option MachineCodeSymbol) (next : MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.restoreCells head) (MachineCodeSymbol.tick :: next :: remaining) rightWord) =
      some (leftScanConfig (.restoreCells head) (next :: remaining) (MachineCodeSymbol.tick :: rightWord)) := by rfl
theorem restoreCells_header_step (head : Option MachineCodeSymbol) (next : MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.restoreCells head) (MachineCodeSymbol.header :: next :: remaining) rightWord) =
      some (leftScanConfig (.restoreCells head) (next :: remaining) (MachineCodeSymbol.done :: rightWord)) := by rfl
theorem restoreCells_blank_step (head : Option MachineCodeSymbol) (next : MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.restoreCells head) (MachineCodeSymbol.blank :: next :: remaining) rightWord) =
      some (leftScanConfig (.restoreCount head) (next :: remaining) (MachineCodeSymbol.done :: rightWord)) := by rfl
theorem restoreCells_ticks_run_exact (count : Nat) (head : Option MachineCodeSymbol) (next : MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? count (leftScanConfig (.restoreCells head) (List.append (ticks count) (next :: remaining)) rightWord) =
      some (leftScanConfig (.restoreCells head) (next :: remaining) (List.append (ticks count) rightWord)) := by
  induction count generalizing rightWord with
  | zero =>
      rfl
  | succ count ih =>
      change machine.runConfigExact? (count + 1) (leftScanConfig (.restoreCells head) (MachineCodeSymbol.tick :: List.append (ticks count) (next :: remaining)) rightWord) = _
      rw [TuringMachine.runConfigExact?]
      have hrest : List.append (ticks count) (next :: remaining) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      cases hshape : List.append (ticks count) (next :: remaining) with
      | nil => contradiction
      | cons actualNext actualRemaining =>
          rw [restoreCells_tick_step]
          simp only
          have ih' := ih (MachineCodeSymbol.tick :: rightWord)
          rw [hshape] at ih'
          rw [ih']
          have hwords : List.append (ticks count) (MachineCodeSymbol.tick :: rightWord) = List.append (ticks (count + 1)) rightWord := by
            calc
              List.append (ticks count) (MachineCodeSymbol.tick :: rightWord) = MachineCodeSymbol.tick :: List.append (ticks count) rightWord := ticks_append_tick count rightWord
              _ = List.append (ticks (count + 1)) rightWord := by
                rfl
          rw [hwords]
theorem restoreCells_ticks_run_exact_nonempty (count : Nat) (head : Option MachineCodeSymbol) (tail rightWord : Word MachineCodeSymbol) (htail : tail ≠ []) :
    machine.runConfigExact? count (leftScanConfig (.restoreCells head) (List.append (ticks count) tail) rightWord) =
      some (leftScanConfig (.restoreCells head) tail (List.append (ticks count) rightWord)) := by
  cases tail with
  | nil => contradiction
  | cons next remaining =>
      exact restoreCells_ticks_run_exact count head next remaining rightWord
theorem restoreCells_markedCell_run_exact (cell : Option MachineCodeSymbol) (head : Option MachineCodeSymbol) (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (markedCellWord cell).length (leftScanConfig (.restoreCells head) (List.append (markedCellWord cell).reverse (next :: remaining)) rightWord) =
      some (leftScanConfig (.restoreCells head) (next :: remaining) (List.append (optionalCellWord cell) rightWord)) := by
  have hreverse : (markedCellWord cell).reverse = MachineCodeSymbol.header :: ticks (optionalCodeSymbolTag cell) := by
    simp [markedCellWord, List.reverse_append, ticks_reverse]
  rw [markedCellWord_length, hreverse]
  change machine.runConfigExact? (optionalCodeSymbolTag cell + 1) (leftScanConfig (.restoreCells head) (MachineCodeSymbol.header ::
            List.append (ticks (optionalCodeSymbolTag cell)) (next :: remaining)) rightWord) = _
  rw [show optionalCodeSymbolTag cell + 1 = 1 + optionalCodeSymbolTag cell by lia]
  rw [TuringMachine.runConfigExact?_add, TuringMachine.runConfigExact?]
  simp only [TuringMachine.runConfigExact?]
  have hrest : List.append (ticks (optionalCodeSymbolTag cell)) (next :: remaining) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  cases hshape : List.append (ticks (optionalCodeSymbolTag cell)) (next :: remaining) with
  | nil => contradiction
  | cons actualNext actualRemaining =>
      rw [restoreCells_header_step]
      simp only
      have hticks := restoreCells_ticks_run_exact (optionalCodeSymbolTag cell) head next remaining (MachineCodeSymbol.done :: rightWord)
      rw [hshape] at hticks
      rw [hticks, optionalCellWord_eq_ticks_done]
      simp [List.append_assoc]
theorem restoreCells_markedCells_run_exact (cells : List (Option MachineCodeSymbol)) (head : Option MachineCodeSymbol) (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (markedCellsWord cells).length (leftScanConfig (.restoreCells head) (List.append (markedCellsWord cells).reverse (next :: remaining)) rightWord) =
      some (leftScanConfig (.restoreCells head) (next :: remaining) (List.append (cellsPayloadWord cells) rightWord)) := by
  induction cells generalizing next remaining rightWord with
  | nil =>
      rfl
  | cons cell cells ih =>
      have hreverseCell : (markedCellWord cell).reverse = MachineCodeSymbol.header :: ticks (optionalCodeSymbolTag cell) := by
        simp [markedCellWord, List.reverse_append, ticks_reverse]
      rw [markedCellsWord_cons]
      have hlength : (List.append (markedCellWord cell) (markedCellsWord cells) : Word MachineCodeSymbol).length =
            (markedCellsWord cells).length + (markedCellWord cell).length := by
        simp
        lia
      rw [hlength, TuringMachine.runConfigExact?_add]
      have hreverseAppend : (List.append (markedCellWord cell) (markedCellsWord cells) : Word MachineCodeSymbol).reverse =
            List.append (markedCellsWord cells).reverse (markedCellWord cell).reverse := by
        exact List.reverse_append
      have hsource : List.append (List.append (markedCellWord cell) (markedCellsWord cells)).reverse (next :: remaining) =
            List.append (markedCellsWord cells).reverse (MachineCodeSymbol.header :: List.append (ticks (optionalCodeSymbolTag cell)) (next :: remaining)) := by
        rw [hreverseAppend, hreverseCell]
        exact List.append_assoc _ _ _
      rw [hsource]
      rw [ih (next := MachineCodeSymbol.header) (remaining := List.append (ticks (optionalCodeSymbolTag cell)) (next :: remaining)) (rightWord := rightWord)]
      simp only
      have hcellSource : (MachineCodeSymbol.header :: List.append (ticks (optionalCodeSymbolTag cell)) (next :: remaining) : Word MachineCodeSymbol) =
            List.append (markedCellWord cell).reverse (next :: remaining) := by
        rw [hreverseCell]
        rfl
      rw [hcellSource]
      rw [restoreCells_markedCell_run_exact cell head next remaining (List.append (cellsPayloadWord cells) rightWord)]
      simp [cellsPayloadWord, List.append_assoc]
def restoreHeadAndCellsSteps (head : Option MachineCodeSymbol) (cells : List (Option MachineCodeSymbol)) : Nat := optionalCodeSymbolTag head + (markedCellsWord cells).length + 1
theorem restoreHeadAndCells_run_exact (head : Option MachineCodeSymbol) (cells : List (Option MachineCodeSymbol)) (next : MachineCodeSymbol)
    (remaining rightAfter : Word MachineCodeSymbol) :
    machine.runConfigExact? (restoreHeadAndCellsSteps head cells) (leftScanConfig (.restoreCells head)
          (List.append (ticks (optionalCodeSymbolTag head)) (List.append (markedCellsWord cells).reverse (MachineCodeSymbol.blank :: next :: remaining)))
          (MachineCodeSymbol.done :: rightAfter)) =
      some (leftScanConfig (.restoreCount head) (next :: remaining)
          (MachineCodeSymbol.done :: List.append (cellsPayloadWord cells) (List.append (optionalCellWord head) rightAfter))) := by
  unfold restoreHeadAndCellsSteps
  rw [show optionalCodeSymbolTag head + (markedCellsWord cells).length + 1 = optionalCodeSymbolTag head + ((markedCellsWord cells).length + 1) by lia]
  rw [TuringMachine.runConfigExact?_add]
  rw [restoreCells_ticks_run_exact_nonempty (optionalCodeSymbolTag head) head (List.append (markedCellsWord cells).reverse (MachineCodeSymbol.blank :: next :: remaining))
    (MachineCodeSymbol.done :: rightAfter) (by
      intro h
      have := congrArg List.length h
      simp at this)]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [restoreCells_markedCells_run_exact cells head MachineCodeSymbol.blank (next :: remaining)]
  simp only
  change machine.runConfigExact? 1 (leftScanConfig (.restoreCells head) (MachineCodeSymbol.blank :: next :: remaining)
          (List.append (cellsPayloadWord cells) (List.append (ticks (optionalCodeSymbolTag head)) (MachineCodeSymbol.done :: rightAfter)))) = _
  rw [TuringMachine.runConfigExact?, restoreCells_blank_step]
  simp only [TuringMachine.runConfigExact?]
  rw [optionalCellWord_eq_ticks_done]
  simp [List.append_assoc]
theorem restoreCount_transition_step (head : Option MachineCodeSymbol) (next : MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.restoreCount head) (MachineCodeSymbol.transition :: next :: remaining) rightWord) =
      some (leftScanConfig (.restoreCount head) (next :: remaining) (MachineCodeSymbol.tick :: rightWord)) := by rfl
theorem restoreCount_done_step (head : Option MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.restoreCount head) (MachineCodeSymbol.done :: remaining) rightWord) =
      some (leftScanConfig (.seekTopHeader head) remaining (MachineCodeSymbol.done :: rightWord)) := by cases remaining <;> rfl
theorem restoreCount_markers_run_exact (count : Nat) (head : Option MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? count (leftScanConfig (.restoreCount head) (List.append (transitionMarkers count) (MachineCodeSymbol.done :: remaining)) rightWord) =
      some (leftScanConfig (.restoreCount head) (MachineCodeSymbol.done :: remaining) (List.append (ticks count) rightWord)) := by
  induction count generalizing rightWord with
  | zero =>
      rfl
  | succ count ih =>
      change machine.runConfigExact? (count + 1) (leftScanConfig (.restoreCount head) (MachineCodeSymbol.transition ::
              List.append (transitionMarkers count) (MachineCodeSymbol.done :: remaining)) rightWord) = _
      rw [TuringMachine.runConfigExact?]
      have hrest : List.append (transitionMarkers count) (MachineCodeSymbol.done :: remaining) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      cases hshape : List.append (transitionMarkers count) (MachineCodeSymbol.done :: remaining) with
      | nil => contradiction
      | cons next rest =>
          rw [restoreCount_transition_step]
          simp only
          have ih' := ih (MachineCodeSymbol.tick :: rightWord)
          rw [hshape] at ih'
          rw [ih']
          have hwords : List.append (ticks count) (MachineCodeSymbol.tick :: rightWord) = List.append (ticks (count + 1)) rightWord := by
            calc
              List.append (ticks count) (MachineCodeSymbol.tick :: rightWord) = MachineCodeSymbol.tick :: List.append (ticks count) rightWord := ticks_append_tick count rightWord
              _ = List.append (ticks (count + 1)) rightWord := by
                rfl
          rw [hwords]
theorem restoreCount_run_exact (count : Nat) (head : Option MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1) (leftScanConfig (.restoreCount head) (List.append (transitionMarkers count) (MachineCodeSymbol.done :: remaining)) rightWord) =
      some (leftScanConfig (.seekTopHeader head) remaining (MachineCodeSymbol.done :: List.append (ticks count) rightWord)) := by
  rw [TuringMachine.runConfigExact?_add, restoreCount_markers_run_exact]
  simp only
  change machine.runConfigExact? 1 (leftScanConfig (.restoreCount head) (MachineCodeSymbol.done :: remaining) (List.append (ticks count) rightWord)) = _
  rw [TuringMachine.runConfigExact?, restoreCount_done_step]
  simp only [TuringMachine.runConfigExact?]
theorem seekTopHeader_tick_step (head : Option MachineCodeSymbol) (next : MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.seekTopHeader head) (MachineCodeSymbol.tick :: next :: remaining) rightWord) =
      some (leftScanConfig (.seekTopHeader head) (next :: remaining) (MachineCodeSymbol.tick :: rightWord)) := by rfl
theorem seekTopHeader_done_step (head : Option MachineCodeSymbol) (next : MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.seekTopHeader head) (MachineCodeSymbol.done :: next :: remaining) rightWord) =
      some (leftScanConfig (.seekTopHeader head) (next :: remaining) (MachineCodeSymbol.done :: rightWord)) := by rfl
theorem seekTopHeader_header_step (head : Option MachineCodeSymbol) (rightWord : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.seekTopHeader head) [MachineCodeSymbol.header] rightWord) =
      some (leftScanConfig (.gateBounce head) [] (MachineCodeSymbol.header :: rightWord)) := by rfl
theorem seekTopHeader_ticks_run_exact (count : Nat) (head : Option MachineCodeSymbol) (next : MachineCodeSymbol) (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? count (leftScanConfig (.seekTopHeader head) (List.append (ticks count) (next :: remaining)) rightWord) =
      some (leftScanConfig (.seekTopHeader head) (next :: remaining) (List.append (ticks count) rightWord)) := by
  induction count generalizing rightWord with
  | zero =>
      rfl
  | succ count ih =>
      change machine.runConfigExact? (count + 1) (leftScanConfig (.seekTopHeader head) (MachineCodeSymbol.tick :: List.append (ticks count) (next :: remaining)) rightWord) = _
      rw [TuringMachine.runConfigExact?]
      have hrest : List.append (ticks count) (next :: remaining) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      cases hshape : List.append (ticks count) (next :: remaining) with
      | nil => contradiction
      | cons actualNext actualRemaining =>
          rw [seekTopHeader_tick_step]
          simp only
          have ih' := ih (MachineCodeSymbol.tick :: rightWord)
          rw [hshape] at ih'
          rw [ih']
          have hwords : List.append (ticks count) (MachineCodeSymbol.tick :: rightWord) = List.append (ticks (count + 1)) rightWord := by
            calc
              List.append (ticks count) (MachineCodeSymbol.tick :: rightWord) = MachineCodeSymbol.tick :: List.append (ticks count) rightWord := ticks_append_tick count rightWord
              _ = List.append (ticks (count + 1)) rightWord := by
                rfl
          rw [hwords]
def seekTopHeaderSteps (state fuel : Nat) : Nat := state + 1 + fuel + 1
theorem seekTopHeader_fields_run_exact (state fuel : Nat) (head : Option MachineCodeSymbol) (rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (seekTopHeaderSteps state fuel) (leftScanConfig (.seekTopHeader head)
          (List.append (ticks state) (MachineCodeSymbol.done :: List.append (ticks fuel) [MachineCodeSymbol.header]))
          rightWord) =
      some (leftScanConfig (.gateBounce head) [] (MachineCodeSymbol.header :: List.append (ticks fuel) (MachineCodeSymbol.done :: List.append (ticks state) rightWord))) := by
  unfold seekTopHeaderSteps
  rw [show state + 1 + fuel + 1 = state + (1 + (fuel + 1)) by lia]
  rw [TuringMachine.runConfigExact?_add, seekTopHeader_ticks_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  have hdone : machine.runConfigExact? 1 (leftScanConfig (.seekTopHeader head) (MachineCodeSymbol.done :: List.append (ticks fuel) [MachineCodeSymbol.header])
            (List.append (ticks state) rightWord)) =
        some (leftScanConfig (.seekTopHeader head) (List.append (ticks fuel) [MachineCodeSymbol.header]) (MachineCodeSymbol.done :: List.append (ticks state) rightWord)) := by
    rw [TuringMachine.runConfigExact?]
    have hrest : List.append (ticks fuel) [MachineCodeSymbol.header] ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
    cases hshape : List.append (ticks fuel) [MachineCodeSymbol.header] with
    | nil => contradiction
    | cons next remaining =>
        rw [seekTopHeader_done_step]
        simp only [TuringMachine.runConfigExact?]
  rw [hdone]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [seekTopHeader_ticks_run_exact fuel head MachineCodeSymbol.header []]
  simp only
  change machine.runConfigExact? 1 (leftScanConfig (.seekTopHeader head) [MachineCodeSymbol.header]
          (List.append (ticks fuel) (MachineCodeSymbol.done :: List.append (ticks state) rightWord))) = _
  rw [TuringMachine.runConfigExact?, seekTopHeader_header_step]
  simp only [TuringMachine.runConfigExact?]
def gateTape (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol := match word with
  | [] =>
      { left := [none]
        head := none
        right := [] }
  | first :: rest =>
      { left := [none]
        head := some first
        right := rest.map some }
def gateConfig (head : Option MachineCodeSymbol) (word : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate head
  tape := gateTape word
theorem gateBounce_step (head : Option MachineCodeSymbol) (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    machine.stepConfig (leftScanConfig (.gateBounce head) [] (first :: rest)) = some (gateConfig head (first :: rest)) := by cases rest <;> rfl
theorem encodeNat_reverse_eq_done_ticks (count : Nat) : (MachineDescription.encodeNat count).reverse = MachineCodeSymbol.done :: ticks count := by
  rw [encodeNat_eq_ticks_done]
  simp [List.reverse_append, ticks_reverse]
theorem cellsPayloadAppend_eq_encodePayloadAppend (cells : List (Option MachineCodeSymbol)) (suffix : Word MachineCodeSymbol) :
    cellsPayloadAppend cells suffix = encodeOptionalCodeSymbolsPayloadAppend cells suffix := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      simp only [cellsPayloadAppend, encodeOptionalCodeSymbolsPayloadAppend]
      rw [ih]
      simp [optionalCellWord, encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend]
theorem encodeNatAppend_eq_ticks_done_append (count : Nat) (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend count suffix = List.append (ticks count) (MachineCodeSymbol.done :: suffix) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change MachineCodeSymbol.tick :: MachineDescription.encodeNatAppend count suffix = MachineCodeSymbol.tick :: List.append (ticks count) (MachineCodeSymbol.done :: suffix)
      rw [ih]
def afterHeadWord {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (optionalCellsWord L.right) (Frame.callerTag :: callerData)
def topFieldsRev {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol :=
  List.append (ticks L.state.val) (MachineCodeSymbol.done :: List.append (ticks L.fuel) [MachineCodeSymbol.header])
def countBaseLeftRev {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := MachineCodeSymbol.done :: topFieldsRev L
theorem scannedStateLeft_eq_countBase {stateCount : Nat} (L : Layout stateCount) :
    List.append (MachineDescription.encodeNat L.state.val).reverse (List.append (MachineDescription.encodeNat L.fuel).reverse [MachineCodeSymbol.header]) = countBaseLeftRev L := by
  rw [encodeNat_reverse_eq_done_ticks, encodeNat_reverse_eq_done_ticks]
  simp [countBaseLeftRev, topFieldsRev]
theorem headSuffix_eq_encoding {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : headSuffix L callerData = encodeOptionalCodeSymbolAppend L.head
        (encodeOptionalCodeSymbolsAppend L.right (Frame.callerTag :: callerData)) := by
  unfold headSuffix
  rw [← encodeOptionalCodeSymbolsAppend_eq_append, ← encodeOptionalCodeSymbolAppend_eq_append]
theorem afterStateWord_eq_count_payload {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    afterStateWord L callerData = MachineDescription.encodeNatAppend L.left.length (cellsPayloadAppend L.left (headSuffix L callerData)) := by
  unfold afterStateWord encodeOptionalCodeSymbolsAppend
  rw [headSuffix_eq_encoding, cellsPayloadAppend_eq_encodePayloadAppend]
  rfl
def rebuiltWord {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header :: List.append (ticks L.fuel) (MachineCodeSymbol.done :: List.append (ticks L.state.val)
          (MachineCodeSymbol.done :: List.append (ticks L.left.length) (MachineCodeSymbol.done :: List.append (cellsPayloadWord L.left)
                  (List.append (optionalCellWord L.head) (afterHeadWord L callerData)))))
theorem rebuiltWord_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    rebuiltWord L callerData = Frame.protectedWord L callerData := by
  unfold rebuiltWord Frame.protectedWord Layout.encodeAppend afterHeadWord
  rw [← cellsPayloadAppend_eq_append L.left (List.append (optionalCellWord L.head) (List.append (optionalCellsWord L.right) (Frame.callerTag :: callerData)))]
  rw [cellsPayloadAppend_eq_encodePayloadAppend, ← encodeOptionalCodeSymbolAppend_eq_append]
  rw [← encodeOptionalCodeSymbolsAppend_eq_append]
  rw [encodeNatAppend_eq_ticks_done_append, encodeNatAppend_eq_ticks_done_append]
  unfold encodeOptionalCodeSymbolsAppend
  rw [encodeNatAppend_eq_ticks_done_append, encodeNatAppend_eq_ticks_done_append L.left.length]
theorem decodeHead_cell_run_exact_nonempty (cell : Option MachineCodeSymbol) (leftRev rightAfter : Word MachineCodeSymbol) (hleft : leftRev ≠ []) :
    machine.runConfigExact? (optionalCodeSymbolTag cell + 1) (cursorConfig (.decodeHead ⟨0, by decide⟩) leftRev (List.append (optionalCellWord cell) rightAfter)) =
      some (leftScanConfig (.restoreCells cell) (List.append (ticks (optionalCodeSymbolTag cell)) leftRev) (MachineCodeSymbol.done :: rightAfter)) := by
  cases leftRev with
  | nil => contradiction
  | cons leftHead leftTail =>
      exact decodeHead_cell_run_exact cell leftHead leftTail rightAfter
theorem restoreHeadAndCells_run_exact_nonemptyTail (head : Option MachineCodeSymbol) (cells : List (Option MachineCodeSymbol)) (tail rightAfter : Word MachineCodeSymbol)
    (htail : tail ≠ []) :
    machine.runConfigExact? (restoreHeadAndCellsSteps head cells) (leftScanConfig (.restoreCells head)
          (List.append (ticks (optionalCodeSymbolTag head)) (List.append (markedCellsWord cells).reverse (MachineCodeSymbol.blank :: tail)))
          (MachineCodeSymbol.done :: rightAfter)) =
      some (leftScanConfig (.restoreCount head) tail (MachineCodeSymbol.done :: List.append (cellsPayloadWord cells) (List.append (optionalCellWord head) rightAfter))) := by
  cases tail with
  | nil => contradiction
  | cons next remaining =>
      exact restoreHeadAndCells_run_exact head cells next remaining rightAfter
theorem protectedWord_eq_header_fuel {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Frame.protectedWord L callerData = MachineCodeSymbol.header :: MachineDescription.encodeNatAppend L.fuel (stateSuffix L callerData) := by rfl
def markedCellsSteps (cells : List (Option MachineCodeSymbol)) : Nat := (markedCellsWord cells).length
theorem decodeHead_markedCells_run_exact_steps (cells : List (Option MachineCodeSymbol)) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (markedCellsSteps cells) (cursorConfig (.decodeHead ⟨0, by decide⟩) leftRev (List.append (markedCellsWord cells) suffix)) =
      some (cursorConfig (.decodeHead ⟨0, by decide⟩) (List.append (markedCellsWord cells).reverse leftRev) suffix) := by
  exact decodeHead_markedCells_run_exact cells leftRev suffix
def locatorPostBlankSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  markedCellsSteps L.left + ((optionalCodeSymbolTag L.head + 1) + (restoreHeadAndCellsSteps L.head L.left + ((L.left.length + 1) + (seekTopHeaderSteps L.state.val L.fuel + 1))))
def locatorSteps {stateCount : Nat} (L : Layout stateCount) : Nat := 1 + ((L.fuel + 1) +
      ((L.state.val + 1) + ((2 * L.left.length + 2) + (processCellsSteps [] L.left + (1 + locatorPostBlankSteps L)))))
def locatorStartConfig {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control :=
  cursorConfig .header [] (Frame.protectedWord L callerData)
theorem run_exact {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : machine.runConfigExact? (locatorSteps L) (locatorStartConfig L callerData) =
      some (gateConfig L.head (Frame.protectedWord L callerData)) := by
  unfold locatorSteps
  rw [TuringMachine.runConfigExact?_add]
  have hheader : machine.runConfigExact? 1 (locatorStartConfig L callerData) =
        some (cursorConfig .fuel [MachineCodeSymbol.header] (MachineDescription.encodeNatAppend L.fuel (stateSuffix L callerData))) := by
    unfold locatorStartConfig
    rw [protectedWord_eq_header_fuel, TuringMachine.runConfigExact?, header_step]
    simp only [TuringMachine.runConfigExact?]
  rw [hheader]
  simp only
  rw [TuringMachine.runConfigExact?_add, fuel_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  unfold stateSuffix
  rw [state_run_exact]
  simp only
  rw [scannedStateLeft_eq_countBase, afterStateWord_eq_count_payload, TuringMachine.runConfigExact?_add]
  unfold countBaseLeftRev
  rw [markCountBoundary_roundTrip_exact L.left.length (topFieldsRev L) (cellsPayloadAppend L.left (headSuffix L callerData))]
  simp only
  rw [show MachineCodeSymbol.done :: topFieldsRev L = countBaseLeftRev L by rfl]
  rw [TuringMachine.runConfigExact?_add]
  rw [processAllCells_run_exact L.left (countBaseLeftRev L) (headSuffix L callerData)]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  have hblank : machine.runConfigExact? 1 (cursorConfig .countCheck (List.append (transitionMarkers L.left.length) (countBaseLeftRev L))
            (MachineCodeSymbol.blank :: List.append (markedCellsWord L.left) (headSuffix L callerData))) =
        some (cursorConfig (.decodeHead ⟨0, by decide⟩) (MachineCodeSymbol.blank :: List.append (transitionMarkers L.left.length) (countBaseLeftRev L))
            (List.append (markedCellsWord L.left) (headSuffix L callerData))) := by
    rw [TuringMachine.runConfigExact?, countCheck_blank_step]
    simp only [TuringMachine.runConfigExact?]
  rw [hblank]
  simp only
  unfold locatorPostBlankSteps
  rw [TuringMachine.runConfigExact?_add, decodeHead_markedCells_run_exact_steps]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  have hheadSuffix : headSuffix L callerData = List.append (optionalCellWord L.head) (afterHeadWord L callerData) := by
    rfl
  rw [hheadSuffix]
  have hdecodeLeft : List.append (markedCellsWord L.left).reverse (MachineCodeSymbol.blank :: List.append (transitionMarkers L.left.length) (countBaseLeftRev L)) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  rw [decodeHead_cell_run_exact_nonempty L.head (List.append (markedCellsWord L.left).reverse
      (MachineCodeSymbol.blank :: List.append (transitionMarkers L.left.length) (countBaseLeftRev L)))
    (afterHeadWord L callerData) hdecodeLeft]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  have hrestoreTail : List.append (transitionMarkers L.left.length) (countBaseLeftRev L) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [countBaseLeftRev] at this
  rw [restoreHeadAndCells_run_exact_nonemptyTail L.head L.left (List.append (transitionMarkers L.left.length) (countBaseLeftRev L)) (afterHeadWord L callerData) hrestoreTail]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  unfold countBaseLeftRev
  rw [restoreCount_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  unfold topFieldsRev
  rw [seekTopHeader_fields_run_exact]
  simp only
  change machine.runConfigExact? 1 (leftScanConfig (.gateBounce L.head) ([] : Word MachineCodeSymbol) (rebuiltWord L callerData)) = _
  rw [← rebuiltWord_eq_protectedWord, TuringMachine.runConfigExact?]
  unfold rebuiltWord
  rw [gateBounce_step]
  simp only [TuringMachine.runConfigExact?]
end HeadLocator
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
