import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Context.KeyHead

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.DirectContextUpdate

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

/-!
### Tape-equivalence phase adapters

Each finite phase is proved against a canonical cursor tape.  These adapters
let the next phase consume the equivalent physical endpoint produced by the
preceding rewind without strengthening the public endpoint to an irrelevant
window identity.
-/

namespace DirectPhases

theorem prefix_computes_of_tape_equiv
    (action : Action) (target : Nat)
    (rest : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Prefix.sourceConfig action target rest).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Prefix.machine
        { state := Prefix.Control.target action, tape := sourceTape }
        { state := Prefix.Control.ready action, tape := targetTape } ∧
      Tape.Equiv (Prefix.targetConfig action target rest).tape targetTape := by
  have hrun := Prefix.run_exact action target rest
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨targetConfig', htargetRun, htargetState, htargetTape⟩
  rcases targetConfig' with ⟨state, tape⟩
  simp only [Prefix.targetConfig] at htargetState
  subst state
  exact ⟨tape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun),
    htargetTape⟩

theorem boundary_computes_of_tape_equiv
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (nextCount : Nat)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Boundary.sourceConfig baseLeftRev cells nextCount suffix).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Boundary.machine
        { state := Boundary.Control.locate .count, tape := sourceTape }
        { state := Boundary.Control.ready, tape := targetTape } ∧
      Tape.Equiv
        (Boundary.targetConfig baseLeftRev cells nextCount suffix).tape
        targetTape := by
  have hrun := Boundary.run_exact baseLeftRev cells nextCount suffix
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨targetConfig', htargetRun, htargetState, htargetTape⟩
  rcases targetConfig' with ⟨state, tape⟩
  simp only [Boundary.targetConfig] at htargetState
  subst state
  exact ⟨tape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun),
    htargetTape⟩

theorem prepend_computes_of_tape_equiv
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        baseLeftRev count suffix).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine cell)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord
            baseLeftRev count cell suffix))
        targetTape := by
  rcases FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.run_exact
      baseLeftRev count cell suffix with
    ⟨canonicalEndpoint, hrun, hstate, hcanonicalTape⟩
  rcases canonicalEndpoint with ⟨canonicalState, canonicalTape⟩
  simp only at hstate
  subst canonicalState
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨targetConfig', htargetRun, htargetState, htargetTape⟩
  rcases targetConfig' with ⟨state, tape⟩
  simp only at htargetState
  subst state
  refine ⟨tape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun), ?_⟩
  exact Tape.Equiv.trans hcanonicalTape htargetTape

theorem pop_computes_of_tape_equiv
    (baseLeftRev : Word MachineCodeSymbol)
    (remaining : Nat) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        baseLeftRev remaining cell suffix).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready cell
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord
            baseLeftRev remaining suffix))
        targetTape := by
  rcases FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.run_exact
      baseLeftRev remaining cell suffix with
    ⟨canonicalEndpoint, hrun, hstate, hcanonicalTape⟩
  rcases canonicalEndpoint with ⟨canonicalState, canonicalTape⟩
  simp only at hstate
  subst canonicalState
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨targetConfig', htargetRun, htargetState, htargetTape⟩
  rcases targetConfig' with ⟨state, tape⟩
  simp only at htargetState
  subst state
  refine ⟨tape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun), ?_⟩
  exact Tape.Equiv.trans hcanonicalTape htargetTape

theorem keyHead_computes_of_tape_equiv
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (KeyHead.sourceConfig target head rest).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes KeyHead.machine
        { state := KeyHead.Control.target head, tape := sourceTape }
        { state := KeyHead.Control.ready, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input (KeyHead.targetWord target head rest)) targetTape := by
  have hrun := KeyHead.run_exact target head rest
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨targetConfig', htargetRun, htargetState, htargetTape⟩
  rcases targetConfig' with ⟨state, tape⟩
  simp only [KeyHead.targetConfig] at htargetState
  subst state
  refine ⟨tape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun), ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm (KeyHead.run_exact_target_tape_equiv_input
      target head rest)) htargetTape

def prefixBaseLeftRev (target : Nat) : Word MachineCodeSymbol :=
  Prefix.targetBaseLeftRev target

def rightBaseLeftRev
    (target : Nat) (left : List (Option Bool)) :
    Word MachineCodeSymbol :=
  Boundary.targetBaseLeftRev (prefixBaseLeftRev target) left

theorem prefixBaseLeftRev_reverse (target : Nat) :
    (prefixBaseLeftRev target).reverse =
      MachineDescription.encodeNatAppend target [MachineCodeSymbol.header] := by
  simp [prefixBaseLeftRev, Prefix.targetBaseLeftRev,
    MachineDescription.encodeNatAppend]

theorem rightBaseLeftRev_reverse
    (target : Nat) (left : List (Option Bool)) :
    (rightBaseLeftRev target left).reverse =
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header ::
          MachineDescription.encodeCellListAppend left []) := by
  rw [rightBaseLeftRev, Boundary.targetBaseLeftRev_reverse,
    prefixBaseLeftRev_reverse]
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

theorem prefix_source_tape_eq_context_input
    (action : Action) (target : Nat)
    (left right : List (Option Bool))
    (head : Option Bool)
    (persistent : Word MachineCodeSymbol) :
    (Prefix.sourceConfig action target
      (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
        { left := left, head := head, right := right } persistent)).tape =
      Tape.input
        (contextSourceWord target
          { left := left, head := head, right := right } persistent) := by
  rw [Prefix.source_tape_eq_input]
  rfl

theorem left_cursor_eq_boundary_source
    (action : Action) (target : Nat)
    (left right : List (Option Bool))
    (head : Option Bool)
    (persistent : Word MachineCodeSymbol) :
    (Prefix.targetConfig action target
      (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
        { left := left, head := head, right := right } persistent)).tape =
      (Boundary.sourceConfig (prefixBaseLeftRev target)
        left right.length
        (MachineDescription.encodeCellsAppend right persistent)).tape := by
  rfl

theorem right_cursor_eq_prepend_source
    (target : Nat)
    (left right : List (Option Bool))
    (persistent : Word MachineCodeSymbol) :
    (Boundary.targetConfig (prefixBaseLeftRev target)
      left right.length
      (MachineDescription.encodeCellsAppend right persistent)).tape =
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        (rightBaseLeftRev target left) right.length
        (MachineDescription.encodeCellsAppend right persistent)).tape := by
  rfl

theorem left_cursor_eq_prepend_source
    (action : Action) (target : Nat)
    (left right : List (Option Bool))
    (head : Option Bool)
    (persistent : Word MachineCodeSymbol) :
    (Prefix.targetConfig action target
      (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
        { left := left, head := head, right := right } persistent)).tape =
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        (prefixBaseLeftRev target) left.length
        (MachineDescription.encodeCellsAppend left
          (MachineDescription.encodeCellListAppend right persistent))).tape := by
  rfl

theorem prepend_left_targetWord_eq_context
    (target : Nat) (write head : Option Bool)
    (left right : List (Option Bool))
    (persistent : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord
        (prefixBaseLeftRev target) left.length write
        (MachineDescription.encodeCellsAppend left
          (MachineDescription.encodeCellListAppend right persistent)) =
      contextSourceWord target
        { left := write :: left, head := head, right := right }
        persistent := by
  unfold FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord contextSourceWord
    RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [prefixBaseLeftRev_reverse]
  cases write with
  | none =>
      simp [MachineDescription.encodeCellListAppend,
        MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeCellsAppend, List.append_assoc]
  | some bit =>
      cases bit <;>
        simp [MachineDescription.encodeCellListAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeCellsAppend, List.append_assoc]

theorem prepend_right_targetWord_eq_context
    (target : Nat) (write head : Option Bool)
    (left right : List (Option Bool))
    (persistent : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord
        (rightBaseLeftRev target left) right.length write
        (MachineDescription.encodeCellsAppend right persistent) =
      contextSourceWord target
        { left := left, head := head, right := write :: right }
        persistent := by
  unfold FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord contextSourceWord
    RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [rightBaseLeftRev_reverse]
  have hright :
      MachineDescription.encodeNatAppend (right.length + 1)
          (MachineDescription.encodeCellAppend write
            (MachineDescription.encodeCellsAppend right persistent)) =
        MachineDescription.encodeCellListAppend (write :: right)
          persistent := by
    rfl
  rw [hright]
  have hleft :
      MachineDescription.encodeCellListAppend left
          (MachineDescription.encodeCellListAppend (write :: right) persistent) =
        List.append
          (MachineDescription.encodeCellListAppend left
            ([] : Word MachineCodeSymbol))
          (MachineDescription.encodeCellListAppend (write :: right)
            persistent) := by
    have h := encodeCellListAppend_append left
      ([] : Word MachineCodeSymbol)
      (MachineDescription.encodeCellListAppend (write :: right) persistent)
    change
      MachineDescription.encodeCellListAppend left
          (MachineDescription.encodeCellListAppend (write :: right) persistent) =
        List.append
          (MachineDescription.encodeCellListAppend left
            ([] : Word MachineCodeSymbol))
          (MachineDescription.encodeCellListAppend (write :: right)
            persistent) at h
    exact h
  rw [hleft]
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

theorem pop_left_targetWord_eq_context
    (target : Nat) (head : Option Bool)
    (remainingLeft right : List (Option Bool))
    (persistent : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord
        (prefixBaseLeftRev target) remainingLeft.length
        (MachineDescription.encodeCellsAppend remainingLeft
          (MachineDescription.encodeCellListAppend right persistent)) =
      contextSourceWord target
        { left := remainingLeft, head := head, right := right }
        persistent := by
  unfold FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord contextSourceWord
    RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [prefixBaseLeftRev_reverse]
  simp [MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend,
    List.append_assoc]

theorem pop_right_targetWord_eq_context
    (target : Nat) (head : Option Bool)
    (left remainingRight : List (Option Bool))
    (persistent : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord
        (rightBaseLeftRev target left) remainingRight.length
        (MachineDescription.encodeCellsAppend remainingRight persistent) =
      contextSourceWord target
        { left := left, head := head, right := remainingRight }
        persistent := by
  unfold FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord contextSourceWord
    RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [rightBaseLeftRev_reverse]
  have hright :
      MachineDescription.encodeNatAppend remainingRight.length
          (MachineDescription.encodeCellsAppend remainingRight persistent) =
        MachineDescription.encodeCellListAppend remainingRight persistent := by
    rfl
  rw [hright]
  have hleft :
      MachineDescription.encodeCellListAppend left
          (MachineDescription.encodeCellListAppend remainingRight persistent) =
        List.append
          (MachineDescription.encodeCellListAppend left
            ([] : Word MachineCodeSymbol))
          (MachineDescription.encodeCellListAppend remainingRight persistent) := by
    have h := encodeCellListAppend_append left
      ([] : Word MachineCodeSymbol)
      (MachineDescription.encodeCellListAppend remainingRight persistent)
    change
      MachineDescription.encodeCellListAppend left
          (MachineDescription.encodeCellListAppend remainingRight persistent) =
        List.append
          (MachineDescription.encodeCellListAppend left
            ([] : Word MachineCodeSymbol))
          (MachineDescription.encodeCellListAppend remainingRight persistent)
        at h
    exact h
  rw [hleft]
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

theorem left_cursor_eq_pop_source
    (action : Action) (target : Nat)
    (nextHead head : Option Bool)
    (remainingLeft right : List (Option Bool))
    (persistent : Word MachineCodeSymbol) :
    (Prefix.targetConfig action target
      (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
        { left := nextHead :: remainingLeft, head := head, right := right }
        persistent)).tape =
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        (prefixBaseLeftRev target) remainingLeft.length nextHead
        (MachineDescription.encodeCellsAppend remainingLeft
          (MachineDescription.encodeCellListAppend right persistent))).tape := by
  cases nextHead with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem right_cursor_eq_pop_source
    (target : Nat)
    (nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (persistent : Word MachineCodeSymbol) :
    (Boundary.targetConfig (prefixBaseLeftRev target)
      left (remainingRight.length + 1)
      (MachineDescription.encodeCellAppend nextHead
        (MachineDescription.encodeCellsAppend remainingRight persistent))).tape =
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        (rightBaseLeftRev target left) remainingRight.length nextHead
        (MachineDescription.encodeCellsAppend remainingRight persistent)).tape := by
  cases nextHead with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem position_left
    (action : Action) (target : Nat)
    (left right : List (Option Bool)) (head : Option Bool)
    (persistent : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (contextSourceWord target
          { left := left, head := head, right := right } persistent))
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Prefix.machine
        { state := Prefix.Control.target action, tape := sourceTape }
        { state := Prefix.Control.ready action, tape := targetTape } ∧
      Tape.Equiv
        (Prefix.targetConfig action target
          (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
            { left := left, head := head, right := right } persistent)).tape
        targetTape := by
  apply prefix_computes_of_tape_equiv
  rw [prefix_source_tape_eq_context_input]
  exact hsource

theorem position_right
    (action : Action) (target : Nat)
    (left right : List (Option Bool)) (head : Option Bool)
    (persistent : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Prefix.targetConfig action target
        (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
          { left := left, head := head, right := right } persistent)).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Boundary.machine
        { state := Boundary.Control.locate .count, tape := sourceTape }
        { state := Boundary.Control.ready, tape := targetTape } ∧
      Tape.Equiv
        (Boundary.targetConfig (prefixBaseLeftRev target)
          left right.length
          (MachineDescription.encodeCellsAppend right persistent)).tape
        targetTape := by
  apply boundary_computes_of_tape_equiv
  rw [← left_cursor_eq_boundary_source action target left right head]
  exact hsource

theorem prepend_left
    (action : Action) (target : Nat)
    (write head : Option Bool)
    (left right : List (Option Bool))
    (persistent : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Prefix.targetConfig action target
        (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
          { left := left, head := head, right := right } persistent)).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (contextSourceWord target
            { left := write :: left, head := head, right := right }
            persistent))
        targetTape := by
  have hsource' : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        (prefixBaseLeftRev target) left.length
        (MachineDescription.encodeCellsAppend left
          (MachineDescription.encodeCellListAppend right persistent))).tape
      sourceTape := by
    rw [← left_cursor_eq_prepend_source action target left right head]
    exact hsource
  rcases prepend_computes_of_tape_equiv
      (prefixBaseLeftRev target) left.length write
      (MachineDescription.encodeCellsAppend left
        (MachineDescription.encodeCellListAppend right persistent))
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [prepend_left_targetWord_eq_context target write head left right
    persistent] at htarget
  exact htarget

theorem prepend_right
    (target : Nat) (write head : Option Bool)
    (left right : List (Option Bool))
    (persistent : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Boundary.targetConfig (prefixBaseLeftRev target)
        left right.length
        (MachineDescription.encodeCellsAppend right persistent)).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (contextSourceWord target
            { left := left, head := head, right := write :: right }
            persistent))
        targetTape := by
  have hsource' : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        (rightBaseLeftRev target left) right.length
        (MachineDescription.encodeCellsAppend right persistent)).tape
      sourceTape := by
    rw [← right_cursor_eq_prepend_source target left right]
    exact hsource
  rcases prepend_computes_of_tape_equiv
      (rightBaseLeftRev target left) right.length write
      (MachineDescription.encodeCellsAppend right persistent)
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [prepend_right_targetWord_eq_context target write head left right
    persistent] at htarget
  exact htarget

theorem pop_left
    (action : Action) (target : Nat)
    (nextHead head : Option Bool)
    (remainingLeft right : List (Option Bool))
    (persistent : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Prefix.targetConfig action target
        (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
          { left := nextHead :: remainingLeft, head := head, right := right }
          persistent)).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready nextHead
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (contextSourceWord target
            { left := remainingLeft, head := nextHead, right := right }
            persistent))
        targetTape := by
  have hsource' : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        (prefixBaseLeftRev target) remainingLeft.length nextHead
        (MachineDescription.encodeCellsAppend remainingLeft
          (MachineDescription.encodeCellListAppend right persistent))).tape
      sourceTape := by
    rw [← left_cursor_eq_pop_source action target nextHead head]
    exact hsource
  rcases pop_computes_of_tape_equiv
      (prefixBaseLeftRev target) remainingLeft.length nextHead
      (MachineDescription.encodeCellsAppend remainingLeft
        (MachineDescription.encodeCellListAppend right persistent))
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [pop_left_targetWord_eq_context target nextHead remainingLeft right
    persistent] at htarget
  exact htarget

theorem pop_right
    (target : Nat) (nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (persistent : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Boundary.targetConfig (prefixBaseLeftRev target)
        left (remainingRight.length + 1)
        (MachineDescription.encodeCellAppend nextHead
          (MachineDescription.encodeCellsAppend remainingRight persistent))).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready nextHead
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (contextSourceWord target
            { left := left, head := nextHead, right := remainingRight }
            persistent))
        targetTape := by
  have hsource' : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        (rightBaseLeftRev target left) remainingRight.length nextHead
        (MachineDescription.encodeCellsAppend remainingRight persistent)).tape
      sourceTape := by
    rw [← right_cursor_eq_pop_source target nextHead left]
    exact hsource
  rcases pop_computes_of_tape_equiv
      (rightBaseLeftRev target left) remainingRight.length nextHead
      (MachineDescription.encodeCellsAppend remainingRight persistent)
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [pop_right_targetWord_eq_context target nextHead left remainingRight
    persistent] at htarget
  exact htarget

theorem keyHead_targetWord_eq_nextSingleKeyWorkWord
    (target : Nat) (nextHead : Option Bool)
    (tape : Tape Bool)
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol) :
    KeyHead.targetWord target nextHead
        (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend tape
          (persistentTable transitions callerSuffix)) =
      nextSingleKeyWorkWord target nextHead tape transitions callerSuffix := by
  rfl

theorem materialize_next_key
    (target : Nat) (nextHead : Option Bool)
    (tape : Tape Bool)
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (contextSourceWord target tape
          (persistentTable transitions callerSuffix))) sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes KeyHead.machine
        { state := KeyHead.Control.target nextHead, tape := sourceTape }
        { state := KeyHead.Control.ready, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (nextSingleKeyWorkWord target nextHead tape transitions
            callerSuffix))
        targetTape := by
  let rest := RuntimeKeySingleKeyRepair.protectedTapeContextsAppend tape
    (persistentTable transitions callerSuffix)
  have hsource' : Tape.Equiv
      (KeyHead.sourceConfig target nextHead rest).tape sourceTape := by
    rw [KeyHead.source_tape_eq_input]
    simpa [rest, KeyHead.sourceWord, contextSourceWord] using hsource
  rcases keyHead_computes_of_tape_equiv
      target nextHead rest sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [keyHead_targetWord_eq_nextSingleKeyWorkWord] at htarget
  exact htarget

/-!
### Four direct physical update traces

The traces below compose only already verified finite phases.  Their final
currency is the exact next key followed by the updated contexts and the
unchanged persistent table.  A following phase must still copy and permute
that table into `canonicalScanRowsConfig` order.
-/

theorem update_left_empty_to_next_key
    (target : Nat) (write oldHead : Option Bool)
    (right : List (Option Bool))
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (contextSourceWord target
          { left := [], head := oldHead, right := right }
          (persistentTable transitions callerSuffix))) sourceTape) :
    let action : Action := { write := write, move := Direction.left }
    let updated : Tape Bool :=
      { left := [], head := none, right := write :: right }
    exists leftTape rightTape contextTape keyTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Prefix.machine
        { state := Prefix.Control.target action, tape := sourceTape }
        { state := Prefix.Control.ready action, tape := leftTape } ∧
      TuringMachine.Computes Boundary.machine
        { state := Boundary.Control.locate .count, tape := leftTape }
        { state := Boundary.Control.ready, tape := rightTape } ∧
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := rightTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := contextTape } ∧
      TuringMachine.Computes KeyHead.machine
        { state := KeyHead.Control.target none, tape := contextTape }
        { state := KeyHead.Control.ready, tape := keyTape } ∧
      Tape.Equiv
        (Tape.input
          (nextSingleKeyWorkWord target none updated transitions
            callerSuffix)) keyTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.left }
  let persistent := persistentTable transitions callerSuffix
  let updated : Tape Bool :=
    { left := [], head := none, right := write :: right }
  rcases position_left action target [] right oldHead persistent
      sourceTape hsource with
    ⟨leftTape, hleft, hleftTape⟩
  rcases position_right action target [] right oldHead persistent
      leftTape hleftTape with
    ⟨rightTape, hright, hrightTape⟩
  rcases prepend_right target write oldHead [] right persistent
      rightTape hrightTape with
    ⟨contextTape, hprepend, hcontextTape⟩
  have hcontextForKey : Tape.Equiv
      (Tape.input
        (contextSourceWord target updated
          (persistentTable transitions callerSuffix))) contextTape := by
    simpa [updated, persistent, contextSourceWord,
      RuntimeKeySingleKeyRepair.protectedTapeContextsAppend] using
      hcontextTape
  rcases materialize_next_key target none updated transitions callerSuffix
      contextTape hcontextForKey with
    ⟨keyTape, hkey, hkeyTape⟩
  exact ⟨leftTape, rightTape, contextTape, keyTape,
    hleft, hright, hprepend, hkey, hkeyTape⟩

theorem update_right_empty_to_next_key
    (target : Nat) (write oldHead : Option Bool)
    (left : List (Option Bool))
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (contextSourceWord target
          { left := left, head := oldHead, right := [] }
          (persistentTable transitions callerSuffix))) sourceTape) :
    let action : Action := { write := write, move := Direction.right }
    let updated : Tape Bool :=
      { left := write :: left, head := none, right := [] }
    exists leftTape contextTape keyTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Prefix.machine
        { state := Prefix.Control.target action, tape := sourceTape }
        { state := Prefix.Control.ready action, tape := leftTape } ∧
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := leftTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := contextTape } ∧
      TuringMachine.Computes KeyHead.machine
        { state := KeyHead.Control.target none, tape := contextTape }
        { state := KeyHead.Control.ready, tape := keyTape } ∧
      Tape.Equiv
        (Tape.input
          (nextSingleKeyWorkWord target none updated transitions
            callerSuffix)) keyTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.right }
  let persistent := persistentTable transitions callerSuffix
  let updated : Tape Bool :=
    { left := write :: left, head := none, right := [] }
  rcases position_left action target left [] oldHead persistent
      sourceTape hsource with
    ⟨leftTape, hleft, hleftTape⟩
  rcases prepend_left action target write oldHead left [] persistent
      leftTape hleftTape with
    ⟨contextTape, hprepend, hcontextTape⟩
  have hcontextForKey : Tape.Equiv
      (Tape.input
        (contextSourceWord target updated
          (persistentTable transitions callerSuffix))) contextTape := by
    simpa [updated, persistent, contextSourceWord,
      RuntimeKeySingleKeyRepair.protectedTapeContextsAppend] using
      hcontextTape
  rcases materialize_next_key target none updated transitions callerSuffix
      contextTape hcontextForKey with
    ⟨keyTape, hkey, hkeyTape⟩
  exact ⟨leftTape, contextTape, keyTape,
    hleft, hprepend, hkey, hkeyTape⟩

theorem update_left_nonempty_to_next_key
    (target : Nat) (write oldHead nextHead : Option Bool)
    (remainingLeft right : List (Option Bool))
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (contextSourceWord target
          { left := nextHead :: remainingLeft, head := oldHead,
            right := right }
          (persistentTable transitions callerSuffix))) sourceTape) :
    let action : Action := { write := write, move := Direction.left }
    let updated : Tape Bool :=
      { left := remainingLeft, head := nextHead,
        right := write :: right }
    exists leftTape rightTape writtenTape repointedTape contextTape keyTape :
        Tape MachineCodeSymbol,
      TuringMachine.Computes Prefix.machine
        { state := Prefix.Control.target action, tape := sourceTape }
        { state := Prefix.Control.ready action, tape := leftTape } ∧
      TuringMachine.Computes Boundary.machine
        { state := Boundary.Control.locate .count, tape := leftTape }
        { state := Boundary.Control.ready, tape := rightTape } ∧
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := rightTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := writtenTape } ∧
      TuringMachine.Computes Prefix.machine
        { state := Prefix.Control.target action, tape := writtenTape }
        { state := Prefix.Control.ready action, tape := repointedTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := repointedTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready nextHead
          tape := contextTape } ∧
      TuringMachine.Computes KeyHead.machine
        { state := KeyHead.Control.target nextHead, tape := contextTape }
        { state := KeyHead.Control.ready, tape := keyTape } ∧
      Tape.Equiv
        (Tape.input
          (nextSingleKeyWorkWord target nextHead updated transitions
            callerSuffix)) keyTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.left }
  let persistent := persistentTable transitions callerSuffix
  let written : Tape Bool :=
    { left := nextHead :: remainingLeft, head := oldHead,
      right := write :: right }
  let updated : Tape Bool :=
    { left := remainingLeft, head := nextHead,
      right := write :: right }
  rcases position_left action target (nextHead :: remainingLeft) right
      oldHead persistent sourceTape hsource with
    ⟨leftTape, hleft, hleftTape⟩
  rcases position_right action target (nextHead :: remainingLeft) right
      oldHead persistent leftTape hleftTape with
    ⟨rightTape, hright, hrightTape⟩
  rcases prepend_right target write oldHead
      (nextHead :: remainingLeft) right persistent
      rightTape hrightTape with
    ⟨writtenTape, hprepend, hwrittenTape⟩
  have hwrittenForPosition : Tape.Equiv
      (Tape.input (contextSourceWord target written persistent))
      writtenTape := by
    simpa [written] using hwrittenTape
  rcases position_left action target (nextHead :: remainingLeft)
      (write :: right) oldHead persistent writtenTape
      hwrittenForPosition with
    ⟨repointedTape, hrepoint, hrepointedTape⟩
  rcases pop_left action target nextHead oldHead remainingLeft
      (write :: right) persistent repointedTape hrepointedTape with
    ⟨contextTape, hpop, hcontextTape⟩
  have hcontextForKey : Tape.Equiv
      (Tape.input
        (contextSourceWord target updated
          (persistentTable transitions callerSuffix))) contextTape := by
    simpa [updated, persistent] using hcontextTape
  rcases materialize_next_key target nextHead updated transitions callerSuffix
      contextTape hcontextForKey with
    ⟨keyTape, hkey, hkeyTape⟩
  exact ⟨leftTape, rightTape, writtenTape, repointedTape, contextTape,
    keyTape, hleft, hright, hprepend, hrepoint, hpop, hkey, hkeyTape⟩

theorem update_right_nonempty_to_next_key
    (target : Nat) (write oldHead nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (contextSourceWord target
          { left := left, head := oldHead,
            right := nextHead :: remainingRight }
          (persistentTable transitions callerSuffix))) sourceTape) :
    let action : Action := { write := write, move := Direction.right }
    let updated : Tape Bool :=
      { left := write :: left, head := nextHead,
        right := remainingRight }
    exists leftTape writtenTape repointedTape rightTape contextTape keyTape :
        Tape MachineCodeSymbol,
      TuringMachine.Computes Prefix.machine
        { state := Prefix.Control.target action, tape := sourceTape }
        { state := Prefix.Control.ready action, tape := leftTape } ∧
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := leftTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := writtenTape } ∧
      TuringMachine.Computes Prefix.machine
        { state := Prefix.Control.target action, tape := writtenTape }
        { state := Prefix.Control.ready action, tape := repointedTape } ∧
      TuringMachine.Computes Boundary.machine
        { state := Boundary.Control.locate .count, tape := repointedTape }
        { state := Boundary.Control.ready, tape := rightTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := rightTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready nextHead
          tape := contextTape } ∧
      TuringMachine.Computes KeyHead.machine
        { state := KeyHead.Control.target nextHead, tape := contextTape }
        { state := KeyHead.Control.ready, tape := keyTape } ∧
      Tape.Equiv
        (Tape.input
          (nextSingleKeyWorkWord target nextHead updated transitions
            callerSuffix)) keyTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.right }
  let persistent := persistentTable transitions callerSuffix
  let written : Tape Bool :=
    { left := write :: left, head := oldHead,
      right := nextHead :: remainingRight }
  let updated : Tape Bool :=
    { left := write :: left, head := nextHead,
      right := remainingRight }
  rcases position_left action target left (nextHead :: remainingRight)
      oldHead persistent sourceTape hsource with
    ⟨leftTape, hleft, hleftTape⟩
  rcases prepend_left action target write oldHead left
      (nextHead :: remainingRight) persistent leftTape hleftTape with
    ⟨writtenTape, hprepend, hwrittenTape⟩
  have hwrittenForPosition : Tape.Equiv
      (Tape.input (contextSourceWord target written persistent))
      writtenTape := by
    simpa [written] using hwrittenTape
  rcases position_left action target (write :: left)
      (nextHead :: remainingRight) oldHead persistent writtenTape
      hwrittenForPosition with
    ⟨repointedTape, hrepoint, hrepointedTape⟩
  rcases position_right action target (write :: left)
      (nextHead :: remainingRight) oldHead persistent repointedTape
      hrepointedTape with
    ⟨rightTape, hright, hrightTape⟩
  rcases pop_right target nextHead (write :: left) remainingRight
      persistent rightTape hrightTape with
    ⟨contextTape, hpop, hcontextTape⟩
  have hcontextForKey : Tape.Equiv
      (Tape.input
        (contextSourceWord target updated
          (persistentTable transitions callerSuffix))) contextTape := by
    simpa [updated, persistent] using hcontextTape
  rcases materialize_next_key target nextHead updated transitions callerSuffix
      contextTape hcontextForKey with
    ⟨keyTape, hkey, hkeyTape⟩
  exact ⟨leftTape, writtenTape, repointedTape, rightTape, contextTape,
    keyTape, hleft, hprepend, hrepoint, hright, hpop, hkey, hkeyTape⟩


end DirectPhases

end FiniteRecognizer.Interpreter.DirectContextUpdate

end Computability
end FoC
