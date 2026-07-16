import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Context
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Stack.Skip
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.EncodedList.Prepend

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.StackIteration

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.DirectContextUpdate

abbrev Action := FiniteRecognizer.Interpreter.DirectContextUpdate.Action

def persistent
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend haltState callerSuffix

/-- The arbitrary base preserved by the context phases after `StackSkip` has
crossed every later table copy. -/
def stackBaseLeftRev
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat) : Word MachineCodeSymbol :=
  List.append
    (tableStack (first :: rest) copies).reverse
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)

def stackRightBaseLeftRev
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (left : List (Option Bool)) : Word MachineCodeSymbol :=
  FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
    (stackBaseLeftRev target first rest copies) left

theorem stackBaseLeftRev_reverse
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat) :
    (stackBaseLeftRev target first rest copies).reverse =
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header :: tableStack (first :: rest) copies) := by
  simp only [stackBaseLeftRev, List.reverse_append, List.reverse_reverse]
  simp [FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev,
    MachineDescription.encodeNatAppend, List.append_assoc]
  done

theorem stackRightBaseLeftRev_reverse
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (left : List (Option Bool)) :
    (stackRightBaseLeftRev target first rest copies left).reverse =
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header ::
          List.append (tableStack (first :: rest) copies)
            (MachineDescription.encodeCellListAppend left [])) := by
  unfold stackRightBaseLeftRev
  rw [FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_reverse]
  rw [stackBaseLeftRev_reverse]
  simp [MachineDescription.encodeNatAppend, List.append_assoc]
  done

theorem prefix_source_tape_eq_postSelected
    (action : Action)
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.sourceConfig action target
      (activeProtectedSuffix (first :: rest) copies tape haltState
        callerSuffix)).tape =
      Tape.input
        (postSelectedWord target (first :: rest) copies tape haltState
          callerSuffix) := by
  rw [FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.source_tape_eq_input]
  rfl
  done

theorem prefix_target_tape_eq_stackSkip_source
    (action : Action)
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetConfig action target
      (activeProtectedSuffix (first :: rest) copies tape haltState
        callerSuffix)).tape =
      (FiniteRecognizer.Interpreter.StackSkip.sourceConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest copies (contextTail tape haltState callerSuffix)).tape := by
  rfl
  done

theorem stackSkip_target_tape_eq_boundary_source
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (left right : List (Option Bool))
    (head : Option Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.StackSkip.targetConfig
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
      first rest copies
      (contextTail { left := left, head := head, right := right }
        haltState callerSuffix)).tape =
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.sourceConfig
        (stackBaseLeftRev target first rest copies)
        left right.length
        (MachineDescription.encodeCellsAppend right
          (persistent haltState callerSuffix))).tape := by
  rfl
  done

theorem stackSkip_target_tape_eq_prepend_left_source
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (left right : List (Option Bool))
    (head : Option Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.StackSkip.targetConfig
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
      first rest copies
      (contextTail { left := left, head := head, right := right }
        haltState callerSuffix)).tape =
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        (stackBaseLeftRev target first rest copies)
        left.length
        (MachineDescription.encodeCellsAppend left
          (MachineDescription.encodeCellListAppend right
            (persistent haltState callerSuffix)))).tape := by
  rfl
  done

theorem boundary_target_tape_eq_prepend_right_source
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (left right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      (stackBaseLeftRev target first rest copies)
      left right.length
      (MachineDescription.encodeCellsAppend right
        (persistent haltState callerSuffix))).tape =
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        (stackRightBaseLeftRev target first rest copies left)
        right.length
        (MachineDescription.encodeCellsAppend right
          (persistent haltState callerSuffix))).tape := by
  rfl
  done

theorem stackSkip_target_tape_eq_pop_left_source
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (nextHead : Option Bool)
    (remainingLeft right : List (Option Bool))
    (oldHead : Option Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.StackSkip.targetConfig
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
      first rest copies
      (contextTail
        { left := nextHead :: remainingLeft, head := oldHead, right := right }
        haltState callerSuffix)).tape =
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        (stackBaseLeftRev target first rest copies)
        remainingLeft.length nextHead
        (MachineDescription.encodeCellsAppend remainingLeft
          (MachineDescription.encodeCellListAppend right
            (persistent haltState callerSuffix)))).tape := by
  cases nextHead with
  | none => rfl
  | some bit => cases bit <;> rfl
  done

theorem boundary_target_tape_eq_pop_right_source
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      (stackBaseLeftRev target first rest copies)
      left (remainingRight.length + 1)
      (MachineDescription.encodeCellAppend nextHead
        (MachineDescription.encodeCellsAppend remainingRight
          (persistent haltState callerSuffix)))).tape =
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        (stackRightBaseLeftRev target first rest copies left)
        remainingRight.length nextHead
        (MachineDescription.encodeCellsAppend remainingRight
          (persistent haltState callerSuffix))).tape := by
  cases nextHead with
  | none => rfl
  | some bit => cases bit <;> rfl
  done

theorem prepend_left_targetWord_eq_postSelected
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (write head : Option Bool)
    (left right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord
        (stackBaseLeftRev target first rest copies)
        left.length write
        (MachineDescription.encodeCellsAppend left
          (MachineDescription.encodeCellListAppend right
            (persistent haltState callerSuffix))) =
      postSelectedWord target (first :: rest) copies
        { left := write :: left, head := head, right := right }
        haltState callerSuffix := by
  unfold FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord postSelectedWord
    activeProtectedSuffix contextTail
    RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [stackBaseLeftRev_reverse]
  cases write with
  | none =>
      simp [persistent, MachineDescription.encodeCellListAppend,
        MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeCellsAppend, List.append_assoc]
  | some bit =>
      cases bit <;>
        simp [persistent, MachineDescription.encodeCellListAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeCellsAppend, List.append_assoc]
  done

theorem prepend_right_targetWord_eq_postSelected
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (write head : Option Bool)
    (left right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord
        (stackRightBaseLeftRev target first rest copies left)
        right.length write
        (MachineDescription.encodeCellsAppend right
          (persistent haltState callerSuffix)) =
      postSelectedWord target (first :: rest) copies
        { left := left, head := head, right := write :: right }
        haltState callerSuffix := by
  unfold FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.targetWord postSelectedWord
    activeProtectedSuffix contextTail
    RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [stackRightBaseLeftRev_reverse]
  have hright :
      MachineDescription.encodeNatAppend (right.length + 1)
          (MachineDescription.encodeCellAppend write
            (MachineDescription.encodeCellsAppend right
              (persistent haltState callerSuffix))) =
        MachineDescription.encodeCellListAppend (write :: right)
          (persistent haltState callerSuffix) := by
    rfl
  rw [hright]
  have hleft :
      MachineDescription.encodeCellListAppend left
          (MachineDescription.encodeCellListAppend (write :: right)
            (persistent haltState callerSuffix)) =
        List.append
          (MachineDescription.encodeCellListAppend left [])
          (MachineDescription.encodeCellListAppend (write :: right)
            (persistent haltState callerSuffix)) := by
    simpa using encodeCellListAppend_append left
      ([] : Word MachineCodeSymbol)
      (MachineDescription.encodeCellListAppend (write :: right)
        (persistent haltState callerSuffix))
  have hcontext := congrArg
    (fun tail : Word MachineCodeSymbol =>
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header ::
          List.append (tableStack (first :: rest) copies) tail))
    hleft
  simpa [persistent, MachineDescription.encodeNatAppend,
    List.append_assoc] using hcontext.symm
  done

theorem pop_left_targetWord_eq_postSelected
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (head : Option Bool)
    (remainingLeft right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord
        (stackBaseLeftRev target first rest copies)
        remainingLeft.length
        (MachineDescription.encodeCellsAppend remainingLeft
          (MachineDescription.encodeCellListAppend right
            (persistent haltState callerSuffix))) =
      postSelectedWord target (first :: rest) copies
        { left := remainingLeft, head := head, right := right }
        haltState callerSuffix := by
  unfold FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord postSelectedWord
    activeProtectedSuffix contextTail
    RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [stackBaseLeftRev_reverse]
  simp [persistent, MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend, List.append_assoc]
  done

theorem pop_right_targetWord_eq_postSelected
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (head : Option Bool)
    (left remainingRight : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord
        (stackRightBaseLeftRev target first rest copies left)
        remainingRight.length
        (MachineDescription.encodeCellsAppend remainingRight
          (persistent haltState callerSuffix)) =
      postSelectedWord target (first :: rest) copies
        { left := left, head := head, right := remainingRight }
        haltState callerSuffix := by
  unfold FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.targetWord postSelectedWord
    activeProtectedSuffix contextTail
    RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [stackRightBaseLeftRev_reverse]
  have hright :
      MachineDescription.encodeNatAppend remainingRight.length
          (MachineDescription.encodeCellsAppend remainingRight
            (persistent haltState callerSuffix)) =
        MachineDescription.encodeCellListAppend remainingRight
          (persistent haltState callerSuffix) := by
    rfl
  rw [hright]
  have hleft :
      MachineDescription.encodeCellListAppend left
          (MachineDescription.encodeCellListAppend remainingRight
            (persistent haltState callerSuffix)) =
        List.append
          (MachineDescription.encodeCellListAppend left [])
          (MachineDescription.encodeCellListAppend remainingRight
            (persistent haltState callerSuffix)) := by
    simpa using encodeCellListAppend_append left
      ([] : Word MachineCodeSymbol)
      (MachineDescription.encodeCellListAppend remainingRight
        (persistent haltState callerSuffix))
  have hcontext := congrArg
    (fun tail : Word MachineCodeSymbol =>
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header ::
          List.append (tableStack (first :: rest) copies) tail))
    hleft
  simpa [persistent, MachineDescription.encodeNatAppend,
    List.append_assoc] using hcontext.symm
  done

/-!
### Tape-equivalence phase adapters
-/

theorem stackSkip_computes_of_tape_equiv
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.sourceConfig baseLeftRev first rest copies
        context).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := targetTape } ∧
      Tape.Equiv
        (FiniteRecognizer.Interpreter.StackSkip.targetConfig baseLeftRev first rest copies
          context).tape targetTape := by
  have hrun := FiniteRecognizer.Interpreter.StackSkip.run_exact
    baseLeftRev first rest copies context
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨targetConfig', htargetRun, htargetState, htargetTape⟩
  rcases targetConfig' with ⟨state, tape⟩
  simp only [FiniteRecognizer.Interpreter.StackSkip.targetConfig,
    FiniteRecognizer.Interpreter.StackSkip.cursorConfig] at htargetState
  subst state
  exact ⟨tape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun),
    htargetTape⟩
  done

theorem position_after_stack
    (action : Action)
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) copies tape haltState
          callerSuffix)) sourceTape) :
    exists prefixTape contextTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.target action
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.ready action
          tape := prefixTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := prefixTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := contextTape } ∧
      Tape.Equiv
        (FiniteRecognizer.Interpreter.StackSkip.targetConfig
          (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
          first rest copies (contextTail tape haltState callerSuffix)).tape
        contextTape := by
  have hprefixSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.sourceConfig action target
        (activeProtectedSuffix (first :: rest) copies tape haltState
          callerSuffix)).tape sourceTape := by
    rw [prefix_source_tape_eq_postSelected]
    exact hsource
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.prefix_computes_of_tape_equiv
      action target
      (activeProtectedSuffix (first :: rest) copies tape haltState
        callerSuffix)
      sourceTape hprefixSource with
    ⟨prefixTape, hprefix, hprefixTape⟩
  have hskipSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.sourceConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest copies (contextTail tape haltState callerSuffix)).tape
      prefixTape := by
    rw [← prefix_target_tape_eq_stackSkip_source action]
    exact hprefixTape
  rcases stackSkip_computes_of_tape_equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
      first rest copies (contextTail tape haltState callerSuffix)
      prefixTape hskipSource with
    ⟨contextTape, hskip, hcontextTape⟩
  exact ⟨prefixTape, contextTape, hprefix, hskip, hcontextTape⟩
  done

theorem nextCopyRestager_computes_of_tape_equiv
    (nextHead : Option Bool)
    (target : Nat)
    (rest : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (NextCopyRestager.sourceConfig nextHead target rest).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes NextCopyRestager.machine
        { state := NextCopyRestager.Control.target nextHead
          tape := sourceTape }
        { state := NextCopyRestager.Control.ready nextHead
          tape := targetTape } ∧
      Tape.Equiv
        (NextCopyRestager.targetConfig nextHead target rest).tape
        targetTape := by
  have hrun := NextCopyRestager.run_exact nextHead target rest
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨targetConfig', htargetRun, htargetState, htargetTape⟩
  rcases targetConfig' with ⟨state, tape⟩
  simp only [NextCopyRestager.targetConfig] at htargetState
  subst state
  exact ⟨tape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun),
    htargetTape⟩
  done

def nextCopyRest
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (updatedTape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeTransitionsAppend (first :: rest)
    (MachineCodeSymbol.header ::
      List.append (tableStack (first :: rest) copies)
        (contextTail updatedTape haltState callerSuffix))

theorem activeProtectedSuffix_succ_eq_nextCopyRest
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (updatedTape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    activeProtectedSuffix (first :: rest) (copies + 1)
        updatedTape haltState callerSuffix =
      nextCopyRest first rest copies updatedTape haltState callerSuffix := by
  unfold activeProtectedSuffix nextCopyRest
  change
    List.append
        (MachineDescription.encodeTransitionsAppend (first :: rest)
          (MachineCodeSymbol.header :: tableStack (first :: rest) copies))
        (contextTail updatedTape haltState callerSuffix) =
      MachineDescription.encodeTransitionsAppend (first :: rest)
        (MachineCodeSymbol.header ::
          List.append (tableStack (first :: rest) copies)
            (contextTail updatedTape haltState callerSuffix))
  simpa using MachineDescription.encodeTransitionsAppend_append
    (first :: rest)
    (MachineCodeSymbol.header :: tableStack (first :: rest) copies)
    (contextTail updatedTape haltState callerSuffix)
  done

theorem postSelected_succ_eq_nextCopy_sourceWord
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (updatedTape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    postSelectedWord target (first :: rest) (copies + 1)
        updatedTape haltState callerSuffix =
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header ::
          nextCopyRest first rest copies updatedTape haltState
            callerSuffix) := by
  unfold postSelectedWord
  rw [activeProtectedSuffix_succ_eq_nextCopyRest]
  done

theorem nextCopyRestager_source_tape_eq_postSelected_succ
    (nextHead : Option Bool)
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (updatedTape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (NextCopyRestager.sourceConfig nextHead target
      (nextCopyRest first rest copies updatedTape haltState
        callerSuffix)).tape =
      Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          updatedTape haltState callerSuffix) := by
  rw [postSelected_succ_eq_nextCopy_sourceWord]
  cases target <;> rfl
  done

theorem nextCopyRestager_target_tape_eq_next_scan
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (updatedTape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (NextCopyRestager.targetConfig (Tape.read updatedTape) target
      (nextCopyRest first rest copies updatedTape haltState
        callerSuffix)).tape =
      (canonicalScanRowsConfig
        { state := target, tape := updatedTape } [] (first :: rest)
        (activeProtectedSuffix (first :: rest) copies updatedTape
          haltState callerSuffix)).tape := by
  unfold NextCopyRestager.targetConfig canonicalScanRowsConfig
    nextCopyRest activeProtectedSuffix
  simp only [processedRows, List.nil_append]
  let work : Word MachineCodeSymbol :=
    List.append
      (runtimeKeyBuilderKeyCode target (Tape.read updatedTape))
      (MachineDescription.encodeTransitionsAppend (first :: rest)
        (MachineCodeSymbol.header ::
          List.append (tableStack (first :: rest) copies)
            (contextTail updatedTape haltState callerSuffix)))
  change SerializedShift.cursorTape [MachineCodeSymbol.header] work =
    runtimeKeyComparatorTape [MachineCodeSymbol.header] work
  cases work <;> rfl
  done

/-!
### Arbitrary-base context phase compositions
-/

theorem boundary_from_stack
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (left right : List (Option Bool))
    (head : Option Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest copies
        (contextTail { left := left, head := head, right := right }
          haltState callerSuffix)).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.ready
          tape := targetTape } ∧
      Tape.Equiv
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
          (stackBaseLeftRev target first rest copies)
          left right.length
          (MachineDescription.encodeCellsAppend right
            (persistent haltState callerSuffix))).tape targetTape := by
  apply FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.boundary_computes_of_tape_equiv
  rw [← stackSkip_target_tape_eq_boundary_source target first rest copies
    left right head haltState callerSuffix]
  exact hsource
  done

theorem prepend_left_from_stack
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (write head : Option Bool)
    (left right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest copies
        (contextTail { left := left, head := head, right := right }
          haltState callerSuffix)).tape sourceTape) :
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
          (postSelectedWord target (first :: rest) copies
            { left := write :: left, head := head, right := right }
            haltState callerSuffix)) targetTape := by
  have hsource' : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        (stackBaseLeftRev target first rest copies)
        left.length
        (MachineDescription.encodeCellsAppend left
          (MachineDescription.encodeCellListAppend right
            (persistent haltState callerSuffix)))).tape sourceTape := by
    rw [← stackSkip_target_tape_eq_prepend_left_source target first rest
      copies left right head haltState callerSuffix]
    exact hsource
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.prepend_computes_of_tape_equiv
      (stackBaseLeftRev target first rest copies)
      left.length write
      (MachineDescription.encodeCellsAppend left
        (MachineDescription.encodeCellListAppend right
          (persistent haltState callerSuffix)))
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [prepend_left_targetWord_eq_postSelected] at htarget
  exact htarget
  done

theorem prepend_right_from_boundary
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (write head : Option Bool)
    (left right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
        (stackBaseLeftRev target first rest copies)
        left right.length
        (MachineDescription.encodeCellsAppend right
          (persistent haltState callerSuffix))).tape sourceTape) :
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
          (postSelectedWord target (first :: rest) copies
            { left := left, head := head, right := write :: right }
            haltState callerSuffix)) targetTape := by
  have hsource' : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.sourceConfig
        (stackRightBaseLeftRev target first rest copies left)
        right.length
        (MachineDescription.encodeCellsAppend right
          (persistent haltState callerSuffix))).tape sourceTape := by
    rw [← boundary_target_tape_eq_prepend_right_source target first rest
      copies left right haltState callerSuffix]
    exact hsource
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.prepend_computes_of_tape_equiv
      (stackRightBaseLeftRev target first rest copies left)
      right.length write
      (MachineDescription.encodeCellsAppend right
        (persistent haltState callerSuffix))
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [prepend_right_targetWord_eq_postSelected] at htarget
  exact htarget
  done

theorem pop_left_from_stack
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (nextHead oldHead : Option Bool)
    (remainingLeft right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest copies
        (contextTail
          { left := nextHead :: remainingLeft, head := oldHead,
            right := right }
          haltState callerSuffix)).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready nextHead
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (postSelectedWord target (first :: rest) copies
            { left := remainingLeft, head := nextHead, right := right }
            haltState callerSuffix)) targetTape := by
  have hsource' : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        (stackBaseLeftRev target first rest copies)
        remainingLeft.length nextHead
        (MachineDescription.encodeCellsAppend remainingLeft
          (MachineDescription.encodeCellListAppend right
            (persistent haltState callerSuffix)))).tape sourceTape := by
    rw [← stackSkip_target_tape_eq_pop_left_source target first rest copies
      nextHead remainingLeft right oldHead haltState callerSuffix]
    exact hsource
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.pop_computes_of_tape_equiv
      (stackBaseLeftRev target first rest copies)
      remainingLeft.length nextHead
      (MachineDescription.encodeCellsAppend remainingLeft
        (MachineDescription.encodeCellListAppend right
          (persistent haltState callerSuffix)))
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [pop_left_targetWord_eq_postSelected] at htarget
  exact htarget
  done

theorem pop_right_from_boundary
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
        (stackBaseLeftRev target first rest copies)
        left (remainingRight.length + 1)
        (MachineDescription.encodeCellAppend nextHead
          (MachineDescription.encodeCellsAppend remainingRight
            (persistent haltState callerSuffix)))).tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready nextHead
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (postSelectedWord target (first :: rest) copies
            { left := left, head := nextHead, right := remainingRight }
            haltState callerSuffix)) targetTape := by
  have hsource' : Tape.Equiv
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.sourceConfig
        (stackRightBaseLeftRev target first rest copies left)
        remainingRight.length nextHead
        (MachineDescription.encodeCellsAppend remainingRight
          (persistent haltState callerSuffix))).tape sourceTape := by
    rw [← boundary_target_tape_eq_pop_right_source target first rest copies
      nextHead left remainingRight haltState callerSuffix]
    exact hsource
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.pop_computes_of_tape_equiv
      (stackRightBaseLeftRev target first rest copies left)
      remainingRight.length nextHead
      (MachineDescription.encodeCellsAppend remainingRight
        (persistent haltState callerSuffix))
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [pop_right_targetWord_eq_postSelected] at htarget
  exact htarget
  done

theorem restage_next_scan
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (updatedTape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          updatedTape haltState callerSuffix)) sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes NextCopyRestager.machine
        { state := NextCopyRestager.Control.target (Tape.read updatedTape)
          tape := sourceTape }
        { state := NextCopyRestager.Control.ready (Tape.read updatedTape)
          tape := targetTape } ∧
      Tape.Equiv
        (canonicalScanRowsConfig
          { state := target, tape := updatedTape } [] (first :: rest)
          (activeProtectedSuffix (first :: rest) copies updatedTape
            haltState callerSuffix)).tape targetTape := by
  have hsource' : Tape.Equiv
      (NextCopyRestager.sourceConfig (Tape.read updatedTape) target
        (nextCopyRest first rest copies updatedTape haltState
          callerSuffix)).tape sourceTape := by
    rw [nextCopyRestager_source_tape_eq_postSelected_succ]
    exact hsource
  rcases nextCopyRestager_computes_of_tape_equiv
      (Tape.read updatedTape) target
      (nextCopyRest first rest copies updatedTape haltState callerSuffix)
      sourceTape hsource' with
    ⟨targetTape, hrun, htarget⟩
  refine ⟨targetTape, hrun, ?_⟩
  rw [nextCopyRestager_target_tape_eq_next_scan] at htarget
  exact htarget
  done

/-!
### Four complete nonempty-table loop traces

Each trace begins at the named selected-row cleanup boundary.  The stack has
`copies + 1` tables, so one is available for the next guarded scan; the
restager consumes that front copy from the stack currency and leaves `copies`
later copies protected behind the active table.
-/

theorem iterate_left_empty
    (target : Nat)
    (write oldHead : Option Bool)
    (right : List (Option Bool))
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          { left := [], head := oldHead, right := right }
          haltState callerSuffix)) sourceTape) :
    let action : Action := { write := write, move := Direction.left }
    let updated : Tape Bool :=
      { left := [], head := none, right := write :: right }
    exists prefixTape stackTape boundaryTape updatedPhysical scanTape :
        Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.target action
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.ready action
          tape := prefixTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := prefixTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := stackTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.locate .count
          tape := stackTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.ready
          tape := boundaryTape } ∧
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := boundaryTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := updatedPhysical } ∧
      TuringMachine.Computes NextCopyRestager.machine
        { state := NextCopyRestager.Control.target (Tape.read updated)
          tape := updatedPhysical }
        { state := NextCopyRestager.Control.ready (Tape.read updated)
          tape := scanTape } ∧
      Tape.Equiv
        (canonicalScanRowsConfig
          { state := target, tape := updated } [] (first :: rest)
          (activeProtectedSuffix (first :: rest) copies updated
            haltState callerSuffix)).tape scanTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.left }
  let oldTape : Tape Bool :=
    { left := [], head := oldHead, right := right }
  let updated : Tape Bool :=
    { left := [], head := none, right := write :: right }
  rcases position_after_stack action target first rest (copies + 1)
      oldTape haltState callerSuffix sourceTape
      (by simpa [oldTape] using hsource) with
    ⟨prefixTape, stackTape, hprefix, hskip, hstackTape⟩
  rcases boundary_from_stack target first rest (copies + 1)
      [] right oldHead haltState callerSuffix stackTape
      (by simpa [oldTape] using hstackTape) with
    ⟨boundaryTape, hboundary, hboundaryTape⟩
  rcases prepend_right_from_boundary target first rest (copies + 1)
      write oldHead [] right haltState callerSuffix boundaryTape
      hboundaryTape with
    ⟨updatedPhysical, hprepend, hupdatedPhysical⟩
  have hupdated : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          updated haltState callerSuffix)) updatedPhysical := by
    simpa [updated, postSelectedWord, activeProtectedSuffix, contextTail,
      RuntimeKeySingleKeyRepair.protectedTapeContextsAppend] using
      hupdatedPhysical
  rcases restage_next_scan target first rest copies updated haltState
      callerSuffix updatedPhysical hupdated with
    ⟨scanTape, hrestage, hscanTape⟩
  exact ⟨prefixTape, stackTape, boundaryTape, updatedPhysical, scanTape,
    hprefix, hskip, hboundary, hprepend, hrestage, hscanTape⟩
  done

theorem iterate_right_empty
    (target : Nat)
    (write oldHead : Option Bool)
    (left : List (Option Bool))
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          { left := left, head := oldHead, right := [] }
          haltState callerSuffix)) sourceTape) :
    let action : Action := { write := write, move := Direction.right }
    let updated : Tape Bool :=
      { left := write :: left, head := none, right := [] }
    exists prefixTape stackTape updatedPhysical scanTape :
        Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.target action
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.ready action
          tape := prefixTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := prefixTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := stackTape } ∧
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := stackTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := updatedPhysical } ∧
      TuringMachine.Computes NextCopyRestager.machine
        { state := NextCopyRestager.Control.target (Tape.read updated)
          tape := updatedPhysical }
        { state := NextCopyRestager.Control.ready (Tape.read updated)
          tape := scanTape } ∧
      Tape.Equiv
        (canonicalScanRowsConfig
          { state := target, tape := updated } [] (first :: rest)
          (activeProtectedSuffix (first :: rest) copies updated
            haltState callerSuffix)).tape scanTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.right }
  let oldTape : Tape Bool :=
    { left := left, head := oldHead, right := [] }
  let updated : Tape Bool :=
    { left := write :: left, head := none, right := [] }
  rcases position_after_stack action target first rest (copies + 1)
      oldTape haltState callerSuffix sourceTape
      (by simpa [oldTape] using hsource) with
    ⟨prefixTape, stackTape, hprefix, hskip, hstackTape⟩
  rcases prepend_left_from_stack target first rest (copies + 1)
      write oldHead left [] haltState callerSuffix stackTape
      (by simpa [oldTape] using hstackTape) with
    ⟨updatedPhysical, hprepend, hupdatedPhysical⟩
  have hupdated : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          updated haltState callerSuffix)) updatedPhysical := by
    simpa [updated, postSelectedWord, activeProtectedSuffix, contextTail,
      RuntimeKeySingleKeyRepair.protectedTapeContextsAppend] using
      hupdatedPhysical
  rcases restage_next_scan target first rest copies updated haltState
      callerSuffix updatedPhysical hupdated with
    ⟨scanTape, hrestage, hscanTape⟩
  exact ⟨prefixTape, stackTape, updatedPhysical, scanTape,
    hprefix, hskip, hprepend, hrestage, hscanTape⟩
  done

theorem iterate_left_nonempty
    (target : Nat)
    (write oldHead nextHead : Option Bool)
    (remainingLeft right : List (Option Bool))
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          { left := nextHead :: remainingLeft, head := oldHead,
            right := right }
          haltState callerSuffix)) sourceTape) :
    let action : Action := { write := write, move := Direction.left }
    let updated : Tape Bool :=
      { left := remainingLeft, head := nextHead, right := write :: right }
    exists prefixTape stackTape boundaryTape writtenTape reprefixTape
        restackTape updatedPhysical scanTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.target action
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.ready action
          tape := prefixTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := prefixTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := stackTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.locate .count
          tape := stackTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.ready
          tape := boundaryTape } ∧
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := boundaryTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := writtenTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.target action
          tape := writtenTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.ready action
          tape := reprefixTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := reprefixTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := restackTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := restackTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready nextHead
          tape := updatedPhysical } ∧
      TuringMachine.Computes NextCopyRestager.machine
        { state := NextCopyRestager.Control.target (Tape.read updated)
          tape := updatedPhysical }
        { state := NextCopyRestager.Control.ready (Tape.read updated)
          tape := scanTape } ∧
      Tape.Equiv
        (canonicalScanRowsConfig
          { state := target, tape := updated } [] (first :: rest)
          (activeProtectedSuffix (first :: rest) copies updated
            haltState callerSuffix)).tape scanTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.left }
  let oldTape : Tape Bool :=
    { left := nextHead :: remainingLeft, head := oldHead, right := right }
  let written : Tape Bool :=
    { left := nextHead :: remainingLeft, head := oldHead,
      right := write :: right }
  let updated : Tape Bool :=
    { left := remainingLeft, head := nextHead, right := write :: right }
  rcases position_after_stack action target first rest (copies + 1)
      oldTape haltState callerSuffix sourceTape
      (by simpa [oldTape] using hsource) with
    ⟨prefixTape, stackTape, hprefix, hskip, hstackTape⟩
  rcases boundary_from_stack target first rest (copies + 1)
      (nextHead :: remainingLeft) right oldHead haltState callerSuffix
      stackTape (by simpa [oldTape] using hstackTape) with
    ⟨boundaryTape, hboundary, hboundaryTape⟩
  rcases prepend_right_from_boundary target first rest (copies + 1)
      write oldHead (nextHead :: remainingLeft) right haltState
      callerSuffix boundaryTape hboundaryTape with
    ⟨writtenTape, hprepend, hwrittenTape⟩
  have hwritten : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          written haltState callerSuffix)) writtenTape := by
    simpa [written] using hwrittenTape
  rcases position_after_stack action target first rest (copies + 1)
      written haltState callerSuffix writtenTape hwritten with
    ⟨reprefixTape, restackTape, hreprefix, hreskip, hrestackTape⟩
  rcases pop_left_from_stack target first rest (copies + 1)
      nextHead oldHead remainingLeft (write :: right) haltState callerSuffix
      restackTape (by simpa [written] using hrestackTape) with
    ⟨updatedPhysical, hpop, hupdatedPhysical⟩
  have hupdated : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          updated haltState callerSuffix)) updatedPhysical := by
    simpa [updated] using hupdatedPhysical
  rcases restage_next_scan target first rest copies updated haltState
      callerSuffix updatedPhysical hupdated with
    ⟨scanTape, hrestage, hscanTape⟩
  exact ⟨prefixTape, stackTape, boundaryTape, writtenTape,
    reprefixTape, restackTape, updatedPhysical, scanTape,
    hprefix, hskip, hboundary, hprepend, hreprefix, hreskip,
    hpop, hrestage, hscanTape⟩
  done

theorem iterate_right_nonempty
    (target : Nat)
    (write oldHead nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          { left := left, head := oldHead,
            right := nextHead :: remainingRight }
          haltState callerSuffix)) sourceTape) :
    let action : Action := { write := write, move := Direction.right }
    let updated : Tape Bool :=
      { left := write :: left, head := nextHead, right := remainingRight }
    exists prefixTape stackTape writtenTape reprefixTape restackTape
        boundaryTape updatedPhysical scanTape : Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.target action
          tape := sourceTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.ready action
          tape := prefixTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := prefixTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := stackTape } ∧
      TuringMachine.Computes
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine write)
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.locate .count
          tape := stackTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert
            (.rewind .gate)
          tape := writtenTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.target action
          tape := writtenTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.ready action
          tape := reprefixTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := reprefixTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := restackTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.locate .count
          tape := restackTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.ready
          tape := boundaryTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.locate .count
          tape := boundaryTape }
        { state := FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.ready nextHead
          tape := updatedPhysical } ∧
      TuringMachine.Computes NextCopyRestager.machine
        { state := NextCopyRestager.Control.target (Tape.read updated)
          tape := updatedPhysical }
        { state := NextCopyRestager.Control.ready (Tape.read updated)
          tape := scanTape } ∧
      Tape.Equiv
        (canonicalScanRowsConfig
          { state := target, tape := updated } [] (first :: rest)
          (activeProtectedSuffix (first :: rest) copies updated
            haltState callerSuffix)).tape scanTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.right }
  let oldTape : Tape Bool :=
    { left := left, head := oldHead, right := nextHead :: remainingRight }
  let written : Tape Bool :=
    { left := write :: left, head := oldHead,
      right := nextHead :: remainingRight }
  let updated : Tape Bool :=
    { left := write :: left, head := nextHead, right := remainingRight }
  rcases position_after_stack action target first rest (copies + 1)
      oldTape haltState callerSuffix sourceTape
      (by simpa [oldTape] using hsource) with
    ⟨prefixTape, stackTape, hprefix, hskip, hstackTape⟩
  rcases prepend_left_from_stack target first rest (copies + 1)
      write oldHead left (nextHead :: remainingRight) haltState
      callerSuffix stackTape (by simpa [oldTape] using hstackTape) with
    ⟨writtenTape, hprepend, hwrittenTape⟩
  have hwritten : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          written haltState callerSuffix)) writtenTape := by
    simpa [written] using hwrittenTape
  rcases position_after_stack action target first rest (copies + 1)
      written haltState callerSuffix writtenTape hwritten with
    ⟨reprefixTape, restackTape, hreprefix, hreskip, hrestackTape⟩
  rcases boundary_from_stack target first rest (copies + 1)
      (write :: left) (nextHead :: remainingRight) oldHead haltState
      callerSuffix restackTape (by simpa [written] using hrestackTape) with
    ⟨boundaryTape, hboundary, hboundaryTape⟩
  rcases pop_right_from_boundary target first rest (copies + 1)
      nextHead (write :: left) remainingRight haltState callerSuffix
      boundaryTape hboundaryTape with
    ⟨updatedPhysical, hpop, hupdatedPhysical⟩
  have hupdated : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          updated haltState callerSuffix)) updatedPhysical := by
    simpa [updated] using hupdatedPhysical
  rcases restage_next_scan target first rest copies updated haltState
      callerSuffix updatedPhysical hupdated with
    ⟨scanTape, hrestage, hscanTape⟩
  exact ⟨prefixTape, stackTape, writtenTape, reprefixTape, restackTape,
    boundaryTape, updatedPhysical, scanTape,
    hprefix, hskip, hprepend, hreprefix, hreskip, hboundary,
    hpop, hrestage, hscanTape⟩
  done


end FiniteRecognizer.Interpreter.StackIteration

end Computability
end FoC
