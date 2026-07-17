import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.FinalGate.HaltCopier

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.FinalGateMaterializer

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.StackIteration

theorem leftBoundary_target_tape_eq_rightBoundary_source
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (left right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      (stackBaseLeftRev target first rest 0)
      left right.length
      (MachineDescription.encodeCellsAppend right
        (persistent haltState callerSuffix))).tape =
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.sourceConfig
      (stackRightBaseLeftRev target first rest 0 left)
      right haltState callerSuffix).tape := by
  rfl
  done

theorem rightBoundary_target_tape_eq_haltMarker_source
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (left right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      (stackRightBaseLeftRev target first rest 0 left)
      right haltState callerSuffix).tape =
    (HaltMarker.sourceConfig
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
        (stackRightBaseLeftRev target first rest 0 left) right)
      haltState callerSuffix).tape := by
  rfl
  done

def safeContextSymbol (symbol : MachineCodeSymbol) : Prop :=
  symbol ≠ MachineCodeSymbol.header ∧
    symbol ≠ MachineCodeSymbol.moveRight

theorem encodeNat_safeContextSymbol
    (value : Nat)
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol (MachineDescription.encodeNat value)) :
    safeContextSymbol symbol := by
  induction value with
  | zero =>
      change List.Mem symbol [MachineCodeSymbol.done] at hmem
      cases hmem with
      | head => simp [safeContextSymbol]
      | tail _ htail => cases htail
  | succ value ih =>
      change List.Mem symbol
        (MachineCodeSymbol.tick :: MachineDescription.encodeNat value) at hmem
      cases hmem with
      | head => simp [safeContextSymbol]
      | tail _ htail => exact ih htail
  done

theorem encodeCells_safeContextSymbol
    (cells : List (Option Bool))
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol
      (MachineDescription.encodeCellsAppend cells [])) :
    safeContextSymbol symbol := by
  induction cells with
  | nil =>
      change List.Mem symbol [] at hmem
      cases hmem
  | cons cell rest ih =>
      cases cell with
      | none =>
          change List.Mem symbol
            (MachineCodeSymbol.blank ::
              MachineDescription.encodeCellsAppend rest []) at hmem
          cases hmem with
          | head => simp [safeContextSymbol]
          | tail _ htail => exact ih htail
      | some bit =>
          cases bit with
          | false =>
              change List.Mem symbol
                (MachineCodeSymbol.zero ::
                  MachineDescription.encodeCellsAppend rest []) at hmem
              cases hmem with
              | head => simp [safeContextSymbol]
              | tail _ htail => exact ih htail
          | true =>
              change List.Mem symbol
                (MachineCodeSymbol.one ::
                  MachineDescription.encodeCellsAppend rest []) at hmem
              cases hmem with
              | head => simp [safeContextSymbol]
              | tail _ htail => exact ih htail
  done

theorem encodeCellList_safeContextSymbol
    (cells : List (Option Bool))
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol
      (MachineDescription.encodeCellListAppend cells [])) :
    safeContextSymbol symbol := by
  simp only [MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend] at hmem
  rcases List.mem_append.mp hmem with hcount | hcells
  · exact encodeNat_safeContextSymbol cells.length symbol hcount
  · exact encodeCells_safeContextSymbol cells symbol hcells
  done

def contextPrefix
    (left right : List (Option Bool)) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellListAppend left
    (MachineDescription.encodeCellListAppend right [])

theorem contextPrefix_safeContextSymbol
    (left right : List (Option Bool))
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol (contextPrefix left right)) :
    safeContextSymbol symbol := by
  have hsplit : contextPrefix left right =
      List.append
        (MachineDescription.encodeCellListAppend left [])
        (MachineDescription.encodeCellListAppend right []) := by
    simpa [contextPrefix] using
      (encodeCellListAppend_append left []
        (MachineDescription.encodeCellListAppend right []))
  rw [hsplit] at hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · exact encodeCellList_safeContextSymbol left symbol hleft
  · exact encodeCellList_safeContextSymbol right symbol hright
  done

theorem contextPrefix_decompose
    (left right : List (Option Bool)) :
    exists firstContext secondContext : MachineCodeSymbol,
    exists gap : Word MachineCodeSymbol,
      contextPrefix left right = firstContext :: secondContext :: gap ∧
      (forall symbol : MachineCodeSymbol,
        List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.header) ∧
      (forall symbol : MachineCodeSymbol,
        List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.moveRight) := by
  have hshape : exists firstContext secondContext : MachineCodeSymbol,
      exists gap : Word MachineCodeSymbol,
        contextPrefix left right = firstContext :: secondContext :: gap := by
    cases left with
    | nil =>
        refine ⟨MachineCodeSymbol.done,
          tokenSymbol (firstToken right.length),
          List.append (tokenTail right.length)
            (MachineDescription.encodeCellsAppend right []), ?_⟩
        unfold contextPrefix
        simp only [MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend, List.length_nil,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend]
        rw [encodeNat_eq_firstToken_cons_tail]
        simp
    | cons cell rest =>
        refine ⟨MachineCodeSymbol.tick,
          tokenSymbol (firstToken rest.length),
          List.append (tokenTail rest.length)
            (MachineDescription.encodeCellsAppend (cell :: rest)
              (MachineDescription.encodeCellListAppend right [])), ?_⟩
        unfold contextPrefix
        simp only [MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend, List.length_cons,
          MachineDescription.encodeNat]
        rw [encodeNat_eq_firstToken_cons_tail]
        simp
  rcases hshape with ⟨firstContext, secondContext, gap, hshape⟩
  refine ⟨firstContext, secondContext, gap, hshape, ?_, ?_⟩
  · intro symbol hmem
    have hfull : List.Mem symbol
        (firstContext :: secondContext :: gap) :=
      List.Mem.tail firstContext (List.Mem.tail secondContext hmem)
    have hprefix : List.Mem symbol (contextPrefix left right) := by
      rw [hshape]
      exact hfull
    exact (contextPrefix_safeContextSymbol left right symbol hprefix).left
  · intro symbol hmem
    have hfull : List.Mem symbol
        (firstContext :: secondContext :: gap) :=
      List.Mem.tail firstContext (List.Mem.tail secondContext hmem)
    have hprefix : List.Mem symbol (contextPrefix left right) := by
      rw [hshape]
      exact hfull
    exact (contextPrefix_safeContextSymbol left right symbol hprefix).right
  done

theorem finalBaseLeftRev_reverse
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (left right : List (Option Bool)) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
      (stackRightBaseLeftRev target first rest 0 left) right).reverse =
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header :: MachineCodeSymbol.header ::
          contextPrefix left right) := by
  rw [FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_reverse]
  rw [stackRightBaseLeftRev_reverse]
  simp [tableStack, contextPrefix,
    MachineDescription.encodeNatAppend, List.append_assoc]
  change
    (List.append
      (MachineDescription.encodeCellListAppend left [])
      (MachineDescription.encodeCellListAppend right []) :
        Word MachineCodeSymbol) =
      MachineDescription.encodeCellListAppend left
        (MachineDescription.encodeCellListAppend right [])
  exact
    (encodeCellListAppend_append left []
      (MachineDescription.encodeCellListAppend right [])).symm
  done

theorem haltCopier_output_eq_finalComparator_word
    (currentState haltState : Nat) :
    HaltCopier.outputWord
        (PrefixBuilder.comparatorPrefix currentState) haltState =
      MachineCodeSymbol.header ::
        runtimeKeyComparatorBody
          (List.replicate currentState MachineCodeSymbol.tick) none
          (List.replicate haltState MachineCodeSymbol.tick) none [] := by
  simp [HaltCopier.outputWord, PrefixBuilder.comparatorPrefix,
    runtimeKeyComparatorBody, runtimeKeyCellSymbol,
    MachineDescription.encodeNatAppend,
    runtimeKey_encodeNat_eq_replicate_tick_done,
    List.append_assoc]
  done

theorem haltCopier_output_tape_eq_finalComparator_source
    (currentState haltState : Nat) :
    Tape.input
        (HaltCopier.outputWord
          (PrefixBuilder.comparatorPrefix currentState) haltState) =
      (finalComparatorSourceConfig currentState haltState []).tape := by
  rw [haltCopier_output_eq_finalComparator_word]
  rfl
  done

theorem haltMarker_target_tape_eq_rewind_scan
    (baseLeftRev : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol)
    (hbase : baseLeftRev ≠ []) :
    (HaltMarker.targetConfig baseLeftRev value suffix).tape =
      (Dispatch.NeighborProbe.PrefixRewind.scanConfig baseLeftRev
        (MachineCodeSymbol.moveRight ::
          List.append (tokenTail value) suffix)).tape := by
  cases baseLeftRev with
  | nil => exact False.elim (hbase rfl)
  | cons first rest => rfl
  done

theorem prefixBuilder_target_tape_eq_haltCopier_source
    (currentState haltState : Nat)
    (gap suffix : Word MachineCodeSymbol) :
    (PrefixBuilder.targetConfig (firstToken haltState)
      currentState gap (tokenTail haltState) suffix).tape =
      (HaltCopier.sourceConfig
        (PrefixBuilder.comparatorPrefix currentState)
        gap haltState suffix).tape := by
  rfl
  done

theorem computes_transport_of_tape_equiv
    {symbol state : Type}
    {M : TuringMachine symbol state}
    {source target : TuringMachine.Configuration symbol state}
    {actualSourceTape : Tape symbol}
    (hcomputes : TuringMachine.Computes M source target)
    (hsource : Tape.Equiv source.tape actualSourceTape) :
    exists actualTarget : TuringMachine.Configuration symbol state,
      TuringMachine.Computes M
        { state := source.state, tape := actualSourceTape } actualTarget ∧
      actualTarget.state = target.state ∧
      Tape.Equiv target.tape actualTarget.tape := by
  rcases TuringMachine.computes_to_computesIn hcomputes with
    ⟨steps, hcomputesIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcomputesIn hsource with
    ⟨actualTarget, hactual, hstate, htape⟩
  exact ⟨actualTarget,
    TuringMachine.computesIn_to_computes hactual, hstate, htape⟩
  done

theorem finalMarkedWord_eq_prefixBuilder_source
    (currentState : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (left right : List (Option Bool))
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (firstContext secondContext : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (hcontext : contextPrefix left right =
      firstContext :: secondContext :: gap) :
    (List.append
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
          (stackRightBaseLeftRev currentState first rest 0 left)
          right).reverse
        (MachineCodeSymbol.moveRight ::
          List.append (tokenTail haltState) suffix) :
      Word MachineCodeSymbol) =
      PrefixBuilder.sourceWord currentState firstContext secondContext
        gap (tokenTail haltState) suffix := by
  rw [finalBaseLeftRev_reverse]
  rw [hcontext]
  simp [PrefixBuilder.sourceWord,
    MachineDescription.encodeNatAppend, List.append_assoc]
  done

theorem finalGate_materializes_comparator
    (currentState : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (left right : List (Option Bool))
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    exists markerTape rewindTape prefixTape finalTape :
        Tape MachineCodeSymbol,
      TuringMachine.Computes HaltMarker.machine
        { state := HaltMarker.Control.enter
          tape :=
            (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
              (stackRightBaseLeftRev currentState first rest 0 left)
              right haltState suffix).tape }
        { state := HaltMarker.Control.ready (firstToken haltState)
          tape := markerTape } ∧
      TuringMachine.Computes
        RewindWord.machine
        { state := RewindWord.Control.scan
          tape := markerTape }
        { state := RewindWord.Control.gate
          tape := rewindTape } ∧
      TuringMachine.Computes PrefixBuilder.machine
        { state := PrefixBuilder.Control.start (firstToken haltState)
          tape := rewindTape }
        { state := PrefixBuilder.Control.ready (firstToken haltState)
          tape := prefixTape } ∧
      TuringMachine.Computes HaltCopier.machine
        { state := HaltCopier.Control.seekSource (firstToken haltState)
          tape := prefixTape }
        { state := HaltCopier.Control.ready
          tape := finalTape } ∧
      Tape.Equiv finalTape
        (finalComparatorSourceConfig currentState haltState []).tape := by
  let baseLeftRev : Word MachineCodeSymbol :=
    FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
      (stackRightBaseLeftRev currentState first rest 0 left) right
  rcases contextPrefix_decompose left right with
    ⟨firstContext, secondContext, gap, hcontext,
      hgapHeader, hgapMarker⟩
  let markedTail : Word MachineCodeSymbol :=
    MachineCodeSymbol.moveRight ::
      List.append (tokenTail haltState) suffix
  let fullMarkedWord : Word MachineCodeSymbol :=
    List.append baseLeftRev.reverse markedTail
  let markerTape : Tape MachineCodeSymbol :=
    (HaltMarker.targetConfig baseLeftRev haltState suffix).tape
  have hmarkerRaw := HaltMarker.run_exact
    baseLeftRev haltState suffix
  have hmarkerCanonical : TuringMachine.Computes HaltMarker.machine
      (HaltMarker.sourceConfig baseLeftRev haltState suffix)
      (HaltMarker.targetConfig baseLeftRev haltState suffix) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hmarkerRaw)
  have hmarker : TuringMachine.Computes HaltMarker.machine
      { state := HaltMarker.Control.enter
        tape :=
          (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
            (stackRightBaseLeftRev currentState first rest 0 left)
            right haltState suffix).tape }
      { state := HaltMarker.Control.ready (firstToken haltState)
        tape := markerTape } := by
    simpa [baseLeftRev, markerTape, HaltMarker.sourceConfig,
      HaltMarker.targetConfig,
      rightBoundary_target_tape_eq_haltMarker_source] using
      hmarkerCanonical
  have hbase : baseLeftRev ≠ [] := by
    exact FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_ne_nil
      (stackRightBaseLeftRev currentState first rest 0 left) right
  have hmarkerScan : markerTape =
      (Dispatch.NeighborProbe.PrefixRewind.scanConfig
        baseLeftRev markedTail).tape := by
    simpa [markerTape, markedTail] using
      haltMarker_target_tape_eq_rewind_scan
        baseLeftRev haltState suffix hbase
  have hrewindRaw :=
    Dispatch.NeighborProbe.PrefixRewind.scan_run_exact
      baseLeftRev markedTail
  have hrewindCanonical :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrewindRaw)
  let rewindTape : Tape MachineCodeSymbol :=
    (Dispatch.NeighborProbe.PrefixRewind.gateConfig
      fullMarkedWord).tape
  have hrewind : TuringMachine.Computes
      RewindWord.machine
      { state := RewindWord.Control.scan
        tape := markerTape }
      { state := RewindWord.Control.gate
        tape := rewindTape } := by
    simpa [hmarkerScan, rewindTape, fullMarkedWord,
      Dispatch.NeighborProbe.PrefixRewind.scanConfig,
      Dispatch.NeighborProbe.PrefixRewind.gateConfig] using
      hrewindCanonical
  have hword : fullMarkedWord =
      PrefixBuilder.sourceWord currentState firstContext secondContext
        gap (tokenTail haltState) suffix := by
    dsimp [fullMarkedWord, baseLeftRev, markedTail]
    change
      (List.append
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
          (stackRightBaseLeftRev currentState first rest 0 left)
          right).reverse
        (MachineCodeSymbol.moveRight ::
          List.append (tokenTail haltState) suffix) :
        List MachineCodeSymbol) = _
    exact finalMarkedWord_eq_prefixBuilder_source currentState first rest
      left right haltState suffix firstContext secondContext gap hcontext
  have hgateSource : Tape.Equiv
      (PrefixBuilder.sourceConfig (firstToken haltState) currentState
        firstContext secondContext gap (tokenTail haltState) suffix).tape
      rewindTape := by
    have hgate := Tape.Equiv.symm
      (Dispatch.NeighborProbe.PrefixRewind.gateTape_equiv_input
        fullMarkedWord)
    simpa [PrefixBuilder.sourceConfig, rewindTape,
      Dispatch.NeighborProbe.PrefixRewind.gateConfig, hword] using hgate
  have hprefixRaw := PrefixBuilder.run_exact (firstToken haltState)
    currentState firstContext secondContext gap
    (tokenTail haltState) suffix
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hprefixRaw hgateSource with
    ⟨prefixConfig, hprefixRun, hprefixState, hprefixTape⟩
  rcases prefixConfig with ⟨prefixState, prefixTape⟩
  simp only [PrefixBuilder.targetConfig] at hprefixState
  subst prefixState
  have hprefix : TuringMachine.Computes PrefixBuilder.machine
      { state := PrefixBuilder.Control.start (firstToken haltState)
        tape := rewindTape }
      { state := PrefixBuilder.Control.ready (firstToken haltState)
        tape := prefixTape } :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hprefixRun)
  rcases HaltCopier.copy_computes
      (PrefixBuilder.comparatorPrefix currentState) gap haltState suffix
      hgapHeader hgapMarker with
    ⟨copyTarget, hcopyCanonical, hcopyState, hcopyTape⟩
  have hcopySource : Tape.Equiv
      (HaltCopier.sourceConfig
        (PrefixBuilder.comparatorPrefix currentState)
        gap haltState suffix).tape prefixTape := by
    rw [← prefixBuilder_target_tape_eq_haltCopier_source]
    exact hprefixTape
  rcases computes_transport_of_tape_equiv
      hcopyCanonical hcopySource with
    ⟨actualCopyTarget, hcopyActual, hactualState, hactualTape⟩
  rcases actualCopyTarget with ⟨actualState, finalTape⟩
  have hready : actualState = HaltCopier.Control.ready :=
    hactualState.trans hcopyState
  subst actualState
  have hfinalOutput : Tape.Equiv finalTape
      (Tape.input
        (HaltCopier.outputWord
          (PrefixBuilder.comparatorPrefix currentState) haltState)) :=
    Tape.Equiv.trans (Tape.Equiv.symm hactualTape) hcopyTape
  have hfinal : Tape.Equiv finalTape
      (finalComparatorSourceConfig currentState haltState []).tape := by
    rw [← haltCopier_output_tape_eq_finalComparator_source]
    exact hfinalOutput
  exact ⟨markerTape, rewindTape, prefixTape, finalTape,
    hmarker, hrewind, hprefix, hcopyActual, hfinal⟩
  done


theorem finalGate_materializes_comparator_of_tape_equiv
    (currentState : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (left right : List (Option Bool))
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
        (stackRightBaseLeftRev currentState first rest 0 left)
        right haltState suffix).tape sourceTape) :
    exists markerTape rewindTape prefixTape finalTape :
        Tape MachineCodeSymbol,
      TuringMachine.Computes HaltMarker.machine
        { state := HaltMarker.Control.enter, tape := sourceTape }
        { state := HaltMarker.Control.ready (firstToken haltState)
          tape := markerTape } ∧
      TuringMachine.Computes RewindWord.machine
        { state := RewindWord.Control.scan, tape := markerTape }
        { state := RewindWord.Control.gate, tape := rewindTape } ∧
      TuringMachine.Computes PrefixBuilder.machine
        { state := PrefixBuilder.Control.start (firstToken haltState)
          tape := rewindTape }
        { state := PrefixBuilder.Control.ready (firstToken haltState)
          tape := prefixTape } ∧
      TuringMachine.Computes HaltCopier.machine
        { state := HaltCopier.Control.seekSource (firstToken haltState)
          tape := prefixTape }
        { state := HaltCopier.Control.ready, tape := finalTape } ∧
      Tape.Equiv finalTape
        (finalComparatorSourceConfig currentState haltState []).tape := by
  rcases finalGate_materializes_comparator currentState first rest
      left right haltState suffix with
    ⟨canonicalMarker, canonicalRewind, canonicalPrefix,
      canonicalFinal, hmarker, hrewind, hprefix, hcopy, hfinal⟩
  rcases computes_transport_of_tape_equiv hmarker hsource with
    ⟨markerConfig, hmarkerActual, hmarkerState, hmarkerTape⟩
  rcases markerConfig with ⟨markerState, markerTape⟩
  change markerState = HaltMarker.Control.ready (firstToken haltState) at hmarkerState
  subst markerState
  rcases computes_transport_of_tape_equiv hrewind hmarkerTape with
    ⟨rewindConfig, hrewindActual, hrewindState, hrewindTape⟩
  rcases rewindConfig with ⟨rewindState, rewindTape⟩
  change rewindState = RewindWord.Control.gate at hrewindState
  subst rewindState
  rcases computes_transport_of_tape_equiv hprefix hrewindTape with
    ⟨prefixConfig, hprefixActual, hprefixState, hprefixTape⟩
  rcases prefixConfig with ⟨prefixState, prefixTape⟩
  change prefixState = PrefixBuilder.Control.ready (firstToken haltState) at hprefixState
  subst prefixState
  rcases computes_transport_of_tape_equiv hcopy hprefixTape with
    ⟨finalConfig, hcopyActual, hcopyState, hcopyTape⟩
  rcases finalConfig with ⟨finalState, finalTape⟩
  change finalState = HaltCopier.Control.ready at hcopyState
  subst finalState
  have hfinalActual : Tape.Equiv finalTape
      (finalComparatorSourceConfig currentState haltState []).tape :=
    Tape.Equiv.trans (Tape.Equiv.symm hcopyTape) hfinal
  exact ⟨markerTape, rewindTape, prefixTape, finalTape,
    hmarkerActual, hrewindActual, hprefixActual, hcopyActual,
    hfinalActual⟩
  done


theorem lastSuccess_zeroCopy_trace
    (action : Action)
    (currentState : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (left right : List (Option Bool))
    (head : Option Bool)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    exists prefixTape contextTape leftBoundaryTape rightBoundaryTape :
        Tape MachineCodeSymbol,
    exists markerTape rewindTape gatePrefixTape finalTape comparatorTape :
        Tape MachineCodeSymbol,
      TuringMachine.Computes FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.target action
          tape := Tape.input
            (postSelectedWord currentState (first :: rest) 0
              { left := left, head := head, right := right }
              haltState suffix) }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.ready action
          tape := prefixTape } ∧
      TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
          tape := prefixTape }
        { state := FiniteRecognizer.Interpreter.StackSkip.Control.ready
          tape := contextTape } ∧
      TuringMachine.Computes
        FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.locate .count
          tape := contextTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.ready
          tape := leftBoundaryTape } ∧
      TuringMachine.Computes
        FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.locate .count
          tape := leftBoundaryTape }
        { state := FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.ready
          tape := rightBoundaryTape } ∧
      TuringMachine.Computes HaltMarker.machine
        { state := HaltMarker.Control.enter, tape := rightBoundaryTape }
        { state := HaltMarker.Control.ready (firstToken haltState)
          tape := markerTape } ∧
      TuringMachine.Computes RewindWord.machine
        { state := RewindWord.Control.scan, tape := markerTape }
        { state := RewindWord.Control.gate, tape := rewindTape } ∧
      TuringMachine.Computes PrefixBuilder.machine
        { state := PrefixBuilder.Control.start (firstToken haltState)
          tape := rewindTape }
        { state := PrefixBuilder.Control.ready (firstToken haltState)
          tape := gatePrefixTape } ∧
      TuringMachine.Computes HaltCopier.machine
        { state := HaltCopier.Control.seekSource (firstToken haltState)
          tape := gatePrefixTape }
        { state := HaltCopier.Control.ready, tape := finalTape } ∧
      TuringMachine.Computes runtimeKeyComparatorMachine
        { state := RuntimeKeyComparatorState.needHeader, tape := finalTape }
        { state :=
            if currentState = haltState then
              RuntimeKeyComparatorState.matched
            else
              RuntimeKeyComparatorState.missed
          tape := comparatorTape } := by
  let updatedTape : Tape Bool :=
    { left := left, head := head, right := right }
  let sourceTape : Tape MachineCodeSymbol :=
    Tape.input
      (postSelectedWord currentState (first :: rest) 0 updatedTape
        haltState suffix)
  rcases position_after_stack action currentState first rest 0
      updatedTape haltState suffix sourceTape (Tape.Equiv.refl sourceTape) with
    ⟨prefixTape, contextTape, hprefix, hskip, hcontext⟩
  rcases boundary_from_stack currentState first rest 0
      left right head haltState suffix contextTape hcontext with
    ⟨leftBoundaryTape, hleftBoundary, hleftTape⟩
  have hrightSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.sourceConfig
        (stackRightBaseLeftRev currentState first rest 0 left)
        right haltState suffix).tape leftBoundaryTape := by
    rw [← leftBoundary_target_tape_eq_rightBoundary_source]
    exact hleftTape
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.boundary_computes_of_tape_equiv
      (stackRightBaseLeftRev currentState first rest 0 left)
      right haltState suffix leftBoundaryTape hrightSource with
    ⟨rightBoundaryTape, hrightBoundary, hrightTape⟩
  rcases finalGate_materializes_comparator_of_tape_equiv
      currentState first rest left right haltState suffix
      rightBoundaryTape hrightTape with
    ⟨markerTape, rewindTape, gatePrefixTape, finalTape,
      hmarker, hrewind, hgatePrefix, hcopy, hfinal⟩
  have hcomparatorCanonical :=
    finalComparator_computes_exact currentState haltState []
  rcases computes_transport_of_tape_equiv hcomparatorCanonical
      (Tape.Equiv.symm hfinal) with
    ⟨comparatorConfig, hcomparator, hcomparatorState, _⟩
  rcases comparatorConfig with ⟨comparatorState, comparatorTape⟩
  change comparatorState =
    (if currentState = haltState then
      RuntimeKeyComparatorState.matched
    else RuntimeKeyComparatorState.missed) at hcomparatorState
  subst comparatorState
  exact ⟨prefixTape, contextTape, leftBoundaryTape, rightBoundaryTape,
    markerTape, rewindTape, gatePrefixTape, finalTape, comparatorTape,
    by simpa [sourceTape, updatedTape] using hprefix,
    hskip, hleftBoundary, hrightBoundary, hmarker, hrewind,
    hgatePrefix, hcopy, hcomparator⟩
  done


end FiniteRecognizer.Interpreter.FinalGateMaterializer

end Computability
end FoC
