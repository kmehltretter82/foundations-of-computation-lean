import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.PhaseSum.Machine

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.RuntimePhaseSum

open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.StackIteration
open FiniteRecognizer.Interpreter.SelectedUpdateIntegration
open FiniteRecognizer.Interpreter.FinalGateMaterializer
open FiniteRecognizer.Interpreter.NoMatchFinalGate
open FiniteRecognizer.Interpreter.NoMatchFinalGate.LastMiss
open FiniteRecognizer.Interpreter.SemanticIteration
open FiniteRecognizer.Interpreter.BoundedLoopInduction
open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

/-! ## Concrete bounded-loop macro routes -/

theorem stackProbe_zero_computes
    (action : Action)
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    let stackSource :=
      (FiniteRecognizer.Interpreter.StackSkip.sourceConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest 0 (contextTail tape haltState callerSuffix)).tape
    TuringMachine.Computes machine
      { state := Control.stackProbe action, tape := stackSource }
      { state := Control.stack (.initial action true)
          FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
        tape := stackSource } := by
  dsimp only
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  exact TuringMachine.Computes.refl _


theorem bounce_tape_eq_self
    (tape : Tape MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (hread : Tape.read tape = some symbol)
    (hleft : tape.left ≠ []) :
    Tape.move Direction.right
        (Tape.write
          (Tape.read (Tape.move Direction.left
            (Tape.write (some symbol) tape)))
          (Tape.move Direction.left (Tape.write (some symbol) tape))) =
      tape := by
  rcases tape with ⟨left, head, right⟩
  simp only [Tape.read] at hread
  subst head
  cases left with
  | nil => exact False.elim (hleft rfl)
  | cons leftHead leftTail =>
      rfl

theorem stackProbe_succ_computes
    (action : Action)
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    let stackSource :=
      (FiniteRecognizer.Interpreter.StackSkip.sourceConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest (copies + 1)
        (contextTail tape haltState callerSuffix)).tape
    TuringMachine.Computes machine
      { state := Control.stackProbe action, tape := stackSource }
      { state := Control.stack (.initial action false)
          FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
        tape := stackSource } := by
  dsimp only
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  exact TuringMachine.Computes.refl _

theorem leftProbe_empty_computes
    (action : Action)
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (head : Option Bool)
    (right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    let stackTarget :=
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest (copies + 1)
        (contextTail { left := [], head := head, right := right }
          haltState callerSuffix)).tape
    TuringMachine.Computes machine
      { state := Control.leftProbe action, tape := stackTarget }
      { state := Control.boundary (.leftWrite action true)
          (.locate .count)
        tape := stackTarget } := by
  dsimp only
  let stackTarget :=
    (FiniteRecognizer.Interpreter.StackSkip.targetConfig
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
      first rest (copies + 1)
      (contextTail { left := [], head := head, right := right }
        haltState callerSuffix)).tape
  change TuringMachine.Computes machine
    { state := Control.leftProbe action, tape := stackTarget }
    { state := Control.boundary (.leftWrite action true) (.locate .count),
      tape := stackTarget }
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  have hread : Tape.read stackTarget = some MachineCodeSymbol.done := by
    rfl
  have hleft : stackTarget.left ≠ [] := by
    change List.map some
      (List.append
        (FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack (first :: rest)
          (copies + 1)).reverse
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)) ≠ []
    intro hnil
    have happend := List.map_eq_nil_iff.mp hnil
    have hbase := (List.append_eq_nil_iff.mp happend).2
    simp [FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev] at hbase
  rw [bounce_tape_eq_self stackTarget MachineCodeSymbol.done hread hleft]
  exact TuringMachine.Computes.refl _

theorem leftProbe_nonempty_computes
    (action : Action)
    (target : Nat)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (nextHead : Option Bool)
    (remainingLeft : List (Option Bool))
    (head : Option Bool)
    (right : List (Option Bool))
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    let stackTarget :=
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest (copies + 1)
        (contextTail
          { left := nextHead :: remainingLeft, head := head, right := right }
          haltState callerSuffix)).tape
    TuringMachine.Computes machine
      { state := Control.leftProbe action, tape := stackTarget }
      { state := Control.boundary (.leftWrite action false)
          (.locate .count)
        tape := stackTarget } := by
  dsimp only
  let stackTarget :=
    (FiniteRecognizer.Interpreter.StackSkip.targetConfig
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
      first rest (copies + 1)
      (contextTail
        { left := nextHead :: remainingLeft, head := head, right := right }
        haltState callerSuffix)).tape
  change TuringMachine.Computes machine
    { state := Control.leftProbe action, tape := stackTarget }
    { state := Control.boundary (.leftWrite action false) (.locate .count),
      tape := stackTarget }
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  have hread : Tape.read stackTarget = some MachineCodeSymbol.tick := by
    rfl
  have hleft : stackTarget.left ≠ [] := by
    change List.map some
      (List.append
        (FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack (first :: rest)
          (copies + 1)).reverse
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)) ≠ []
    intro hnil
    have happend := List.map_eq_nil_iff.mp hnil
    have hbase := (List.append_eq_nil_iff.mp happend).2
    simp [FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev] at hbase
  rw [bounce_tape_eq_self stackTarget MachineCodeSymbol.tick hread hleft]
  exact TuringMachine.Computes.refl _

theorem rightProbe_empty_computes
    (action : Action)
    (baseLeftRev : Word MachineCodeSymbol)
    (left : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    let boundaryTarget :=
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
        baseLeftRev left 0 suffix).tape
    TuringMachine.Computes machine
      { state := Control.rightProbe action, tape := boundaryTarget }
      { state := Control.rewind (.rightEmpty action) RewindWord.Control.scan
        tape := boundaryTarget } := by
  dsimp only
  let boundaryTarget :=
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      baseLeftRev left 0 suffix).tape
  change TuringMachine.Computes machine
    { state := Control.rightProbe action, tape := boundaryTarget }
    { state := Control.rewind (.rightEmpty action) RewindWord.Control.scan,
      tape := boundaryTarget }
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  have hread : Tape.read boundaryTarget = some MachineCodeSymbol.done := by
    rfl
  have hleft : boundaryTarget.left ≠ [] := by
    change List.map some
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
        baseLeftRev left) ≠ []
    intro hnil
    exact FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_ne_nil
      baseLeftRev left (List.map_eq_nil_iff.mp hnil)
  rw [bounce_tape_eq_self boundaryTarget MachineCodeSymbol.done hread hleft]
  exact TuringMachine.Computes.refl _

theorem rightProbe_nonempty_computes
    (action : Action)
    (baseLeftRev : Word MachineCodeSymbol)
    (left : List (Option Bool))
    (remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    let boundaryTarget :=
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
        baseLeftRev left (remaining + 1) suffix).tape
    TuringMachine.Computes machine
      { state := Control.rightProbe action, tape := boundaryTarget }
      { state := Control.pop (.right action) (.locate .count)
        tape := boundaryTarget } := by
  dsimp only
  let boundaryTarget :=
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      baseLeftRev left (remaining + 1) suffix).tape
  change TuringMachine.Computes machine
    { state := Control.rightProbe action, tape := boundaryTarget }
    { state := Control.pop (.right action) (.locate .count),
      tape := boundaryTarget }
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  apply TuringMachine.Computes.step
  · apply TuringMachine.Step.mk
    rfl
  have hread : Tape.read boundaryTarget = some MachineCodeSymbol.tick := by
    rfl
  have hleft : boundaryTarget.left ≠ [] := by
    change List.map some
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
        baseLeftRev left) ≠ []
    intro hnil
    exact FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_ne_nil
      baseLeftRev left (List.map_eq_nil_iff.mp hnil)
  rw [bounce_tape_eq_self boundaryTarget MachineCodeSymbol.tick hread hleft]
  exact TuringMachine.Computes.refl _


theorem left_empty_tail
    (target : Nat)
    (write oldHead : Option Bool)
    (right : List (Option Bool))
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (contextTape : Tape MachineCodeSymbol)
    (hcontext : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest (copies + 1)
        (contextTail { left := [], head := oldHead, right := right }
          haltState callerSuffix)).tape contextTape) :
    let action : Action := { write := write, move := Direction.left }
    let updated : Tape Bool :=
      { left := [], head := none, right := write :: right }
    exists scanTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.leftProbe action, tape := contextTape }
        { state := Control.scan
            (.inner RuntimeKeyComparatorState.scanQuery)
          tape := scanTape } ∧
      Tape.Equiv
        (loopSourceConfig { state := target, tape := updated }
          (first :: rest) copies haltState callerSuffix).tape scanTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.left }
  let updated : Tape Bool :=
    { left := [], head := none, right := write :: right }
  have hprobeCanonical := leftProbe_empty_computes action target first rest
    copies oldHead right haltState callerSuffix
  rcases computes_transport_of_tape_equiv hprobeCanonical hcontext with
    ⟨probeConfig, hprobe, hprobeState, hprobeTape⟩
  rcases probeConfig with ⟨probeState, probeTape⟩
  change probeState = Control.boundary (.leftWrite action true)
    (.locate .count) at hprobeState
  subst probeState
  rcases boundary_from_stack target first rest (copies + 1) [] right
      oldHead haltState callerSuffix probeTape (by simpa using hprobeTape) with
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
  refine ⟨scanTape, ?_, ?_⟩
  · apply TuringMachine.computes_trans hprobe
    apply TuringMachine.computes_trans
      (by simpa [boundaryEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        boundary_computes (BoundaryMode.leftWrite action true) hboundary)
    apply TuringMachine.computes_trans
      (by simpa [prependEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prepend_computes (PrependMode.left action true) hprepend)
    simpa [restageEmbed, updated, Tape.read,
      TuringMachine.PhaseEmbedding.liftConfig] using
      restage_computes hrestage
  · simpa [loopSourceConfig, updated] using hscanTape


theorem left_nonempty_tail
    (target : Nat)
    (write oldHead nextHead : Option Bool)
    (remainingLeft right : List (Option Bool))
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (contextTape : Tape MachineCodeSymbol)
    (hcontext : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest (copies + 1)
        (contextTail
          { left := nextHead :: remainingLeft, head := oldHead,
            right := right }
          haltState callerSuffix)).tape contextTape) :
    let action : Action := { write := write, move := Direction.left }
    let updated : Tape Bool :=
      { left := remainingLeft, head := nextHead, right := write :: right }
    exists scanTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.leftProbe action, tape := contextTape }
        { state := Control.scan
            (.inner RuntimeKeyComparatorState.scanQuery)
          tape := scanTape } ∧
      Tape.Equiv
        (loopSourceConfig { state := target, tape := updated }
          (first :: rest) copies haltState callerSuffix).tape scanTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.left }
  let written : Tape Bool :=
    { left := nextHead :: remainingLeft, head := oldHead,
      right := write :: right }
  let updated : Tape Bool :=
    { left := remainingLeft, head := nextHead, right := write :: right }
  have hprobeCanonical := leftProbe_nonempty_computes action target first
    rest copies nextHead remainingLeft oldHead right haltState callerSuffix
  rcases computes_transport_of_tape_equiv hprobeCanonical hcontext with
    ⟨probeConfig, hprobe, hprobeState, hprobeTape⟩
  rcases probeConfig with ⟨probeState, probeTape⟩
  change probeState = Control.boundary (.leftWrite action false)
    (.locate .count) at hprobeState
  subst probeState
  rcases boundary_from_stack target first rest (copies + 1)
      (nextHead :: remainingLeft) right oldHead haltState callerSuffix
      probeTape (by simpa using hprobeTape) with
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
  refine ⟨scanTape, ?_, ?_⟩
  · apply TuringMachine.computes_trans hprobe
    apply TuringMachine.computes_trans
      (by simpa [boundaryEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        boundary_computes (BoundaryMode.leftWrite action false) hboundary)
    apply TuringMachine.computes_trans
      (by simpa [prependEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prepend_computes (PrependMode.left action false) hprepend)
    apply TuringMachine.computes_trans
      (by simpa [prefixEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prefix_computes PrefixPurpose.leftPop hreprefix)
    apply TuringMachine.computes_trans
      (by simpa [stackEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        stack_computes (StackPurpose.leftPop action) hreskip)
    apply TuringMachine.computes_trans
      (by simpa [popEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        pop_computes (PopMode.left action) hpop)
    simpa [restageEmbed, updated, Tape.read,
      TuringMachine.PhaseEmbedding.liftConfig] using
      restage_computes hrestage
  · simpa [loopSourceConfig, updated] using hscanTape


theorem right_nonempty_tail
    (target : Nat)
    (write oldHead nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (contextTape : Tape MachineCodeSymbol)
    (hcontext : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest (copies + 1)
        (contextTail
          { left := left, head := oldHead,
            right := nextHead :: remainingRight }
          haltState callerSuffix)).tape contextTape) :
    let action : Action := { write := write, move := Direction.right }
    let updated : Tape Bool :=
      { left := write :: left, head := nextHead, right := remainingRight }
    exists scanTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.prepend (.right action) (.locate .count),
          tape := contextTape }
        { state := Control.scan
            (.inner RuntimeKeyComparatorState.scanQuery)
          tape := scanTape } ∧
      Tape.Equiv
        (loopSourceConfig { state := target, tape := updated }
          (first :: rest) copies haltState callerSuffix).tape scanTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.right }
  let written : Tape Bool :=
    { left := write :: left, head := oldHead,
      right := nextHead :: remainingRight }
  let updated : Tape Bool :=
    { left := write :: left, head := nextHead, right := remainingRight }
  rcases prepend_left_from_stack target first rest (copies + 1)
      write oldHead left (nextHead :: remainingRight) haltState
      callerSuffix contextTape hcontext with
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
  let boundarySuffix :=
    MachineDescription.encodeCellsAppend (nextHead :: remainingRight)
      (persistent haltState callerSuffix)
  have hprobeCanonical := rightProbe_nonempty_computes action
    (stackBaseLeftRev target first rest (copies + 1)) (write :: left)
    remainingRight.length boundarySuffix
  rcases computes_transport_of_tape_equiv hprobeCanonical
      (by simpa [boundarySuffix] using hboundaryTape) with
    ⟨probeConfig, hprobe, hprobeState, hprobeTape⟩
  rcases probeConfig with ⟨probeState, probeTape⟩
  change probeState = Control.pop (.right action) (.locate .count) at hprobeState
  subst probeState
  rcases pop_right_from_boundary target first rest (copies + 1)
      nextHead (write :: left) remainingRight haltState callerSuffix
      probeTape (by
        simpa [boundarySuffix, MachineDescription.encodeCellsAppend] using
          hprobeTape) with
    ⟨updatedPhysical, hpop, hupdatedPhysical⟩
  have hupdated : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          updated haltState callerSuffix)) updatedPhysical := by
    simpa [updated] using hupdatedPhysical
  rcases restage_next_scan target first rest copies updated haltState
      callerSuffix updatedPhysical hupdated with
    ⟨scanTape, hrestage, hscanTape⟩
  refine ⟨scanTape, ?_, ?_⟩
  · apply TuringMachine.computes_trans
      (by simpa [prependEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prepend_computes (PrependMode.right action) hprepend)
    apply TuringMachine.computes_trans
      (by simpa [prefixEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prefix_computes PrefixPurpose.rightCheck hreprefix)
    apply TuringMachine.computes_trans
      (by simpa [stackEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        stack_computes (StackPurpose.rightCheck action) hreskip)
    apply TuringMachine.computes_trans
      (by simpa [boundaryEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        boundary_computes (BoundaryMode.rightCheck action) hboundary)
    apply TuringMachine.computes_trans hprobe
    apply TuringMachine.computes_trans
      (by simpa [popEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        pop_computes (PopMode.right action) hpop)
    simpa [restageEmbed, updated, Tape.read,
      TuringMachine.PhaseEmbedding.liftConfig] using
      restage_computes hrestage
  · simpa [loopSourceConfig, updated] using hscanTape


theorem right_empty_tail
    (target : Nat)
    (write oldHead : Option Bool)
    (left : List (Option Bool))
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (contextTape : Tape MachineCodeSymbol)
    (hcontext : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.targetConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest (copies + 1)
        (contextTail { left := left, head := oldHead, right := [] }
          haltState callerSuffix)).tape contextTape) :
    let action : Action := { write := write, move := Direction.right }
    let updated : Tape Bool :=
      { left := write :: left, head := none, right := [] }
    exists scanTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.prepend (.right action) (.locate .count),
          tape := contextTape }
        { state := Control.scan
            (.inner RuntimeKeyComparatorState.scanQuery)
          tape := scanTape } ∧
      Tape.Equiv
        (loopSourceConfig { state := target, tape := updated }
          (first :: rest) copies haltState callerSuffix).tape scanTape := by
  dsimp only
  let action : Action := { write := write, move := Direction.right }
  let written : Tape Bool :=
    { left := write :: left, head := oldHead, right := [] }
  let updated : Tape Bool :=
    { left := write :: left, head := none, right := [] }
  rcases prepend_left_from_stack target first rest (copies + 1)
      write oldHead left [] haltState callerSuffix contextTape hcontext with
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
      (write :: left) [] oldHead haltState callerSuffix restackTape
      (by simpa [written] using hrestackTape) with
    ⟨boundaryTape, hboundary, hboundaryTape⟩
  let boundaryBase := stackBaseLeftRev target first rest (copies + 1)
  let boundarySuffix := persistent haltState callerSuffix
  have hprobeCanonical := rightProbe_empty_computes action boundaryBase
    (write :: left) boundarySuffix
  rcases computes_transport_of_tape_equiv hprobeCanonical
      (by simpa [boundaryBase, boundarySuffix,
          MachineDescription.encodeCellsAppend] using hboundaryTape) with
    ⟨probeConfig, hprobe, hprobeState, hprobeTape⟩
  rcases probeConfig with ⟨probeState, probeTape⟩
  change probeState = Control.rewind (.rightEmpty action)
    RewindWord.Control.scan at hprobeState
  subst probeState
  let rewindLeftRev :=
    FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev boundaryBase
      (write :: left)
  let fullWord : Word MachineCodeSymbol :=
    List.append rewindLeftRev.reverse
      (MachineCodeSymbol.done :: boundarySuffix)
  have hrewindRaw :=
    Dispatch.NeighborProbe.PrefixRewind.scan_run_exact
      (MachineCodeSymbol.done :: rewindLeftRev) boundarySuffix
  have hrewindCanonical : TuringMachine.Computes RewindWord.machine
      { state := RewindWord.Control.scan
        tape :=
          (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig boundaryBase
            (write :: left) 0 boundarySuffix).tape }
      { state := RewindWord.Control.gate
        tape :=
          (Dispatch.NeighborProbe.PrefixRewind.gateConfig fullWord).tape } := by
    apply TuringMachine.computesIn_to_computes
    apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    simpa [rewindLeftRev, fullWord,
      Dispatch.NeighborProbe.PrefixRewind.scanConfig,
      Dispatch.NeighborProbe.PrefixRewind.scanTape,
      Dispatch.NeighborProbe.PrefixRewind.gateConfig,
      FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig,
      MachineDescription.encodeNatAppend,
      runtimeKey_encodeNat_eq_replicate_tick_done, List.reverse_cons,
      List.append_assoc] using hrewindRaw
  rcases computes_transport_of_tape_equiv hrewindCanonical
      (by simpa [boundaryBase, boundarySuffix] using hprobeTape) with
    ⟨rewindConfig, hrewind, hrewindState, hrewindTape⟩
  rcases rewindConfig with ⟨rewindState, rewindTape⟩
  change rewindState = RewindWord.Control.gate at hrewindState
  subst rewindState
  have hfullWord : fullWord =
      postSelectedWord target (first :: rest) (copies + 1) updated
        haltState callerSuffix := by
    let emptyRight :=
      MachineDescription.encodeCellListAppend []
        (persistent haltState callerSuffix)
    have hemptyRight : emptyRight =
        MachineCodeSymbol.done :: persistent haltState callerSuffix := by
      rfl
    let activePrefix : Word MachineCodeSymbol :=
      MachineCodeSymbol.header ::
        FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack (first :: rest) (copies + 1)
    calc
      fullWord =
          Word.Concat
            (MachineDescription.encodeNatAppend target activePrefix)
            (Word.Concat
              (MachineDescription.encodeCellListAppend (write :: left) [])
              emptyRight) := by
                simp [fullWord, rewindLeftRev, boundaryBase, boundarySuffix,
                  activePrefix,
                  FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_reverse,
                  stackBaseLeftRev_reverse, hemptyRight, Word.Concat,
                  List.append_assoc]
      _ = Word.Concat
            (MachineDescription.encodeNatAppend target activePrefix)
            (MachineDescription.encodeCellListAppend (write :: left)
              emptyRight) := by
                apply congrArg (fun tail : Word MachineCodeSymbol =>
                  Word.Concat
                    (MachineDescription.encodeNatAppend target activePrefix)
                    tail)
                simpa [Word.Concat] using
                  (encodeCellListAppend_append (write :: left) []
                    emptyRight).symm
      _ = MachineDescription.encodeNatAppend target
            (Word.Concat activePrefix
              (MachineDescription.encodeCellListAppend (write :: left)
                emptyRight)) := by
                simpa [Word.Concat] using (encodeNatAppend_append target
                  activePrefix
                  (MachineDescription.encodeCellListAppend (write :: left)
                    emptyRight)).symm
      _ = postSelectedWord target (first :: rest) (copies + 1) updated
            haltState callerSuffix := by
                simp [activePrefix, emptyRight, postSelectedWord,
                  activeProtectedSuffix, contextTail, updated,
                  RuntimeKeySingleKeyRepair.protectedTapeContextsAppend,
                  persistent, Word.Concat, List.append_assoc]
  have hrestageSource : Tape.Equiv
      (Tape.input
        (postSelectedWord target (first :: rest) (copies + 1)
          updated haltState callerSuffix)) rewindTape := by
    rw [← hfullWord]
    exact Tape.Equiv.trans
      (Tape.Equiv.symm
        (Dispatch.NeighborProbe.PrefixRewind.gateTape_equiv_input fullWord))
      hrewindTape
  rcases restage_next_scan target first rest copies updated haltState
      callerSuffix rewindTape hrestageSource with
    ⟨scanTape, hrestage, hscanTape⟩
  refine ⟨scanTape, ?_, ?_⟩
  · apply TuringMachine.computes_trans
      (by simpa [prependEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prepend_computes (PrependMode.right action) hprepend)
    apply TuringMachine.computes_trans
      (by simpa [prefixEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prefix_computes PrefixPurpose.rightCheck hreprefix)
    apply TuringMachine.computes_trans
      (by simpa [stackEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        stack_computes (StackPurpose.rightCheck action) hreskip)
    apply TuringMachine.computes_trans
      (by simpa [boundaryEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        boundary_computes (BoundaryMode.rightCheck action) hboundary)
    apply TuringMachine.computes_trans hprobe
    apply TuringMachine.computes_trans
      (by simpa [rewindEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        rewind_computes (RewindMode.rightEmpty action) hrewind)
    simpa [restageEmbed, updated, Tape.read,
      TuringMachine.PhaseEmbedding.liftConfig] using
      restage_computes hrestage
  · simpa [loopSourceConfig, updated] using hscanTape


theorem miss_route
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (current : MachineDescription.Configuration)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (htransitions : D.transitions = first :: rest)
    (hlookup :
      D.lookupTransition current.state (Tape.read current.tape) = none)
    (hsource : Tape.Equiv
      (loopSourceConfig current (first :: rest) copies haltState
        callerSuffix).tape sourceTape) :
    exists terminalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (outerLoopConfig scanEmbed current (first :: rest) copies haltState
          callerSuffix sourceTape)
        (outerTerminalConfig finalCompareEmbed current haltState
          terminalTape) := by
  have hmissD := lookupTransition_eq_none_every_misses D current hlookup
  have hmiss : forall row : TransitionDescription,
      List.Mem row (first :: rest) ->
        MachineDescription.Matches current.state
          (Tape.read current.tape) row = false := by
    intro row hmem
    exact hmissD row (by simpa [htransitions] using hmem)
  let protectedSuffix :=
    activeProtectedSuffix (first :: rest) copies current.tape haltState
      callerSuffix
  have hscan : TuringMachine.Computes comparatorMachine
      (loopSourceConfig current (first :: rest) copies haltState
        callerSuffix)
      (canonicalExhaustedRowsTarget current (first :: rest)
        protectedSuffix) := by
    simpa [loopSourceConfig, protectedSuffix] using
      comparator_computes_all_miss_exhausted current [] (first :: rest)
        protectedSuffix hmiss
  rcases lastMiss_trace current (first :: rest) first rest copies haltState
      callerSuffix with
    ⟨stackTape, leftBoundaryTape, rightBoundaryTape, markerTape,
      rewindTape, builderTape, finalTape, comparatorTape,
      hskip, hleft, hright, hmarker, hrewind, hbuilder, hcopy,
      hcompare⟩
  have hcanonical : TuringMachine.Computes machine
      (outerLoopConfig scanEmbed current (first :: rest) copies haltState
        callerSuffix
        (loopSourceConfig current (first :: rest) copies haltState
          callerSuffix).tape)
      (outerTerminalConfig finalCompareEmbed current haltState
        comparatorTape) := by
    apply TuringMachine.computes_trans
      (by simpa [outerLoopConfig, loopSourceConfig,
          canonicalExhaustedRowsTarget, scanEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using scan_computes hscan)
    apply TuringMachine.computes_trans
      (by simpa [protectedSuffix, canonicalExhaustedRowsTarget, stackEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        stack_computes StackPurpose.miss hskip)
    apply TuringMachine.computes_trans
      (by simpa [boundaryEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        boundary_computes BoundaryMode.missLeft hleft)
    apply TuringMachine.computes_trans
      (by simpa [boundaryEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        boundary_computes BoundaryMode.missRight hright)
    apply TuringMachine.computes_trans
      (by simpa [doubleMarkerEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        doubleMarker_computes hmarker)
    apply TuringMachine.computes_trans
      (by simpa [rewindEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        rewind_computes RewindMode.finalMiss hrewind)
    apply TuringMachine.computes_trans
      (by simpa [currentBuilderEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        currentBuilder_computes hbuilder)
    apply TuringMachine.computes_trans
      (by simpa [haltCopierEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        haltCopier_computes hcopy)
    simpa [outerTerminalConfig, finalCompareEmbed,
      TuringMachine.PhaseEmbedding.liftConfig] using
      finalCompare_computes hcompare
  rcases computes_transport_of_tape_equiv hcanonical hsource with
    ⟨actualTarget, hactual, htargetState, _⟩
  rcases actualTarget with ⟨targetState, terminalTape⟩
  simp only at htargetState
  subst targetState
  exact ⟨terminalTape, by
    simpa [outerLoopConfig, outerTerminalConfig] using hactual⟩


theorem lastSuccess_route
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (current : MachineDescription.Configuration)
    (selected : TransitionDescription)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (htransitions : D.transitions = first :: rest)
    (hlookup :
      D.lookupTransition current.state (Tape.read current.tape) =
        some selected)
    (hsource : Tape.Equiv
      (loopSourceConfig current (first :: rest) 0 haltState
        callerSuffix).tape sourceTape) :
    exists terminalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (outerLoopConfig scanEmbed current (first :: rest) 0 haltState
          callerSuffix sourceTape)
        (outerTerminalConfig finalCompareEmbed
          (selectedNextConfig current selected) haltState terminalTape) := by
  rcases lookupTransition_eq_some_first_decompose D current selected
      hlookup with ⟨before, after, hdecompose, hmiss, hmatch⟩
  have hrows : first :: rest = List.append before (selected :: after) :=
    htransitions.symm.trans hdecompose
  rcases FiniteRecognizer.Interpreter.SelectedToStack.first_match_to_postSelected
      current before selected after 0 haltState callerSuffix hmiss hmatch with
    ⟨extractedTape, actionTape, cleanedTape, hscan, hextract,
      haction, hcleanup, hcleaned⟩
  let action : Action :=
    FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction selected
  have hprefixSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.sourceConfig action
        selected.target
        (activeProtectedSuffix (first :: rest) 0 current.tape haltState
          callerSuffix)).tape cleanedTape := by
    rw [prefix_source_tape_eq_postSelected]
    exact Tape.Equiv.symm (by
      simpa [action, hrows] using hcleaned)
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.prefix_computes_of_tape_equiv
      action selected.target
      (activeProtectedSuffix (first :: rest) 0 current.tape haltState
        callerSuffix)
      cleanedTape hprefixSource with
    ⟨prefixTape, hprefix, hprefixTape⟩
  have hprobeCanonical := stackProbe_zero_computes action selected.target
    first rest current.tape haltState callerSuffix
  have hprobeSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.sourceConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev
          selected.target)
        first rest 0 (contextTail current.tape haltState callerSuffix)).tape
      prefixTape := by
    rw [← prefix_target_tape_eq_stackSkip_source action]
    exact hprefixTape
  rcases computes_transport_of_tape_equiv hprobeCanonical hprobeSource with
    ⟨probeConfig, hprobe, hprobeState, hprobeTape⟩
  rcases probeConfig with ⟨probeState, probeTape⟩
  change probeState = Control.stack (.initial action true)
    FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader at hprobeState
  subst probeState
  rcases stackSkip_computes_of_tape_equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev
        selected.target)
      first rest 0 (contextTail current.tape haltState callerSuffix)
      probeTape (by simpa using hprobeTape) with
    ⟨contextTape, hskip, hcontext⟩
  rcases boundary_from_stack selected.target first rest 0
      current.tape.left current.tape.right current.tape.head haltState
      callerSuffix contextTape hcontext with
    ⟨leftBoundaryTape, hleftBoundary, hleftTape⟩
  have hrightSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.sourceConfig
        (stackRightBaseLeftRev selected.target first rest 0
          current.tape.left)
        current.tape.right haltState callerSuffix).tape leftBoundaryTape := by
    rw [← FiniteRecognizer.Interpreter.FinalGateMaterializer.leftBoundary_target_tape_eq_rightBoundary_source]
    exact hleftTape
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.boundary_computes_of_tape_equiv
      (stackRightBaseLeftRev selected.target first rest 0
        current.tape.left)
      current.tape.right haltState callerSuffix leftBoundaryTape
      hrightSource with
    ⟨rightBoundaryTape, hrightBoundary, hrightTape⟩
  rcases finalGate_materializes_comparator_of_tape_equiv
      selected.target first rest current.tape.left current.tape.right
      haltState callerSuffix rightBoundaryTape hrightTape with
    ⟨markerTape, rewindTape, gatePrefixTape, finalTape,
      hmarker, hrewind, hgatePrefix, hcopy, hfinal⟩
  have hcomparatorCanonical :=
    finalComparator_computes_exact selected.target haltState []
  rcases computes_transport_of_tape_equiv hcomparatorCanonical
      (Tape.Equiv.symm hfinal) with
    ⟨comparatorConfig, hcompare, hcompareState, _⟩
  rcases comparatorConfig with ⟨compareState, comparatorTape⟩
  change compareState =
    (if selected.target = haltState then RuntimeKeyComparatorState.matched
     else RuntimeKeyComparatorState.missed) at hcompareState
  subst compareState
  have hselectedHandoff :
      (canonicalSeparatedRowTarget current before selected after
        (activeProtectedSuffix (before ++ selected :: after) 0 current.tape
          haltState callerSuffix)).tape =
      (extractorSourceConfig current before selected after
        (activeProtectedSuffix (before ++ selected :: after) 0 current.tape
          haltState callerSuffix)).tape := by
    simpa [canonicalSelectedRowTarget] using
      (comparator_selected_tape_eq_extractor_source current before selected
        after
        (activeProtectedSuffix (before ++ selected :: after) 0 current.tape
          haltState callerSuffix))
  have hcanonical : TuringMachine.Computes machine
      (outerLoopConfig scanEmbed current (first :: rest) 0 haltState
        callerSuffix
        (loopSourceConfig current (first :: rest) 0 haltState
          callerSuffix).tape)
      (outerTerminalConfig finalCompareEmbed
        (selectedNextConfig current selected) haltState comparatorTape) := by
    apply TuringMachine.computes_trans
      (by simpa [outerLoopConfig, loopSourceConfig, hrows, scanEmbed,
          canonicalSelectedRowTarget,
          TuringMachine.PhaseEmbedding.liftConfig] using scan_computes hscan)
    apply TuringMachine.computes_trans
      (by
        rw [hselectedHandoff]
        simpa [extractEmbed, extractorSourceConfig,
            RuntimeKeySelectedExtractorArbitrary.singleKeySourceConfig,
            TuringMachine.PhaseEmbedding.liftConfig] using
          extract_computes hextract)
    apply TuringMachine.computes_trans
      (by simpa [actionEmbed, action,
          FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
          TuringMachine.PhaseEmbedding.liftConfig] using
        action_computes haction)
    apply TuringMachine.computes_trans
      (by simpa [cleanupEmbed, action,
          FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
          TuringMachine.PhaseEmbedding.liftConfig] using
        cleanup_computes hcleanup)
    apply TuringMachine.computes_trans
      (by simpa [prefixEmbed, action,
          FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prefix_computes PrefixPurpose.initial hprefix)
    apply TuringMachine.computes_trans hprobe
    apply TuringMachine.computes_trans
      (by simpa [stackEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        stack_computes (StackPurpose.initial action true) hskip)
    apply TuringMachine.computes_trans
      (by simpa [boundaryEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        boundary_computes BoundaryMode.finalLeft hleftBoundary)
    apply TuringMachine.computes_trans
      (by simpa [boundaryEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        boundary_computes BoundaryMode.finalRight hrightBoundary)
    apply TuringMachine.computes_trans
      (by simpa [haltMarkerEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        haltMarker_computes hmarker)
    apply TuringMachine.computes_trans
      (by simpa [rewindEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        (rewind_computes
          (RewindMode.finalSuccess (firstToken haltState)) hrewind))
    apply TuringMachine.computes_trans
      (by simpa [prefixBuilderEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prefixBuilder_computes hgatePrefix)
    apply TuringMachine.computes_trans
      (by simpa [haltCopierEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        haltCopier_computes hcopy)
    have hterminalEq :
        { state := finalCompareEmbed
            (if selected.target = haltState then
              RuntimeKeyComparatorState.matched
             else RuntimeKeyComparatorState.missed)
          tape := comparatorTape } =
        outerTerminalConfig finalCompareEmbed
          (selectedNextConfig current selected) haltState comparatorTape := by
      rfl
    rw [← hterminalEq]
    simpa [finalComparatorSourceConfig, finalCompareEmbed,
      TuringMachine.PhaseEmbedding.liftConfig] using
      finalCompare_computes hcompare
  rcases computes_transport_of_tape_equiv hcanonical hsource with
    ⟨actualTarget, hactual, htargetState, _⟩
  rcases actualTarget with ⟨targetState, terminalTape⟩
  simp only at htargetState
  subst targetState
  exact ⟨terminalTape, by
    simpa [outerLoopConfig, outerTerminalConfig] using hactual⟩


theorem nextSuccess_route
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (current : MachineDescription.Configuration)
    (selected : TransitionDescription)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (htransitions : D.transitions = first :: rest)
    (hlookup :
      D.lookupTransition current.state (Tape.read current.tape) =
        some selected)
    (hsource : Tape.Equiv
      (loopSourceConfig current (first :: rest) (copies + 1) haltState
        callerSuffix).tape sourceTape) :
    exists nextTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (outerLoopConfig scanEmbed current (first :: rest) (copies + 1)
          haltState callerSuffix sourceTape)
        (outerLoopConfig scanEmbed (selectedNextConfig current selected)
          (first :: rest) copies haltState callerSuffix nextTape) ∧
      Tape.Equiv
        (loopSourceConfig (selectedNextConfig current selected)
          (first :: rest) copies haltState callerSuffix).tape nextTape := by
  rcases current with ⟨currentState, ⟨left, oldHead, right⟩⟩
  rcases selected with
    ⟨selectedSource, selectedRead, write, selectedMove, target⟩
  rcases lookupTransition_eq_some_first_decompose D
      { state := currentState,
        tape := { left := left, head := oldHead, right := right } }
      (⟨selectedSource, selectedRead, write, selectedMove, target⟩ :
        TransitionDescription)
      hlookup with ⟨before, after, hdecompose, hmiss, hmatch⟩
  have hrows : first :: rest =
      List.append before
        ((⟨selectedSource, selectedRead, write, selectedMove, target⟩ :
          TransitionDescription) :: after) :=
    htransitions.symm.trans hdecompose
  have hsourceRows : Tape.Equiv
      (loopSourceConfig
        { state := currentState,
          tape := { left := left, head := oldHead, right := right } }
        (List.append before
          ((⟨selectedSource, selectedRead, write, selectedMove, target⟩ :
            TransitionDescription) :: after))
        (copies + 1) haltState callerSuffix).tape sourceTape := by
    simpa [hrows] using hsource
  rcases firstMatchPhysicalTrace_of_tape_equiv
      { state := currentState,
        tape := { left := left, head := oldHead, right := right } }
      before
      (⟨selectedSource, selectedRead, write, selectedMove, target⟩ :
        TransitionDescription)
      after (copies + 1) haltState callerSuffix sourceTape hmiss hmatch
      hsourceRows with
    ⟨cleanedTape, htrace⟩
  dsimp [FirstMatchPhysicalTrace] at htrace
  rcases htrace with
    ⟨selectedTape, extractedTape, actionTape, hscan, hextract,
      haction, hcleanup, hcleaned⟩
  let action : Action :=
    FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction
      (⟨selectedSource, selectedRead, write, selectedMove, target⟩ :
        TransitionDescription)
  have hprefixSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.sourceConfig action target
        (activeProtectedSuffix (first :: rest) (copies + 1)
          { left := left, head := oldHead, right := right }
          haltState callerSuffix)).tape cleanedTape := by
    rw [prefix_source_tape_eq_postSelected]
    exact Tape.Equiv.symm (by
      simpa [action, hrows] using hcleaned)
  rcases FiniteRecognizer.Interpreter.DirectContextUpdate.DirectPhases.prefix_computes_of_tape_equiv
      action target
      (activeProtectedSuffix (first :: rest) (copies + 1)
        { left := left, head := oldHead, right := right }
        haltState callerSuffix)
      cleanedTape hprefixSource with
    ⟨prefixTape, hprefix, hprefixTape⟩
  have hprobeCanonical := stackProbe_succ_computes action target first rest
    copies { left := left, head := oldHead, right := right }
    haltState callerSuffix
  have hprobeSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.StackSkip.sourceConfig
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
        first rest (copies + 1)
        (contextTail { left := left, head := oldHead, right := right }
          haltState callerSuffix)).tape prefixTape := by
    rw [← prefix_target_tape_eq_stackSkip_source action]
    exact hprefixTape
  rcases computes_transport_of_tape_equiv hprobeCanonical hprobeSource with
    ⟨probeConfig, hprobe, hprobeState, hprobeTape⟩
  rcases probeConfig with ⟨probeState, probeTape⟩
  change probeState = Control.stack (.initial action false)
    FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader at hprobeState
  subst probeState
  rcases stackSkip_computes_of_tape_equiv
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.targetBaseLeftRev target)
      first rest (copies + 1)
      (contextTail { left := left, head := oldHead, right := right }
        haltState callerSuffix)
      probeTape (by simpa using hprobeTape) with
    ⟨contextTape, hskip, hcontext⟩
  have hfront : TuringMachine.Computes machine
      (outerLoopConfig scanEmbed
        { state := currentState,
          tape := { left := left, head := oldHead, right := right } }
        (first :: rest) (copies + 1) haltState callerSuffix sourceTape)
      { state := Control.stack (.initial action false)
          FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
        tape := probeTape } := by
    apply TuringMachine.computes_trans
      (by simpa [outerLoopConfig, loopSourceWithTape, loopSourceConfig,
          hrows, scanEmbed, TuringMachine.PhaseEmbedding.liftConfig] using
        scan_computes hscan)
    apply TuringMachine.computes_trans
      (by simpa [extractEmbed,
          TuringMachine.PhaseEmbedding.liftConfig] using
        extract_computes hextract)
    apply TuringMachine.computes_trans
      (by simpa [actionEmbed, action,
          FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
          TuringMachine.PhaseEmbedding.liftConfig] using
        action_computes haction)
    apply TuringMachine.computes_trans
      (by simpa [cleanupEmbed, action,
          FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
          TuringMachine.PhaseEmbedding.liftConfig] using
        cleanup_computes hcleanup)
    apply TuringMachine.computes_trans
      (by simpa [prefixEmbed, action,
          FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
          TuringMachine.PhaseEmbedding.liftConfig] using
        prefix_computes PrefixPurpose.initial hprefix)
    simpa [action, FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction] using hprobe
  cases selectedMove with
  | left =>
      cases left with
      | nil =>
          rcases left_empty_tail target write oldHead right first rest copies
              haltState callerSuffix contextTape (by simpa using hcontext) with
            ⟨scanTape, htail, hnext⟩
          have hstack : TuringMachine.Computes machine
              { state := Control.stack (.initial action false)
                  FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
                tape := probeTape }
              { state := Control.leftProbe action, tape := contextTape } := by
            simpa [stackEmbed, action,
              FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
              TuringMachine.PhaseEmbedding.liftConfig] using
              stack_computes (StackPurpose.initial action false) hskip
          refine ⟨scanTape, ?_, ?_⟩
          · have hrun := TuringMachine.computes_trans hfront
                (TuringMachine.computes_trans hstack htail)
            simpa [outerLoopConfig, loopSourceConfig, canonicalScanRowsConfig,
              selectedNextConfig,
              scanEmbed, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight] using hrun
          · simpa [selectedNextConfig, Tape.write, Tape.move,
              Tape.moveLeft, Tape.moveRight] using hnext
      | cons nextHead remainingLeft =>
          rcases left_nonempty_tail target write oldHead nextHead
              remainingLeft right first rest copies haltState callerSuffix
              contextTape (by simpa using hcontext) with
            ⟨scanTape, htail, hnext⟩
          have hstack : TuringMachine.Computes machine
              { state := Control.stack (.initial action false)
                  FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
                tape := probeTape }
              { state := Control.leftProbe action, tape := contextTape } := by
            simpa [stackEmbed, action,
              FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
              TuringMachine.PhaseEmbedding.liftConfig] using
              stack_computes (StackPurpose.initial action false) hskip
          refine ⟨scanTape, ?_, ?_⟩
          · have hrun := TuringMachine.computes_trans hfront
                (TuringMachine.computes_trans hstack htail)
            simpa [outerLoopConfig, loopSourceConfig, canonicalScanRowsConfig,
              selectedNextConfig,
              scanEmbed, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight] using hrun
          · simpa [selectedNextConfig, Tape.write, Tape.move,
              Tape.moveLeft, Tape.moveRight] using hnext
  | right =>
      cases right with
      | nil =>
          rcases right_empty_tail target write oldHead left first rest copies
              haltState callerSuffix contextTape (by simpa using hcontext) with
            ⟨scanTape, htail, hnext⟩
          have hstack : TuringMachine.Computes machine
              { state := Control.stack (.initial action false)
                  FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
                tape := probeTape }
              { state := Control.prepend (.right action) (.locate .count),
                tape := contextTape } := by
            simpa [stackEmbed, action,
              FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
              TuringMachine.PhaseEmbedding.liftConfig] using
              stack_computes (StackPurpose.initial action false) hskip
          refine ⟨scanTape, ?_, ?_⟩
          · have hrun := TuringMachine.computes_trans hfront
                (TuringMachine.computes_trans hstack htail)
            simpa [outerLoopConfig, loopSourceConfig, canonicalScanRowsConfig,
              selectedNextConfig,
              scanEmbed, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight] using hrun
          · simpa [selectedNextConfig, Tape.write, Tape.move,
              Tape.moveLeft, Tape.moveRight] using hnext
      | cons nextHead remainingRight =>
          rcases right_nonempty_tail target write oldHead nextHead left
              remainingRight first rest copies haltState callerSuffix
              contextTape (by simpa using hcontext) with
            ⟨scanTape, htail, hnext⟩
          have hstack : TuringMachine.Computes machine
              { state := Control.stack (.initial action false)
                  FiniteRecognizer.Interpreter.StackSkip.Control.afterHeader
                tape := probeTape }
              { state := Control.prepend (.right action) (.locate .count),
                tape := contextTape } := by
            simpa [stackEmbed, action,
              FiniteRecognizer.Interpreter.RuntimeLeftCleanup.selectedAction,
              TuringMachine.PhaseEmbedding.liftConfig] using
              stack_computes (StackPurpose.initial action false) hskip
          refine ⟨scanTape, ?_, ?_⟩
          · have hrun := TuringMachine.computes_trans hfront
                (TuringMachine.computes_trans hstack htail)
            simpa [outerLoopConfig, loopSourceConfig, canonicalScanRowsConfig,
              selectedNextConfig,
              scanEmbed, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight] using hrun
          · simpa [selectedNextConfig, Tape.write, Tape.move,
              Tape.moveLeft, Tape.moveRight] using hnext


/-- The concrete finite phase sum discharges every macro obligation used by
the semantic bounded-loop induction. -/
def runtimeLoopPhaseContract : RuntimeLoopPhaseContract machine where
  loopEmbed := scanEmbed
  finalEmbed := finalCompareEmbed
  miss := miss_route
  lastSuccess := lastSuccess_route
  nextSuccess := nextSuccess_route

/-- The finite runtime phase sum executes the bounded semantic interpreter
from any padding-equivalent physical loop entry. -/
theorem runtime_bounded_loop_computes
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest)
    (copies : Nat)
    (current : MachineDescription.Configuration)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (loopSourceConfig current (first :: rest) copies haltState
        callerSuffix).tape sourceTape) :
    exists terminalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (outerLoopConfig scanEmbed current (first :: rest) copies
          haltState callerSuffix sourceTape)
        (outerTerminalConfig finalCompareEmbed
          (D.runConfig (copies + 1) current) haltState terminalTape) := by
  exact bounded_loop_computes machine runtimeLoopPhaseContract D first rest
    htransitions copies current haltState callerSuffix sourceTape hsource


end FiniteRecognizer.Interpreter.RuntimePhaseSum

end Computability
end FoC
