import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.PairMaterializer.Machine
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CallerAwareFinish
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.EquivWitness

/-!
# Product pair-prefix materializer runs

Exact empty and nonempty branch schedules for the fixed pair-prefix
materializer, together with the unified product-composition witness family.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductPairMaterializer

/-! ## Empty branch schedules -/

def emptyCallerCells {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (rightFuel : Nat) : List (Option MachineCodeSymbol) :=
  some MachineCodeSymbol.header ::
    ProductCleanupShapes.emptyOpaqueRightCells right rightFuel

theorem cleanupDeleted_eq_emptyPositionSource
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    cleanupEmptyConfig (left := left) (right := right)
        (ProductCleanup.DynamicRightFuel.deletedConfig [] leftFuel
          (ProductCleanupShapes.emptyOpaqueRightCells right rightFuel)) =
      positionEmptyConfig (left := left) (right := right)
        (EmptyHeaderPositioner.sourceConfig leftFuel
          (emptyCallerCells right rightFuel)) := by
  apply ProductEquivWitness.config_eq_of_state_tape_eq
  · simp [cleanupEmptyConfig, positionEmptyConfig,
      TuringMachine.PhaseEmbedding.liftConfig, cleanupEmptyEmbed,
      positionEmptyEmbed, ProductCleanup.DynamicRightFuel.deletedConfig,
      EmptyHeaderPositioner.sourceConfig,
      EmptyHeaderPositioner.scanConfig,
      EmptyHeaderPositioner.machine,
      ProductCleanup.DynamicRightFuel.machine]
  · change
      (match MachineDescription.encodeNatAppend leftFuel [] with
      | [] =>
          { left := [none]
            head := none
            right := emptyCallerCells right rightFuel }
      | first :: rest =>
          { left := [none]
            head := some first
            right := List.append (rest.map some)
              (none :: emptyCallerCells right rightFuel) }) =
        EmptyHeaderPositioner.scanTape []
          (MachineDescription.encodeNat leftFuel)
          (emptyCallerCells right rightFuel)
    simp [MachineDescription.encodeNatAppend,
      EmptyHeaderPositioner.scanTape, Word]
    cases MachineDescription.encodeNat leftFuel <;> rfl

theorem emptyPositionTarget_equiv_packedSource
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    Tape.Equiv
      (ProductGapExpander.emptyPackedSourceConfig
        left right leftFuel rightFuel).tape
      (EmptyHeaderPositioner.paddedTargetConfig leftFuel
        (emptyCallerCells right rightFuel)).tape := by
  rw [ProductGapExpander.emptyPackedSourceConfig_eq_generic]
  rw [ProductGapExpander.EmptyContract.pairCallerData_empty_eq_header_body]
  refine ⟨rfl, rfl, ?_⟩
  change Tape.dropTrailingNone _ =
    Tape.dropTrailingNone (List.append _ [none])
  exact (FoC.Computability.dropTrailingNone_append_none _).symm

def emptyPositionSchedule
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (machine left right)
      (cleanupEmptyConfig
        (ProductCleanup.DynamicRightFuel.deletedConfig [] leftFuel
          (ProductCleanupShapes.emptyOpaqueRightCells right rightFuel)))
      (gapEmptyConfig
        (ProductGapExpander.emptyPackedSourceConfig
          left right leftFuel rightFuel)) := by
  let callerCells := emptyCallerCells right rightFuel
  let source := EmptyHeaderPositioner.sourceConfig leftFuel callerCells
  let endpoint :=
    EmptyHeaderPositioner.paddedTargetConfig leftFuel callerCells
  have hinner := EmptyHeaderPositioner.run_exact leftFuel callerCells
  have hlift := positionEmpty_run_lift left right hinner
  refine
    { endpoint := positionEmptyConfig endpoint
      steps := EmptyHeaderPositioner.runSteps leftFuel
      run_exact := ?_
      endpoint_state := ?_
      canonical_tape_equiv := ?_ }
  · rw [cleanupDeleted_eq_emptyPositionSource]
    simpa [source, callerCells, endpoint] using hlift
  · rfl
  · simpa [endpoint, callerCells, positionEmptyConfig, gapEmptyConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        emptyPositionTarget_equiv_packedSource
          left right leftFuel rightFuel

def emptyGapSchedule
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (machine left right)
      (gapEmptyConfig
        (ProductGapExpander.emptyPackedSourceConfig
          left right leftFuel rightFuel))
      (gapEmptyConfig
        (ProductGapExpander.emptyWriterTargetConfig
          left right leftFuel rightFuel)) := by
  apply ProductEquivWitness.RunsToEquiv.exact
    (ProductGapExpander.runSteps (emptyExtra left) leftFuel)
  exact gapEmpty_run_lift left right
    (ProductGapExpander.run_empty_to_writer_exact
      left right leftFuel rightFuel)

theorem emptyGapTarget_eq_finishSource
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    gapEmptyConfig (left := left) (right := right)
        (ProductGapExpander.emptyWriterTargetConfig
          left right leftFuel rightFuel) =
      finishConfig
        (ProductCallerAwareFinish.emptyWriterSource
          left right leftFuel rightFuel) := by
  rfl

def emptyFinishSchedule
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (machine left right)
      (gapEmptyConfig
        (ProductGapExpander.emptyWriterTargetConfig
          left right leftFuel rightFuel))
      (ProductEquivWitness.pairCanonicalTarget
        (machine left right) left right [] leftFuel rightFuel) := by
  let branch :=
    ProductCallerAwareFinish.empty_finish_run
      left right leftFuel rightFuel
  have hlift := finish_run_lift left right branch.run_exact
  refine
    { endpoint := finishConfig branch.endpoint
      steps := branch.steps
      run_exact := ?_
      endpoint_state := ?_
      canonical_tape_equiv := branch.canonical_tape_equiv }
  · rw [emptyGapTarget_eq_finishSource]
    simpa [branch] using hlift
  · have hstate := congrArg Control.finish branch.endpoint_state
    simpa [branch, ProductEquivWitness.pairCanonicalTarget,
      ProductCallerAwareFinish.emptyCanonicalTarget,
      finishConfig, machine,
      TuringMachine.PhaseEmbedding.liftConfig] using hstate

def emptyPostCleanupSchedule
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (machine left right)
      (cleanupEmptyConfig
        (ProductCleanup.DynamicRightFuel.deletedConfig [] leftFuel
          (ProductCleanupShapes.emptyOpaqueRightCells right rightFuel)))
      (ProductEquivWitness.pairCanonicalTarget
        (machine left right) left right [] leftFuel rightFuel) :=
  (emptyPositionSchedule left right leftFuel rightFuel).trans
    ((emptyGapSchedule left right leftFuel rightFuel).trans
      (emptyFinishSchedule left right leftFuel rightFuel))

theorem emptyCleanupSchedule_nonempty
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (cleanupEmptyConfig
          (ProductCleanup.DynamicRightFuel.sourceConfig []
            leftFuel rightFuel
            (ProductCleanupShapes.emptyOpaqueRightCells
              right rightFuel)))
        (cleanupEmptyConfig
          (ProductCleanup.DynamicRightFuel.deletedConfig [] leftFuel
            (ProductCleanupShapes.emptyOpaqueRightCells
              right rightFuel)))) := by
  rcases ProductCleanup.DynamicRightFuel.run_to_deleted
      ([] : Word MachineCodeSymbol) leftFuel rightFuel
      (ProductCleanupShapes.emptyOpaqueRightCells right rightFuel) with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  have hlift := cleanupEmpty_run_lift left right hrun
  refine ⟨
    { endpoint := cleanupEmptyConfig endpoint
      steps := steps
      run_exact := hlift
      endpoint_state := ?_
      canonical_tape_equiv := htape }⟩
  simpa [cleanupEmptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    ProductCleanup.DynamicRightFuel.deletedConfig] using
      congrArg cleanupEmptyEmbed hstate

theorem emptyCleanupSourceTape_eq_prefixShiftSource
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    (ProductCleanup.DynamicRightFuel.sourceConfig []
      leftFuel rightFuel
      (ProductCleanupShapes.emptyOpaqueRightCells right rightFuel)).tape =
    ProductCleanupShapes.prefixShiftSourceTape
      (ProductPrefix.retainedOuterRev [] leftFuel rightFuel)
      (ProductCleanupShapes.emptyOpaqueRightCells right rightFuel) := by
  rw [ProductCleanupShapes.retainedOuterRev_eq_retainedRawPrefix_reverse]
  rfl

theorem emptyPrefixSchedule_nonempty
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (TuringMachine.initial (machine left right)
          (GeneratedCode.nestedStageCode [] rightFuel leftFuel))
        (cleanupEmptyConfig
          (ProductCleanup.DynamicRightFuel.sourceConfig []
            leftFuel rightFuel
            (ProductCleanupShapes.emptyOpaqueRightCells
              right rightFuel)))) := by
  rcases ProductCleanupShapes.prefix_run_to_opaque_prefix_shift_source
      right ([] : Word MachineCodeSymbol) leftFuel rightFuel with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  let prefixEndpoint : Config (Control left right) :=
    finishConfig
      (ProductFinish.prefixConfig
        (ProductPrefix.materializerConfig endpoint))
  let cleanupInner : Config ProductCleanup.DynamicRightFuel.Control :=
    { state := ProductCleanup.DynamicRightFuel.machine.start
      tape := Tape.move Direction.left endpoint.tape }
  let cleanupEndpoint : Config (Control left right) :=
    cleanupEmptyConfig cleanupInner
  have hfinish := ProductFinish.prefix_run_lift left right hrun
  have hmaster := finish_run_lift left right hfinish
  have hprefix :
      (machine left right).runConfigExact? steps
          (TuringMachine.initial (machine left right)
            (GeneratedCode.nestedStageCode [] rightFuel leftFuel)) =
        some prefixEndpoint := by
    simpa [prefixEndpoint, TuringMachine.initial, machine,
      finishConfig, ProductFinish.prefixConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      ProductFinish.machine] using hmaster
  have hhandoff :
      (machine left right).runConfigExact? 1 prefixEndpoint =
        some cleanupEndpoint := by
    rcases endpoint with ⟨endpointState, endpointTape⟩
    change endpointState =
      ProductRightPrefix.rightTerminalState right [] at hstate
    change endpointState = .emptyPrepend .gate at hstate
    subst endpointState
    simp [prefixEndpoint, cleanupEndpoint, cleanupInner,
      TuringMachine.runConfigExact?, TuringMachine.stepConfig,
      machine, transition, emptyPrefixEndpoint,
      finishConfig, ProductFinish.prefixConfig,
      ProductPrefix.materializerConfig, cleanupEmptyConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      ProductFinish.write_read_eq_self,
      ProductCleanup.DynamicRightFuel.machine]
  have hfull :
      (machine left right).runConfigExact? (steps + 1)
          (TuringMachine.initial (machine left right)
            (GeneratedCode.nestedStageCode [] rightFuel leftFuel)) =
        some cleanupEndpoint := by
    rw [InitialMaterializer.ExactRun.append, hprefix]
    exact hhandoff
  refine ⟨
    { endpoint := cleanupEndpoint
      steps := steps + 1
      run_exact := hfull
      endpoint_state := ?_
      canonical_tape_equiv := ?_ }⟩
  · rfl
  · change Tape.Equiv
      (ProductCleanup.DynamicRightFuel.sourceConfig []
        leftFuel rightFuel
        (ProductCleanupShapes.emptyOpaqueRightCells
          right rightFuel)).tape
      (Tape.move Direction.left endpoint.tape)
    rw [emptyCleanupSourceTape_eq_prefixShiftSource]
    exact htape

theorem emptyMasterSchedule_nonempty
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (TuringMachine.initial (machine left right)
          (GeneratedCode.nestedStageCode [] rightFuel leftFuel))
        (ProductEquivWitness.pairCanonicalTarget
          (machine left right) left right [] leftFuel rightFuel)) := by
  rcases emptyPrefixSchedule_nonempty
      left right leftFuel rightFuel with ⟨prefixSchedule⟩
  rcases emptyCleanupSchedule_nonempty
      left right leftFuel rightFuel with ⟨cleanup⟩
  exact ⟨prefixSchedule.trans
    (cleanup.trans (emptyPostCleanupSchedule
      left right leftFuel rightFuel))⟩

theorem emptyPairPrefixWitness_exists
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    exists pairPrefix : ProductComposition.PairPrefixWitness
        (machine left right) left right [] leftFuel rightFuel,
      pairPrefix.source =
        TuringMachine.initial (machine left right)
          (GeneratedCode.nestedStageCode [] rightFuel leftFuel) := by
  rcases emptyMasterSchedule_nonempty
      left right leftFuel rightFuel with ⟨schedule⟩
  refine ⟨ProductEquivWitness.pairPrefixWitness_of_runsToEquiv
    (machine left right) left right [] leftFuel rightFuel
      (haltingTransitionsDisabled left right) schedule, rfl⟩

/-! ## Nonempty branch schedules -/

namespace NonemptyPackPositioner

def scanTape (leftRev remaining : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := List.append (leftRev.map some) [none]
        head := none
        right := some MachineCodeSymbol.header :: opaqueRight }
  | current :: rest =>
      { left := List.append (leftRev.map some) [none]
        head := some current
        right := List.append (rest.map some)
          (none :: some MachineCodeSymbol.header :: opaqueRight) }

def scanConfig (leftRev remaining : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) : Config Control :=
  { state := .scan
    tape := scanTape leftRev remaining opaqueRight }

def sourceConfig (word : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) : Config Control :=
  scanConfig [] word opaqueRight

def headerConfig (word : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) : Config Control :=
  { state := .header
    tape := Tape.move Direction.right
      (scanTape word.reverse [] opaqueRight) }

def paddedTargetConfig (word : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) : Config Control :=
  { state := .halt
    tape := Tape.move Direction.right
      (headerConfig word opaqueRight).tape }

theorem scan_step (leftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (scanConfig leftRev (current :: rest) opaqueRight) =
      some (scanConfig (current :: leftRev) rest opaqueRight) := by
  cases rest <;> cases opaqueRight <;> rfl

theorem scan_run_exact (remaining leftRev : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? remaining.length
        (scanConfig leftRev remaining opaqueRight) =
      some (scanConfig
        (List.append remaining.reverse leftRev) [] opaqueRight) := by
  induction remaining generalizing leftRev with
  | nil => rfl
  | cons current remaining ih =>
      change machine.runConfigExact? (remaining.length + 1)
          (scanConfig leftRev (current :: remaining) opaqueRight) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step]
      simp only
      rw [ih (current :: leftRev)]
      simp [List.reverse_cons, List.append_assoc]

theorem gap_step (word : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    machine.stepConfig (scanConfig word.reverse [] opaqueRight) =
      some (headerConfig word opaqueRight) := by
  cases word <;> cases opaqueRight <;> rfl

theorem header_step (word : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    machine.stepConfig (headerConfig word opaqueRight) =
      some (paddedTargetConfig word opaqueRight) := by
  cases word <;> cases opaqueRight <;> rfl

def runSteps (word : Word MachineCodeSymbol) : Nat :=
  word.length + 2

theorem run_exact (word : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (runSteps word)
        (sourceConfig word opaqueRight) =
      some (paddedTargetConfig word opaqueRight) := by
  unfold runSteps sourceConfig
  rw [show word.length + 2 = word.length + (1 + 1) by lia]
  rw [InitialMaterializer.ExactRun.append]
  have hscan := scan_run_exact word ([] : Word MachineCodeSymbol)
    opaqueRight
  have hscan' : machine.runConfigExact? word.length
      (scanConfig [] word opaqueRight) =
        some (scanConfig word.reverse [] opaqueRight) := by
    simpa [Word] using hscan
  rw [hscan']
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [show machine.runConfigExact? 1
      (scanConfig word.reverse [] opaqueRight) =
        some (headerConfig word opaqueRight) by
    rw [TuringMachine.runConfigExact?]
    exact gap_step word opaqueRight]
  simp only
  rw [TuringMachine.runConfigExact?]
  exact header_step word opaqueRight

end NonemptyPackPositioner

theorem cleanupDeleted_eq_nonemptyPositionSource
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    cleanupNonemptyConfig (left := left) (right := right)
        (ProductCleanup.DynamicRightFuel.deletedConfig
          (headSymbol :: rest) leftFuel
          (ProductCleanupShapes.nonemptyOpaqueRightCells
            right headSymbol rest rightFuel)) =
      positionNonemptyConfig (left := left) (right := right)
        (NonemptyPackPositioner.sourceConfig
          (MachineDescription.encodeNatAppend leftFuel
            (headSymbol :: rest))
          (ProductCleanupShapes.nonemptyOpaqueRightCells
            right headSymbol rest rightFuel)) := by
  apply ProductEquivWitness.config_eq_of_state_tape_eq
  · simp [cleanupNonemptyConfig, positionNonemptyConfig,
      TuringMachine.PhaseEmbedding.liftConfig, cleanupNonemptyEmbed,
      positionNonemptyEmbed,
      ProductCleanup.DynamicRightFuel.deletedConfig,
      NonemptyPackPositioner.sourceConfig,
      NonemptyPackPositioner.scanConfig,
      ProductCleanup.DynamicRightFuel.machine,
      NonemptyPackPositioner.machine]
  · change
      (match MachineDescription.encodeNatAppend leftFuel
          (headSymbol :: rest) with
      | [] =>
          { left := [none]
            head := none
            right := some MachineCodeSymbol.header ::
              ProductCleanupShapes.nonemptyOpaqueRightCells
                right headSymbol rest rightFuel }
      | first :: suffix =>
          { left := [none]
            head := some first
            right := List.append (suffix.map some)
              (none :: some MachineCodeSymbol.header ::
                ProductCleanupShapes.nonemptyOpaqueRightCells
                  right headSymbol rest rightFuel) }) =
        NonemptyPackPositioner.scanTape []
          (MachineDescription.encodeNatAppend leftFuel
            (headSymbol :: rest))
          (ProductCleanupShapes.nonemptyOpaqueRightCells
            right headSymbol rest rightFuel)
    cases leftFuel <;> rfl

theorem nonemptyPositionTarget_eq_compactorPaddedSource
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    positionNonemptyConfig (left := left) (right := right)
        (NonemptyPackPositioner.paddedTargetConfig
          (MachineDescription.encodeNatAppend leftFuel
            (headSymbol :: rest))
          (ProductCleanupShapes.nonemptyOpaqueRightCells
            right headSymbol rest rightFuel)) =
      compactorConfig (left := left) (right := right)
        (ProductCleanup.Pack.nonemptyPaddedSourceConfig
          (ProductGapExpander.Nonempty.packedOuterLeft
            (headSymbol :: rest) leftFuel)
          right headSymbol rest rightFuel) := by
  apply ProductEquivWitness.config_eq_of_state_tape_eq
  · simp [positionNonemptyConfig, compactorConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      positionNonemptyEmbed, compactorEmbed,
      NonemptyPackPositioner.paddedTargetConfig,
      NonemptyPackPositioner.headerConfig,
      NonemptyPackPositioner.machine,
      ProductCleanup.Pack.nonemptyPaddedSourceConfig,
      StageInput.TwoBlankCompactor.config,
      StageInput.TwoBlankCompactor.machine]
  · cases leftFuel <;> cases rightFuel <;>
      simp [positionNonemptyConfig, compactorConfig,
        TuringMachine.PhaseEmbedding.liftConfig,
        NonemptyPackPositioner.paddedTargetConfig,
        NonemptyPackPositioner.headerConfig,
        NonemptyPackPositioner.scanTape,
        ProductCleanupShapes.nonemptyOpaqueRightCells,
        ProductCleanup.Pack.nonemptyPaddedSourceConfig,
        ProductCleanup.Pack.nonemptyPaddedSourceTape,
        ProductCleanup.Pack.nonemptyCleanSourceConfig,
        ProductCleanup.Pack.seekConfig, ProductCleanup.Pack.seekTape,
        ProductCleanup.Pack.nonemptyBody,
        StageInput.TwoBlankCompactor.config,
        StageInput.TwoBlankCompactor.materializerBody,
        ProductGapExpander.Nonempty.packedOuterLeft,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, List.map_append,
        List.append_assoc, Tape.move, Tape.moveRight]

def nonemptyPositionSchedule
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (machine left right)
      (cleanupNonemptyConfig
        (ProductCleanup.DynamicRightFuel.deletedConfig
          (headSymbol :: rest) leftFuel
          (ProductCleanupShapes.nonemptyOpaqueRightCells
            right headSymbol rest rightFuel)))
      (compactorConfig
        (ProductCleanup.Pack.nonemptyPaddedSourceConfig
          (ProductGapExpander.Nonempty.packedOuterLeft
            (headSymbol :: rest) leftFuel)
          right headSymbol rest rightFuel)) := by
  apply ProductEquivWitness.RunsToEquiv.exact
    (NonemptyPackPositioner.runSteps
      (MachineDescription.encodeNatAppend leftFuel
        (headSymbol :: rest)))
  rw [cleanupDeleted_eq_nonemptyPositionSource]
  rw [← nonemptyPositionTarget_eq_compactorPaddedSource]
  exact positionNonempty_run_lift left right
    (NonemptyPackPositioner.run_exact
      (MachineDescription.encodeNatAppend leftFuel
        (headSymbol :: rest))
      (ProductCleanupShapes.nonemptyOpaqueRightCells
        right headSymbol rest rightFuel))

theorem nonemptyCleanupSchedule_nonempty
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (cleanupNonemptyConfig
          (ProductCleanup.DynamicRightFuel.sourceConfig
            (headSymbol :: rest) leftFuel rightFuel
            (ProductCleanupShapes.nonemptyOpaqueRightCells
              right headSymbol rest rightFuel)))
        (cleanupNonemptyConfig
          (ProductCleanup.DynamicRightFuel.deletedConfig
            (headSymbol :: rest) leftFuel
            (ProductCleanupShapes.nonemptyOpaqueRightCells
              right headSymbol rest rightFuel)))) := by
  rcases ProductCleanup.DynamicRightFuel.run_to_deleted
      (headSymbol :: rest) leftFuel rightFuel
      (ProductCleanupShapes.nonemptyOpaqueRightCells
        right headSymbol rest rightFuel) with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  have hlift := cleanupNonempty_run_lift left right hrun
  refine ⟨
    { endpoint := cleanupNonemptyConfig endpoint
      steps := steps
      run_exact := hlift
      endpoint_state := ?_
      canonical_tape_equiv := htape }⟩
  simpa [cleanupNonemptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    ProductCleanup.DynamicRightFuel.deletedConfig] using
      congrArg cleanupNonemptyEmbed hstate

theorem nonemptyCompactorSchedule_nonempty
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (compactorConfig
          (ProductCleanup.Pack.nonemptyPaddedSourceConfig
            (ProductGapExpander.Nonempty.packedOuterLeft
              (headSymbol :: rest) leftFuel)
            right headSymbol rest rightFuel))
        (gapNonemptyConfig
          (ProductGapExpander.Nonempty.packedSourceConfig
            right headSymbol rest leftFuel rightFuel))) := by
  rcases ProductCleanup.Pack.run_nonempty_from_padded_source
      (ProductGapExpander.Nonempty.packedOuterLeft
        (headSymbol :: rest) leftFuel)
      right headSymbol rest rightFuel with
    ⟨endpoint, hrun, hstate, htape⟩
  have hlift := compactor_run_lift left right hrun
  refine ⟨
    { endpoint := compactorConfig endpoint
      steps := ProductCleanup.Pack.nonemptyRunSteps
        right headSymbol rest rightFuel
      run_exact := hlift
      endpoint_state := ?_
      canonical_tape_equiv := ?_ }⟩
  · have hbridge : compactorEmbed (left := left) (right := right)
        endpoint.state =
      gapNonemptyEmbed (left := left) (right := right)
        (ProductGapExpander.machine (show 0 < 2 by decide)).start := by
      rw [hstate]
      rfl
    simpa [compactorConfig, gapNonemptyConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      ProductGapExpander.Nonempty.packedSourceConfig,
      ProductGapExpander.config,
      ProductGapExpander.machine,
      StageInput.TwoBlankCompactor.machine] using hbridge
  · simpa [compactorConfig, gapNonemptyConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      ProductGapExpander.Nonempty.packedSourceConfig,
      ProductGapExpander.config] using
        Tape.Equiv.symm htape

def nonemptyGapSchedule
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (machine left right)
      (gapNonemptyConfig
        (ProductGapExpander.Nonempty.packedSourceConfig
          right headSymbol rest leftFuel rightFuel))
      (gapNonemptyConfig
        (ProductGapExpander.Nonempty.callerTailTargetConfig
          right headSymbol rest leftFuel rightFuel)) := by
  apply ProductEquivWitness.RunsToEquiv.exact
    (ProductGapExpander.Nonempty.runSteps leftFuel
      (headSymbol :: rest))
  exact gapNonempty_run_lift left right
    (ProductGapExpander.Nonempty.run_exact
      right headSymbol rest leftFuel rightFuel)

theorem nonemptyGapTarget_eq_tailSource
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    gapNonemptyConfig (left := left) (right := right)
        (ProductGapExpander.Nonempty.callerTailTargetConfig
          right headSymbol rest leftFuel rightFuel) =
      finishConfig
        (ProductFinish.materializerConfig
          (InitialMaterializer.FullMaterializerMachine.tailConfig left
            (ProductCallerTail.NonemptyCallerTail.sourceConfig
              (MachineDescription.encodeNat leftFuel).reverse
              headSymbol rest
              (ProductInput.pairCallerData right
                (headSymbol :: rest) rightFuel)))) := by
  rfl

def nonemptyTailSchedule
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (machine left right)
      (gapNonemptyConfig
        (ProductGapExpander.Nonempty.callerTailTargetConfig
          right headSymbol rest leftFuel rightFuel))
      (finishConfig
        (ProductCallerAwareFinish.nonemptySource
          left right headSymbol rest leftFuel rightFuel)) := by
  let callerData := ProductInput.pairCallerData right
    (headSymbol :: rest) rightFuel
  let tailSource := ProductCallerTail.NonemptyCallerTail.sourceConfig
    (MachineDescription.encodeNat leftFuel).reverse
    headSymbol rest callerData
  let tailTarget := ProductCallerTail.NonemptyCallerTail.haltConfig
    headSymbol (MachineDescription.encodeNat leftFuel).reverse
    rest.reverse callerData
  have htail :
      InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact?
          (rest.length + 4) tailSource = some tailTarget := by
    exact ProductCallerTail.NonemptyCallerTail.run_exact
      (MachineDescription.encodeNat leftFuel).reverse
      headSymbol rest callerData
  have hmaterializer :=
    InitialMaterializer.FullMaterializerMachine.tail_run_of_eq_some
    left (rest.length + 4) tailSource tailTarget htail
  have hfinish := ProductFinish.materializer_run_lift
    left right hmaterializer
  have hmaster := finish_run_lift left right hfinish
  apply ProductEquivWitness.RunsToEquiv.exact (rest.length + 4)
  rw [nonemptyGapTarget_eq_tailSource]
  simpa [callerData, tailSource, tailTarget,
    ProductCallerAwareFinish.nonemptySource,
    ProductCallerAwareFinish.nonemptyCallerData] using hmaster

def nonemptyFinishSchedule
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (machine left right)
      (finishConfig
        (ProductCallerAwareFinish.nonemptySource
          left right headSymbol rest leftFuel rightFuel))
      (ProductEquivWitness.pairCanonicalTarget
        (machine left right) left right (headSymbol :: rest)
        leftFuel rightFuel) := by
  let branch := ProductCallerAwareFinish.nonempty_finish_run
    left right headSymbol rest leftFuel rightFuel
  have hlift := finish_run_lift left right branch.run_exact
  refine
    { endpoint := finishConfig branch.endpoint
      steps := branch.steps
      run_exact := hlift
      endpoint_state := ?_
      canonical_tape_equiv := branch.canonical_tape_equiv }
  have hstate := congrArg Control.finish branch.endpoint_state
  simpa [branch, ProductEquivWitness.pairCanonicalTarget,
    ProductCallerAwareFinish.nonemptyCanonicalTarget,
    finishConfig, machine,
    TuringMachine.PhaseEmbedding.liftConfig] using hstate

theorem nonemptyPostCleanupSchedule_nonempty
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (cleanupNonemptyConfig
          (ProductCleanup.DynamicRightFuel.deletedConfig
            (headSymbol :: rest) leftFuel
            (ProductCleanupShapes.nonemptyOpaqueRightCells
              right headSymbol rest rightFuel)))
        (ProductEquivWitness.pairCanonicalTarget
          (machine left right) left right (headSymbol :: rest)
          leftFuel rightFuel)) := by
  rcases nonemptyCompactorSchedule_nonempty
      left right headSymbol rest leftFuel rightFuel with ⟨compactor⟩
  exact ⟨(nonemptyPositionSchedule
      left right headSymbol rest leftFuel rightFuel).trans
    (compactor.trans
      ((nonemptyGapSchedule
        left right headSymbol rest leftFuel rightFuel).trans
        ((nonemptyTailSchedule
          left right headSymbol rest leftFuel rightFuel).trans
          (nonemptyFinishSchedule
            left right headSymbol rest leftFuel rightFuel))))⟩

theorem nonemptyCleanupSourceTape_eq_prefixShiftSource
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    (ProductCleanup.DynamicRightFuel.sourceConfig
      (headSymbol :: rest) leftFuel rightFuel
      (ProductCleanupShapes.nonemptyOpaqueRightCells
        right headSymbol rest rightFuel)).tape =
    ProductCleanupShapes.prefixShiftSourceTape
      (ProductPrefix.retainedOuterRev
        (headSymbol :: rest) leftFuel rightFuel)
      (ProductCleanupShapes.nonemptyOpaqueRightCells
        right headSymbol rest rightFuel) := by
  rw [ProductCleanupShapes.retainedOuterRev_eq_retainedRawPrefix_reverse]
  rfl

theorem nonemptyPrefixSchedule_nonempty
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (TuringMachine.initial (machine left right)
          (GeneratedCode.nestedStageCode
            (headSymbol :: rest) rightFuel leftFuel))
        (cleanupNonemptyConfig
          (ProductCleanup.DynamicRightFuel.sourceConfig
            (headSymbol :: rest) leftFuel rightFuel
            (ProductCleanupShapes.nonemptyOpaqueRightCells
              right headSymbol rest rightFuel)))) := by
  rcases ProductCleanupShapes.prefix_run_to_opaque_prefix_shift_source
      right (headSymbol :: rest) leftFuel rightFuel with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  let prefixEndpoint : Config (Control left right) :=
    finishConfig
      (ProductFinish.prefixConfig
        (ProductPrefix.materializerConfig endpoint))
  let cleanupInner : Config ProductCleanup.DynamicRightFuel.Control :=
    { state := ProductCleanup.DynamicRightFuel.machine.start
      tape := Tape.move Direction.left endpoint.tape }
  let cleanupEndpoint : Config (Control left right) :=
    cleanupNonemptyConfig cleanupInner
  have hfinish := ProductFinish.prefix_run_lift left right hrun
  have hmaster := finish_run_lift left right hfinish
  have hprefix :
      (machine left right).runConfigExact? steps
          (TuringMachine.initial (machine left right)
            (GeneratedCode.nestedStageCode
              (headSymbol :: rest) rightFuel leftFuel)) =
        some prefixEndpoint := by
    simpa [prefixEndpoint, TuringMachine.initial, machine,
      finishConfig, ProductFinish.prefixConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      ProductFinish.machine] using hmaster
  have hhandoff :
      (machine left right).runConfigExact? 1 prefixEndpoint =
        some cleanupEndpoint := by
    rcases endpoint with ⟨endpointState, endpointTape⟩
    change endpointState =
      ProductRightPrefix.rightTerminalState
        right (headSymbol :: rest) at hstate
    change endpointState = .header .halt at hstate
    subst endpointState
    simp [prefixEndpoint, cleanupEndpoint, cleanupInner,
      TuringMachine.runConfigExact?, TuringMachine.stepConfig,
      machine, transition, emptyPrefixEndpoint, nonemptyPrefixEndpoint,
      finishConfig, ProductFinish.prefixConfig,
      ProductPrefix.materializerConfig, cleanupNonemptyConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      ProductFinish.write_read_eq_self,
      ProductCleanup.DynamicRightFuel.machine]
  have hfull :
      (machine left right).runConfigExact? (steps + 1)
          (TuringMachine.initial (machine left right)
            (GeneratedCode.nestedStageCode
              (headSymbol :: rest) rightFuel leftFuel)) =
        some cleanupEndpoint := by
    rw [InitialMaterializer.ExactRun.append, hprefix]
    exact hhandoff
  refine ⟨
    { endpoint := cleanupEndpoint
      steps := steps + 1
      run_exact := hfull
      endpoint_state := ?_
      canonical_tape_equiv := ?_ }⟩
  · rfl
  · change Tape.Equiv
      (ProductCleanup.DynamicRightFuel.sourceConfig
        (headSymbol :: rest) leftFuel rightFuel
        (ProductCleanupShapes.nonemptyOpaqueRightCells
          right headSymbol rest rightFuel)).tape
      (Tape.move Direction.left endpoint.tape)
    rw [nonemptyCleanupSourceTape_eq_prefixShiftSource]
    exact htape

theorem nonemptyMasterSchedule_nonempty
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (TuringMachine.initial (machine left right)
          (GeneratedCode.nestedStageCode
            (headSymbol :: rest) rightFuel leftFuel))
        (ProductEquivWitness.pairCanonicalTarget
          (machine left right) left right (headSymbol :: rest)
          leftFuel rightFuel)) := by
  rcases nonemptyPrefixSchedule_nonempty
      left right headSymbol rest leftFuel rightFuel with ⟨prefixSchedule⟩
  rcases nonemptyCleanupSchedule_nonempty
      left right headSymbol rest leftFuel rightFuel with ⟨cleanup⟩
  rcases nonemptyPostCleanupSchedule_nonempty
      left right headSymbol rest leftFuel rightFuel with ⟨postCleanup⟩
  exact ⟨prefixSchedule.trans (cleanup.trans postCleanup)⟩

/-- Every generated product input reaches a physical endpoint equivalent to
the canonical pair target. -/
theorem runsToPairTarget
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Nonempty
      (ProductEquivWitness.RunsToEquiv (machine left right)
        (TuringMachine.initial (machine left right)
          (GeneratedCode.nestedStageCode input rightFuel leftFuel))
        (ProductEquivWitness.pairCanonicalTarget
          (machine left right) left right input leftFuel rightFuel)) := by
  cases input with
  | nil =>
      exact emptyMasterSchedule_nonempty left right leftFuel rightFuel
  | cons headSymbol rest =>
      exact nonemptyMasterSchedule_nonempty
        left right headSymbol rest leftFuel rightFuel

/-- Complete pair-prefix witnesses consumed by product composition. -/
theorem pairPrefixWitnesses
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    ProductConstruction.PairPrefixWitnesses
      (machine left right) left right := by
  intro input leftFuel rightFuel
  rcases runsToPairTarget left right input leftFuel rightFuel with ⟨schedule⟩
  refine ⟨ProductEquivWitness.pairPrefixWitness_of_runsToEquiv
    (machine left right) left right input leftFuel rightFuel
      (haltingTransitionsDisabled left right) schedule, rfl⟩

end ProductPairMaterializer
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
