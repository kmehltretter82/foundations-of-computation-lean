import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageRunner.Runs
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.Runs
import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode

set_option doc.verso true

/-!
# Tuple-search exact-candidate kernel

A continuation-friendly exact-fuel probe for one generated tuple-search
candidate, with finite hit and miss exits.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.CandidateKernel

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

namespace ProbeReturn

abbrev Kernel (stateCount : Nat) :=
  ExactFuel.StrictProbe.Update.Kernel.kernel stateCount

abbrev ProbeState (stateCount : Nat) :=
  CyclicDriverIntegration.Control stateCount
    (ExactFuel.StrictProbe.Update.Kernel.Control stateCount)

abbrev probeMachine {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :=
  CyclicDriverIntegration.machine selected (Kernel stateCount)

/-- A scheduler-local return shell.  Both probe exits are active gates; the
two-step bounce makes their target tape explicit without erasing the protected
caller suffix. -/
inductive Control (stateCount : Nat) where
  | probe (inner : ProbeState stateCount)
  | hitReturn
  | missReturn
  | hit
  | miss
deriving DecidableEq

namespace Control

def elems (stateCount : Nat) : List (Control stateCount) :=
  (CyclicDriverIntegration.Control.finite stateCount
      (ExactFuel.StrictProbe.Update.Kernel.Control.finite stateCount)).elems.map
    Control.probe ++
  [.hitReturn, .missReturn, .hit, .miss]

def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control <;>
      simp [elems,
        (CyclicDriverIntegration.Control.finite stateCount
          (ExactFuel.StrictProbe.Update.Kernel.Control.finite stateCount)).complete]

end Control

def transition {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Control stateCount -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control stateCount)
  | .probe inner, read =>
      if inner = .accept then
        some (read, Direction.right, .hitReturn)
      else if inner = .reject then
        some (read, Direction.right, .missReturn)
      else
        match CyclicDriverIntegration.transition selected (Kernel stateCount)
            inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .probe target)
  | .hitReturn, read => some (read, Direction.left, .hit)
  | .missReturn, read => some (read, Direction.left, .miss)
  | .hit, _ => none
  | .miss, _ => none

def machine {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .probe (probeMachine selected).start
  halt := .hit
  transition := transition selected
  statesFinite := Control.finite stateCount

theorem machine_haltingTransitionsDisabled {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine.HaltingTransitionsDisabled (machine selected) := by
  intro read
  rfl

theorem miss_transition_none {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (read : Option MachineCodeSymbol) :
    (machine selected).transition .miss read = none := by
  rfl

def probeConfig {stateCount : Nat}
    (c : TuringMachine.Configuration MachineCodeSymbol (ProbeState stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.probe c

def hitConfig {stateCount : Nat} (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  { state := .hit, tape := T }

def missConfig {stateCount : Nat} (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  { state := .miss, tape := T }

def candidateFrame {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (inner outer selectedFuel : Nat) :
    CarriedStateFrame.LoopFrame stateCount :=
  ExactFuel.StrictProbe.StageRunner.initialFrame selected
    (GeneratedCode.nestedStageCode input inner outer) selectedFuel

def candidateTape {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) : Tape MachineCodeSymbol :=
  CyclicDriverWitnesses.canonicalTape callerData selectedFuel
    (candidateFrame selected input inner outer selectedFuel)

def candidateSource {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  probeConfig
    (CyclicRelationalContract.sourceConfig selectedFuel
      (candidateFrame selected input inner outer selectedFuel)
      (candidateTape selected callerData input inner outer selectedFuel))

theorem candidateTape_eq_canonical_input {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) :
    candidateTape selected callerData input inner outer selectedFuel =
      Tape.input
        (Frame.protectedWord
          (ExactFuel.Layout.initial selected
            (GeneratedCode.nestedStageCode input inner outer) selectedFuel)
          callerData) := by
  unfold candidateTape CyclicDriverWitnesses.canonicalTape candidateFrame
  rw [ExactFuel.StrictProbe.StageRunner.initialFrame_withFuel_physicalFrame]

theorem candidateSource_tape_eq_canonical_input {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) :
    (candidateSource selected callerData input
      inner outer selectedFuel).tape =
      Tape.input
        (Frame.protectedWord
          (ExactFuel.Layout.initial selected
            (GeneratedCode.nestedStageCode input inner outer) selectedFuel)
          callerData) := by
  exact candidateTape_eq_canonical_input selected callerData input
    inner outer selectedFuel

theorem cyclic_reject_of_not_halts {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData : Word MachineCodeSymbol) :
    forall fuel (F : CarriedStateFrame.LoopFrame stateCount)
      (T : Tape MachineCodeSymbol),
      RelationalDriverInduction.Represents callerData fuel F T ->
      ¬ TuringMachine.HaltsFromIn selected fuel
          (RelationalDriverInduction.semanticConfig F) ->
      exists endpointTape,
        TuringMachine.Computes (probeMachine selected)
          (CyclicRelationalContract.sourceConfig fuel F T)
          (CyclicRelationalContract.rejectConfig endpointTape) := by
  intro fuel
  induction fuel with
  | zero =>
      intro F T hrep hnot
      have hstate :
          (RelationalDriverInduction.semanticConfig F).state ≠
            selected.halt := by
        intro hhalt
        apply hnot
        exact TuringMachine.haltsFromIn_zero_iff.mpr hhalt
      exact CyclicDriverWitnesses.zeroReject selected
        (Kernel stateCount) callerData F T hrep hstate
  | succ fuel ih =>
      intro F T hrep hnot
      cases htransition :
          selected.transition
            (RelationalDriverInduction.semanticConfig F).state
            (Tape.read (RelationalDriverInduction.semanticConfig F).tape) with
      | none =>
          exact CyclicDriverWitnesses.succMissing selected
            (Kernel stateCount) callerData fuel F T hrep htransition
      | some action =>
          rcases action with ⟨write, direction, nextState⟩
          rcases CyclicDriverWitnesses.succPresent selected
              (Kernel stateCount) callerData
              (ExactFuel.StrictProbe.Update.Runs.selectedUpdateRuns
                selected callerData)
              fuel F T write direction nextState hrep htransition with
            ⟨T', hrep', hprefix⟩
          have hnotTail :
              ¬ TuringMachine.HaltsFromIn selected fuel
                (RelationalDriverInduction.semanticConfig
                  (CarriedStateFrame.afterSelected
                    fuel write direction nextState F)) := by
            intro htail
            apply hnot
            apply
              (TuringMachine.haltsFromIn_succ_iff_of_transition_eq_some
                htransition).mpr
            rw [RelationalDriverInduction.semanticConfig_afterSelected]
              at htail
            simpa [DriverInduction.selectedTarget] using htail
          rcases ih
              (CarriedStateFrame.afterSelected
                fuel write direction nextState F)
              T' hrep' hnotTail with ⟨endpointTape, htail⟩
          exact ⟨endpointTape,
            TuringMachine.computes_trans hprefix htail⟩
      done
  done

theorem probe_computes_lift {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    {source target :
      TuringMachine.Configuration MachineCodeSymbol (ProbeState stateCount)}
    (hrun : TuringMachine.Computes (probeMachine selected) source target) :
    TuringMachine.Computes (machine selected)
      (probeConfig source) (probeConfig target) := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes (n := steps)
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    (inner := probeMachine selected) (outer := machine selected)
    Control.probe
  · intro c d hstep
    cases c with
    | mk inner tape =>
      cases haction :
          CyclicDriverIntegration.transition selected (Kernel stateCount)
            inner (Tape.read tape) with
      | none =>
          simp [TuringMachine.stepConfig, probeMachine,
            CyclicDriverIntegration.machine, haction] at hstep
      | some action =>
          rcases action with ⟨write, direction, nextState⟩
          have hnotAccept :
              inner ≠ CyclicDriverIntegration.Control.accept := by
            intro h
            subst inner
            simp [CyclicDriverIntegration.transition] at haction
          have hnotReject :
              inner ≠ CyclicDriverIntegration.Control.reject := by
            intro h
            subst inner
            simp [CyclicDriverIntegration.transition] at haction
          simp [TuringMachine.stepConfig, probeMachine,
            CyclicDriverIntegration.machine, haction] at hstep
          cases hstep
          simp [TuringMachine.stepConfig, machine,
            TuringMachine.PhaseEmbedding.liftConfig, transition,
            hnotAccept, hnotReject, haction]
  · exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem reject_to_miss_run_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (T : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        (probeConfig (CyclicRelationalContract.rejectConfig T)) =
      some (missConfig (CyclicDriverIntegration.roundTripTape T)) := by
  have hwrite (U : Tape MachineCodeSymbol) :
      Tape.write (Tape.read U) U = U := by
    cases U
    rfl
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, probeConfig, missConfig,
    CyclicRelationalContract.rejectConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, hwrite]

theorem reject_to_miss_computes {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Computes (machine selected)
      (probeConfig (CyclicRelationalContract.rejectConfig T))
      (missConfig (CyclicDriverIntegration.roundTripTape T)) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (reject_to_miss_run_exact selected T))

/-- A canonical scheduled candidate that fails the exact selected-machine
predicate reaches a finite miss return.  The protected caller word is part of
the source frame, and the returned physical tape is stated explicitly rather
than normalized away. -/
theorem candidate_miss_of_not_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat)
    (hnot :
      ¬ TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)) :
    exists endpointTape,
      TuringMachine.Computes (machine selected)
        (candidateSource selected callerData input
          inner outer selectedFuel)
        (missConfig (CyclicDriverIntegration.roundTripTape endpointTape)) := by
  have hrep :
      RelationalDriverInduction.Represents callerData selectedFuel
        (candidateFrame selected input inner outer selectedFuel)
        (candidateTape selected callerData input inner outer selectedFuel) := by
    unfold candidateTape CyclicDriverWitnesses.canonicalTape
      RelationalDriverInduction.Represents
    exact Tape.Equiv.refl _
  have hnotSemantic :
      ¬ TuringMachine.HaltsFromIn selected selectedFuel
        (RelationalDriverInduction.semanticConfig
          (candidateFrame selected input inner outer selectedFuel)) := by
    intro hhalt
    apply hnot
    simpa [TuringMachine.HaltsOnInputIn, candidateFrame,
      ExactFuel.StrictProbe.StageRunner.initialFrame_semanticConfig]
      using hhalt
  rcases cyclic_reject_of_not_halts selected callerData selectedFuel
      (candidateFrame selected input inner outer selectedFuel)
      (candidateTape selected callerData input inner outer selectedFuel)
      hrep hnotSemantic with ⟨endpointTape, hreject⟩
  have hrejectOuter := probe_computes_lift selected hreject
  refine ⟨endpointTape, ?_⟩
  simpa [candidateSource] using
    TuringMachine.computes_trans hrejectOuter
      (reject_to_miss_computes selected endpointTape)

theorem cyclic_accept_of_halts {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep : RelationalDriverInduction.Represents callerData fuel F T)
    (hhalt : TuringMachine.HaltsFromIn selected fuel
      (RelationalDriverInduction.semanticConfig F)) :
    exists endpointTape,
      TuringMachine.Computes (probeMachine selected)
        (CyclicRelationalContract.sourceConfig fuel F T)
        (CyclicRelationalContract.acceptConfig endpointTape) := by
  let W := CyclicDriverWitnesses.runWitnesses selected
    (Kernel stateCount) callerData
    (ExactFuel.StrictProbe.Update.Runs.selectedUpdateRuns
      selected callerData)
  have hsource : TuringMachine.HaltsFrom (probeMachine selected)
      (CyclicRelationalContract.sourceConfig fuel F T) := by
    exact (CyclicRelationalContract.haltsFrom_source_iff selected
      (Kernel stateCount) callerData W fuel F T hrep).mpr hhalt
  rcases hsource with ⟨endpoint, hrun, hhalted⟩
  cases endpoint with
  | mk endpointState endpointTape =>
      have hstate : endpointState =
          CyclicDriverIntegration.Control.accept := by
        simpa [TuringMachine.Halted, probeMachine,
          CyclicDriverIntegration.machine] using hhalted
      subst endpointState
      exact ⟨endpointTape, by
        simpa [CyclicRelationalContract.acceptConfig] using hrun⟩

theorem accept_to_hit_run_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (T : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        (probeConfig (CyclicRelationalContract.acceptConfig T)) =
      some (hitConfig (CyclicDriverIntegration.roundTripTape T)) := by
  have hwrite (U : Tape MachineCodeSymbol) :
      Tape.write (Tape.read U) U = U := by
    cases U
    rfl
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, probeConfig, hitConfig,
    CyclicRelationalContract.acceptConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, hwrite]

theorem accept_to_hit_computes {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Computes (machine selected)
      (probeConfig (CyclicRelationalContract.acceptConfig T))
      (hitConfig (CyclicDriverIntegration.roundTripTape T)) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (accept_to_hit_run_exact selected T))

theorem candidate_hit_of_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat)
    (hhalt : TuringMachine.HaltsOnInputIn selected selectedFuel
      (GeneratedCode.nestedStageCode input inner outer)) :
    exists endpointTape,
      TuringMachine.Computes (machine selected)
        (candidateSource selected callerData input
          inner outer selectedFuel)
        (hitConfig (CyclicDriverIntegration.roundTripTape endpointTape)) := by
  have hrep :
      RelationalDriverInduction.Represents callerData selectedFuel
        (candidateFrame selected input inner outer selectedFuel)
        (candidateTape selected callerData input inner outer selectedFuel) := by
    unfold candidateTape CyclicDriverWitnesses.canonicalTape
      RelationalDriverInduction.Represents
    exact Tape.Equiv.refl _
  have hsemantic :
      TuringMachine.HaltsFromIn selected selectedFuel
        (RelationalDriverInduction.semanticConfig
          (candidateFrame selected input inner outer selectedFuel)) := by
    simpa [TuringMachine.HaltsOnInputIn, candidateFrame,
      ExactFuel.StrictProbe.StageRunner.initialFrame_semanticConfig]
      using hhalt
  rcases cyclic_accept_of_halts selected callerData selectedFuel
      (candidateFrame selected input inner outer selectedFuel)
      (candidateTape selected callerData input inner outer selectedFuel)
      hrep hsemantic with ⟨endpointTape, haccept⟩
  have hacceptOuter := probe_computes_lift selected haccept
  refine ⟨endpointTape, ?_⟩
  simpa [candidateSource] using
    TuringMachine.computes_trans hacceptOuter
      (accept_to_hit_computes selected endpointTape)

theorem candidate_hit_iff_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) :
    (exists endpointTape,
      TuringMachine.Computes (machine selected)
        (candidateSource selected callerData input
          inner outer selectedFuel)
        (hitConfig (CyclicDriverIntegration.roundTripTape endpointTape))) ↔
      TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer) := by
  constructor
  · intro hhit
    by_cases hexact :
        TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)
    · exact hexact
    · exfalso
      rcases candidate_miss_of_not_exact selected callerData input
          inner outer selectedFuel hexact with ⟨missBase, hmiss⟩
      have hmissNotHalted :
          ¬ TuringMachine.Halted (machine selected)
            (missConfig (CyclicDriverIntegration.roundTripTape missBase)) := by
        simp [TuringMachine.Halted, machine, missConfig]
      have hmissStuck : forall next,
          ¬ TuringMachine.Step (machine selected)
            (missConfig (CyclicDriverIntegration.roundTripTape missBase))
            next := by
        intro next
        exact TuringMachine.not_step_of_transition_eq_none
          (miss_transition_none selected
            (Tape.read (CyclicDriverIntegration.roundTripTape missBase)))
      have hnotSource :=
        TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          (machine_haltingTransitionsDisabled selected)
          hmiss hmissNotHalted hmissStuck
      apply hnotSource
      rcases hhit with ⟨hitBase, hhit⟩
      exact ⟨hitConfig (CyclicDriverIntegration.roundTripTape hitBase),
        hhit, rfl⟩
  · intro hhalt
    exact candidate_hit_of_exact selected callerData input
      inner outer selectedFuel hhalt

def ExactCandidateSpec {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) : Prop :=
  ((exists endpointTape,
      TuringMachine.Computes (machine selected)
        (candidateSource selected callerData input
          inner outer selectedFuel)
        (hitConfig (CyclicDriverIntegration.roundTripTape endpointTape))) ↔
      TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer)) ∧
    (¬ TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer) →
      exists endpointTape,
        TuringMachine.Computes (machine selected)
          (candidateSource selected callerData input
            inner outer selectedFuel)
          (missConfig
            (CyclicDriverIntegration.roundTripTape endpointTape)))

theorem exactCandidateSpec {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) :
    ExactCandidateSpec selected callerData input
      inner outer selectedFuel := by
  exact ⟨candidate_hit_iff_exact selected callerData input
      inner outer selectedFuel,
    candidate_miss_of_not_exact selected callerData input
      inner outer selectedFuel⟩

theorem candidate_total {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) :
    (TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer) ∧
      exists endpointTape,
        TuringMachine.Computes (machine selected)
          (candidateSource selected callerData input
            inner outer selectedFuel)
          (hitConfig
            (CyclicDriverIntegration.roundTripTape endpointTape))) ∨
    (¬ TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer) ∧
      exists endpointTape,
        TuringMachine.Computes (machine selected)
          (candidateSource selected callerData input
            inner outer selectedFuel)
          (missConfig
            (CyclicDriverIntegration.roundTripTape endpointTape))) := by
  by_cases hhalt : TuringMachine.HaltsOnInputIn selected selectedFuel
      (GeneratedCode.nestedStageCode input inner outer)
  · exact Or.inl ⟨hhalt,
      candidate_hit_of_exact selected callerData input
        inner outer selectedFuel hhalt⟩
  · exact Or.inr ⟨hhalt,
      candidate_miss_of_not_exact selected callerData input
        inner outer selectedFuel hhalt⟩


end ProbeReturn

end FoC.Computability.FiniteRecognizer.TupleSearch.CandidateKernel
