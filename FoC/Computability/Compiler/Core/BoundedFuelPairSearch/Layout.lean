import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SearchSemantics
import FoC.Computability.Compiler.Structured.Lowering.Layout

set_option doc.verso true

/-!
# Physical layouts for bounded fuel-pair search

This module fixes the semantic boundary between candidate enumeration and the
fixed-description bounded simulator.  The encoded {lit}`candidateFuel` is part
of the supplied runner's input.  The distinct {lit}`scheduleBound` is stored in
the simulator layout's stage field and controls how many runner steps are
executed.

No transition table is defined here.  The exact code words, simulator layouts,
and phase invariant below are the targets that the table implementation must
preserve.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace BoundedFuelPairSearch

/-!
## Candidate code and raw bits
-/

/-- The complete code-word input supplied to the candidate runner. -/
def CandidateCode
    (w : Word Bool) (limit candidateFuel : Nat) :
    Word MachineCodeSymbol :=
  PairedRecognizerDovetailControllerStageAttemptFuelInputCode
    w limit candidateFuel

/-- Exact physical Boolean bits supplied to the candidate runner. -/
def CandidateInputBits
    (w : Word Bool) (limit candidateFuel : Nat) : Word Bool :=
  encodeCodeWordAsInput (CandidateCode w limit candidateFuel)

theorem candidateCode_eq_stageInputCodeAppend
    (w : Word Bool) (limit candidateFuel : Nat) :
    CandidateCode w limit candidateFuel =
      DovetailLayout.stageInputCodeAppend w limit
        (encodeNatAppend candidateFuel []) := by
  rfl

theorem decodeCandidateInputBits
    (w : Word Bool) (limit candidateFuel : Nat) :
    decodeCodeWordAsInput (CandidateInputBits w limit candidateFuel) =
      some (CandidateCode w limit candidateFuel) := by
  exact decodeCodeWordAsInput_encodeCodeWordAsInput _

theorem decodeCandidateCode_stageInput
    (w : Word Bool) (limit candidateFuel : Nat) :
    DovetailLayout.decodeStageInput
        (CandidateCode w limit candidateFuel) =
      some ((w, limit), encodeNatAppend candidateFuel []) := by
  exact DovetailLayout.decodeStageInput_stageInputCodeAppend
    w limit (encodeNatAppend candidateFuel [])

theorem decodeCandidateFuelSuffix
    (candidateFuel : Nat) :
    decodeNat (encodeNatAppend candidateFuel []) =
      some (candidateFuel, []) := by
  exact decodeNat_encodeNatAppend candidateFuel []

theorem candidateInputBits_injective
    {w₁ w₂ : Word Bool}
    {limit₁ limit₂ candidateFuel₁ candidateFuel₂ : Nat}
    (h :
      CandidateInputBits w₁ limit₁ candidateFuel₁ =
        CandidateInputBits w₂ limit₂ candidateFuel₂) :
    w₁ = w₂ ∧ limit₁ = limit₂ ∧
      candidateFuel₁ = candidateFuel₂ := by
  apply
    pairedRecognizerDovetailControllerStageAttemptFuelInputCode_injective
  exact encodeCodeWordAsInput_injective h

/-!
## Schedule indices
-/

/-- One candidate in the finite square tested at a schedule bound. -/
structure ScheduleIndex where
  scheduleBound : Nat
  limit : Nat
  candidateFuel : Nat
  limit_le : limit ≤ scheduleBound
  candidateFuel_le : candidateFuel ≤ scheduleBound

namespace ScheduleIndex

def pair (i : ScheduleIndex) : Nat × Nat :=
  (i.limit, i.candidateFuel)

theorem pair_mem_schedule (i : ScheduleIndex) :
    i.pair ∈
      pairedRecognizerDovetailControllerStageAttemptFuelPairSchedule
        i.scheduleBound := by
  exact
    mem_pairedRecognizerDovetailControllerStageAttemptFuelPairSchedule_iff.mpr
      ⟨i.limit_le, i.candidateFuel_le⟩

end ScheduleIndex

/-!
## Counter-field serialization
-/

/-- Self-delimiting counter fields kept on logical tape 1. -/
def CounterCode (i : ScheduleIndex) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    encodeNatAppend i.scheduleBound
      (encodeNatAppend i.limit
        (encodeNatAppend i.candidateFuel []))

/-- Parse the complete schedule/limit/candidate-fuel counter block. -/
def decodeCounterCode
    (code : Word MachineCodeSymbol) : Option (Nat × Nat × Nat) :=
  match code with
  | MachineCodeSymbol.header :: rest =>
      match decodeNat rest with
      | none => none
      | some (scheduleBound, rest) =>
          match decodeNat rest with
          | none => none
          | some (limit, rest) =>
              match decodeNat rest with
              | some (candidateFuel, []) =>
                  some (scheduleBound, limit, candidateFuel)
              | _ => none
  | _ => none

/-- Exact Boolean encoding stored on logical tape 1. -/
def CounterBits (i : ScheduleIndex) : Word Bool :=
  encodeCodeWordAsInput (CounterCode i)

theorem decodeCounterCode_encode (i : ScheduleIndex) :
    decodeCounterCode (CounterCode i) =
      some (i.scheduleBound, i.limit, i.candidateFuel) := by
  simp [decodeCounterCode, CounterCode, decodeNat_encodeNatAppend]

theorem decodeCounterBits (i : ScheduleIndex) :
    decodeCodeWordAsInput (CounterBits i) = some (CounterCode i) := by
  exact decodeCodeWordAsInput_encodeCodeWordAsInput _

/-!
## Candidate simulator layouts
-/

/-- Canonical simulator input for one scheduled candidate. -/
def CandidateInitialLayout
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) : SimulatorLayout :=
  SimulatorLayout.initial runner
    (CandidateInputBits w i.limit i.candidateFuel)
    i.scheduleBound

/-- Canonical simulator result after the scheduled number of runner steps. -/
def CandidateRunLayout
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) : SimulatorLayout :=
  SimulatorLayout.run runner i.scheduleBound
    (CandidateInitialLayout runner w i)

@[simp] theorem candidateInitialLayout_input
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (CandidateInitialLayout runner w i).input =
      CandidateInputBits w i.limit i.candidateFuel := by
  rfl

@[simp] theorem candidateInitialLayout_stage
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (CandidateInitialLayout runner w i).stage = i.scheduleBound := by
  rfl

@[simp] theorem candidateInitialLayout_config
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (CandidateInitialLayout runner w i).config =
      runner.initial (CandidateInputBits w i.limit i.candidateFuel) := by
  rfl

@[simp] theorem candidateInitialLayout_hit
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (CandidateInitialLayout runner w i).hit = false := by
  rfl

@[simp] theorem candidateRunLayout_input
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (CandidateRunLayout runner w i).input =
      CandidateInputBits w i.limit i.candidateFuel := by
  rfl

@[simp] theorem candidateRunLayout_stage
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (CandidateRunLayout runner w i).stage = i.scheduleBound := by
  rfl

@[simp] theorem candidateRunLayout_config
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (CandidateRunLayout runner w i).config =
      runner.runConfig i.scheduleBound
        (runner.initial
          (CandidateInputBits w i.limit i.candidateFuel)) := by
  rfl

theorem candidateRunLayout_hit
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (CandidateRunLayout runner w i).hit =
      SimulatorLayout.hitsFromConfigByBool runner
        (runner.initial
          (CandidateInputBits w i.limit i.candidateFuel))
        i.scheduleBound := by
  simp [CandidateRunLayout, CandidateInitialLayout, SimulatorLayout.run,
    SimulatorLayout.initial]

theorem decodeCandidateInitialLayout_encode
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    SimulatorLayout.decodeComplete
        (SimulatorLayout.encode (CandidateInitialLayout runner w i)) =
      some (CandidateInitialLayout runner w i) := by
  exact SimulatorLayout.decodeComplete_encode _

theorem decodeCandidateRunLayout_encode
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    SimulatorLayout.decodeComplete
        (SimulatorLayout.encode (CandidateRunLayout runner w i)) =
      some (CandidateRunLayout runner w i) := by
  exact SimulatorLayout.decodeComplete_encode _

theorem candidateRunLayout_haltsWithOutputIn_iff
    (runner : MachineDescription) (w out : Word Bool)
    (i : ScheduleIndex) :
    ((CandidateRunLayout runner w i).config.state = runner.halt ∧
        Tape.normalizedOutput
            (CandidateRunLayout runner w i).config.tape = out) <->
      runner.HaltsWithOutputIn i.scheduleBound
        (CandidateInputBits w i.limit i.candidateFuel) out := by
  simp [CandidateRunLayout, CandidateInitialLayout,
    MachineDescription.HaltsWithOutputIn, SimulatorLayout.run,
    SimulatorLayout.initial]

/-- The fixed-Boolean validator seam after one bounded simulator run. -/
theorem candidateRunLayout_fixedBoolSuccess_iff
    (runner : MachineDescription) (w : Word Bool) (b : Bool)
    (i : ScheduleIndex) :
    ((CandidateRunLayout runner w i).config.state = runner.halt ∧
        Tape.normalizedOutput
            (CandidateRunLayout runner w i).config.tape =
          encodeCodeWordAsInput (encodeBoolWord [b])) <->
      runner.HaltsWithOutputIn i.scheduleBound
        (CandidateInputBits w i.limit i.candidateFuel)
        (encodeCodeWordAsInput (encodeBoolWord [b])) := by
  exact candidateRunLayout_haltsWithOutputIn_iff
    runner w (encodeCodeWordAsInput (encodeBoolWord [b])) i

/-!
## Serialized one-tape simulator boundary
-/

/-- The two stable boundaries of one bounded-simulator invocation. -/
inductive SimulatorPhase where
  | ready
  | ran
deriving Repr, DecidableEq

/-- Exact semantic layout represented at a serialized simulator boundary. -/
def SimulatorPhase.layout
    (phase : SimulatorPhase)
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) : SimulatorLayout :=
  match phase with
  | .ready => CandidateInitialLayout runner w i
  | .ran => CandidateRunLayout runner w i

/-- Boolean code-word representation consumed and produced by the #18 kernel. -/
def SerializedPhaseCode
    (phase : SimulatorPhase)
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) : Word MachineCodeSymbol :=
  SimulatorLayout.encode (phase.layout runner w i)

/-- Raw Boolean representation consumed and produced by the #18 machine. -/
def SerializedPhaseBits
    (phase : SimulatorPhase)
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) : Word Bool :=
  encodeCodeWordAsInput (SerializedPhaseCode phase runner w i)

/-- Exact physical one-tape invariant at a bounded-simulator boundary. -/
def SerializedLayoutInvariant
    (phase : SimulatorPhase)
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) (bits : Word Bool) : Prop :=
  bits = SerializedPhaseBits phase runner w i

theorem decodeSerializedPhaseBits
    (phase : SimulatorPhase)
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    decodeCodeWordAsInput
        (SerializedPhaseBits phase runner w i) =
      some (SimulatorLayout.encode (phase.layout runner w i)) := by
  exact decodeCodeWordAsInput_encodeCodeWordAsInput _

@[simp] theorem simulatorPhase_layout_input
    (phase : SimulatorPhase)
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (phase.layout runner w i).input =
      CandidateInputBits w i.limit i.candidateFuel := by
  cases phase <;> rfl

@[simp] theorem simulatorPhase_layout_stage
    (phase : SimulatorPhase)
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (phase.layout runner w i).stage = i.scheduleBound := by
  cases phase <;> rfl

theorem serializedReadyBits_eq_fixedSimulatorInput
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    SerializedPhaseBits .ready runner w i =
      FixedDescriptionBoundedSimulatorInput
        (CandidateInitialLayout runner w i) := by
  rfl

theorem serializedRanBits_eq_fixedSimulatorOutput
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    SerializedPhaseBits .ran runner w i =
      FixedDescriptionBoundedSimulatorOutput runner
        (CandidateInitialLayout runner w i) := by
  rfl

theorem fixedSimulatorCode_transitions_serializedPhase
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    (FixedDescriptionBoundedSimulatorCode runner).transform
        (SerializedPhaseCode .ready runner w i) =
      some (SerializedPhaseCode .ran runner w i) := by
  exact
    fixedDescriptionBoundedSimulatorCode_encode runner
      (CandidateInitialLayout runner w i)

theorem fixedSimulatorCode_transitions_serializedBits
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    Option.map encodeCodeWordAsInput
        ((FixedDescriptionBoundedSimulatorCode runner).transform
          (SerializedPhaseCode .ready runner w i)) =
      some (SerializedPhaseBits .ran runner w i) := by
  rw [fixedSimulatorCode_transitions_serializedPhase]
  rfl

/-!
## Three-logical-tape phase invariant
-/

/-- Schedule coordinate together with its bounded-simulator boundary phase. -/
structure PhaseIndex where
  schedule : ScheduleIndex
  simulatorPhase : SimulatorPhase

/-- Tape 0 keeps the public input at its canonical home position. -/
def PublicInputTape (w : Word Bool) : Tape Bool :=
  Tape.input w

/-- Tape 1 contains the exact self-delimiting counter fields. -/
def CounterTape (i : ScheduleIndex) : Tape Bool :=
  Tape.input (CounterBits i)

/-- Tape 2 contains the serialized simulator layout for this phase. -/
def SimulatorTape
    (runner : MachineDescription) (w : Word Bool)
    (i : PhaseIndex) : Tape Bool :=
  Tape.input
    (SerializedPhaseBits i.simulatorPhase runner w i.schedule)

/-- Exact guarded physical encoding of the three logical phase tapes. -/
def PhysicalPhaseTape
    (runner : MachineDescription) (w : Word Bool)
    (i : PhaseIndex) : Tape Bool :=
  CommonGround.FiniteTransducers.Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
      (PublicInputTape w)
      (CounterTape i.schedule)
      (SimulatorTape runner w i)

/-- Strong physical-layout invariant used at every #18 call boundary. -/
def PhysicalLayoutInvariant
    (runner : MachineDescription) (w : Word Bool)
    (i : PhaseIndex) (physical : Tape Bool) : Prop :=
  physical = PhysicalPhaseTape runner w i

theorem publicInputTape_normalizedOutput (w : Word Bool) :
    Tape.normalizedOutput (PublicInputTape w) = w := by
  simpa [PublicInputTape, Tape.output] using
    Tape.normalizedOutput_output w

theorem counterTape_normalizedOutput (i : ScheduleIndex) :
    Tape.normalizedOutput (CounterTape i) = CounterBits i := by
  simpa [CounterTape, Tape.output] using
    Tape.normalizedOutput_output (CounterBits i)

theorem simulatorTape_normalizedOutput
    (runner : MachineDescription) (w : Word Bool)
    (i : PhaseIndex) :
    Tape.normalizedOutput (SimulatorTape runner w i) =
      SerializedPhaseBits i.simulatorPhase runner w i.schedule := by
  simpa [SimulatorTape, Tape.output] using
    Tape.normalizedOutput_output
      (SerializedPhaseBits i.simulatorPhase runner w i.schedule)

/-- Moving from {lit}`ready` to {lit}`ran` changes only logical tape 2. -/
theorem physicalPhaseTape_ready_ran_fields
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    let ready : PhaseIndex := ⟨i, .ready⟩
    let ran : PhaseIndex := ⟨i, .ran⟩
    PublicInputTape w = PublicInputTape w ∧
      CounterTape ready.schedule = CounterTape ran.schedule ∧
      (SimulatorTape runner w ready =
        Tape.input (FixedDescriptionBoundedSimulatorInput
          (CandidateInitialLayout runner w i))) ∧
      (SimulatorTape runner w ran =
        Tape.input (FixedDescriptionBoundedSimulatorOutput runner
          (CandidateInitialLayout runner w i))) := by
  simp [SimulatorTape, serializedReadyBits_eq_fixedSimulatorInput,
    serializedRanBits_eq_fixedSimulatorOutput]

end BoundedFuelPairSearch

end Computability
end FoC
