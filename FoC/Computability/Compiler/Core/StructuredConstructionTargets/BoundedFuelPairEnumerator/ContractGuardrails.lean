import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppendGenerated
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutput
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.TwoStageEndpoints

set_option doc.verso true

/-!
# Bounded fuel-pair enumerator contract guardrails

The former all-witness exact endpoint contract for the bounded fuel-pair
enumerator is inconsistent for an arbitrary subroutine-ready runner.  This
module records the generic target-functionality forced by determinism and a
small concrete runner whose two witnesses share one public input but demand
different targets.

The obsolete construction module has been retired.  The small historical
contract shapes needed to state the refutation live here with the guardrail.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open StructuredConstructionTargets
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace BoundedFuelPairEnumeratorContractGuardrails

/-- Minimal witness shape from the retired all-result enumerator contract. -/
structure HistoricalWitness (runner : MachineDescription) where
  input : Word Bool
  searchLimit : Nat
  limit : Nat
  fuel : Nat
  result : Word Bool
  limit_le_searchLimit : limit <= searchLimit
  fuel_le_searchLimit : fuel <= searchLimit
  runner_halts :
    runner.HaltsWithOutput
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          input limit fuel))
      (encodeCodeWordAsInput (encodeBoolWord result))

/-- Conflicting public target from the retired all-result contract. -/
def historicalRightShiftedOutputTape
    {runner : MachineDescription} (i : HistoricalWitness runner) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input (encodeCodeWordAsInput (encodeBoolWord i.result)))

/-- Minimal historical public spec retained solely for the refutation. -/
def HistoricalRightShiftedSpec
    (runner enumerator : MachineDescription) : Prop :=
  enumerator.SubroutineReady ∧
    (forall i : HistoricalWitness runner,
      enumerator.HaltsWithTape i.input
        (historicalRightShiftedOutputTape i)) ∧
      forall w : Word Bool, forall T : Tape Bool,
        enumerator.HaltsWithTape w T ->
          exists i : HistoricalWitness runner,
            w = i.input ∧ T = historicalRightShiftedOutputTape i

/-- Retired construction quantifier, localized with its checked guardrail. -/
def HistoricalRightShiftedSpecConstruction : Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      exists enumerator : MachineDescription,
        HistoricalRightShiftedSpec runner enumerator

/-- Public syntax map from the retired all-witness enumerator contract. -/
def boundedFuelPairEnumeratorStructuredInputBits
    (w : Word Bool) : Word Bool :=
  w

/-- Logical input tape from the retired all-witness enumerator contract. -/
def boundedFuelPairEnumeratorStructuredInputTape
    {runner : MachineDescription}
    (i : HistoricalWitness runner) : Tape Bool :=
  Tape.input (boundedFuelPairEnumeratorStructuredInputBits i.input)

/-- Shared initialized tape from the retired all-witness contract. -/
def boundedFuelPairEnumeratorStructuredInitializedTape
    (w : Word Bool) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (Tape.input (boundedFuelPairEnumeratorStructuredInputBits w))
    Tape.blank

/-- Conflicting exact target from the retired all-witness contract. -/
def boundedFuelPairEnumeratorStructuredLoweredTape
    {runner : MachineDescription}
    (i : HistoricalWitness runner) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (boundedFuelPairEnumeratorStructuredInputTape i)
    Tape.blank
    (historicalRightShiftedOutputTape i)

/-- Historical false exact semantic-core construction, retained only so the
checked impossibility theorem continues to state the rejected contract. -/
def BoundedFuelPairEnumeratorStructuredExactSemanticCoreConstruction
    (runner : MachineDescription) : Prop :=
  Structured3EndpointExactSemanticCoreConstruction
    (fun i : HistoricalWitness runner => i.input)
    boundedFuelPairEnumeratorStructuredInitializedTape
    boundedFuelPairEnumeratorStructuredLoweredTape
    historicalRightShiftedOutputTape
    boundedFuelPairEnumeratorStructuredInputTape
    (fun _i : HistoricalWitness runner => Tape.blank)

/--
An exact semantic core has a functional target on every fiber of its public
syntax map.  Thus two semantic witnesses with the same public input cannot
demand different exact lowered tapes.
-/
theorem exactSemanticCoreSpec_lowered_eq_of_syntax_eq
    {σ ι : Type}
    {syntaxOf : ι -> σ}
    {initialized : σ -> Tape Bool}
    {lowered : ι -> Tape Bool}
    {core : MachineDescription}
    (hspec :
      Structured3EndpointExactSemanticCoreSpec
        syntaxOf initialized lowered core)
    (hhaltFree : core.HaltTransitionFree)
    {i j : ι}
    (hsyntax : syntaxOf i = syntaxOf j) :
    lowered i = lowered j := by
  exact
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hhaltFree (hspec.forward i)
      (by simpa [hsyntax] using hspec.forward j)

/-- Construction-level form of exact target functionality. -/
theorem exactSemanticCoreConstruction_lowered_eq_of_syntax_eq
    {σ ι : Type}
    {syntaxOf : ι -> σ}
    {initialized : σ -> Tape Bool}
    {lowered output tape0 tape1 : ι -> Tape Bool}
    (hcore :
      Structured3EndpointExactSemanticCoreConstruction
        syntaxOf initialized lowered output tape0 tape1)
    {i j : ι}
    (hsyntax : syntaxOf i = syntaxOf j) :
    lowered i = lowered j := by
  rcases hcore with ⟨C⟩
  have hready :=
    lowerStructured3Description_subroutineReady
      C.coreWellFormed C.coreSupportsRows
  exact
    exactSemanticCoreSpec_lowered_eq_of_syntax_eq
      C.semanticCore hready.right hsyntax

/--
The current public right-shifted spec likewise forces a functional target on
every fiber of the witness input field.
-/
theorem rightShiftedSpec_target_eq_of_input_eq
    {runner enumerator : MachineDescription}
    (hspec : HistoricalRightShiftedSpec runner enumerator)
    {i j : HistoricalWitness runner}
    (hinput : i.input = j.input) :
    historicalRightShiftedOutputTape i =
      historicalRightShiftedOutputTape j := by
  exact
    MachineDescription.haltsWithTape_functional_of_haltTransitionFree
      hspec.left.right (hspec.right.left i)
      (by simpa [hinput] using hspec.right.left j)

/-- State update for the finite probe runner used below. -/
def probeNext (state : Nat) (bit : Bool) : Nat :=
  if state = 7 then
    if bit then 8 else 20
  else
    (state + 1) % 32

/-- Optional output emitted by the finite probe runner. -/
def probeEmit (state : Nat) (_bit : Bool) : Option Bool :=
  match state with
  | 0 => some false
  | 1 => some false
  | 2 => some true
  | 3 => some false
  | 4 => some false
  | 5 => some false
  | 6 => some true
  | 7 => some true
  | 8 => some false
  | 9 => some true
  | 10 => some false
  | 11 => some true
  | 20 => some false
  | 21 => some true
  | 22 => some true
  | 23 => some false
  | _ => none

/--
A 32-state optional-output transducer that accepts the two concrete candidate
inputs used in the collision below and emits different encoded Boolean words.
-/
def probeRunner : MachineDescription :=
  generatedStatefulOptionAppendDescription 32 0 probeNext probeEmit []

/-- The probe update remains inside its finite state block. -/
theorem probeNext_lt
    (state : Nat) (bit : Bool) (_hstate : state < 32) :
    probeNext state bit < 32 := by
  unfold probeNext
  split
  · cases bit <;> decide
  · exact Nat.mod_lt _ (by decide)

/-- The finite probe is well formed and halt-transition-free. -/
theorem probeRunner_subroutineReady : probeRunner.SubroutineReady := by
  exact
    generatedStatefulOptionAppendDescription_subroutineReady
      32 0 probeNext probeEmit [] (by decide) probeNext_lt

/-- Encoded runner input for public word {lit}`[]` and candidate pair
{lit}`(0, 0)`. -/
def probeInputFalse : Word Bool :=
  encodeCodeWordAsInput
    (PairedRecognizerDovetailControllerStageAttemptFuelInputCode [] 0 0)

/-- Encoded runner input for public word {lit}`[]` and candidate pair
{lit}`(1, 0)`. -/
def probeInputTrue : Word Bool :=
  encodeCodeWordAsInput
    (PairedRecognizerDovetailControllerStageAttemptFuelInputCode [] 1 0)

/-- Encoded singleton-false runner output. -/
def probeOutputFalse : Word Bool :=
  encodeCodeWordAsInput (encodeBoolWord [false])

/-- Encoded singleton-true runner output. -/
def probeOutputTrue : Word Bool :=
  encodeCodeWordAsInput (encodeBoolWord [true])

/-- The probe maps its first candidate input to encoded {lit}`[false]`. -/
theorem probeOutputFrom_false :
    statefulOptionOutputFrom probeNext probeEmit 0 probeInputFalse =
      probeOutputFalse := by
  rfl

/-- The probe maps its second candidate input to encoded {lit}`[true]`. -/
theorem probeOutputFrom_true :
    statefulOptionOutputFrom probeNext probeEmit 0 probeInputTrue =
      probeOutputTrue := by
  rfl

private theorem fstSourceTape_zero_equiv_input (input : Word Bool) :
    Tape.Equiv (FSTSourceTape input 0) (Tape.input input) := by
  cases input <;>
    simp [FSTSourceTape, tapeAtCells, Tape.input, Tape.blank, Tape.Equiv,
      Tape.dropTrailingNone]
  rw [dropTrailingNone_append_none]

private theorem probeRunner_haltsWithOutput_of_eval
    (input output : Word Bool)
    (heval :
      statefulOptionOutputFrom probeNext probeEmit 0 input = output) :
    probeRunner.HaltsWithOutput input output := by
  have hcompiled :=
    statefulOptionAppendTransducer_compiledByGeneratedDescription
      32 0 probeNext probeEmit [] (by decide) probeNext_lt
  have hruns :=
    statefulOptionAppendTransducer_runsToOutput
      32 0 probeNext probeEmit [] input (by decide) probeNext_lt
  have hrunsOutput :
      (statefulOptionAppendTransducer
          32 0 probeNext probeEmit []).RunsToOutput input output := by
    simpa [heval] using hruns
  have hfrom :
      probeRunner.HaltsFromTape
        (FSTSourceTape input 0)
        (FSTStatefulOptionAppendTargetTape
          probeNext probeEmit 0 input [] 0) := by
    simpa [probeRunner] using
      hcompiled.right input output 0 hrunsOutput
  have hfromOutput :
      probeRunner.HaltsFromTapeWithOutput
        (FSTSourceTape input 0) output := by
    simpa [FSTStatefulOptionAppendTargetTape_normalizedOutput, heval] using
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape hfrom
  have hcanonical :
      probeRunner.HaltsFromTapeWithOutput (Tape.input input) output :=
    MachineDescription.haltsFromTapeWithOutput_of_input_equiv
      (fstSourceTape_zero_equiv_input input) hfromOutput
  rcases hcanonical with ⟨n, hn⟩
  exact
    ⟨n, by
      simpa [HaltsWithOutputIn, HaltsFromTapeWithOutputIn,
        MachineDescription.initial] using hn⟩

/-- The probe runner halts on the first candidate with encoded false output. -/
theorem probeRunner_halts_false :
    probeRunner.HaltsWithOutput probeInputFalse probeOutputFalse :=
  probeRunner_haltsWithOutput_of_eval
    probeInputFalse probeOutputFalse probeOutputFrom_false

/-- The probe runner halts on the second candidate with encoded true output. -/
theorem probeRunner_halts_true :
    probeRunner.HaltsWithOutput probeInputTrue probeOutputTrue :=
  probeRunner_haltsWithOutput_of_eval
    probeInputTrue probeOutputTrue probeOutputFrom_true

/-- Witness with public input {lit}`[]`, pair {lit}`(0, 0)`, and result
{lit}`[false]`. -/
def falseWitness :
    HistoricalWitness probeRunner where
  input := []
  searchLimit := 0
  limit := 0
  fuel := 0
  result := [false]
  limit_le_searchLimit := by decide
  fuel_le_searchLimit := by decide
  runner_halts := by
    simpa [probeInputFalse, probeOutputFalse] using
      probeRunner_halts_false

/-- Witness with public input {lit}`[]`, pair {lit}`(1, 0)`, and result
{lit}`[true]`. -/
def trueWitness :
    HistoricalWitness probeRunner where
  input := []
  searchLimit := 1
  limit := 1
  fuel := 0
  result := [true]
  limit_le_searchLimit := by decide
  fuel_le_searchLimit := by decide
  runner_halts := by
    simpa [probeInputTrue, probeOutputTrue] using
      probeRunner_halts_true

/-- The two witnesses demand different exact structured-core targets. -/
theorem loweredTape_ne :
    boundedFuelPairEnumeratorStructuredLoweredTape falseWitness ≠
      boundedFuelPairEnumeratorStructuredLoweredTape trueWitness := by
  decide

/-- The two witnesses demand different public right-shifted targets. -/
theorem rightShiftedOutputTape_ne :
    historicalRightShiftedOutputTape falseWitness ≠
      historicalRightShiftedOutputTape trueWitness := by
  decide

/--
The current exact semantic-core construction is impossible even for the
subroutine-ready finite probe runner.
-/
theorem currentExactSemanticCoreConstruction_impossible :
    ¬ BoundedFuelPairEnumeratorStructuredExactSemanticCoreConstruction
      probeRunner := by
  intro hcore
  apply loweredTape_ne
  exact
    exactSemanticCoreConstruction_lowered_eq_of_syntax_eq
      hcore (by rfl)

/--
The current public right-shifted construction is impossible for the same
subroutine-ready finite probe runner.
-/
theorem currentRightShiftedSpecConstruction_impossible :
    ¬ HistoricalRightShiftedSpecConstruction := by
  intro hconstruction
  rcases hconstruction probeRunner probeRunner_subroutineReady with
    ⟨enumerator, hspec⟩
  apply rightShiftedOutputTape_ne
  exact rightShiftedSpec_target_eq_of_input_eq hspec (by rfl)

#print axioms currentExactSemanticCoreConstruction_impossible
#print axioms currentRightShiftedSpecConstruction_impossible

end BoundedFuelPairEnumeratorContractGuardrails

end Computability
end FoC
