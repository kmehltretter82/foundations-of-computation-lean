import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutput
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Validation
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter
import FoC.Computability.Compiler.Structured.Lowering.Composition

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace BoundedFuelPairSearch

/-- The Boolean expansion of the canonical singleton Boolean-word code. -/
def singletonBoolWordBits (b : Bool) : Word Bool :=
  [ false, false, true, false
  , false, false, true, true
  , false, true, b, !b ]

theorem encode_singleton_boolWord_eq_bits (b : Bool) :
    encodeCodeWordAsInput (encodeBoolWord [b]) =
      singletonBoolWordBits b := by
  cases b <;> rfl

/-- A smallest-purpose success-only checker for one construction-time Boolean.
It accepts exactly the twelve-bit canonical encoding and requires a blank
immediately afterward. -/
def FixedBoolWordRecognizerDescription (b : Bool) : MachineDescription where
  stateCount := 14
  start := 0
  halt := 13
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 1 (some false) (some false) Direction.right 2
    , transition 2 (some true) (some true) Direction.right 3
    , transition 3 (some false) (some false) Direction.right 4
    , transition 4 (some false) (some false) Direction.right 5
    , transition 5 (some false) (some false) Direction.right 6
    , transition 6 (some true) (some true) Direction.right 7
    , transition 7 (some true) (some true) Direction.right 8
    , transition 8 (some false) (some false) Direction.right 9
    , transition 9 (some true) (some true) Direction.right 10
    , transition 10 (some b) (some b) Direction.right 11
    , transition 11 (some (!b)) (some (!b)) Direction.right 12
    , transition 12 none none Direction.right 13 ]

theorem fixedBoolWordRecognizerDescription_subroutineReady (b : Bool) :
    (FixedBoolWordRecognizerDescription b).SubroutineReady := by
  apply machineDescription_subroutineReady_of_transition_checks
  all_goals cases b <;> decide

theorem fixedBoolWordRecognizerDescription_wellFormed (b : Bool) :
    (FixedBoolWordRecognizerDescription b).WellFormed :=
  (fixedBoolWordRecognizerDescription_subroutineReady b).left

theorem fixedBoolWordRecognizerDescription_haltTransitionFree (b : Bool) :
    (FixedBoolWordRecognizerDescription b).HaltTransitionFree :=
  (fixedBoolWordRecognizerDescription_subroutineReady b).right

theorem fixedBoolWordRecognizerDescription_accepts (b : Bool) :
    (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput (encodeBoolWord [b])) := by
  refine ⟨13, ?_⟩
  cases b <;> decide

private theorem fixedBoolWordRecognizerDescription_rejects_empty
    (b : Bool) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput (encodeBoolWord [])) := by
  rintro ⟨n, hn⟩
  apply
    (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      (fixedBoolWordRecognizerDescription_haltTransitionFree b)
      (k := 3)
      (c := (FixedBoolWordRecognizerDescription b).initial
        (encodeCodeWordAsInput (encodeBoolWord [])))
      (stuck :=
        (FixedBoolWordRecognizerDescription b).runConfig 3
          ((FixedBoolWordRecognizerDescription b).initial
            (encodeCodeWordAsInput (encodeBoolWord []))))
      rfl (by cases b <;> decide) (by cases b <;> decide))
  exact hn

private theorem fixedBoolWordRecognizerDescription_rejects_long
    (b x y : Bool) (ys : Word Bool) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput (encodeBoolWord (x :: y :: ys))) := by
  rintro ⟨n, hn⟩
  apply
    (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      (fixedBoolWordRecognizerDescription_haltTransitionFree b)
      (k := 7)
      (c := (FixedBoolWordRecognizerDescription b).initial
        (encodeCodeWordAsInput (encodeBoolWord (x :: y :: ys))))
      (stuck :=
        (FixedBoolWordRecognizerDescription b).runConfig 7
          ((FixedBoolWordRecognizerDescription b).initial
            (encodeCodeWordAsInput (encodeBoolWord (x :: y :: ys)))))
      rfl (by cases b <;> rfl)
      (by
        change 7 ≠ 13
        decide))
  exact hn

private theorem fixedBoolWordRecognizerDescription_rejects_true_for_false :
    ¬ (FixedBoolWordRecognizerDescription false).HaltsOnInput
      (encodeCodeWordAsInput (encodeBoolWord [true])) := by
  rintro ⟨n, hn⟩
  apply
    (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      (fixedBoolWordRecognizerDescription_haltTransitionFree false)
      (k := 10)
      (c := (FixedBoolWordRecognizerDescription false).initial
        (encodeCodeWordAsInput (encodeBoolWord [true])))
      (stuck :=
        (FixedBoolWordRecognizerDescription false).runConfig 10
          ((FixedBoolWordRecognizerDescription false).initial
            (encodeCodeWordAsInput (encodeBoolWord [true]))))
      rfl (by decide) (by decide))
  exact hn

private theorem fixedBoolWordRecognizerDescription_rejects_false_for_true :
    ¬ (FixedBoolWordRecognizerDescription true).HaltsOnInput
      (encodeCodeWordAsInput (encodeBoolWord [false])) := by
  rintro ⟨n, hn⟩
  apply
    (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      (fixedBoolWordRecognizerDescription_haltTransitionFree true)
      (k := 10)
      (c := (FixedBoolWordRecognizerDescription true).initial
        (encodeCodeWordAsInput (encodeBoolWord [false])))
      (stuck :=
        (FixedBoolWordRecognizerDescription true).runConfig 10
          ((FixedBoolWordRecognizerDescription true).initial
            (encodeCodeWordAsInput (encodeBoolWord [false]))))
      rfl (by decide) (by decide))
  exact hn

/-- Closed success-only behavior on the canonical Boolean-word family emitted
by the checked-in fuel-output endpoint. -/
theorem fixedBoolWordRecognizerDescription_haltsOnInput_iff
    (b : Bool) (result : Word Bool) :
    (FixedBoolWordRecognizerDescription b).HaltsOnInput
        (encodeCodeWordAsInput (encodeBoolWord result)) ↔
      result = [b] := by
  constructor
  · intro hhalt
    cases result with
    | nil =>
        exact False.elim
          (fixedBoolWordRecognizerDescription_rejects_empty b hhalt)
    | cons x rest =>
        cases rest with
        | nil =>
            cases b <;> cases x
            · rfl
            · exact False.elim
                (fixedBoolWordRecognizerDescription_rejects_true_for_false
                  hhalt)
            · exact False.elim
                (fixedBoolWordRecognizerDescription_rejects_false_for_true
                  hhalt)
            · rfl
        | cons y ys =>
            exact False.elim
              (fixedBoolWordRecognizerDescription_rejects_long
                b x y ys hhalt)
  · intro hresult
    rw [hresult]
    exact fixedBoolWordRecognizerDescription_accepts b

def fixedBoolWordRecognizerTargetTape (b : Bool) : Tape Bool :=
  ((FixedBoolWordRecognizerDescription b).runConfig 13
    ((FixedBoolWordRecognizerDescription b).initial
      (encodeCodeWordAsInput (encodeBoolWord [b])))).tape

theorem fixedBoolWordRecognizerDescription_haltsFromTape
    (b : Bool) :
    (FixedBoolWordRecognizerDescription b).HaltsFromTape
      (Tape.input (encodeCodeWordAsInput (encodeBoolWord [b])))
      (fixedBoolWordRecognizerTargetTape b) := by
  refine ⟨13, ?_⟩
  constructor
  · cases b <;> decide
  · rfl

/-- The fixed checker has no source-equivalence collision: on every tape
equivalent to a canonical encoded Boolean word, halting is still exactly
singleton equality with the construction-time Boolean. -/
theorem fixedBoolWordRecognizerDescription_haltsFromEquiv_iff
    (b : Bool) (result : Word Bool) (Tin : Tape Bool)
    (hin : Tape.Equiv Tin
      (Tape.input (encodeCodeWordAsInput (encodeBoolWord result)))) :
    (exists Tout : Tape Bool,
      (FixedBoolWordRecognizerDescription b).HaltsFromTape Tin Tout) ↔
      result = [b] := by
  constructor
  · rintro ⟨Tout, hhalt⟩
    rcases
        MachineDescription.HaltsFromTapeEquiv_of_input_equiv hin hhalt with
      ⟨Tactual, hcanonical, _hactual⟩
    apply
      (fixedBoolWordRecognizerDescription_haltsOnInput_iff b result).mp
    rcases hcanonical with ⟨n, hn⟩
    exact ⟨n, hn.left⟩
  · intro hresult
    subst result
    rcases
        MachineDescription.HaltsFromTapeEquiv_of_input_equiv
          (Tape.Equiv.symm hin)
          (fixedBoolWordRecognizerDescription_haltsFromTape b) with
      ⟨Tactual, hactual, _hTactual⟩
    exact ⟨Tactual, hactual⟩

private theorem fixedBoolWordRecognizerDescription_not_halts_of_stuck_at
    (b : Bool) (bits : Word Bool) (k : Nat)
    (hstep :
      (FixedBoolWordRecognizerDescription b).stepConfig
          ((FixedBoolWordRecognizerDescription b).runConfig k
            ((FixedBoolWordRecognizerDescription b).initial bits)) = none)
    (hstate :
      ((FixedBoolWordRecognizerDescription b).runConfig k
          ((FixedBoolWordRecognizerDescription b).initial bits)).state ≠
        (FixedBoolWordRecognizerDescription b).halt) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput bits := by
  rintro ⟨n, hn⟩
  exact
    (CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
      (fixedBoolWordRecognizerDescription_haltTransitionFree b)
      (k := k)
      (c := (FixedBoolWordRecognizerDescription b).initial bits)
      (stuck :=
        (FixedBoolWordRecognizerDescription b).runConfig k
          ((FixedBoolWordRecognizerDescription b).initial bits))
      rfl hstep hstate) hn

private theorem fixedBoolWordRecognizerDescription_rejects_empty_code
    (b : Bool) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput []) := by
  apply fixedBoolWordRecognizerDescription_not_halts_of_stuck_at b _ 0
  · cases b <;> decide
  · cases b <;> decide

private theorem fixedBoolWordRecognizerDescription_rejects_non_tick
    (b : Bool) (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (hsymbol : symbol ≠ MachineCodeSymbol.tick) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput (symbol :: rest)) := by
  apply fixedBoolWordRecognizerDescription_not_halts_of_stuck_at b _ 4
  · cases symbol with
    | tick => exact (hsymbol rfl).elim
    | header | transition | done | blank | zero | one | moveLeft | moveRight =>
        cases b <;> rfl
  · cases symbol with
    | tick => exact (hsymbol rfl).elim
    | header | transition =>
        cases b <;> change 2 ≠ 13 <;> decide
    | done =>
        cases b <;> change 3 ≠ 13 <;> decide
    | blank | zero | one | moveLeft =>
        cases b <;> change 1 ≠ 13 <;> decide
    | moveRight =>
        cases b <;> change 0 ≠ 13 <;> decide

private theorem fixedBoolWordRecognizerDescription_rejects_tick_only
    (b : Bool) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput [MachineCodeSymbol.tick]) := by
  apply fixedBoolWordRecognizerDescription_not_halts_of_stuck_at b _ 4
  · cases b <;> decide
  · cases b <;> decide

private theorem fixedBoolWordRecognizerDescription_rejects_non_done
    (b : Bool) (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (hsymbol : symbol ≠ MachineCodeSymbol.done) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput
        (MachineCodeSymbol.tick :: symbol :: rest)) := by
  apply fixedBoolWordRecognizerDescription_not_halts_of_stuck_at b _ 8
  · cases symbol with
    | done => exact (hsymbol rfl).elim
    | header | transition | tick | blank | zero | one | moveLeft | moveRight =>
        cases b <;> rfl
  · cases symbol with
    | done => exact (hsymbol rfl).elim
    | header | transition =>
        cases b <;> change 6 ≠ 13 <;> decide
    | tick =>
        cases b <;> change 7 ≠ 13 <;> decide
    | blank | zero | one | moveLeft =>
        cases b <;> change 5 ≠ 13 <;> decide
    | moveRight =>
        cases b <;> change 4 ≠ 13 <;> decide

private theorem fixedBoolWordRecognizerDescription_rejects_tick_done_only
    (b : Bool) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput
        [MachineCodeSymbol.tick, MachineCodeSymbol.done]) := by
  apply fixedBoolWordRecognizerDescription_not_halts_of_stuck_at b _ 8
  · cases b <;> decide
  · cases b <;> decide

def singletonBoolCodeSymbol : Bool → MachineCodeSymbol
  | false => MachineCodeSymbol.zero
  | true => MachineCodeSymbol.one

theorem encodeBoolWord_singleton_eq (b : Bool) :
    encodeBoolWord [b] =
      [MachineCodeSymbol.tick, MachineCodeSymbol.done,
        singletonBoolCodeSymbol b] := by
  cases b <;> rfl

private theorem fixedBoolWordRecognizerDescription_rejects_wrong_cell
    (b : Bool) (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (hsymbol : symbol ≠ singletonBoolCodeSymbol b) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput
        (MachineCodeSymbol.tick :: MachineCodeSymbol.done ::
          symbol :: rest)) := by
  apply fixedBoolWordRecognizerDescription_not_halts_of_stuck_at b _ 12
  · cases b with
    | false =>
        cases symbol with
        | zero => exact (hsymbol rfl).elim
        | header | transition | tick | done | blank | one | moveLeft |
            moveRight => rfl
    | true =>
        cases symbol with
        | one => exact (hsymbol rfl).elim
        | header | transition | tick | done | blank | zero | moveLeft |
            moveRight => rfl
  · cases b with
    | false =>
        cases symbol with
        | zero => exact (hsymbol rfl).elim
        | header | transition | tick | done =>
            change 9 ≠ 13
            decide
        | blank =>
            change 11 ≠ 13
            decide
        | one | moveLeft =>
            change 10 ≠ 13
            decide
        | moveRight =>
            change 8 ≠ 13
            decide
    | true =>
        cases symbol with
        | one => exact (hsymbol rfl).elim
        | header | transition | tick | done =>
            change 9 ≠ 13
            decide
        | blank | zero =>
            change 10 ≠ 13
            decide
        | moveLeft =>
            change 11 ≠ 13
            decide
        | moveRight =>
            change 8 ≠ 13
            decide

private theorem fixedBoolWordRecognizerDescription_rejects_extra_symbol
    (b : Bool) (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    ¬ (FixedBoolWordRecognizerDescription b).HaltsOnInput
      (encodeCodeWordAsInput
        (MachineCodeSymbol.tick :: MachineCodeSymbol.done ::
          singletonBoolCodeSymbol b :: symbol :: rest)) := by
  apply fixedBoolWordRecognizerDescription_not_halts_of_stuck_at b _ 12
  · cases b <;> cases symbol <;> rfl
  · cases b <;> cases symbol <;> change 12 ≠ 13 <;> decide

/-- Full closed contract needed after FuelOutput: the checker accepts an
arbitrary encoded code word exactly when it is the fixed singleton Boolean
word, not merely when it happens to decode as some Boolean word. -/
theorem fixedBoolWordRecognizerDescription_haltsOnCodeWord_iff
    (b : Bool) (code : Word MachineCodeSymbol) :
    (FixedBoolWordRecognizerDescription b).HaltsOnInput
        (encodeCodeWordAsInput code) ↔
      code = encodeBoolWord [b] := by
  constructor
  · intro hhalt
    cases code with
    | nil =>
        exact False.elim
          (fixedBoolWordRecognizerDescription_rejects_empty_code b hhalt)
    | cons first rest =>
        by_cases hfirst : first = MachineCodeSymbol.tick
        · subst first
          cases rest with
          | nil =>
              exact False.elim
                (fixedBoolWordRecognizerDescription_rejects_tick_only
                  b hhalt)
          | cons second rest =>
              by_cases hsecond : second = MachineCodeSymbol.done
              · subst second
                cases rest with
                | nil =>
                    exact False.elim
                      (fixedBoolWordRecognizerDescription_rejects_tick_done_only
                        b hhalt)
                | cons third rest =>
                    by_cases hthird : third = singletonBoolCodeSymbol b
                    · subst third
                      cases rest with
                      | nil =>
                          exact (encodeBoolWord_singleton_eq b).symm
                      | cons extra tail =>
                          exact False.elim
                            (fixedBoolWordRecognizerDescription_rejects_extra_symbol
                              b extra tail hhalt)
                    · exact False.elim
                        (fixedBoolWordRecognizerDescription_rejects_wrong_cell
                          b third rest hthird hhalt)
              · exact False.elim
                  (fixedBoolWordRecognizerDescription_rejects_non_done
                    b second rest hsecond hhalt)
        · exact False.elim
            (fixedBoolWordRecognizerDescription_rejects_non_tick
              b first rest hfirst hhalt)
  · intro hcode
    rw [hcode]
    exact fixedBoolWordRecognizerDescription_accepts b

theorem fixedBoolWordRecognizerDescription_haltsFromEquivCode_iff
    (b : Bool) (code : Word MachineCodeSymbol) (Tin : Tape Bool)
    (hin : Tape.Equiv Tin
      (Tape.input (encodeCodeWordAsInput code))) :
    (exists Tout : Tape Bool,
      (FixedBoolWordRecognizerDescription b).HaltsFromTape Tin Tout) ↔
      code = encodeBoolWord [b] := by
  constructor
  · rintro ⟨Tout, hhalt⟩
    rcases
        MachineDescription.HaltsFromTapeEquiv_of_input_equiv hin hhalt with
      ⟨Tactual, hcanonical, _hactual⟩
    apply
      (fixedBoolWordRecognizerDescription_haltsOnCodeWord_iff b code).mp
    rcases hcanonical with ⟨n, hn⟩
    exact ⟨n, hn.left⟩
  · intro hcode
    subst code
    rcases
        MachineDescription.HaltsFromTapeEquiv_of_input_equiv
          (Tape.Equiv.symm hin)
          (fixedBoolWordRecognizerDescription_haltsFromTape b) with
      ⟨Tactual, hactual, _hTactual⟩
    exact ⟨Tactual, hactual⟩

/-- Concrete success-only post-simulator contract.  Unlike the total
validator seam, this recognizer is permitted to diverge on every mismatch. -/
def FixedBoolSimulatorLayoutRecognizerSpec
    (attempt recognizer : MachineDescription) (b : Bool) : Prop :=
  recognizer.SubroutineReady ∧
    forall L : SimulatorLayout,
      recognizer.HaltsOnInput (SimulatorLayout.asBoolInput L) ↔
        BoundedFuelPairSearch.CandidateLayoutSuccess attempt b L

/-- FuelOutput followed by the fixed singleton checker is a concrete
success-only recognizer for a serialized simulator result. -/
theorem fixedBoolSimulatorLayoutRecognizerConstruction
    (attempt : MachineDescription) (b : Bool) :
    exists recognizer : MachineDescription,
      FixedBoolSimulatorLayoutRecognizerSpec attempt recognizer b := by
  rcases
      StructuredConstructionTargets.fuelOutputStructuredEndpointEquivIndexedConstruction_core
        attempt with
    ⟨W, hW⟩
  let checker := FixedBoolWordRecognizerDescription b
  let recognizer :=
    canonicalPrimitiveSeqDescription W.machine checker
  refine ⟨recognizer, ?_, ?_⟩
  · exact canonicalPrimitiveSeqDescription_subroutineReady
      W.machine_subroutineReady
      (fixedBoolWordRecognizerDescription_subroutineReady b)
  · intro L
    constructor
    · intro hhalt
      rcases hhalt with ⟨n, hn⟩
      let Tout : Tape Bool :=
        (recognizer.runConfig n
          (recognizer.initial (SimulatorLayout.asBoolInput L))).tape
      have hseq :
          recognizer.HaltsFromTape (SimulatorLayout.tape L) Tout := by
        refine ⟨n, ?_⟩
        constructor
        · simpa only [MachineDescription.HaltsIn,
            MachineDescription.initial, SimulatorLayout.tape] using hn
        · rfl
      rcases
          canonicalPrimitiveSeqDescription_haltsFromTape_inv
            W.machine_subroutineReady
            (fixedBoolWordRecognizerDescription_subroutineReady b)
            (by simpa [recognizer, checker] using hseq) with
        ⟨Tmid, hFuelOutput, hchecker⟩
      rcases
          hW.closedIndex (SimulatorLayout.asBoolInput L) Tmid
            (by simpa [SimulatorLayout.tape] using hFuelOutput) with
        ⟨i, hinput, hTmid⟩
      have hencodedLayout :
          SimulatorLayout.encode L = SimulatorLayout.encode i.1.1 := by
        apply encodeCodeWordAsInput_injective
        simpa [SimulatorLayout.asBoolInput,
          StructuredConstructionTargets.fuelOutputStructuredInputBits] using
          hinput
      have hLayout : L = i.1.1 := by
        have hdecode :=
          congrArg SimulatorLayout.decodeComplete hencodedLayout
        simpa [SimulatorLayout.decodeComplete_encode] using hdecode
      have hhandoff :
          Tape.Equiv
            (canonicalPrimitiveSeqHandoffTape Tmid)
            (Tape.input
              (encodeCodeWordAsInput i.1.2)) := by
        exact Tape.Equiv.trans
          (canonicalPrimitiveSeqHandoffTape_equiv Tmid)
          (by
            simpa [
              PairedRecognizerDovetailControllerStageAttemptFuelOutputTape,
              CommonGround.CodeWordEmitters.ExactOutputTape,
              PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode]
              using hTmid)
      have houtputCode : i.1.2 = encodeBoolWord [b] :=
        (fixedBoolWordRecognizerDescription_haltsFromEquivCode_iff
          b i.1.2 (canonicalPrimitiveSeqHandoffTape Tmid) hhandoff).mp
          ⟨Tout, by
            simpa [checker, canonicalPrimitiveSeqHandoffTape] using hchecker⟩
      constructor
      · simpa [hLayout] using i.2.left
      · calc
          Tape.normalizedOutput L.config.tape =
              encodeCodeWordAsInput i.1.2 := by
            simpa [hLayout] using i.2.right
          _ = encodeCodeWordAsInput (encodeBoolWord [b]) := by
            rw [houtputCode]
    · intro hsuccess
      let i :
          PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
            attempt :=
        ⟨(L, encodeBoolWord [b]), hsuccess⟩
      have hFuelOutput :
          W.machine.HaltsFromTapeEquiv
            (SimulatorLayout.tape L)
            (Tape.input
              (encodeCodeWordAsInput (encodeBoolWord [b]))) := by
        simpa [i, SimulatorLayout.tape,
          SimulatorLayout.asBoolInput,
          StructuredConstructionTargets.fuelOutputStructuredInputBits,
          PairedRecognizerDovetailControllerStageAttemptFuelOutputTape,
          CommonGround.CodeWordEmitters.ExactOutputTape,
          PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode,
          PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode]
          using hW.forward i
      have hseq :=
        canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
          W.machine_subroutineReady
          (fixedBoolWordRecognizerDescription_subroutineReady b)
          hFuelOutput
          (fixedBoolWordRecognizerDescription_haltsFromTape b).toEquiv
      rcases hseq with ⟨Tactual, hactual, _hTactual⟩
      rcases hactual with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa only [MachineDescription.HaltsIn,
        MachineDescription.initial, recognizer, checker,
        SimulatorLayout.tape] using hn.left

/-- The fair success-only route needs independent source and checker fuels.
All four semantic coordinates are bounded by one finite square. -/
structure SuccessOnlyScheduleIndex where
  scheduleBound : Nat
  limit : Nat
  candidateFuel : Nat
  sourceFuel : Nat
  checkerFuel : Nat
  limit_le : limit ≤ scheduleBound
  candidateFuel_le : candidateFuel ≤ scheduleBound
  sourceFuel_le : sourceFuel ≤ scheduleBound
  checkerFuel_le : checkerFuel ≤ scheduleBound

def successOnlySourceInitialLayout
    (source : MachineDescription) (w : Word Bool)
    (limit candidateFuel sourceFuel : Nat) : SimulatorLayout :=
  SimulatorLayout.initial source
    (BoundedFuelPairSearch.CandidateInputBits w limit candidateFuel)
    sourceFuel

def successOnlySourceRunLayout
    (source : MachineDescription) (w : Word Bool)
    (limit candidateFuel sourceFuel : Nat) : SimulatorLayout :=
  SimulatorLayout.run source sourceFuel
    (successOnlySourceInitialLayout source w limit candidateFuel sourceFuel)

def successOnlyCheckerInitialLayout
    (recognizer source : MachineDescription) (w : Word Bool)
    (limit candidateFuel sourceFuel checkerFuel : Nat) : SimulatorLayout :=
  SimulatorLayout.initial recognizer
    (SimulatorLayout.asBoolInput
      (successOnlySourceRunLayout source w limit candidateFuel sourceFuel))
    checkerFuel

def successOnlyCheckerRunLayout
    (recognizer source : MachineDescription) (w : Word Bool)
    (limit candidateFuel sourceFuel checkerFuel : Nat) : SimulatorLayout :=
  SimulatorLayout.run recognizer checkerFuel
    (successOnlyCheckerInitialLayout recognizer source w
      limit candidateFuel sourceFuel checkerFuel)

theorem successOnlySourceRunLayout_success_iff
    (source : MachineDescription) (w : Word Bool) (b : Bool)
    (limit candidateFuel sourceFuel : Nat) :
    BoundedFuelPairSearch.CandidateLayoutSuccess source b
        (successOnlySourceRunLayout source w
          limit candidateFuel sourceFuel) ↔
      source.HaltsWithOutputIn sourceFuel
        (BoundedFuelPairSearch.CandidateInputBits w limit candidateFuel)
        (encodeCodeWordAsInput (encodeBoolWord [b])) := by
  simp [BoundedFuelPairSearch.CandidateLayoutSuccess,
    successOnlySourceRunLayout, successOnlySourceInitialLayout,
    MachineDescription.HaltsWithOutputIn,
    SimulatorLayout.run, SimulatorLayout.initial]

theorem successOnlyCheckerRunLayout_hit_eq_true_iff
    (recognizer source : MachineDescription) (w : Word Bool)
    (limit candidateFuel sourceFuel checkerFuel : Nat) :
    (successOnlyCheckerRunLayout recognizer source w
        limit candidateFuel sourceFuel checkerFuel).hit = true ↔
      exists n : Nat,
        n ≤ checkerFuel ∧
          recognizer.HaltsIn n
            (SimulatorLayout.asBoolInput
              (successOnlySourceRunLayout source w
                limit candidateFuel sourceFuel)) := by
  rw [successOnlyCheckerRunLayout,
    SimulatorLayout.run_hit_eq_true_iff]
  simp [successOnlyCheckerInitialLayout,
    SimulatorLayout.initial, MachineDescription.HaltsIn]

/-- The four-coordinate square is semantically fair: success of the bounded
outer simulation is equivalent to the original fixed-output evidence. -/
theorem evidence_iff_exists_successOnlySchedule_hit
    {source recognizer : MachineDescription} {b : Bool}
    (hrecognizer :
      FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (w : Word Bool) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
        source w b ↔
      exists i : SuccessOnlyScheduleIndex,
        (successOnlyCheckerRunLayout recognizer source w
          i.limit i.candidateFuel i.sourceFuel i.checkerFuel).hit = true := by
  constructor
  · rintro ⟨limit, candidateFuel, sourceFuel, hsource⟩
    have hsuccess :
        BoundedFuelPairSearch.CandidateLayoutSuccess source b
          (successOnlySourceRunLayout source w
            limit candidateFuel sourceFuel) :=
      (successOnlySourceRunLayout_success_iff
        source w b limit candidateFuel sourceFuel).mpr hsource
    have hrecognizerHalts :
        recognizer.HaltsOnInput
          (SimulatorLayout.asBoolInput
            (successOnlySourceRunLayout source w
              limit candidateFuel sourceFuel)) :=
      (hrecognizer.right
        (successOnlySourceRunLayout source w
          limit candidateFuel sourceFuel)).mpr hsuccess
    rcases hrecognizerHalts with ⟨checkerFuel, hchecker⟩
    let bound :=
      Nat.max (Nat.max limit candidateFuel)
        (Nat.max sourceFuel checkerFuel)
    let i : SuccessOnlyScheduleIndex :=
      { scheduleBound := bound
        limit := limit
        candidateFuel := candidateFuel
        sourceFuel := sourceFuel
        checkerFuel := checkerFuel
        limit_le := by
          exact Nat.le_trans (Nat.le_max_left _ _)
            (Nat.le_max_left _ _)
        candidateFuel_le := by
          exact Nat.le_trans (Nat.le_max_right _ _)
            (Nat.le_max_left _ _)
        sourceFuel_le := by
          exact Nat.le_trans (Nat.le_max_left _ _)
            (Nat.le_max_right _ _)
        checkerFuel_le := by
          exact Nat.le_trans (Nat.le_max_right _ _)
            (Nat.le_max_right _ _) }
    refine ⟨i, ?_⟩
    apply
      (successOnlyCheckerRunLayout_hit_eq_true_iff
        recognizer source w limit candidateFuel sourceFuel checkerFuel).mpr
    exact ⟨checkerFuel, Nat.le_refl _, hchecker⟩
  · rintro ⟨i, hhit⟩
    have hbounded :=
      (successOnlyCheckerRunLayout_hit_eq_true_iff
        recognizer source w i.limit i.candidateFuel
          i.sourceFuel i.checkerFuel).mp hhit
    rcases hbounded with ⟨n, _hn, hhalt⟩
    have hsuccess :=
      (hrecognizer.right
        (successOnlySourceRunLayout source w
          i.limit i.candidateFuel i.sourceFuel)).mp ⟨n, hhalt⟩
    have hsource :=
      (successOnlySourceRunLayout_success_iff
        source w b i.limit i.candidateFuel i.sourceFuel).mp hsuccess
    exact ⟨i.limit, i.candidateFuel, i.sourceFuel, hsource⟩

/-- Public #18 supplies the concrete bounded wrapper for the success-only
recognizer at every four-coordinate schedule point. -/
def SuccessOnlyFairBoundedWrapperSpec
    (recognizer simulator : MachineDescription) : Prop :=
  simulator.SubroutineReady ∧
    forall source : MachineDescription,
    forall w : Word Bool,
    forall i : SuccessOnlyScheduleIndex,
      simulator.HaltsFromTapeEquiv
        (SimulatorLayout.tape
          (successOnlyCheckerInitialLayout recognizer source w
            i.limit i.candidateFuel i.sourceFuel i.checkerFuel))
        (FixedDescriptionBoundedSimulatorCanonicalOutputTape recognizer
          (successOnlyCheckerInitialLayout recognizer source w
            i.limit i.candidateFuel i.sourceFuel i.checkerFuel))

theorem successOnlyFairBoundedWrapperConstruction :
    forall recognizer : MachineDescription,
      exists simulator : MachineDescription,
        SuccessOnlyFairBoundedWrapperSpec recognizer simulator := by
  intro recognizer
  rcases
      EncRewriters.BoundedLayoutRunner.fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner
        recognizer with
    ⟨simulator, hsimulator⟩
  refine ⟨simulator, hsimulator.left, ?_⟩
  intro source w i
  exact hsimulator.haltsFromTapeEquiv
    (successOnlyCheckerInitialLayout recognizer source w
      i.limit i.candidateFuel i.sourceFuel i.checkerFuel)


end BoundedFuelPairSearch

end Computability
end FoC
