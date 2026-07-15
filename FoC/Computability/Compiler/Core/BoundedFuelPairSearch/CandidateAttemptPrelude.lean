import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RawLayoutHandoff
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.DiagonalSchedule
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.FusedLayoutEmission
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SwappedLayoutEmission
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RawLayoutPreparation
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SimulatorHitExtractor

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace BoundedFuelPairSearch
namespace U12CandidateAttemptLoop

open StructuredConstructionTargets
open StructuredConstructionTargets.FusedLayoutEmission
open StructuredConstructionTargets.SwappedLayoutEmission
open StructuredConstructionTargets.RawLayoutPreparation
open StructuredConstructionTargets.FuelSimulatorCore
open StructuredConstructionTargets.FuelSimulatorCore.RawLayoutEmission

/-- The first bounded simulator consumes the actual carried emitter
representative and returns an actual representative of the semantic source
run layout. -/
theorem sourceSimulator_haltsFromTapeEquiv_carried
    {source sourceSimulator : MachineDescription}
    (hsourceSimulator :
      FixedDescriptionBoundedSimulatorEquivSpec source sourceSimulator)
    (w : Word Bool) (limit candidateFuel sourceFuel : Nat)
    (A2 : Tape Bool)
    (hA2 : Tape.Equiv A2
      (rawEmissionOutputTape source
        (CandidateInputBits w limit candidateFuel) sourceFuel)) :
    sourceSimulator.HaltsFromTapeEquiv
      (keepL.apply A2)
      (SimulatorLayout.tape
        (successOnlySourceRunLayout source w
          limit candidateFuel sourceFuel)) := by
  let L := successOnlySourceInitialLayout source w
    limit candidateFuel sourceFuel
  have hcanonical := hsourceSimulator.haltsFromTapeEquiv L
  have hcanonical' : sourceSimulator.HaltsFromTapeEquiv
      (SimulatorLayout.tape L)
      (SimulatorLayout.tape
        (successOnlySourceRunLayout source w
          limit candidateFuel sourceFuel)) := by
    simpa [FixedDescriptionBoundedSimulatorCanonicalOutputTape,
      successOnlySourceRunLayout, L, successOnlySourceInitialLayout,
      SimulatorLayout.initial] using hcanonical
  have hinput : Tape.Equiv (keepL.apply A2)
      (SimulatorLayout.tape L) := by
    change Tape.Equiv (Tape.move Direction.left A2)
      (SimulatorLayout.tape L)
    refine Tape.Equiv.trans (Tape.Equiv.move hA2 Direction.left) ?_
    rw [rawEmissionOutputTape_move_left]
    exact Tape.Equiv.refl _
  rcases hcanonical' with ⟨actual, hhalt, hactual⟩
  rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      (Tape.Equiv.symm hinput) hhalt with
    ⟨actual', hhalt', hactual'⟩
  exact ⟨actual', hhalt', Tape.Equiv.trans hactual' hactual⟩

/-- The checker bounded simulator likewise consumes its actual carried
emitter representative. -/
theorem checkerSimulator_haltsFromTapeEquiv_carried
    {recognizer checkerSimulator : MachineDescription}
    (hcheckerSimulator :
      SuccessOnlyFairBoundedWrapperSpec recognizer checkerSimulator)
    (source : MachineDescription) (w : Word Bool)
    (i : SuccessOnlyScheduleIndex) (A2 : Tape Bool)
    (hA2 : Tape.Equiv A2
      (rawEmissionOutputTape recognizer
        (SimulatorLayout.asBoolInput
          (successOnlySourceRunLayout source w
            i.limit i.candidateFuel i.sourceFuel))
        i.checkerFuel)) :
    checkerSimulator.HaltsFromTapeEquiv
      (keepL.apply A2)
      (SimulatorLayout.tape
        (successOnlyCheckerRunLayout recognizer source w
          i.limit i.candidateFuel i.sourceFuel i.checkerFuel)) := by
  let raw := SimulatorLayout.asBoolInput
    (successOnlySourceRunLayout source w
      i.limit i.candidateFuel i.sourceFuel)
  let L := successOnlyCheckerInitialLayout recognizer source w
    i.limit i.candidateFuel i.sourceFuel i.checkerFuel
  have hcanonical := hcheckerSimulator.right source w i
  have hcanonical' : checkerSimulator.HaltsFromTapeEquiv
      (SimulatorLayout.tape L)
      (SimulatorLayout.tape
        (successOnlyCheckerRunLayout recognizer source w
          i.limit i.candidateFuel i.sourceFuel i.checkerFuel)) := by
    simpa [FixedDescriptionBoundedSimulatorCanonicalOutputTape,
      successOnlyCheckerRunLayout, L, successOnlyCheckerInitialLayout,
      SimulatorLayout.initial] using hcanonical
  have hinput : Tape.Equiv (keepL.apply A2)
      (SimulatorLayout.tape L) := by
    change Tape.Equiv (Tape.move Direction.left A2)
      (SimulatorLayout.tape L)
    refine Tape.Equiv.trans (Tape.Equiv.move hA2 Direction.left) ?_
    rw [rawEmissionOutputTape_move_left]
    exact Tape.Equiv.refl _
  rcases hcanonical' with ⟨actual, hhalt, hactual⟩
  rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      (Tape.Equiv.symm hinput) hhalt with
    ⟨actual', hhalt', hactual'⟩
  exact ⟨actual', hhalt', Tape.Equiv.trans hactual' hactual⟩

/-- The total hit extractor accepts an arbitrary actual representative of the
semantic checker run. -/
theorem hitExtractor_haltsFromTapeEquiv_carried
    (L : SimulatorLayout) (Tin : Tape Bool)
    (hin : Tape.Equiv Tin (SimulatorLayout.tape L)) :
    SimulatorHitExtractorDescription.HaltsFromTapeEquiv Tin
      (SimulatorHitEmitterTargetTape L) := by
  rcases simulatorHitExtractorDescription_haltsFromTapeEquiv L with
    ⟨actual, hhalt, hactual⟩
  rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      (Tape.Equiv.symm hin) hhalt with
    ⟨actual', hhalt', hactual'⟩
  exact ⟨actual', hhalt', Tape.Equiv.trans hactual' hactual⟩

theorem candidateInputBits_exists_cons
    (w : Word Bool) (limit candidateFuel : Nat) :
    exists head : Bool, exists tail : Word Bool,
      CandidateInputBits w limit candidateFuel = head :: tail := by
  refine ⟨false, (CandidateInputBits w limit candidateFuel).tail, ?_⟩
  cases w <;> rfl

theorem simulatorLayoutAsBoolInput_exists_cons
    (L : SimulatorLayout) :
    exists head : Bool, exists tail : Word Bool,
      SimulatorLayout.asBoolInput L = head :: tail := by
  refine ⟨false, (SimulatorLayout.asBoolInput L).tail, ?_⟩
  cases L <;> rfl

theorem cursorFuelSourceTape_equiv_injective
    {m n : Nat}
    (h : Tape.Equiv (cursorFuelSourceTape m) (cursorFuelSourceTape n)) :
    m = n := by
  have hbits := Tape.Equiv.normalizedOutput_eq h
  have hencoded : encodeNat m = encodeNat n := by
    apply encodeCodeWordAsInput_injective
    simpa [cursorFuelSourceTape, tapeAtCells, Tape.normalizedOutput,
      Tape.cells, stageNatBits, List.filterMap_map, Function.comp_def]
      using hbits
  have hdecoded := congrArg decodeNat hencoded
  have hm : decodeNat (encodeNat m) =
      some (m, (show Word MachineCodeSymbol from [])) :=
    by simpa using! decodeNat_encodeNat_append m []
  have hn : decodeNat (encodeNat n) =
      some (n, (show Word MachineCodeSymbol from [])) :=
    by simpa using! decodeNat_encodeNat_append n []
  rw [hm, hn] at hdecoded
  injection hdecoded with hp
  exact congrArg Prod.fst hp

theorem normalizedOutput_input (w : Word Bool) :
    Tape.normalizedOutput (Tape.input w) = w := by
  cases w <;>
    simp [Tape.input, Tape.blank, Tape.normalizedOutput, Tape.cells,
      List.filterMap_map, Function.comp_def]

theorem persistentCursor_eq
    (w : Word Bool) (c d : SuccessOnlyDiagonalCursor)
    (T0 T1 T2 : Tape Bool)
    (hc0 : Tape.Equiv T0 (cursorFuelSourceTape c.checkerFuel))
    (hc1 : Tape.Equiv T1 (cursorFuelSourceTape c.sourceFuel))
    (hc2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w c.limit c.candidateFuel)))
    (hd0 : Tape.Equiv T0 (cursorFuelSourceTape d.checkerFuel))
    (hd1 : Tape.Equiv T1 (cursorFuelSourceTape d.sourceFuel))
    (hd2 : Tape.Equiv T2
      (Tape.input (CandidateInputBits w d.limit d.candidateFuel))) :
    c = d := by
  have hchecker : c.checkerFuel = d.checkerFuel :=
    cursorFuelSourceTape_equiv_injective
      (Tape.Equiv.trans (Tape.Equiv.symm hc0) hd0)
  have hsource : c.sourceFuel = d.sourceFuel :=
    cursorFuelSourceTape_equiv_injective
      (Tape.Equiv.trans (Tape.Equiv.symm hc1) hd1)
  have hraw : CandidateInputBits w c.limit c.candidateFuel =
      CandidateInputBits w d.limit d.candidateFuel := by
    have hout := Tape.Equiv.normalizedOutput_eq
      (Tape.Equiv.trans (Tape.Equiv.symm hc2) hd2)
    simpa [normalizedOutput_input] using hout
  have hcoords := candidateInputBits_injective hraw
  cases c
  cases d
  simp only at hchecker hsource hcoords ⊢
  simp_all

theorem diagonalAdvance_ne (cursor : SuccessOnlyDiagonalCursor) :
    cursor.advance ≠ cursor := by
  rcases cursor with ⟨limit, candidateFuel, sourceFuel, checkerFuel⟩
  simp only [SuccessOnlyDiagonalCursor.advance]
  split
  · intro h
    have := congrArg SuccessOnlyDiagonalCursor.limit h
    simp at this
    lia
  · split
    · intro h
      have := congrArg SuccessOnlyDiagonalCursor.candidateFuel h
      simp at this
      lia
    · split
      · intro h
        have := congrArg SuccessOnlyDiagonalCursor.sourceFuel h
        simp at this
        lia
      · intro h
        have := congrArg SuccessOnlyDiagonalCursor.limit h
        simp at this
        lia

/-- Constructively turn failure of a finite all-false claim into a true
Boolean witness. -/
theorem exists_true_below_of_not_all_false
    (f : Nat -> Bool) : forall steps : Nat,
    (¬ forall k : Nat, k < steps -> f k = false) ->
      exists k : Nat, k < steps ∧ f k = true := by
  intro steps
  induction steps with
  | zero =>
      intro h
      exfalso
      apply h
      intro k hk
      exact (Nat.not_lt_zero k hk).elim
  | succ steps ih =>
      intro h
      cases hlast : f steps with
      | true => exact ⟨steps, Nat.lt_succ_self steps, hlast⟩
      | false =>
          have hnotPrefix :
              ¬ forall k : Nat, k < steps -> f k = false := by
            intro hprefix
            apply h
            intro k hk
            have hle : k ≤ steps := Nat.lt_succ_iff.mp hk
            rcases Nat.lt_or_eq_of_le hle with hlt | heq
            · exact hprefix k hlt
            · subst k
              exact hlast
          rcases ih hnotPrefix with ⟨k, hk, htrue⟩
          exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self steps), htrue⟩


end U12CandidateAttemptLoop
end BoundedFuelPairSearch
end Computability
end FoC
