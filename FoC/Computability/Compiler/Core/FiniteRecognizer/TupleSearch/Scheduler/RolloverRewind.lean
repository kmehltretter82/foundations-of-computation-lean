import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.MainRolloverRewind
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.CandidateReset

set_option doc.verso true

/-!
**Rollover rewind.** This adapter rewinds the candidate-reset rollover endpoint
to the canonical next-frame gate.
-/

namespace FoC
namespace Computability
namespace FiniteRecognizer
namespace TupleSearch
namespace Scheduler.RolloverRewind

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

def finalLeftRev
    (geometry : Scheduler.Layout.Geometry)
    (round newBound : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    Scheduler.Rollover.Locator.natPrefixRev 0
      (Scheduler.Rollover.Locator.natPrefixRev 0
        (Scheduler.CandidateReset.mainPrefixRev geometry
          (round + 1) (round + 1) newBound newBound))

theorem finalLeftRev_targetWord
    (geometry : Scheduler.Layout.Geometry)
    (round newBound : Nat) (input : Word MachineCodeSymbol) :
    Word.Concat (Word.Reverse (finalLeftRev geometry round newBound)) input =
      Scheduler.Rollover.targetWord geometry round newBound input := by
  have hnormalized :=
    Scheduler.CandidateReset.finalConfig_normalizedOutput
      geometry (round + 1) (round + 1) newBound newBound input
  rw [Scheduler.CandidateReset.pendingWord_after_rollover_eq_targetWord]
    at hnormalized
  simpa [Word.Concat, Word.Reverse,
    Scheduler.CandidateReset.finalConfig, finalLeftRev,
    Scheduler.CandidateReset.normalizedOutput_cursorTape] using
      hnormalized
  done

theorem rewind_from_finalConfig_equiv
    (geometry : Scheduler.Layout.Geometry)
    (round newBound : Nat) (input : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Scheduler.CandidateReset.finalConfig geometry
        (round + 1) (round + 1) newBound newBound input).tape
      sourceTape) :
    exists gateTape : Tape MachineCodeSymbol,
      TuringMachine.Computes RewindWord.machine
        { state := RewindWord.machine.start, tape := sourceTape }
        { state := RewindWord.machine.halt, tape := gateTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.targetWord geometry round newBound input))
        gateTape := by
  let leftRev := finalLeftRev geometry round newBound
  have hrun := Scheduler.MainRollover.ExactRewind.run_exact
    leftRev input
  have hcanonicalSource : Tape.Equiv
      (Scheduler.MainRollover.ExactRewind.startConfig
        leftRev input).tape sourceTape := by
    change Tape.Equiv
      (Scheduler.MainRollover.ExactRewind.startTape leftRev input)
      sourceTape
    exact Tape.Equiv.trans
      (by
        simpa [leftRev, finalLeftRev,
          Scheduler.CandidateReset.finalConfig] using
          (Scheduler.MainRollover.ExactRewind.startTape_equiv_cursorTape
            leftRev input))
      hsource
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hrun hcanonicalSource with
    ⟨actual, hactual, hstate, htape⟩
  rcases actual with ⟨actualState, gateTape⟩
  simp only at hstate hactual htape
  subst actualState
  refine ⟨gateTape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hactual),
    ?_⟩
  change Tape.Equiv
    (RewindWord.gateTape
      (Word.Concat (Word.Reverse leftRev) input) 0) gateTape at htape
  have hword : Word.Concat (Word.Reverse leftRev) input =
      Scheduler.Rollover.targetWord geometry round newBound input := by
    simpa [leftRev] using
      finalLeftRev_targetWord geometry round newBound input
  have hgate := RewindWord.gateTape_equiv_input
    (Word.Concat (Word.Reverse leftRev) input) 0
  rw [hword] at hgate htape
  exact Tape.Equiv.trans (Tape.Equiv.symm hgate) htape
  done

theorem rewind_from_finalConfig
    (geometry : Scheduler.Layout.Geometry)
    (round newBound : Nat) (input : Word MachineCodeSymbol) :
    exists gateTape : Tape MachineCodeSymbol,
      TuringMachine.Computes RewindWord.machine
        { state := RewindWord.machine.start
          tape :=
            (Scheduler.CandidateReset.finalConfig geometry
              (round + 1) (round + 1) newBound newBound input).tape }
        { state := RewindWord.machine.halt, tape := gateTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.targetWord geometry round newBound input))
        gateTape := by
  exact rewind_from_finalConfig_equiv geometry round newBound input
    (Scheduler.CandidateReset.finalConfig geometry
      (round + 1) (round + 1) newBound newBound input).tape
    (Tape.Equiv.refl _)

end Scheduler.RolloverRewind
end TupleSearch
end FiniteRecognizer
end Computability
end FoC
