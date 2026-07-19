import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.ShapeClosed
import FoC.Computability.Compiler.Dovetail.Scanner.TokenAligned

set_option doc.verso true

/-!
# Word-start simulator-layout recognizer

The token-alignment pre-scanner followed by the checked simulator-layout
scanner recognizes exactly the encoded simulator-layout words from ordinary
word starts.  Forward runs land on a tape equivalent to the canonical
one-cell-right handoff, and any halting run from any word start certifies
membership in the encoded family.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace CanonicalLayouts
namespace SimulatorLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.SeqComposition
open DovetailLayoutScanner

private abbrev CWA := CodeWordAlignedPreScannerDescription
private abbrev CSL := CheckedSimulatorLayoutScannerDescription

def SimulatorLayoutWordStartRecognizerDescription : MachineDescription :=
  seqSubroutine
    CodeWordAlignedPreScannerDescription
    CheckedSimulatorLayoutScannerDescription
    Direction.left

private abbrev REC := SimulatorLayoutWordStartRecognizerDescription

theorem simulatorLayoutWordStartRecognizerDescription_subroutineReady :
    REC.SubroutineReady :=
  seqSubroutine_subroutineReady
    codeWordAlignedPreScannerDescription_subroutineReady
    checkedSimulatorLayoutScannerDescription_subroutineReady

/-- Public input bits of the simulator-layout family. -/
def simulatorLayoutInputBits (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput (SimulatorLayout.encode L)

theorem simulatorLayoutInputBits_eq_fieldBits
    (L : SimulatorLayout) :
    simulatorLayoutInputBits L = simulatorLayoutFieldBits L [] := by
  have h := simulatorLayoutFieldBits_eq_encodeAppend L []
  simpa [simulatorLayoutInputBits, SimulatorLayout.encode,
    encodeCodeWordAsInput] using h

/-- The window-padded input tape is equivalent to the ordinary input tape. -/
theorem paddedStartTape_equiv_input (w : Word Bool) :
    Tape.Equiv
      (tapeAtCells [none] (List.append (w.map some) [none]))
      (Tape.input w) := by
  cases w with
  | nil =>
      refine ⟨rfl, rfl, ?_⟩
      rfl
  | cons b rest =>
      refine ⟨rfl, rfl, ?_⟩
      simpa [tapeAtCells, Tape.input] using
        dropTrailingNone_append_none (rest.map some)

/--
Forward behavior of the word-start recognizer on canonical family inputs:
it halts exactly at the checked handoff tape.
-/
theorem simulatorLayoutWordStartRecognizerDescription_forward
    (L : SimulatorLayout) :
    REC.HaltsFromTape
      (Tape.input (simulatorLayoutInputBits L))
      (checkedSimulatorHandoffTape L) := by
  have hconsCode :
      exists rest : Word MachineCodeSymbol,
        SimulatorLayout.encode L = MachineCodeSymbol.header :: rest := by
    cases L
    exact ⟨_, rfl⟩
  rcases hconsCode with ⟨restCode, hcode⟩
  have hpre :
      CWA.HaltsFromTape
        (Tape.input (simulatorLayoutInputBits L))
        (codeWordAlignedHandoffTape (simulatorLayoutInputBits L)) := by
    rw [show simulatorLayoutInputBits L =
        encodeCodeWordAsInput
          (MachineCodeSymbol.header :: restCode) by
      rw [simulatorLayoutInputBits, hcode]]
    exact
      codeWordAlignedPreScannerDescription_haltsFromTape
        MachineCodeSymbol.header restCode
  rcases runConfig_eq_halt_of_haltsFromTape hpre with ⟨nA, hArun⟩
  rcases
      DovetailLayoutScanner.encodeCodeWordAsInput_cons_bits
        MachineCodeSymbol.header restCode with
    ⟨b0, bitsTail, hbitsCons⟩
  have hbitsShape :
      simulatorLayoutInputBits L = b0 :: bitsTail := by
    rw [simulatorLayoutInputBits, hcode]
    exact hbitsCons
  have hmoveLeft :
      Tape.move Direction.left
          (codeWordAlignedHandoffTape (simulatorLayoutInputBits L)) =
        checkedSimulatorPaddedStartTape L := by
    rw [hbitsShape, move_left_codeWordAlignedHandoffTape_cons]
    rw [checkedSimulatorPaddedStartTape,
      ← simulatorLayoutInputBits_eq_fieldBits, hbitsShape]
  have hBReach :
      exists nB : Nat,
        CSL.runConfig nB
            { state := CSL.start
              tape :=
                Tape.move Direction.left
                  (codeWordAlignedHandoffTape
                    (simulatorLayoutInputBits L)) } =
          { state := CSL.halt
            tape := checkedSimulatorHandoffTape L } := by
    rw [hmoveLeft]
    exact run_checkedSimulatorLayoutScanner_padded_to_checkedHandoff L
  rcases
      seqSubroutine_runConfig_exists
        (A := CWA) (B := CSL) (handoffMove := Direction.left)
        codeWordAlignedPreScannerDescription_subroutineReady
        checkedSimulatorLayoutScannerDescription_subroutineReady
        hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_, ?_⟩
  · simpa [SimulatorLayoutWordStartRecognizerDescription] using
      congrArg Configuration.state hsteps
  · simpa [SimulatorLayoutWordStartRecognizerDescription] using
      congrArg Configuration.tape hsteps

/--
Word-start closedness of the recognizer: a halting run from any word start
certifies that the word encodes a simulator layout, and the final tape is
equivalent to that layout's checked handoff.
-/
theorem simulatorLayoutWordStartRecognizerDescription_closed
    {w : Word Bool} {T : Tape Bool}
    (h : REC.HaltsFromTape (Tape.input w) T) :
    exists L : SimulatorLayout,
      w = simulatorLayoutInputBits L ∧
        Tape.Equiv T (checkedSimulatorHandoffTape L) := by
  rcases
      seqSubroutine_haltsFromTape_inv
        (A := CWA) (B := CSL) (handoffMove := Direction.left)
        codeWordAlignedPreScannerDescription_subroutineReady
        checkedSimulatorLayoutScannerDescription_subroutineReady
        (by
          simpa [SimulatorLayoutWordStartRecognizerDescription] using h) with
    ⟨Tpre, hpre, nB, hcslRun⟩
  rcases codeWordAlignedPreScannerDescription_haltsFromTape_inv hpre with
    ⟨symbol, restCode, hw, hTpre⟩
  rcases
      DovetailLayoutScanner.encodeCodeWordAsInput_cons_bits
        symbol restCode with
    ⟨b0, bitsTail, hbitsCons⟩
  have hwCons : w = b0 :: bitsTail := by
    rw [hw]
    exact hbitsCons
  have hmoveLeft :
      Tape.move Direction.left Tpre =
        tapeAtCells [none] (List.append (w.map some) [none]) := by
    rw [hTpre, hwCons, move_left_codeWordAlignedHandoffTape_cons]
  have hcslFrom :
      CSL.HaltsFromTape
        (tapeAtCells [none] (List.append (w.map some) [none])) T := by
    refine ⟨nB, ?_, ?_⟩
    · rw [← hmoveLeft]
      simpa using congrArg Configuration.state hcslRun
    · rw [← hmoveLeft]
      simpa using congrArg Configuration.tape hcslRun
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := CSL)
        (Tin := tapeAtCells [none] (List.append (w.map some) [none]))
        (Tin' := Tape.input w)
        (Tout := T)
        (paddedStartTape_equiv_input w)
        hcslFrom with
    ⟨Tclean, hcleanRun, hTclean⟩
  have hcleanWith :
      CSL.HaltsWithTape w Tclean := by
    rcases hcleanRun with ⟨n, hn⟩
    exact
      ⟨n, by
        simpa [HaltsWithTapeIn, HaltsFromTapeIn, initial] using hn⟩
  have hcleanWithCode :
      CSL.HaltsWithTape (encodeCodeWordAsInput (symbol :: restCode))
        Tclean := by
    rw [← hw]
    exact hcleanWith
  rcases
      checkedSimulatorLayoutScannerDescription_haltsWithTape_decodeComplete_inv
        hcleanWithCode with
    ⟨L, hdecode⟩
  have hcodeEq :
      symbol :: restCode = SimulatorLayout.encode L :=
    SimulatorLayout.decodeComplete_eq_some_encode hdecode
  have hwL : w = simulatorLayoutInputBits L := by
    rw [hw, hcodeEq]
    rfl
  refine ⟨L, hwL, ?_⟩
  -- Pin the clean halting tape via the transported forward run.
  have hpaddedForward :=
    run_checkedSimulatorLayoutScanner_padded_to_checkedHandoff L
  have hpaddedFrom :
      CSL.HaltsFromTape
        (checkedSimulatorPaddedStartTape L)
        (checkedSimulatorHandoffTape L) := by
    rcases hpaddedForward with ⟨n, hn⟩
    refine ⟨n, ?_, ?_⟩
    · simpa using congrArg Configuration.state hn
    · simpa using congrArg Configuration.tape hn
  have hpaddedEquivInput :
      Tape.Equiv
        (checkedSimulatorPaddedStartTape L)
        (Tape.input w) := by
    have hstart :
        checkedSimulatorPaddedStartTape L =
          tapeAtCells [none] (List.append (w.map some) [none]) := by
      rw [checkedSimulatorPaddedStartTape,
        ← simulatorLayoutInputBits_eq_fieldBits, ← hwL]
    rw [hstart]
    exact paddedStartTape_equiv_input w
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := CSL)
        (Tin := checkedSimulatorPaddedStartTape L)
        (Tin' := Tape.input w)
        (Tout := checkedSimulatorHandoffTape L)
        hpaddedEquivInput
        hpaddedFrom with
    ⟨Tclean', hcleanRun', hTclean'⟩
  have hsame : Tclean = Tclean' :=
    haltsFromTape_functional_of_haltTransitionFree
      (seqSubroutine_haltTransitionFree
        markFirstTransitionBitDescription_subroutineReady
        (seqSubroutine_subroutineReady
          markedSimulatorLayoutBodyScannerDescription_subroutineReady
          returnToFirstMarkerDescription_subroutineReady))
      hcleanRun hcleanRun'
  exact
    Tape.Equiv.trans
      (Tape.Equiv.symm hTclean)
      (by
        rw [hsame]
        exact hTclean')

end SimulatorLayoutScanner
end CanonicalLayouts
end EncRewriters

end Computability
end FoC
