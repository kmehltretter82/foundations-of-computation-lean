import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.Assembly

/-! Tape-2 projection from a logically padded nonempty output word. -/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace Tape2Projector

def paddedNonemptyWordTape (first : Bool) (rest : Word Bool) : Tape Bool :=
  tapeAtCells []
    (List.append ((first :: rest).map some) [none])

def paddedEndpointCells
    (first : Bool) (rest : Word Bool) : List (Option Bool) :=
  List.append ((first :: rest).map some) [none, none]

theorem paddedEndpointCells_filterMap
    (first : Bool) (rest : Word Bool) :
    (paddedEndpointCells first rest).filterMap (fun cell => cell) =
      first :: rest := by
  simp [paddedEndpointCells, Function.comp_def]

theorem logicalTapeBits_guard_paddedNonemptyWordTape
    (first : Bool) (rest : Word Bool) :
    logicalTapeBits
        (guardLogicalTape (paddedNonemptyWordTape first rest)) =
      List.append [false, false, true, true]
        (logicalCellListBits (paddedEndpointCells first rest)) := by
  cases first <;> cases rest <;>
    simp [paddedNonemptyWordTape, paddedEndpointCells,
      tapeAtCells, guardLogicalTape, logicalTapeBits,
      logicalCellListBits, logicalCellBits, List.append_assoc]

theorem prefixTargetTape_eq_parserPaddedSourceTape
    (tape0Bits tape1Bits : Word Bool)
    (first : Bool) (rest : Word Bool) :
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits
          (guardLogicalTape (paddedNonemptyWordTape first rest))) =
      parserExactSourceTape
        (tape0Bits.length + tape1Bits.length + 2)
        (logicalCellListBits (paddedEndpointCells first rest)) := by
  rw [logicalTapeBits_guard_paddedNonemptyWordTape]
  simp [prefixTargetTape, parserExactSourceTape]

theorem logicalCellListBits_paddedEndpointCells_ne_nil
    (first : Bool) (rest : Word Bool) :
    logicalCellListBits (paddedEndpointCells first rest) ≠ [] := by
  cases first <;> cases rest <;>
    simp [paddedEndpointCells, logicalCellListBits, logicalCellBits]

theorem parserDescription_haltsFromTape_exact_remaining
    (padding : Nat) (remaining : Word Bool)
    (hremaining : remaining ≠ []) :
    parserDescription.HaltsFromTape
      (parserExactSourceTape padding remaining)
      (parserTargetTape [false, false] (padding + 3) remaining) := by
  cases h : remaining with
  | nil =>
      exact False.elim (hremaining h)
  | cons first rest =>
      refine ⟨2 * padding + 2 * (first :: rest).length + 14, ?_⟩
      have hrun := parserDescription_run_exact padding first
        (show Word Bool from rest)
      constructor
      · simpa [h] using congrArg (fun c => c.state) hrun
      · simpa [h] using congrArg (fun c => c.tape) hrun

private theorem paddedCanonicalHandoff_equiv (T : Tape Bool) :
    Tape.Equiv T
      (Tape.move Direction.left (Tape.move Direction.right T)) := by
  cases T with
  | mk left head right =>
      cases right <;> cases head <;>
        simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight,
          Tape.dropTrailingNone]

private theorem paddedHaltsFromTapeEquiv_of_equiv_input
    {D : MachineDescription} {Tin Tin' Tout : Tape Bool}
    (hin : Tape.Equiv Tin Tin')
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeEquiv Tin' Tout := by
  rcases h with ⟨actual, hactual, hequiv⟩
  rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      (D := D) (Tin := Tin) (Tin' := Tin') (Tout := actual)
      hin hactual with
    ⟨actual', hactual', hequiv'⟩
  exact ⟨actual', hactual', Tape.Equiv.trans hequiv' hequiv⟩

private theorem paddedCanonicalSeqDescription_haltsFromTapeEquiv_sameTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAhalts : A.HaltsFromTapeEquiv Tin Tmid)
    (hBhalts : B.HaltsFromTapeEquiv Tmid Tout) :
    (canonicalSeqDescription A B).HaltsFromTapeEquiv Tin Tout := by
  let Tnext := Tape.move Direction.left (Tape.move Direction.right Tmid)
  have hBnext : B.HaltsFromTapeEquiv Tnext Tout :=
    paddedHaltsFromTapeEquiv_of_equiv_input
      (paddedCanonicalHandoff_equiv Tmid) hBhalts
  exact
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
      hA hB hAhalts rfl hBnext

theorem endpointTape2ProjectorDescription_haltsFromTapeEquiv_padded
    (T0 T1 : Tape Bool) (first : Bool) (rest : Word Bool) :
    endpointTape2ProjectorDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1
        (paddedNonemptyWordTape first rest))
      (Tape.input (first :: rest)) := by
  let tape0Bits := logicalTapeBits (guardLogicalTape T0)
  let tape1Bits := logicalTapeBits (guardLogicalTape T1)
  let padding := tape0Bits.length + tape1Bits.length + 2
  let cells := paddedEndpointCells first rest
  have hprefix :=
    prefixEraserDescription_haltsFrom_encodedGuardedStructured3Tapes
      T0 T1 (paddedNonemptyWordTape first rest)
  have htarget := prefixTargetTape_eq_parserPaddedSourceTape
    tape0Bits tape1Bits first rest
  change
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits
          (guardLogicalTape (paddedNonemptyWordTape first rest))) =
      parserExactSourceTape padding (logicalCellListBits cells) at htarget
  rw [htarget] at hprefix
  have hparser := parserDescription_haltsFromTape_exact_remaining
    padding (logicalCellListBits cells)
    (logicalCellListBits_paddedEndpointCells_ne_nil first rest)
  have hprefixParser :
      prefixParserDescription.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1
          (paddedNonemptyWordTape first rest))
        (parserTargetTape [false, false] (padding + 3)
          (logicalCellListBits cells)) :=
    paddedCanonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixEraserDescription_subroutineReady
      parserDescription_subroutineReady hprefix.toEquiv hparser.toEquiv
  have hdecoder :=
    decoderDescription_haltsFromTape false [false]
      (padding + 3) cells
  have hdecoder' :
      decoderDescription.HaltsFromTape
        (parserTargetTape [false, false] (padding + 3)
          (logicalCellListBits cells))
        (decoderHaltTape
          (List.append [false, false] (first :: rest))
          (decoderFinalGap (padding + 3) cells)) := by
    simpa [parserTargetTape, decoderSourceTape, cells,
      paddedEndpointCells_filterMap, decodedLogicalCells] using hdecoder
  have hprefixParserDecoder :
      prefixParserDecoderDescription.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1
          (paddedNonemptyWordTape first rest))
        (decoderHaltTape
          (List.append [false, false] (first :: rest))
          (decoderFinalGap (padding + 3) cells)) :=
    paddedCanonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixParserDescription_subroutineReady
      decoderDescription_subroutineReady
      hprefixParser hdecoder'.toEquiv
  have hfinalizer :=
    finalizerDescription_haltsFromTapeEquiv_exact (first :: rest)
      (decoderFinalGap (padding + 3) cells)
  exact
    paddedCanonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixParserDecoderDescription_subroutineReady
      finalizerDescription_subroutineReady
      hprefixParserDecoder hfinalizer

/-- A right-shifted nonempty word with arbitrary invisible far-right logical
blank padding. -/
def rightPaddedShiftedNonemptyWordTape
    (first : Bool) (rest : Word Bool) (padding : Nat) : Tape Bool :=
  match rest with
  | [] =>
      { left := [some first]
        head := none
        right := List.replicate padding none }
  | second :: tail =>
      { left := [some first]
        head := some second
        right := List.append (tail.map some)
          (List.replicate padding none) }

private def rightPaddedShiftedEndpointCells
    (rest : Word Bool) (padding : Nat) : List (Option Bool) :=
  match rest with
  | [] => none :: List.append (List.replicate padding none) [none]
  | first :: tail =>
      List.append ((first :: tail).map some)
        (List.append (List.replicate padding none) [none])

private def rightPaddedShiftedEndpointBits
    (rest : Word Bool) (padding : Nat) : Word Bool :=
  logicalCellListBits (rightPaddedShiftedEndpointCells rest padding)

private theorem rightPaddedShiftedEndpointCells_filterMap
    (rest : Word Bool) (padding : Nat) :
    (rightPaddedShiftedEndpointCells rest padding).filterMap
        (fun cell => cell) = rest := by
  cases rest <;>
    simp [rightPaddedShiftedEndpointCells, Function.comp_def]

private theorem rightPaddedShiftedEndpointBits_ne_nil
    (rest : Word Bool) (padding : Nat) :
    rightPaddedShiftedEndpointBits rest padding ≠ [] := by
  cases rest with
  | nil =>
      simp [rightPaddedShiftedEndpointBits,
        rightPaddedShiftedEndpointCells, logicalCellListBits,
        logicalCellBits]
  | cons first tail =>
      cases first <;>
        simp [rightPaddedShiftedEndpointBits,
          rightPaddedShiftedEndpointCells, logicalCellListBits,
          logicalCellBits]

private theorem logicalTapeBits_guard_rightPaddedShiftedNonemptyWordTape
    (first : Bool) (rest : Word Bool) (padding : Nat) :
    logicalTapeBits
        (guardLogicalTape
          (rightPaddedShiftedNonemptyWordTape first rest padding)) =
      List.append [false, false]
        (List.append (logicalCellBits (some first))
          (List.append [true, true]
            (rightPaddedShiftedEndpointBits rest padding))) := by
  cases first <;> cases rest <;>
    simp [rightPaddedShiftedNonemptyWordTape,
      rightPaddedShiftedEndpointBits,
      rightPaddedShiftedEndpointCells, logicalTapeBits,
      guardLogicalTape, logicalCellListBits, logicalCellBits,
      List.append_assoc]

private theorem prefixTargetTape_eq_parserRightPaddedSourceTape
    (tape0Bits tape1Bits : Word Bool)
    (first : Bool) (rest : Word Bool) (logicalPadding : Nat) :
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits
          (guardLogicalTape
            (rightPaddedShiftedNonemptyWordTape
              first rest logicalPadding))) =
      parserRightSourceTape
        (tape0Bits.length + tape1Bits.length + 2)
        first (rightPaddedShiftedEndpointBits rest logicalPadding) := by
  rw [logicalTapeBits_guard_rightPaddedShiftedNonemptyWordTape]
  simp [prefixTargetTape, parserRightSourceTape,
    List.map_append, List.append_assoc]

private theorem parserDescription_haltsFromTape_right_remaining
    (padding : Nat) (outputFirst : Bool) (remaining : Word Bool)
    (hremaining : remaining ≠ []) :
    parserDescription.HaltsFromTape
      (parserRightSourceTape padding outputFirst remaining)
      (parserTargetTape [false, true, outputFirst] (padding + 4)
        remaining) := by
  cases hremainingEq : remaining with
  | nil => exact False.elim (hremaining hremainingEq)
  | cons first rest =>
      refine
        ⟨2 * padding + 2 * (first :: rest).length + 20, ?_⟩
      have hrun := parserDescription_run_right padding outputFirst first
        (show Word Bool from rest)
      constructor
      · simpa [hremainingEq] using congrArg (fun c => c.state) hrun
      · simpa [hremainingEq] using congrArg (fun c => c.tape) hrun

/-- The marker-preserving endpoint projector accepts arbitrary far-right
logical blank padding in the right-shifted nonempty-word position.  It returns
the ordinary right-shifted representative, up to tape equivalence, so the next
left handoff starts on the canonical input word. -/
theorem endpointTape2ProjectorDescription_haltsFromTapeEquiv_rightPadded
    (T0 T1 : Tape Bool) (first : Bool) (rest : Word Bool)
    (logicalPadding : Nat) :
    endpointTape2ProjectorDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1
        (rightPaddedShiftedNonemptyWordTape
          first rest logicalPadding))
      (Tape.move Direction.right (Tape.input (first :: rest))) := by
  let tape0Bits := logicalTapeBits (guardLogicalTape T0)
  let tape1Bits := logicalTapeBits (guardLogicalTape T1)
  let padding := tape0Bits.length + tape1Bits.length + 2
  let cells := rightPaddedShiftedEndpointCells rest logicalPadding
  let remaining := rightPaddedShiftedEndpointBits rest logicalPadding
  have hprefix :=
    prefixEraserDescription_haltsFrom_encodedGuardedStructured3Tapes
      T0 T1
        (rightPaddedShiftedNonemptyWordTape
          first rest logicalPadding)
  have htarget := prefixTargetTape_eq_parserRightPaddedSourceTape
    tape0Bits tape1Bits first rest logicalPadding
  change
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits
          (guardLogicalTape
            (rightPaddedShiftedNonemptyWordTape
              first rest logicalPadding))) =
      parserRightSourceTape padding first remaining at htarget
  rw [htarget] at hprefix
  have hparser := parserDescription_haltsFromTape_right_remaining
    padding first remaining
      (rightPaddedShiftedEndpointBits_ne_nil rest logicalPadding)
  have hprefixParser :
      prefixParserDescription.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1
          (rightPaddedShiftedNonemptyWordTape
            first rest logicalPadding))
        (parserTargetTape [false, true, first] (padding + 4)
          remaining) :=
    paddedCanonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixEraserDescription_subroutineReady
      parserDescription_subroutineReady hprefix.toEquiv hparser.toEquiv
  have hdecoded : decodedLogicalCells cells = rest := by
    exact rightPaddedShiftedEndpointCells_filterMap rest logicalPadding
  have hdecoderRaw :=
    decoderDescription_haltsFromTape false [true, first]
      (padding + 4) cells
  have hdecoder :
      decoderDescription.HaltsFromTape
        (parserTargetTape [false, true, first] (padding + 4) remaining)
        (decoderHaltTape
          (List.append [false, true] (first :: rest))
          (decoderFinalGap (padding + 4) cells)) := by
    simpa [parserTargetTape, decoderSourceTape, remaining,
      rightPaddedShiftedEndpointBits, cells, hdecoded,
      List.append_assoc] using hdecoderRaw
  have hprefixParserDecoder :
      prefixParserDecoderDescription.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1
          (rightPaddedShiftedNonemptyWordTape
            first rest logicalPadding))
        (decoderHaltTape
          (List.append [false, true] (first :: rest))
          (decoderFinalGap (padding + 4) cells)) :=
    paddedCanonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixParserDescription_subroutineReady
      decoderDescription_subroutineReady
      hprefixParser hdecoder.toEquiv
  have hfinalizer :=
    finalizerDescription_haltsFromTapeEquiv_right first rest
      (decoderFinalGap (padding + 4) cells)
  exact
    paddedCanonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixParserDecoderDescription_subroutineReady
      finalizerDescription_subroutineReady
      hprefixParserDecoder hfinalizer

end Tape2Projector
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
