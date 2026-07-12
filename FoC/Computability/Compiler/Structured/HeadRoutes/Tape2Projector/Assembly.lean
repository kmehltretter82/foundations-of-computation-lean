import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.FinalizerRuns

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace Tape2Projector

private theorem canonicalHandoff_equiv (T : Tape Bool) :
    Tape.Equiv T
      (Tape.move Direction.left (Tape.move Direction.right T)) := by
  cases T with
  | mk left head right =>
      cases right <;> cases head <;>
        simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight,
          Tape.dropTrailingNone]

private theorem haltsFromTapeEquiv_of_equiv_input
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

private theorem canonicalSeqDescription_haltsFromTapeEquiv_sameTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAhalts : A.HaltsFromTapeEquiv Tin Tmid)
    (hBhalts : B.HaltsFromTapeEquiv Tmid Tout) :
    (canonicalSeqDescription A B).HaltsFromTapeEquiv Tin Tout := by
  let Tnext := Tape.move Direction.left (Tape.move Direction.right Tmid)
  have hBnext : B.HaltsFromTapeEquiv Tnext Tout :=
    haltsFromTapeEquiv_of_equiv_input
      (canonicalHandoff_equiv Tmid) hBhalts
  exact
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
      hA hB hAhalts rfl hBnext

theorem remainingEndpointBits_ne_nil (bits : Word Bool) :
    remainingEndpointBits bits ≠ [] := by
  cases bits with
  | nil =>
      decide
  | cons first rest =>
      cases first <;>
        simp [remainingEndpointBits, remainingEndpointCells,
          logicalCellListBits, logicalCellBits]

theorem prefixTargetTape_eq_parserExactSourceTape
    (tape0Bits tape1Bits bits : Word Bool) :
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits (guardLogicalTape (Tape.input bits))) =
      parserExactSourceTape
        (tape0Bits.length + tape1Bits.length + 2)
        (remainingEndpointBits bits) := by
  rw [logicalTapeBits_guard_input]
  simp [prefixTargetTape, parserExactSourceTape]

theorem prefixTargetTape_eq_parserRightSourceTape
    (tape0Bits tape1Bits : Word Bool)
    (first : Bool) (rest : Word Bool) :
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits
          (guardLogicalTape
            (Tape.move Direction.right (Tape.input (first :: rest))))) =
      parserRightSourceTape
        (tape0Bits.length + tape1Bits.length + 2)
        first (remainingEndpointBits rest) := by
  rw [logicalTapeBits_guard_moveRight_input]
  simp [prefixTargetTape, parserRightSourceTape,
    List.map_append, List.append_assoc]

theorem parserDescription_haltsFromTape_exact
    (padding : Nat) (bits : Word Bool) :
    parserDescription.HaltsFromTape
      (parserExactSourceTape padding (remainingEndpointBits bits))
      (parserTargetTape [false, false] (padding + 3)
        (remainingEndpointBits bits)) := by
  cases hremaining : remainingEndpointBits bits with
  | nil =>
      exact False.elim (remainingEndpointBits_ne_nil bits hremaining)
  | cons first rest =>
      refine ⟨2 * padding + 2 * (first :: rest).length + 14, ?_⟩
      have hrun := parserDescription_run_exact padding first
        (show Word Bool from rest)
      constructor
      · simpa using congrArg (fun c => c.state) hrun
      · simpa using congrArg (fun c => c.tape) hrun

theorem parserDescription_haltsFromTape_right
    (padding : Nat) (outputFirst : Bool) (restBits : Word Bool) :
    parserDescription.HaltsFromTape
      (parserRightSourceTape padding outputFirst
        (remainingEndpointBits restBits))
      (parserTargetTape [false, true, outputFirst] (padding + 4)
        (remainingEndpointBits restBits)) := by
  cases hremaining : remainingEndpointBits restBits with
  | nil =>
      exact False.elim (remainingEndpointBits_ne_nil restBits hremaining)
  | cons first rest =>
      refine
        ⟨2 * padding + 2 * (first :: rest).length + 20, ?_⟩
      have hrun := parserDescription_run_right padding outputFirst first
        (show Word Bool from rest)
      constructor
      · simpa using congrArg (fun c => c.state) hrun
      · simpa using congrArg (fun c => c.tape) hrun

def prefixParserDescription : MachineDescription :=
  canonicalSeqDescription prefixEraserDescription parserDescription

theorem prefixParserDescription_subroutineReady :
    prefixParserDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    prefixEraserDescription_subroutineReady
    parserDescription_subroutineReady

def prefixParserDecoderDescription : MachineDescription :=
  canonicalSeqDescription prefixParserDescription decoderDescription

theorem prefixParserDecoderDescription_subroutineReady :
    prefixParserDecoderDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    prefixParserDescription_subroutineReady
    decoderDescription_subroutineReady

def endpointTape2ProjectorDescription : MachineDescription :=
  canonicalSeqDescription prefixParserDecoderDescription
    finalizerDescription

theorem endpointTape2ProjectorDescription_subroutineReady :
    endpointTape2ProjectorDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    prefixParserDecoderDescription_subroutineReady
    finalizerDescription_subroutineReady

theorem endpointTape2ProjectorDescription_haltsFromTapeEquiv_exact
    (T0 T1 : Tape Bool) (bits : Word Bool) :
    endpointTape2ProjectorDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1 (Tape.input bits))
      (Tape.input bits) := by
  let tape0Bits := logicalTapeBits (guardLogicalTape T0)
  let tape1Bits := logicalTapeBits (guardLogicalTape T1)
  let padding := tape0Bits.length + tape1Bits.length + 2
  have hprefix :=
    prefixEraserDescription_haltsFrom_encodedGuardedStructured3Tapes
      T0 T1 (Tape.input bits)
  have htarget := prefixTargetTape_eq_parserExactSourceTape
    tape0Bits tape1Bits bits
  change
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits (guardLogicalTape (Tape.input bits))) =
      parserExactSourceTape padding (remainingEndpointBits bits) at htarget
  rw [htarget] at hprefix
  have hparser := parserDescription_haltsFromTape_exact padding bits
  have hprefixParser :
      prefixParserDescription.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 (Tape.input bits))
        (parserTargetTape [false, false] (padding + 3)
          (remainingEndpointBits bits)) :=
    canonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixEraserDescription_subroutineReady
      parserDescription_subroutineReady hprefix.toEquiv hparser.toEquiv
  have hdecoder :=
    decoderDescription_haltsFrom_parserTargetTape
      false [false] bits (padding + 3)
  have hprefixParserDecoder :
      prefixParserDecoderDescription.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 (Tape.input bits))
        (decoderHaltTape (List.append [false, false] bits)
          (decoderFinalGap (padding + 3)
            (remainingEndpointCells bits))) :=
    canonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixParserDescription_subroutineReady
      decoderDescription_subroutineReady
      hprefixParser hdecoder.toEquiv
  have hfinalizer :=
    finalizerDescription_haltsFromTapeEquiv_exact bits
      (decoderFinalGap (padding + 3) (remainingEndpointCells bits))
  exact
    canonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixParserDecoderDescription_subroutineReady
      finalizerDescription_subroutineReady
      hprefixParserDecoder hfinalizer

theorem endpointTape2ProjectorDescription_haltsFromTapeEquiv_right
    (T0 T1 : Tape Bool) (first : Bool) (rest : Word Bool) :
    endpointTape2ProjectorDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1
        (Tape.move Direction.right (Tape.input (first :: rest))))
      (Tape.move Direction.right (Tape.input (first :: rest))) := by
  let tape0Bits := logicalTapeBits (guardLogicalTape T0)
  let tape1Bits := logicalTapeBits (guardLogicalTape T1)
  let padding := tape0Bits.length + tape1Bits.length + 2
  have hprefix :=
    prefixEraserDescription_haltsFrom_encodedGuardedStructured3Tapes
      T0 T1 (Tape.move Direction.right (Tape.input (first :: rest)))
  have htarget := prefixTargetTape_eq_parserRightSourceTape
    tape0Bits tape1Bits first rest
  change
    prefixTargetTape tape0Bits tape1Bits
        (logicalTapeBits
          (guardLogicalTape
            (Tape.move Direction.right (Tape.input (first :: rest))))) =
      parserRightSourceTape padding first (remainingEndpointBits rest) at htarget
  rw [htarget] at hprefix
  have hparser := parserDescription_haltsFromTape_right padding first rest
  have hprefixParser :
      prefixParserDescription.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1
          (Tape.move Direction.right (Tape.input (first :: rest))))
        (parserTargetTape [false, true, first] (padding + 4)
          (remainingEndpointBits rest)) :=
    canonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixEraserDescription_subroutineReady
      parserDescription_subroutineReady hprefix.toEquiv hparser.toEquiv
  have hdecoder :=
    decoderDescription_haltsFrom_parserTargetTape
      false [true, first] rest (padding + 4)
  have hdecoder' :
      decoderDescription.HaltsFromTape
        (parserTargetTape [false, true, first] (padding + 4)
          (remainingEndpointBits rest))
        (decoderHaltTape
          (List.append [false, true] (first :: rest))
          (decoderFinalGap (padding + 4)
            (remainingEndpointCells rest))) := by
    simpa [List.append_assoc] using hdecoder
  have hprefixParserDecoder :
      prefixParserDecoderDescription.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1
          (Tape.move Direction.right (Tape.input (first :: rest))))
        (decoderHaltTape
          (List.append [false, true] (first :: rest))
          (decoderFinalGap (padding + 4)
            (remainingEndpointCells rest))) :=
    canonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixParserDescription_subroutineReady
      decoderDescription_subroutineReady
      hprefixParser hdecoder'.toEquiv
  have hfinalizer :=
    finalizerDescription_haltsFromTapeEquiv_right first rest
      (decoderFinalGap (padding + 4) (remainingEndpointCells rest))
  exact
    canonicalSeqDescription_haltsFromTapeEquiv_sameTape
      prefixParserDecoderDescription_subroutineReady
      finalizerDescription_subroutineReady
      hprefixParserDecoder hfinalizer

theorem endpointTape2ProjectorDescription_spec :
    StructuredTape2ProjectorSpec endpointTape2ProjectorDescription := by
  constructor
  · exact endpointTape2ProjectorDescription_subroutineReady
  · intro T0 T1 T2 hendpoint
    rcases hendpoint with hExact | hRight
    · rcases hExact with ⟨bits, rfl⟩
      exact
        endpointTape2ProjectorDescription_haltsFromTapeEquiv_exact
          T0 T1 bits
    · rcases hRight with ⟨first, rest, rfl⟩
      exact
        endpointTape2ProjectorDescription_haltsFromTapeEquiv_right
          T0 T1 first rest

end Tape2Projector
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
