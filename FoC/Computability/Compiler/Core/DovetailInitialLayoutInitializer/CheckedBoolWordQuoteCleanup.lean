import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.BoolWordQuoter

set_option doc.verso true

/-!
# Checked Bool-word quote cleanup obstruction

The direct checked Bool-word quoter leaves a copied trailer after the desired
encoded Bool-word field.  An exact post-cleanup from that halted tape to a
plain input-tape target cannot exist in this tape model: machine steps do not
decrease tape context length, while deleting the copied trailer would have to
decrease it.
-/

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def checkedNonemptyBoolWordQuoteExactBits
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineCodeSymbol.header ::
      MachineDescription.encodeBoolWordAppend (b :: rest)
        (MachineDescription.encodeNatAppend stage suffix))

def checkedNonemptyBoolWordQuoteNativeHaltTape
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) : Tape Bool :=
  tapeAtCells [some false]
    (some false ::
      ((List.append
        (checkedNonemptyBoolWordQuoteDirectSourceBits b rest
          (MachineDescription.encodeNatAppend stage suffix))
        (checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits rest)).map some))

theorem checkedNonemptyBoolWordQuoteExactBits_eq
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) :
    checkedNonemptyBoolWordQuoteExactBits b rest stage suffix =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (checkedNonemptyBoolWordQuoteDirectSourceBits b rest
          (MachineDescription.encodeNatAppend stage suffix)) := by
  simp [checkedNonemptyBoolWordQuoteExactBits,
    MachineDescription.encodeCodeWordAsInput,
    checkedNonemptyBoolWordQuoteDirectSourceBits_eq]

theorem checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits_length_ge_three
    (rest : Word Bool) :
    3 ≤ (checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits rest).length := by
  unfold checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits
  unfold inputTapeRightCellsDirectCopierDoneBits
  simp [MachineDescription.encodeCodeSymbolAsInput, List.length_append]
  omega

theorem checkedNonemptyBoolWordQuoteNativeHaltTape_contextLength_gt_exact
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) :
    Tape.contextLength
        (checkedNonemptyBoolWordQuoteNativeHaltTape b rest stage suffix) >
      Tape.contextLength
        (Tape.input
          (checkedNonemptyBoolWordQuoteExactBits b rest stage suffix)) := by
  have htrailer :=
    checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits_length_ge_three
      rest
  simp [checkedNonemptyBoolWordQuoteNativeHaltTape,
    checkedNonemptyBoolWordQuoteExactBits_eq,
    MachineDescription.encodeCodeSymbolAsInput, tapeAtCells,
    Tape.input, Tape.contextLength, List.length_append] at *
  omega

theorem checkedNonemptyBoolWordQuoteNativeHaltTape_not_run_exactInput
    (D : MachineDescription) (n : Nat)
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) :
    D.runConfig n
        { state := D.start
          tape :=
            checkedNonemptyBoolWordQuoteNativeHaltTape
              b rest stage suffix } ≠
      { state := D.halt
        tape :=
          Tape.input
            (checkedNonemptyBoolWordQuoteExactBits
              b rest stage suffix) } := by
  intro hrun
  have hmono :=
    MachineDescription.runConfig_contextLength_mono D n
      { state := D.start
        tape :=
          checkedNonemptyBoolWordQuoteNativeHaltTape
            b rest stage suffix }
  have hfinal :
      Tape.contextLength
          ((D.runConfig n
            { state := D.start
              tape :=
                checkedNonemptyBoolWordQuoteNativeHaltTape
                  b rest stage suffix }).tape) =
        Tape.contextLength
          (Tape.input
            (checkedNonemptyBoolWordQuoteExactBits
              b rest stage suffix)) := by
    simpa using congrArg
      (fun c : MachineDescription.Configuration =>
        Tape.contextLength c.tape) hrun
  have hgt :=
    checkedNonemptyBoolWordQuoteNativeHaltTape_contextLength_gt_exact
      b rest stage suffix
  have hle :
      Tape.contextLength
          (checkedNonemptyBoolWordQuoteNativeHaltTape
            b rest stage suffix) ≤
        Tape.contextLength
          (Tape.input
            (checkedNonemptyBoolWordQuoteExactBits
              b rest stage suffix)) := by
    simpa [hfinal] using hmono
  omega

end DovetailInitialLayoutInitializer
end Computability
end FoC
