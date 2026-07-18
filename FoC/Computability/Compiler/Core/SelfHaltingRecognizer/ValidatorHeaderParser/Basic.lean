import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTokenGate
import FoC.Computability.Compiler.Core.EncodingLemmas

set_option doc.verso true

/-!
# Exact-code validator: Boolean header and fixed-field parser

This is the physical Boolean parser for M4 leaf 2.  It starts on the first bit
of a token-aligned input, checks the four-bit header token and the four unary
natural-number fields ({lit}`stateCount`, {lit}`start`, {lit}`halt`, and
{lit}`transitionCount`),
then halts on the first bit of the transition-record region.

The unbounded natural values are deliberately retained in their unary tape
encodings.  A finite control cannot carry arbitrary naturals; later bounds and
counted-transition phases must rescan or mark these preserved fields.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-!
## Concrete machine

States 0--3 check the header {lit}`0000`.  Each four-state field block checks
the common {lit}`001` prefix of a unary token; its fourth state loops on
{lit}`0` ({lit}`tick`) or advances on {lit}`1` ({lit}`done`). State 20 halts.
-/

/-- Boolean header/fixed-field parser used by the exact-code validator. -/
def ValidatorHeaderParserDescription : MachineDescription where
  stateCount := 21
  start := 0
  halt := 20
  transitions :=
    [ keepMove 0 (some false) Direction.right 1
    , keepMove 1 (some false) Direction.right 2
    , keepMove 2 (some false) Direction.right 3
    , keepMove 3 (some false) Direction.right 4

    , keepMove 4 (some false) Direction.right 5
    , keepMove 5 (some false) Direction.right 6
    , keepMove 6 (some true) Direction.right 7
    , keepMove 7 (some false) Direction.right 4
    , keepMove 7 (some true) Direction.right 8

    , keepMove 8 (some false) Direction.right 9
    , keepMove 9 (some false) Direction.right 10
    , keepMove 10 (some true) Direction.right 11
    , keepMove 11 (some false) Direction.right 8
    , keepMove 11 (some true) Direction.right 12

    , keepMove 12 (some false) Direction.right 13
    , keepMove 13 (some false) Direction.right 14
    , keepMove 14 (some true) Direction.right 15
    , keepMove 15 (some false) Direction.right 12
    , keepMove 15 (some true) Direction.right 16

    , keepMove 16 (some false) Direction.right 17
    , keepMove 17 (some false) Direction.right 18
    , keepMove 18 (some true) Direction.right 19
    , keepMove 19 (some false) Direction.right 16
    , keepMove 19 (some true) Direction.right 20
    ]

private abbrev VHP := ValidatorHeaderParserDescription

theorem validatorHeaderParserDescription_wellFormed :
    VHP.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := VHP.transitions)
      (stateCount := VHP.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := VHP.transitions)
      (by decide)

theorem validatorHeaderParserDescription_haltTransitionFree :
    VHP.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := VHP.transitions)
    (state := VHP.halt)
    (by decide)

theorem validatorHeaderParserDescription_subroutineReady :
    VHP.SubroutineReady :=
  ⟨validatorHeaderParserDescription_wellFormed,
    validatorHeaderParserDescription_haltTransitionFree⟩

/-!
## Exact tape layouts
-/

/-- Code-symbol prefix consumed by the header parser. -/
def validatorHeaderFieldsPrefix
    (stateCount start halt transitionCount : Nat) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    encodeNatAppend stateCount
      (encodeNatAppend start
        (encodeNatAppend halt
          (encodeNatAppend transitionCount [])))

/-- Complete code view presented to this leaf, with an arbitrary suffix. -/
def validatorHeaderFieldsCode
    (stateCount start halt transitionCount : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    encodeNatAppend stateCount
      (encodeNatAppend start
        (encodeNatAppend halt
          (encodeNatAppend transitionCount suffix)))

theorem validatorHeaderFieldsCode_eq_prefix_append
    (stateCount start halt transitionCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    validatorHeaderFieldsCode stateCount start halt transitionCount suffix =
      List.append
        (validatorHeaderFieldsPrefix stateCount start halt transitionCount)
        suffix := by
  simp [validatorHeaderFieldsCode, validatorHeaderFieldsPrefix,
    encodeNatAppend, List.append_assoc]

/-- Padded source tape supplied by the token-gate handoff move. -/
def validatorHeaderFieldsPaddedStartTape
    (stateCount start halt transitionCount : Nat)
    (suffix : Word MachineCodeSymbol) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((encodeCodeWordAsInput
        (validatorHeaderFieldsCode stateCount start halt transitionCount
          suffix)).map some)
      [none])

/-- Exact leaf-2 handoff: the prefix is left of the head, suffix at the head. -/
def validatorHeaderFieldsHandoffTape
    (stateCount start halt transitionCount : Nat)
    (suffix : Word MachineCodeSymbol) : Tape Bool :=
  tapeAtCells
    (List.append
      (((encodeCodeWordAsInput
        (validatorHeaderFieldsPrefix stateCount start halt transitionCount)).reverse).map
          some)
      [none])
    (List.append ((encodeCodeWordAsInput suffix).map some) [none])

/-- Bit-level handoff used by the all-input inversion before token alignment. -/
def validatorHeaderFieldsBitHandoffTape
    (prefixBits restBits : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (prefixBits.reverse.map some) [none])
    (List.append (restBits.map some) [none])

end SelfHaltingRecognizer
end Computability
end FoC
