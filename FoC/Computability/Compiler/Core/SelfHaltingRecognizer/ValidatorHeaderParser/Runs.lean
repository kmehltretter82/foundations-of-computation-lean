import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorHeaderParser.Basic

set_option doc.verso true

/-!
# Exact runs of the Boolean header parser

Small four-step token lemmas are composed into unary-field runs and then into
the exact leaf-2 handoff.  The parser never writes: the complete checked prefix
is preserved to the left of the head for later bounds and determinism phases.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

private abbrev VHP := ValidatorHeaderParserDescription

def validatorHeaderSymbolCells
    (symbol : MachineCodeSymbol) : List (Option Bool) :=
  (encodeCodeSymbolAsInput symbol).map some

private def validatorHeaderNatCells (n : Nat) : List (Option Bool) :=
  (encodeCodeWordAsInput (encodeNat n)).map some
private theorem validatorHeaderMapSomeAppend
    (left right : Word Bool) :
    (List.append left right).map some =
      List.append (left.map some) (right.map some) := by
  induction left with
  | nil =>
      rfl
  | cons bit rest ih =>
      show some bit :: (List.append rest right).map some = _
      rw [ih]
      rfl

private theorem validatorHeaderMapSomeReverse (bits : Word Bool) :
    bits.reverse.map some = (bits.map some).reverse :=
  List.map_reverse
private theorem validatorHeaderAppendTail
    (a b c d e f tail : List (Option Bool)) :
    List.append
        (List.append a
          (List.append b (List.append c (List.append d (List.append e f)))))
        tail =
      List.append a
        (List.append b
          (List.append c (List.append d (List.append e (List.append f tail))))) := by
  induction a <;> simp

private theorem validatorHeaderAppendNil
    (a b c d e : List (Option Bool)) :
    List.append a
        (List.append b (List.append c (List.append d (List.append e [])))) =
      List.append a (List.append b (List.append c (List.append d e))) := by
  exact congrArg (fun rest =>
    List.append a (List.append b (List.append c (List.append d rest)))) (List.append_nil e)

private theorem validatorHeaderReverseAppend
    (a b c d e tail : List (Option Bool)) :
    List.append e.reverse
        (List.append d.reverse
          (List.append c.reverse
            (List.append b.reverse (List.append a.reverse tail)))) =
      List.append
        (List.append a (List.append b (List.append c (List.append d e)))).reverse
        tail := by
  induction a <;> simp

private def validatorHeaderFieldFuel (n : Nat) : Nat :=
  4 * (n + 1)

/-- Exact number of steps used to scan the header and four unary fields. -/
def validatorHeaderParserSteps
    (stateCount start halt transitionCount : Nat) : Nat :=
  4 +
    (validatorHeaderFieldFuel stateCount +
      (validatorHeaderFieldFuel start +
        (validatorHeaderFieldFuel halt +
          validatorHeaderFieldFuel transitionCount)))

theorem run_validatorHeader_header
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 0 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.header)
            restCells)) =
      config 4
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.header).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_validatorHeader_stateCount_tick
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 4 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.tick)
            restCells)) =
      config 4
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.tick).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_validatorHeader_stateCount_done
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 4 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.done)
            restCells)) =
      config 8
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.done).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_validatorHeader_start_tick
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 8 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.tick)
            restCells)) =
      config 8
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.tick).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_validatorHeader_start_done
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 8 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.done)
            restCells)) =
      config 12
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.done).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_validatorHeader_halt_tick
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 12 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.tick)
            restCells)) =
      config 12
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.tick).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_validatorHeader_halt_done
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 12 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.done)
            restCells)) =
      config 16
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.done).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_validatorHeader_transitionCount_tick
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 16 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.tick)
            restCells)) =
      config 16
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.tick).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_validatorHeader_transitionCount_done
    (leftRev restCells : List (Option Bool)) :
    VHP.runConfig 4
        (config 16 leftRev
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.done)
            restCells)) =
      config 20
        (List.append
          ((validatorHeaderSymbolCells MachineCodeSymbol.done).reverse)
          leftRev)
        restCells := by
  cases restCells <;>
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem validatorHeaderNatCells_succ (n : Nat) :
    validatorHeaderNatCells (n + 1) =
      List.append
        (validatorHeaderSymbolCells MachineCodeSymbol.tick)
        (validatorHeaderNatCells n) := by
  simp [validatorHeaderNatCells, validatorHeaderSymbolCells,
    encodeNat, encodeCodeSymbolAsInput]

private theorem validatorHeaderNatCells_succ_append
    (n : Nat) (restCells : List (Option Bool)) :
    List.append (validatorHeaderNatCells (n + 1)) restCells =
      List.append
        (validatorHeaderSymbolCells MachineCodeSymbol.tick)
        (List.append (validatorHeaderNatCells n) restCells) := by
  rw [validatorHeaderNatCells_succ]
  exact List.append_assoc _ _ _

private theorem run_validatorHeader_stateCount_nat
    (n : Nat) (leftRev restCells : List (Option Bool)) :
    VHP.runConfig (validatorHeaderFieldFuel n)
        (config 4 leftRev
          (List.append (validatorHeaderNatCells n) restCells)) =
      config 8
        (List.append (validatorHeaderNatCells n).reverse leftRev)
        restCells := by
  induction n generalizing leftRev with
  | zero =>
      simpa [validatorHeaderFieldFuel, validatorHeaderNatCells,
        validatorHeaderSymbolCells, encodeNat, encodeCodeWordAsInput] using
        run_validatorHeader_stateCount_done leftRev restCells
  | succ n ih =>
      rw [show validatorHeaderFieldFuel (n + 1) =
          4 + validatorHeaderFieldFuel n by
        simp [validatorHeaderFieldFuel]
        lia]
      rw [runConfig_add, validatorHeaderNatCells_succ_append]
      rw [run_validatorHeader_stateCount_tick, ih]
      simp [validatorHeaderNatCells_succ, List.reverse_append,
        List.append_assoc]

private theorem run_validatorHeader_start_nat
    (n : Nat) (leftRev restCells : List (Option Bool)) :
    VHP.runConfig (validatorHeaderFieldFuel n)
        (config 8 leftRev
          (List.append (validatorHeaderNatCells n) restCells)) =
      config 12
        (List.append (validatorHeaderNatCells n).reverse leftRev)
        restCells := by
  induction n generalizing leftRev with
  | zero =>
      simpa [validatorHeaderFieldFuel, validatorHeaderNatCells,
        validatorHeaderSymbolCells, encodeNat, encodeCodeWordAsInput] using
        run_validatorHeader_start_done leftRev restCells
  | succ n ih =>
      rw [show validatorHeaderFieldFuel (n + 1) =
          4 + validatorHeaderFieldFuel n by
        simp [validatorHeaderFieldFuel]
        lia]
      rw [runConfig_add, validatorHeaderNatCells_succ_append]
      rw [run_validatorHeader_start_tick, ih]
      simp [validatorHeaderNatCells_succ, List.reverse_append,
        List.append_assoc]

private theorem run_validatorHeader_halt_nat
    (n : Nat) (leftRev restCells : List (Option Bool)) :
    VHP.runConfig (validatorHeaderFieldFuel n)
        (config 12 leftRev
          (List.append (validatorHeaderNatCells n) restCells)) =
      config 16
        (List.append (validatorHeaderNatCells n).reverse leftRev)
        restCells := by
  induction n generalizing leftRev with
  | zero =>
      simpa [validatorHeaderFieldFuel, validatorHeaderNatCells,
        validatorHeaderSymbolCells, encodeNat, encodeCodeWordAsInput] using
        run_validatorHeader_halt_done leftRev restCells
  | succ n ih =>
      rw [show validatorHeaderFieldFuel (n + 1) =
          4 + validatorHeaderFieldFuel n by
        simp [validatorHeaderFieldFuel]
        lia]
      rw [runConfig_add, validatorHeaderNatCells_succ_append]
      rw [run_validatorHeader_halt_tick, ih]
      simp [validatorHeaderNatCells_succ, List.reverse_append,
        List.append_assoc]

private theorem run_validatorHeader_transitionCount_nat
    (n : Nat) (leftRev restCells : List (Option Bool)) :
    VHP.runConfig (validatorHeaderFieldFuel n)
        (config 16 leftRev
          (List.append (validatorHeaderNatCells n) restCells)) =
      config 20
        (List.append (validatorHeaderNatCells n).reverse leftRev)
        restCells := by
  induction n generalizing leftRev with
  | zero =>
      simpa [validatorHeaderFieldFuel, validatorHeaderNatCells,
        validatorHeaderSymbolCells, encodeNat, encodeCodeWordAsInput] using
        run_validatorHeader_transitionCount_done leftRev restCells
  | succ n ih =>
      rw [show validatorHeaderFieldFuel (n + 1) =
          4 + validatorHeaderFieldFuel n by
        simp [validatorHeaderFieldFuel]
        lia]
      rw [runConfig_add, validatorHeaderNatCells_succ_append]
      rw [run_validatorHeader_transitionCount_tick, ih]
      simp [validatorHeaderNatCells_succ, List.reverse_append,
        List.append_assoc]

private theorem validatorHeaderFieldsCode_cells
    (stateCount start halt transitionCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    List.append
        ((encodeCodeWordAsInput
          (validatorHeaderFieldsCode stateCount start halt transitionCount
            suffix)).map some)
        [none] =
      List.append
        (validatorHeaderSymbolCells MachineCodeSymbol.header)
        (List.append (validatorHeaderNatCells stateCount)
          (List.append (validatorHeaderNatCells start)
            (List.append (validatorHeaderNatCells halt)
              (List.append (validatorHeaderNatCells transitionCount)
                (List.append ((encodeCodeWordAsInput suffix).map some)
                  [none]))))) := by
  unfold validatorHeaderSymbolCells validatorHeaderNatCells
  simp only [validatorHeaderFieldsCode, encodeNatAppend,
    encodeCodeWordAsInput]
  rw [encodeCodeWordAsInput_append, encodeCodeWordAsInput_append,
    encodeCodeWordAsInput_append, encodeCodeWordAsInput_append]
  rw [validatorHeaderMapSomeAppend, validatorHeaderMapSomeAppend,
    validatorHeaderMapSomeAppend, validatorHeaderMapSomeAppend,
    validatorHeaderMapSomeAppend]
  exact validatorHeaderAppendTail _ _ _ _ _ _ _

private theorem validatorHeaderFieldsPrefix_cells
    (stateCount start halt transitionCount : Nat) :
    (encodeCodeWordAsInput
      (validatorHeaderFieldsPrefix stateCount start halt
        transitionCount)).map some =
      List.append
        (validatorHeaderSymbolCells MachineCodeSymbol.header)
        (List.append (validatorHeaderNatCells stateCount)
          (List.append (validatorHeaderNatCells start)
            (List.append (validatorHeaderNatCells halt)
              (validatorHeaderNatCells transitionCount)))) := by
  unfold validatorHeaderSymbolCells validatorHeaderNatCells
  simp only [validatorHeaderFieldsPrefix, encodeNatAppend,
    encodeCodeWordAsInput]
  rw [encodeCodeWordAsInput_append, encodeCodeWordAsInput_append,
    encodeCodeWordAsInput_append, encodeCodeWordAsInput_append]
  rw [validatorHeaderMapSomeAppend, validatorHeaderMapSomeAppend,
    validatorHeaderMapSomeAppend, validatorHeaderMapSomeAppend,
    validatorHeaderMapSomeAppend]
  exact validatorHeaderAppendNil _ _ _ _ _

/--
Exact forward run of leaf 2.  The machine preserves the complete encoded
prefix, halts at the first suffix bit, and retains the terminal padding blank.
-/
theorem run_validatorHeaderParser
    (stateCount start halt transitionCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    VHP.runConfig
        (validatorHeaderParserSteps stateCount start halt transitionCount)
        { state := VHP.start
          tape :=
            validatorHeaderFieldsPaddedStartTape
              stateCount start halt transitionCount suffix } =
      { state := VHP.halt
        tape :=
          validatorHeaderFieldsHandoffTape
            stateCount start halt transitionCount suffix } := by
  change
    VHP.runConfig
        (validatorHeaderParserSteps stateCount start halt transitionCount)
        (config 0 [none]
          (List.append
            ((encodeCodeWordAsInput
              (validatorHeaderFieldsCode stateCount start halt
                transitionCount suffix)).map some)
            [none])) =
      config 20
        (List.append
          (((encodeCodeWordAsInput
            (validatorHeaderFieldsPrefix stateCount start halt
              transitionCount)).reverse).map some)
          [none])
        (List.append ((encodeCodeWordAsInput suffix).map some) [none])
  rw [validatorHeaderFieldsCode_cells]
  simp only [validatorHeaderParserSteps]
  rw [runConfig_add, run_validatorHeader_header]
  rw [runConfig_add, run_validatorHeader_stateCount_nat]
  rw [runConfig_add, run_validatorHeader_start_nat]
  rw [runConfig_add, run_validatorHeader_halt_nat]
  rw [run_validatorHeader_transitionCount_nat]
  rw [validatorHeaderMapSomeReverse, validatorHeaderFieldsPrefix_cells]
  exact congrArg
    (fun leftRev =>
      config 20 leftRev
        (List.append ((encodeCodeWordAsInput suffix).map some) [none]))
    (validatorHeaderReverseAppend
      (validatorHeaderSymbolCells MachineCodeSymbol.header)
      (validatorHeaderNatCells stateCount)
      (validatorHeaderNatCells start)
      (validatorHeaderNatCells halt)
      (validatorHeaderNatCells transitionCount)
      [none])

/-- Forward halting contract at the exact leaf-2 handoff tape. -/
theorem validatorHeaderParserDescription_haltsFromTape
    (stateCount start halt transitionCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    VHP.HaltsFromTape
      (validatorHeaderFieldsPaddedStartTape
        stateCount start halt transitionCount suffix)
      (validatorHeaderFieldsHandoffTape
        stateCount start halt transitionCount suffix) := by
  refine
    ⟨validatorHeaderParserSteps stateCount start halt transitionCount,
      ?_, ?_⟩
  · simpa using congrArg Configuration.state
      (run_validatorHeaderParser stateCount start halt transitionCount suffix)
  · simpa using congrArg Configuration.tape
      (run_validatorHeaderParser stateCount start halt transitionCount suffix)

end SelfHaltingRecognizer
end Computability
end FoC
