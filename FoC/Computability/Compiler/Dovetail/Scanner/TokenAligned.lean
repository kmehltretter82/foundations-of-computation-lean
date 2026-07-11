import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.DovetailStagePrefix

set_option doc.verso true

/-!
# Token-alignment pre-scanner

Every {name (full := FoC.Computability.MachineCodeSymbol)}`MachineCodeSymbol`
expands to a four-bit group under
{name (full := FoC.Computability.MachineDescription.encodeCodeSymbolAsInput)}`encodeCodeSymbolAsInput`,
and the valid groups are exactly the eight groups led by {lit}`false` plus
{lit}`true,false,false,false`.  The pre-scanner validates that a public input
word is a nonempty concatenation of valid groups, then rewinds and halts with
the head on bit 1 without writing.

Closedness of this one small machine converts word-start recognizer
obligations over arbitrary {lit}`Word Bool` inputs into code-word
obligations, which is the currency of the existing closed scanner stack.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

/--
Token-alignment pre-scanner.  States 0–3 walk a {lit}`false`-led group, states
5–7 walk the {lit}`true,false,false,false` group, state 8 rewinds to the left
fringe blank, and states 9–10 return the head to bit 1.
-/
def CodeWordAlignedPreScannerDescription : MachineDescription where
  stateCount := 11
  start := 0
  halt := 10
  transitions :=
    [ keepMove 0 (some false) Direction.right 1
    , keepMove 0 (some true) Direction.right 5
    , keepMove 0 none Direction.left 8
    , keepMove 1 (some false) Direction.right 2
    , keepMove 1 (some true) Direction.right 2
    , keepMove 2 (some false) Direction.right 3
    , keepMove 2 (some true) Direction.right 3
    , keepMove 3 (some false) Direction.right 0
    , keepMove 3 (some true) Direction.right 0
    , keepMove 5 (some false) Direction.right 6
    , keepMove 6 (some false) Direction.right 7
    , keepMove 7 (some false) Direction.right 0
    , keepMove 8 (some false) Direction.left 8
    , keepMove 8 (some true) Direction.left 8
    , keepMove 8 none Direction.right 9
    , keepMove 9 (some false) Direction.right 10
    , keepMove 9 (some true) Direction.right 10
    ]

private abbrev CWA := CodeWordAlignedPreScannerDescription

theorem codeWordAlignedPreScannerDescription_wellFormed :
    CWA.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := CWA.transitions)
      (stateCount := CWA.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := CWA.transitions)
      (by decide)

theorem codeWordAlignedPreScannerDescription_haltTransitionFree :
    CWA.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := CWA.transitions)
    (state := CWA.halt)
    (by decide)

theorem codeWordAlignedPreScannerDescription_subroutineReady :
    CWA.SubroutineReady :=
  ⟨codeWordAlignedPreScannerDescription_wellFormed,
    codeWordAlignedPreScannerDescription_haltTransitionFree⟩

/-!
## Aligned-word decoder

The reference decoder for what the pre-scanner accepts: a partial map from
four-bit groups to code symbols, iterated over the word.
-/

/-- Decode one four-bit group to its code symbol. -/
def decodeAlignedSymbol : Bool -> Bool -> Bool -> Bool ->
    Option MachineCodeSymbol
  | false, false, false, false => some MachineCodeSymbol.header
  | false, false, false, true => some MachineCodeSymbol.transition
  | false, false, true, false => some MachineCodeSymbol.tick
  | false, false, true, true => some MachineCodeSymbol.done
  | false, true, false, false => some MachineCodeSymbol.blank
  | false, true, false, true => some MachineCodeSymbol.zero
  | false, true, true, false => some MachineCodeSymbol.one
  | false, true, true, true => some MachineCodeSymbol.moveLeft
  | true, false, false, false => some MachineCodeSymbol.moveRight
  | _, _, _, _ => none

/-- Decode a bit word as a concatenation of four-bit symbol groups. -/
def decodeAlignedWord : Word Bool -> Option (Word MachineCodeSymbol)
  | [] => some []
  | b0 :: b1 :: b2 :: b3 :: rest =>
      match decodeAlignedSymbol b0 b1 b2 b3, decodeAlignedWord rest with
      | some symbol, some code => some (symbol :: code)
      | _, _ => none
  | _ => none

theorem decodeAlignedSymbol_eq_some_iff
    (b0 b1 b2 b3 : Bool) (symbol : MachineCodeSymbol) :
    decodeAlignedSymbol b0 b1 b2 b3 = some symbol <->
      encodeCodeSymbolAsInput symbol = [b0, b1, b2, b3] := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases symbol <;>
    decide

theorem decodeAlignedWord_encodeCodeWordAsInput
    (code : Word MachineCodeSymbol) :
    decodeAlignedWord (encodeCodeWordAsInput code) = some code := by
  induction code with
  | nil =>
      rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          decodeAlignedWord, decodeAlignedSymbol, ih]

theorem decodeAlignedWord_eq_some_encodeCodeWordAsInput :
    forall {w : Word Bool} {code : Word MachineCodeSymbol},
      decodeAlignedWord w = some code ->
        w = encodeCodeWordAsInput code
  | [], code, h => by
      simp [decodeAlignedWord] at h
      rw [← h]
      rfl
  | b0 :: b1 :: b2 :: b3 :: rest, code, h => by
      simp only [decodeAlignedWord] at h
      cases hsymbol : decodeAlignedSymbol b0 b1 b2 b3 with
      | none =>
          rw [hsymbol] at h
          cases h
      | some symbol =>
          rw [hsymbol] at h
          cases hrest : decodeAlignedWord rest with
          | none =>
              rw [hrest] at h
              cases h
          | some restCode =>
              rw [hrest] at h
              cases h
              have htail :
                  rest = encodeCodeWordAsInput restCode :=
                decodeAlignedWord_eq_some_encodeCodeWordAsInput hrest
              have hgroup :
                  encodeCodeSymbolAsInput symbol = [b0, b1, b2, b3] :=
            (decodeAlignedSymbol_eq_some_iff b0 b1 b2 b3 symbol).mp hsymbol
              simp [encodeCodeWordAsInput, hgroup, htail]
  | [_], _, h => by
      simp [decodeAlignedWord] at h
  | [_, _], _, h => by
      simp [decodeAlignedWord] at h
  | [_, _, _], _, h => by
      simp [decodeAlignedWord] at h

/-!
## Forward runs
-/

/--
Exact handoff tape of the pre-scanner: the input word with the left fringe
blank and the terminal blank visited, and the head returned to bit 1.
-/
def codeWordAlignedHandoffTape (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.right
    (tapeAtCells [none] (List.append (bits.map some) [none]))

private theorem run_codeWordAligned_scanToken
    (symbol : MachineCodeSymbol) (leftRev restCells : List (Option Bool)) :
    CWA.runConfig 4
        (config 0 leftRev
          (List.append
            ((encodeCodeSymbolAsInput symbol).map some) restCells)) =
      config 0
        (List.append
          (((encodeCodeSymbolAsInput symbol).reverse).map some) leftRev)
        restCells := by
  cases symbol <;> cases restCells <;>
    simp [CodeWordAlignedPreScannerDescription, encodeCodeSymbolAsInput,
      config, tapeAtCells, keepMove, runConfig, stepConfig,
      lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem run_codeWordAligned_scanCode
    (code : Word MachineCodeSymbol) (leftRev : List (Option Bool)) :
    CWA.runConfig (4 * code.length)
        (config 0 leftRev ((encodeCodeWordAsInput code).map some)) =
      config 0
        (List.append
          (((encodeCodeWordAsInput code).reverse).map some) leftRev)
        [] := by
  induction code generalizing leftRev with
  | nil =>
      simp [encodeCodeWordAsInput, runConfig]
  | cons symbol rest ih =>
      rw [show 4 * (symbol :: rest).length = 4 + 4 * rest.length by
        simp [List.length_cons]
        lia]
      rw [runConfig_add]
      have hcells :
          (encodeCodeWordAsInput (symbol :: rest)).map some =
            List.append ((encodeCodeSymbolAsInput symbol).map some)
              ((encodeCodeWordAsInput rest).map some) := by
        simp [encodeCodeWordAsInput, List.map_append]
      rw [hcells, run_codeWordAligned_scanToken symbol leftRev]
      rw [ih]
      simp [encodeCodeWordAsInput, List.reverse_append, List.map_append,
        List.append_assoc]

/-- Rewind-phase configuration: {lit}`remainingRev` holds the cells still left
of the head in reversed order, {lit}`scanned` the cells already walked. -/
private def rewindScanConfig (remainingRev scanned : Word Bool) :
    Configuration :=
  match remainingRev with
  | [] =>
      config 8 []
        (none :: List.append (scanned.map some) [none])
  | bit :: rest =>
      config 8 (rest.map some)
        (some bit :: List.append (scanned.map some) [none])

private theorem run_codeWordAligned_rewind
    (remainingRev scanned : Word Bool)
    (hne : List.append remainingRev.reverse scanned ≠ []) :
    CWA.runConfig (remainingRev.length + 2)
        (rewindScanConfig remainingRev scanned) =
      { state := CWA.halt
        tape :=
          codeWordAlignedHandoffTape
            (List.append remainingRev.reverse scanned) } := by
  induction remainingRev generalizing scanned with
  | nil =>
      cases scanned with
      | nil =>
          exact absurd rfl hne
      | cons s ss =>
          cases s <;> cases ss <;>
            simp [rewindScanConfig,
              CodeWordAlignedPreScannerDescription,
              codeWordAlignedHandoffTape,
              config, tapeAtCells, keepMove, runConfig,
              stepConfig, lookupTransition,
              Matches, transition,
              Tape.read, Tape.write, Tape.move,
              Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 2 = 1 + (rest.length + 2) by
        simp [List.length_cons]
        lia]
      rw [runConfig_add]
      have hstep :
          CWA.runConfig 1 (rewindScanConfig (bit :: rest) scanned) =
            rewindScanConfig rest (bit :: scanned) := by
        cases bit <;> cases rest <;>
          simp [rewindScanConfig,
            CodeWordAlignedPreScannerDescription,
            config, tapeAtCells, keepMove, runConfig,
            stepConfig, lookupTransition,
            Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih (bit :: scanned) (by simp)]
      simp [List.reverse_cons, List.append_assoc]

/--
Forward behavior on canonical code-word inputs: the pre-scanner validates the
whole word and halts at the exact handoff tape.
-/
private theorem run_codeWordAligned_boundary
    (bitsRev : Word Bool) :
    CWA.runConfig 1 (config 0 (bitsRev.map some) []) =
      rewindScanConfig bitsRev [] := by
  cases bitsRev with
  | nil =>
      simp [rewindScanConfig,
        CodeWordAlignedPreScannerDescription,
        config, tapeAtCells, keepMove, runConfig,
        stepConfig, lookupTransition,
        Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons bit restRev =>
      cases bit <;>
        simp [rewindScanConfig,
          CodeWordAlignedPreScannerDescription,
          config, tapeAtCells, keepMove, runConfig,
          stepConfig, lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem run_codeWordAligned_full
    (bits : Word Bool) (code : Word MachineCodeSymbol)
    (hbits : bits = encodeCodeWordAsInput code)
    (hne : bits ≠ []) :
    CWA.runConfig
        (4 * code.length + (1 + (bits.reverse.length + 2)))
        { state := CWA.start, tape := Tape.input bits } =
      { state := CWA.halt
        tape := codeWordAlignedHandoffTape bits } := by
  have hinit :
      ({ state := CWA.start, tape := Tape.input bits } :
          Configuration) =
        config 0 [] (bits.map some) := by
    cases bits <;> rfl
  have hscan :
      CWA.runConfig (4 * code.length)
          (config 0 [] (bits.map some)) =
        config 0 ((bits.reverse).map some) [] := by
    rw [hbits]
    simpa using run_codeWordAligned_scanCode code []
  have hrewind :
      CWA.runConfig (bits.reverse.length + 2)
          (rewindScanConfig bits.reverse []) =
        { state := CWA.halt
          tape := codeWordAlignedHandoffTape bits } := by
    have h :=
      run_codeWordAligned_rewind bits.reverse []
        (by
          cases bits with
          | nil => exact absurd rfl hne
          | cons b bs => simp)
    simpa using h
  rw [runConfig_add, hinit, hscan, runConfig_add,
    run_codeWordAligned_boundary, hrewind]

/--
Forward behavior on canonical code-word inputs: the pre-scanner validates the
whole word and halts at the exact handoff tape.
-/
theorem codeWordAlignedPreScannerDescription_haltsFromTape
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    CWA.HaltsFromTape
      (Tape.input (encodeCodeWordAsInput (symbol :: rest)))
      (codeWordAlignedHandoffTape
        (encodeCodeWordAsInput (symbol :: rest))) := by
  have hne : encodeCodeWordAsInput (symbol :: rest) ≠ [] := by
    cases symbol <;> simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  have hrun :=
    run_codeWordAligned_full
      (encodeCodeWordAsInput (symbol :: rest)) (symbol :: rest) rfl hne
  refine ⟨4 * (symbol :: rest).length +
      (1 + ((encodeCodeWordAsInput (symbol :: rest)).reverse.length + 2)),
    ?_, ?_⟩
  · simpa using congrArg Configuration.state hrun
  · simpa using congrArg Configuration.tape hrun

/-!
## Closedness

Any halting run of the pre-scanner from a word start certifies that the word
is a nonempty canonical code-word encoding and pins the exact handoff tape.
-/

private theorem ne_halt_of_run_stuck
    {c : Configuration} (k : Nat)
    (hstuck : CWA.stepConfig (CWA.runConfig k c) = none)
    (hstate : (CWA.runConfig k c).state ≠ CWA.halt) :
    forall n : Nat, (CWA.runConfig n c).state ≠ CWA.halt := by
  intro n
  exact
    CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_ne_halt_region
      codeWordAlignedPreScannerDescription_haltTransitionFree
      (rfl : CWA.runConfig k c = CWA.runConfig k c)
      (fun m => by
        rw [runConfig_of_stepConfig_none hstuck]
        exact hstate)

private theorem run_state0_ne_halt_of_decode_none :
    forall (w : Word Bool) (leftRev : List (Option Bool)),
      decodeAlignedWord w = none ->
        forall n : Nat,
          (CWA.runConfig n (config 0 leftRev (w.map some))).state ≠
            CWA.halt
  | [], _leftRev, h => by
      simp [decodeAlignedWord] at h
  | [b0], leftRev, _h => by
      cases b0 <;>
        exact
          ne_halt_of_run_stuck 1
            (by
              simp [CodeWordAlignedPreScannerDescription,
                config, tapeAtCells, keepMove, runConfig,
                stepConfig, lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight])
            (by
              simp [CodeWordAlignedPreScannerDescription,
                config, tapeAtCells, keepMove, runConfig,
                stepConfig, lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight])
  | [b0, b1], leftRev, _h => by
      cases b0 <;> cases b1 <;>
        exact
          ne_halt_of_run_stuck 2
            (by
              simp [CodeWordAlignedPreScannerDescription,
                config, tapeAtCells, keepMove, runConfig,
                stepConfig, lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight])
            (by
              simp [CodeWordAlignedPreScannerDescription,
                config, tapeAtCells, keepMove, runConfig,
                stepConfig, lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight])
  | [b0, b1, b2], leftRev, _h => by
      cases b0 <;> cases b1 <;> cases b2 <;>
        exact
          ne_halt_of_run_stuck 3
            (by
              simp [CodeWordAlignedPreScannerDescription,
                config, tapeAtCells, keepMove, runConfig,
                stepConfig, lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight])
            (by
              simp [CodeWordAlignedPreScannerDescription,
                config, tapeAtCells, keepMove, runConfig,
                stepConfig, lookupTransition,
                Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight])
  | b0 :: b1 :: b2 :: b3 :: rest, leftRev, h => by
      simp only [decodeAlignedWord] at h
      cases hsym : decodeAlignedSymbol b0 b1 b2 b3 with
      | some symbol =>
          rw [hsym] at h
          cases hrest : decodeAlignedWord rest with
          | some code =>
              rw [hrest] at h
              cases h
          | none =>
              rw [hrest] at h
              intro n
              have hgroup :
                  encodeCodeSymbolAsInput symbol = [b0, b1, b2, b3] :=
                (decodeAlignedSymbol_eq_some_iff b0 b1 b2 b3 symbol).mp hsym
              have hcells :
                  ((b0 :: b1 :: b2 :: b3 :: rest).map some :
                      List (Option Bool)) =
                    List.append
                      ((encodeCodeSymbolAsInput symbol).map some)
                      (rest.map some) := by
                rw [hgroup]
                rfl
              have hreach :
                  CWA.runConfig 4
                      (config 0 leftRev
                        ((b0 :: b1 :: b2 :: b3 :: rest).map some)) =
                    config 0
                      (List.append
                        (((encodeCodeSymbolAsInput symbol).reverse).map some)
                        leftRev)
                      (rest.map some) := by
                rw [hcells]
                exact run_codeWordAligned_scanToken symbol leftRev
                  (rest.map some)
              exact
                CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_ne_halt_region
                  codeWordAlignedPreScannerDescription_haltTransitionFree
                  hreach
                  (run_state0_ne_halt_of_decode_none rest
                    (List.append
                      (((encodeCodeSymbolAsInput symbol).reverse).map some)
                      leftRev)
                    hrest)
      | none =>
          cases b0 with
          | false =>
              exfalso
              cases b1 <;> cases b2 <;> cases b3 <;>
                simp [decodeAlignedSymbol] at hsym
          | true =>
              cases b1 with
              | true =>
                  exact
                    ne_halt_of_run_stuck 1
                      (by
                        cases rest <;>
                          simp [CodeWordAlignedPreScannerDescription,
                            config, tapeAtCells, keepMove, runConfig,
                            stepConfig, lookupTransition,
                            Matches, transition,
                            Tape.read, Tape.write, Tape.move,
                            Tape.moveRight])
                      (by
                        cases rest <;>
                          simp [CodeWordAlignedPreScannerDescription,
                            config, tapeAtCells, keepMove, runConfig,
                            stepConfig, lookupTransition,
                            Matches, transition,
                            Tape.read, Tape.write, Tape.move,
                            Tape.moveRight])
              | false =>
                  cases b2 with
                  | true =>
                      exact
                        ne_halt_of_run_stuck 2
                          (by
                            cases rest <;>
                              simp [CodeWordAlignedPreScannerDescription,
                                config, tapeAtCells, keepMove, runConfig,
                                stepConfig, lookupTransition,
                                Matches, transition,
                                Tape.read, Tape.write, Tape.move,
                                Tape.moveRight])
                          (by
                            cases rest <;>
                              simp [CodeWordAlignedPreScannerDescription,
                                config, tapeAtCells, keepMove, runConfig,
                                stepConfig, lookupTransition,
                                Matches, transition,
                                Tape.read, Tape.write, Tape.move,
                                Tape.moveRight])
                  | false =>
                      cases b3 with
                      | true =>
                          exact
                            ne_halt_of_run_stuck 3
                              (by
                                cases rest <;>
                                  simp [CodeWordAlignedPreScannerDescription,
                                    config, tapeAtCells, keepMove,
                                    runConfig,
                                    stepConfig,
                                    lookupTransition,
                                    Matches,
                                    transition,
                                    Tape.read, Tape.write, Tape.move,
                                    Tape.moveRight])
                              (by
                                cases rest <;>
                                  simp [CodeWordAlignedPreScannerDescription,
                                    config, tapeAtCells, keepMove,
                                    runConfig,
                                    stepConfig,
                                    lookupTransition,
                                    Matches,
                                    transition,
                                    Tape.read, Tape.write, Tape.move,
                                    Tape.moveRight])
                      | false =>
                          exfalso
                          simp [decodeAlignedSymbol] at hsym

/--
Word-start closedness of the pre-scanner: a halting run certifies that the
word is a nonempty canonical code-word encoding, and the final tape is the
exact handoff tape.
-/
theorem codeWordAlignedPreScannerDescription_haltsFromTape_inv
    {w : Word Bool} {T : Tape Bool}
    (h : CWA.HaltsFromTape (Tape.input w) T) :
    exists symbol : MachineCodeSymbol,
    exists rest : Word MachineCodeSymbol,
      w = encodeCodeWordAsInput (symbol :: rest) ∧
        T = codeWordAlignedHandoffTape w := by
  have hinit :
      ({ state := CWA.start, tape := Tape.input w } :
          Configuration) =
        config 0 [] (w.map some) := by
    cases w <;> rfl
  cases hdec : decodeAlignedWord w with
  | none =>
      exfalso
      rcases h with ⟨n, hn⟩
      have hstate :
          (CWA.runConfig n
            { state := CWA.start, tape := Tape.input w }).state =
            CWA.halt := hn.left
      rw [hinit] at hstate
      exact run_state0_ne_halt_of_decode_none w [] hdec n hstate
  | some code =>
      have hw : w = encodeCodeWordAsInput code :=
        decodeAlignedWord_eq_some_encodeCodeWordAsInput hdec
      cases code with
      | nil =>
          exfalso
          rcases h with ⟨n, hn⟩
          have hstate :
              (CWA.runConfig n
                { state := CWA.start, tape := Tape.input w }).state =
                CWA.halt := hn.left
          have hwnil : w = [] := by
            rw [hw]
            rfl
          rw [hwnil] at hstate
          exact
            ne_halt_of_run_stuck 2
              (by decide)
              (by decide)
              n hstate
      | cons symbol rest =>
          refine ⟨symbol, rest, by rw [hw], ?_⟩
          have hforward :
              CWA.HaltsFromTape
                (Tape.input w)
                (codeWordAlignedHandoffTape w) := by
            rw [hw]
            exact
              codeWordAlignedPreScannerDescription_haltsFromTape
                symbol rest
          exact
            haltsFromTape_functional_of_haltTransitionFree
              codeWordAlignedPreScannerDescription_haltTransitionFree
              h hforward

end DovetailLayoutScanner
end CanonicalLayouts
end EncRewriters

end Computability
end FoC
