import FoC.Computability.Compiler

set_option doc.verso true

/-!
# Finite executable program descriptions

This module packages the description-backed staged programs used to close the
concrete Chapter 5 Section 5.2 bridges.  The finite syntax is intentionally
small: a program description contains concrete {lit}`MachineDescription` data,
and its staged semantics reads the corresponding finite-step interpreter.

The module does not assert that every semantic Lean staged program has finite
syntax.  Instead, it proves compiler bridges for the finite programs whose
machine descriptions are explicitly supplied.

## Book coordinates

Used by:
- Chapter 5, Section 5.2: finite trace recognizers, finite dovetailing
  deciders, and finite partial unary range programs.
-/

namespace FoC
namespace Computability

open Languages

namespace Tape

/-!
## Output tape decoding

The machine layer states output using {name}`Tape.output`.  Finite partial
range programs need the inverse direction: if a halted configuration is in
standard output form, extract the word it displays.
-/

def outputRight? : List (Option symbol) -> Option (Word symbol)
  | [] => some []
  | some a :: rest =>
      match outputRight? rest with
      | none => none
      | some w => some (a :: w)
  | none :: _ => none

def toOutput? (T : Tape symbol) : Option (Word symbol) :=
  match T.left, T.head with
  | [], none =>
      match T.right with
      | [] => some []
      | _ :: _ => none
  | [], some a =>
      match outputRight? T.right with
      | none => none
      | some rest => some (a :: rest)
  | _ :: _, _ => none

theorem outputRight?_map_some (w : Word symbol) :
    outputRight? (w.map some) = some w := by
  induction w with
  | nil =>
      rfl
  | cons a rest ih =>
      simp [outputRight?, ih]

theorem outputRight?_eq_some_map
    {cells : List (Option symbol)} {w : Word symbol}
    (h : outputRight? cells = some w) :
    cells = w.map some := by
  induction cells generalizing w with
  | nil =>
      cases w with
      | nil => rfl
      | cons _ _ => cases h
  | cons cell rest ih =>
      cases cell with
      | none =>
          cases h
      | some a =>
          cases hrest : outputRight? rest with
          | none =>
              simp [outputRight?, hrest] at h
          | some tail =>
              simp [outputRight?, hrest] at h
              cases h
              rw [ih hrest]
              simp

theorem toOutput?_output (w : Word symbol) :
    toOutput? (Tape.output w) = some w := by
  cases w with
  | nil =>
      rfl
  | cons a rest =>
      simp [Tape.output, Tape.input, toOutput?, outputRight?_map_some]

theorem toOutput?_eq_some_output
    {T : Tape symbol} {w : Word symbol}
    (h : toOutput? T = some w) :
    T = Tape.output w := by
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          cases head with
          | none =>
              cases right with
              | nil =>
                  cases w with
                  | nil => rfl
                  | cons _ _ => cases h
              | cons _ _ =>
                  cases h
          | some a =>
              cases hright : outputRight? right with
              | none =>
                  simp [toOutput?, hright] at h
              | some rest =>
                  simp [toOutput?, hright] at h
                  cases h
                  rw [outputRight?_eq_some_map hright]
                  rfl
      | cons _ _ =>
          cases h

end Tape

namespace MachineDescription

theorem haltsWithOutputIn_output_unique {D : MachineDescription}
    {n : Nat} {w out₁ out₂ : Word Bool}
    (h₁ : D.HaltsWithOutputIn n w out₁)
    (h₂ : D.HaltsWithOutputIn n w out₂) :
    out₁ = out₂ := by
  exact Tape.output_injective (Eq.trans h₁.right.symm h₂.right)

end MachineDescription

/-!
## Finite acceptor programs
-/

structure FiniteAcceptorProgram where
  description : MachineDescription

namespace FiniteAcceptorProgram

def trace (P : FiniteAcceptorProgram) (w : Word Bool) (n : Nat) : Prop :=
  P.description.HaltsIn n w

def toStagedProgram (P : FiniteAcceptorProgram) :
    StagedProgram Bool Unit where
  run w n :=
    let final := P.description.runConfig n (P.description.initial w)
    if final.state = P.description.halt then some [] else none

def compile (P : FiniteAcceptorProgram) : MachineDescription :=
  P.description

theorem toStagedProgram_run_iff
    (P : FiniteAcceptorProgram) (w : Word Bool) (n : Nat) :
    P.toStagedProgram.run w n = some [] <-> P.trace w n := by
  constructor
  · intro h
    by_cases ht :
      (P.description.runConfig n (P.description.initial w)).state =
        P.description.halt
    · exact ht
    · simp [toStagedProgram, ht] at h
  · intro ht
    have hhalt :
        (P.description.runConfig n (P.description.initial w)).state =
          P.description.halt := by
      simpa [trace, MachineDescription.HaltsIn] using ht
    simp [toStagedProgram, hhalt]
    rfl

theorem compiledByDescription
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed) :
    ProgramCompiledByDescription P.toStagedProgram P.compile := by
  constructor
  · exact hD
  · intro w
    constructor
    · intro hhalt
      cases hhalt with
      | intro n hn =>
          exists n
          exact (toStagedProgram_run_iff P w n).mpr hn
    · intro hprog
      cases hprog with
      | intro n hn =>
          exists n
          exact (toStagedProgram_run_iff P w n).mp hn

theorem traceRecognizer_compiledByDescription
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed) :
    ProgramCompiledByDescription
      (TraceRecognizerProgram P.trace) P.compile := by
  classical
  constructor
  · exact hD
  · intro w
    constructor
    · intro hhalt
      cases hhalt with
      | intro n hn =>
          exact Exists.intro n
            (traceRecognizerProgram_run_of_trace
              (trace := P.trace) (w := w) (n := n)
              (by simpa [compile, trace] using hn))
    · intro hprog
      cases hprog with
      | intro n hn =>
          by_cases ht : P.trace w n
          · exact Exists.intro n (by simpa [compile, trace] using ht)
          · simp [TraceRecognizerProgram, ht] at hn

theorem traceRecognizer_programAcceptableByDescription
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (htrace : AcceptanceTrace P.trace L) :
    ProgramAcceptableByDescription L := by
  exists TraceRecognizerProgram P.trace
  exists P.compile
  constructor
  · exact traceRecognizerProgram_acceptsLanguage htrace
  · exact traceRecognizer_compiledByDescription P hD

theorem traceRecognizer_turingAcceptable
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (htrace : AcceptanceTrace P.trace L) :
    TuringAcceptable L :=
  programAcceptableByDescription_turingAcceptable
    (traceRecognizer_programAcceptableByDescription P hD htrace)

end FiniteAcceptorProgram

/-!
## Finite Boolean programs
-/

structure FiniteBoolProgram where
  description : MachineDescription

namespace FiniteBoolProgram

def toStagedProgram (P : FiniteBoolProgram) :
    StagedProgram Bool Bool where
  run w n :=
    let final := P.description.runConfig n (P.description.initial w)
    if final.state = P.description.halt ∧
        final.tape = Tape.output [true] then
      some [true]
    else if final.state = P.description.halt ∧
        final.tape = Tape.output [false] then
      some [false]
    else
      none

def compile (P : FiniteBoolProgram) : MachineDescription :=
  P.description

theorem toStagedProgram_run_true_of_halts
    {P : FiniteBoolProgram} {w : Word Bool} {n : Nat}
    (h : P.description.HaltsWithOutputIn n w [true]) :
    P.toStagedProgram.run w n = some [true] := by
  unfold MachineDescription.HaltsWithOutputIn at h
  simp [toStagedProgram, h]
  rfl

theorem toStagedProgram_run_false_of_halts
    {P : FiniteBoolProgram} {w : Word Bool} {n : Nat}
    (h : P.description.HaltsWithOutputIn n w [false]) :
    P.toStagedProgram.run w n = some [false] := by
  unfold MachineDescription.HaltsWithOutputIn at h
  have hnot :
      ¬((P.description.runConfig n (P.description.initial w)).state =
          P.description.halt ∧
        (P.description.runConfig n (P.description.initial w)).tape =
          Tape.output [true]) := by
    intro htrue
    have hEq := MachineDescription.haltsWithOutputIn_output_unique htrue h
    cases hEq
  have hTapeNe : Tape.output [false] ≠ Tape.output [true] := by
    intro htape
    have hEq := Tape.output_injective htape
    cases hEq
  simp [toStagedProgram, h, hTapeNe]
  rfl

theorem compiledByDescription
    (P : FiniteBoolProgram)
    (hD : P.description.WellFormed) :
    BoolProgramCompiledByDescription P.toStagedProgram P.compile := by
  constructor
  · exact hD
  · intro w b
    cases b
    · constructor
      · intro hhalt
        cases hhalt with
        | intro n hn =>
          exists n
          exact toStagedProgram_run_false_of_halts hn
      · intro hprog
        cases hprog with
        | intro n hn =>
            by_cases htrue :
              (P.description.runConfig n (P.description.initial w)).state =
                  P.description.halt ∧
                  (P.description.runConfig n (P.description.initial w)).tape =
                  Tape.output [true]
            · simp [toStagedProgram, htrue] at hn
              cases hn
            · by_cases hfalse :
                (P.description.runConfig n (P.description.initial w)).state =
                    P.description.halt ∧
                  (P.description.runConfig n (P.description.initial w)).tape =
                    Tape.output [false]
              · exact Exists.intro n hfalse
              · simp [toStagedProgram, htrue, hfalse] at hn
    · constructor
      · intro hhalt
        cases hhalt with
        | intro n hn =>
          exists n
          exact toStagedProgram_run_true_of_halts hn
      · intro hprog
        cases hprog with
        | intro n hn =>
            by_cases htrue :
              (P.description.runConfig n (P.description.initial w)).state =
                  P.description.halt ∧
                (P.description.runConfig n (P.description.initial w)).tape =
                  Tape.output [true]
            · exact Exists.intro n htrue
            · by_cases hfalse :
                (P.description.runConfig n (P.description.initial w)).state =
                    P.description.halt ∧
                  (P.description.runConfig n (P.description.initial w)).tape =
                    Tape.output [false]
              · have hTapeNe : Tape.output [false] ≠ Tape.output [true] := by
                  intro htape
                  have hEq := Tape.output_injective htape
                  cases hEq
                simp [toStagedProgram, hfalse, hTapeNe] at hn
                cases hn
              · simp [toStagedProgram, htrue, hfalse] at hn

theorem programBoolDecidableByDescription
    (P : FiniteBoolProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (hdecides : ProgramBoolDecides P.toStagedProgram L) :
    ProgramBoolDecidableByDescription L := by
  exists P.toStagedProgram
  exists P.compile
  exact And.intro hdecides (compiledByDescription P hD)

theorem turingDecidable
    (P : FiniteBoolProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (hdecides : ProgramBoolDecides P.toStagedProgram L) :
    TuringDecidable L :=
  programBoolDecidableByDescription_turingDecidable
    (programBoolDecidableByDescription P hD hdecides)

end FiniteBoolProgram

/-!
## Finite dovetailing programs

A finite dovetail program records the two finite trace recognizers and the
finite Boolean machine description that realizes the dovetailing staged
program.  The construction of that Boolean description is separate machine
engineering; once supplied, the bridge to recursive languages is concrete.
-/

structure FiniteDovetailProgram where
  accept : FiniteAcceptorProgram
  reject : FiniteAcceptorProgram
  decider : FiniteBoolProgram

namespace FiniteDovetailProgram

noncomputable def toStagedProgram (P : FiniteDovetailProgram) :
    StagedProgram Bool Bool :=
  DovetailProgram P.accept.trace P.reject.trace

def Compiled (P : FiniteDovetailProgram) : Prop :=
  BoolProgramCompiledByDescription P.toStagedProgram P.decider.compile

theorem programBoolDecidableByDescription
    (P : FiniteDovetailProgram)
    {L : Language Bool}
    (htraces :
      ComplementaryAcceptanceTraces P.accept.trace P.reject.trace L)
    (hcompiled : P.Compiled) :
    ProgramBoolDecidableByDescription L := by
  exists P.toStagedProgram
  exists P.decider.compile
  exact And.intro (dovetailProgram_decides htraces) hcompiled

theorem turingDecidable
    (P : FiniteDovetailProgram)
    {L : Language Bool}
    (htraces :
      ComplementaryAcceptanceTraces P.accept.trace P.reject.trace L)
    (hcompiled : P.Compiled) :
    TuringDecidable L :=
  programBoolDecidableByDescription_turingDecidable
    (programBoolDecidableByDescription P htraces hcompiled)

end FiniteDovetailProgram

/-!
## Finite partial unary range programs
-/

structure FinitePartialUnaryRangeProgram where
  description : MachineDescription

namespace FinitePartialUnaryRangeProgram

def encodeInput (w : Word Unit) : Word Bool :=
  EncodeWord (fun _ : Unit => true) w

def toStagedProgram (P : FinitePartialUnaryRangeProgram) :
    StagedProgram Unit Bool where
  run w n :=
    let final := P.description.runConfig n
      (P.description.initial (encodeInput w))
    if final.state = P.description.halt then
      Tape.toOutput? final.tape
    else
      none

def outputRange (P : FinitePartialUnaryRangeProgram) :
    Language Bool :=
  ProgramRangeLanguage P.toStagedProgram

def descriptionOutputRange (P : FinitePartialUnaryRangeProgram) :
    Language Bool :=
  fun out => exists w : Word Unit, exists n : Nat,
    P.description.HaltsWithOutputIn n (encodeInput w) out

theorem outputRange_equal_descriptionOutputRange
    (P : FinitePartialUnaryRangeProgram) :
    Language.Equal P.outputRange P.descriptionOutputRange := by
  intro out
  constructor
  · intro h
    cases h with
    | intro w hw =>
        cases hw with
        | intro n hn =>
            unfold toStagedProgram at hn
            simp only at hn
            by_cases hhalt :
              (P.description.runConfig n
                (P.description.initial (encodeInput w))).state =
                P.description.halt
            · have hout :
                Tape.toOutput?
                  (P.description.runConfig n
                    (P.description.initial (encodeInput w))).tape =
                    some out := by
                  simpa [hhalt] using hn
              have htape := Tape.toOutput?_eq_some_output hout
              exact Exists.intro w (Exists.intro n (And.intro hhalt htape))
            · simp [hhalt] at hn
  · intro h
    cases h with
    | intro w hw =>
        cases hw with
        | intro n hn =>
            exists w
            exists n
            unfold toStagedProgram
            simp [hn.left, hn.right, Tape.toOutput?_output]

end FinitePartialUnaryRangeProgram

end Computability
end FoC
