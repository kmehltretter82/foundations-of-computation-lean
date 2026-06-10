import FoC.Computability.Encoding
import FoC.Computability.MachineBuilder
import FoC.Computability.Program

set_option doc.verso true

/-!
# Description-backed program compilation

This module connects the concrete machine descriptions from
{module}`FoC.Computability.Encoding` with the staged-program layer from
{module}`FoC.Computability.Program`.

The compiler predicates here are deliberately explicit.  A staged program is
compiled only when a finite {lit}`MachineDescription` is supplied and proved
to realize the same halting or output behavior.  This avoids treating arbitrary
Lean functions as finitely encodable programs.  Names with
{lit}`Semantic...Assumption` mark theorem-shape assumptions over arbitrary
Lean objects; names with {lit}`FiniteSource...Construction` mark compiler
targets whose inputs are concrete finite data.

## Book coordinates

Used by:
- Chapter 5, Section 5.2: compiler principles for acceptors, Boolean deciders,
  and partial unary range/program descriptions.
- Chapter 5, Section 5.3: exact simulation between decoded descriptions and
  their compiled one-tape Turing machines.
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-!
## Exact simulation for compiled descriptions

Well-formed transition tables run in lockstep with their compiled
{name}`TuringMachine`.  The first direction follows the functional
interpreter; the reverse direction says a compiled transition step can only
come from a description-table transition.
-/

theorem lookupTransition_mem {D : MachineDescription}
    {source : Nat} {read : Option Bool} {t : TransitionDescription}
    (h : D.lookupTransition source read = some t) :
    t ∈ D.transitions := by
  unfold lookupTransition at h
  let p := Matches source read
  have hmem :
      forall l : List TransitionDescription,
        l.find? p = some t -> t ∈ l := by
    intro l
    induction l with
    | nil =>
        intro hnil
        simp at hnil
    | cons a rest ih =>
        intro hfind
        rw [List.find?_cons] at hfind
        cases hm : p a
        · simp [hm] at hfind
          have ht : t ∈ rest := ih hfind
          simp [ht]
        · simp [hm] at hfind
          cases hfind
          simp
  exact hmem D.transitions h

theorem stepConfig_state_bound {D : MachineDescription}
    {c d : Configuration}
    (hD : D.WellFormed)
    (hstep : D.stepConfig c = some d) :
    d.state < D.stateCount := by
  unfold stepConfig at hstep
  cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      rw [hlookup] at hstep
      cases hstep
  | some t =>
      rw [hlookup] at hstep
      cases hstep
      have htmem : t ∈ D.transitions := lookupTransition_mem hlookup
      exact (hD.right.right.right.left t htmem).right

theorem runConfig_of_stepConfig_none {D : MachineDescription}
    {c : Configuration}
    (hstep : D.stepConfig c = none) :
    forall n : Nat, D.runConfig n c = c := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n _ih =>
      simp [runConfig, hstep]

theorem runConfig_add (D : MachineDescription)
    (n m : Nat) (c : Configuration) :
    D.runConfig (n + m) c =
      D.runConfig m (D.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      simp [runConfig]
  | succ n ih =>
      rw [Nat.succ_add]
      simp [runConfig]
      cases hstep : D.stepConfig c with
      | none =>
          simp [runConfig_of_stepConfig_none hstep]
      | some next =>
          simp [ih next]

theorem firstReaches_halt_of_runConfig_eq
    {D : MachineDescription}
    (hD : D.HaltTransitionFree)
    {n : Nat} {c : Configuration} {T : Tape Bool}
    (hrun : D.runConfig n c = { state := D.halt, tape := T }) :
    exists m : Nat,
      m ≤ n ∧
        D.runConfig m c = { state := D.halt, tape := T } ∧
        forall k : Nat,
          k < m -> (D.runConfig k c).state ≠ D.halt := by
  induction n generalizing c with
  | zero =>
      exists 0
      simp [hrun]
  | succ n ih =>
      by_cases hcHalt : c.state = D.halt
      · have hc :
            c = { state := D.halt, tape := c.tape } := by
          cases c with
          | mk state tape =>
              simp at hcHalt ⊢
              exact hcHalt
        have hstable :
            D.runConfig (n + 1) c = c := by
          rw [hc]
          exact runConfig_halt hD c.tape (n + 1)
        have hcFinal : c = { state := D.halt, tape := T } := by
          rw [← hstable]
          exact hrun
        exists 0
        constructor
        · omega
        constructor
        · simp [hcFinal, runConfig]
        · intro k hk
          omega
      · cases hstep : D.stepConfig c with
        | none =>
            have hsame : D.runConfig (n + 1) c = c := by
              simp [runConfig, hstep]
            have hstate : c.state = D.halt := by
              have hfinal : c = { state := D.halt, tape := T } := by
                rw [← hsame]
                exact hrun
              simpa using congrArg (fun d : Configuration => d.state) hfinal
            exact False.elim (hcHalt hstate)
        | some next =>
            have hnext :
                D.runConfig n next = { state := D.halt, tape := T } := by
              simpa [runConfig, hstep] using hrun
            rcases ih hnext with ⟨m, hmle, hmrun, hmfirst⟩
            exists m + 1
            constructor
            · omega
            constructor
            · simp [runConfig, hstep, hmrun]
            · intro k hk
              cases k with
              | zero =>
                  simpa [runConfig] using hcHalt
              | succ j =>
                  have hj : j < m := by omega
                  simpa [runConfig, hstep] using hmfirst j hj

theorem runConfig_state_bound {D : MachineDescription}
    (hD : D.WellFormed) {n : Nat} {c : Configuration}
    (hc : c.state < D.stateCount) :
    (D.runConfig n c).state < D.stateCount := by
  induction n generalizing c with
  | zero =>
      exact hc
  | succ n ih =>
      change
        (match D.stepConfig c with
        | none => c
        | some next => D.runConfig n next).state < D.stateCount
      cases hstep : D.stepConfig c with
      | none =>
          exact hc
      | some _ =>
          exact ih (stepConfig_state_bound hD hstep)

theorem stepConfig_contextLength_mono {D : MachineDescription}
    {c d : Configuration}
    (hstep : D.stepConfig c = some d) :
    Tape.contextLength c.tape ≤ Tape.contextLength d.tape := by
  unfold stepConfig at hstep
  cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      rw [hlookup] at hstep
      cases hstep
  | some t =>
      rw [hlookup] at hstep
      cases hstep
      exact Tape.contextLength_move_write_ge t.move t.write c.tape

theorem runConfig_contextLength_mono
    (D : MachineDescription) (n : Nat) (c : Configuration) :
    Tape.contextLength c.tape ≤
      Tape.contextLength (D.runConfig n c).tape := by
  induction n generalizing c with
  | zero =>
      exact Nat.le_refl _
  | succ n ih =>
      change
        Tape.contextLength c.tape ≤
          Tape.contextLength
            (match D.stepConfig c with
            | none => c
            | some next => D.runConfig n next).tape
      cases hstep : D.stepConfig c with
      | none =>
          exact Nat.le_refl _
      | some next =>
          exact Nat.le_trans (stepConfig_contextLength_mono hstep)
            (ih next)

theorem runConfig_toTuringMachine_computes {D : MachineDescription}
    (hD : D.WellFormed) {n : Nat} {c : Configuration}
    (hc : c.state < D.stateCount) :
    TuringMachine.Computes D.toTuringMachine
      (D.toTMConfig c) (D.toTMConfig (D.runConfig n c)) := by
  induction n generalizing c with
  | zero =>
      exact TuringMachine.Computes.refl (D.toTMConfig c)
  | succ n ih =>
      change TuringMachine.Computes D.toTuringMachine (D.toTMConfig c)
        (D.toTMConfig
          (match D.stepConfig c with
          | none => c
          | some next => D.runConfig n next))
      cases hstep : D.stepConfig c with
      | none =>
          exact TuringMachine.Computes.refl (D.toTMConfig c)
      | some _ =>
          exact TuringMachine.Computes.step
            (MachineDescription.toTuringMachine_step_of_stepConfig
              (D := D)
              (hsource := Nat.lt_trans hc
                (Nat.lt_succ_self D.stateCount))
              hstep)
            (ih (stepConfig_state_bound hD hstep))

theorem toTuringMachine_step_to_stepConfig {D : MachineDescription}
    {c : Configuration}
    {e : TuringMachine.Configuration Bool (Fin (D.stateCount + 1))}
    (hc : c.state < D.stateCount)
    (hstep : TuringMachine.Step D.toTuringMachine (D.toTMConfig c) e) :
    exists d : Configuration, D.stepConfig c = some d ∧ e = D.toTMConfig d := by
  cases hstep with
  | mk haction =>
      change
        (match
          D.lookupTransition (D.stateOfNat c.state).val (Tape.read c.tape)
        with
        | none => none
        | some t => some (t.write, t.move, D.stateOfNat t.target)) =
          some _ at haction
      rw [stateOfNat_val_of_lt
        (Nat.lt_trans hc (Nat.lt_succ_self D.stateCount))] at haction
      cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
      | none =>
          rw [hlookup] at haction
          cases haction
      | some t =>
          rw [hlookup] at haction
          cases haction
          exists
            { state := t.target
              tape := Tape.move t.move (Tape.write t.write c.tape) }
          constructor
          · simp [stepConfig, hlookup]
          · rfl

theorem toTuringMachine_computesIn_to_runConfig {D : MachineDescription}
    (hD : D.WellFormed) {n : Nat} {c : Configuration}
    (hc : c.state < D.stateCount)
    {e : TuringMachine.Configuration Bool (Fin (D.stateCount + 1))}
    (hcomp : TuringMachine.ComputesIn D.toTuringMachine n (D.toTMConfig c) e) :
    e = D.toTMConfig (D.runConfig n c) := by
  induction n generalizing c e with
  | zero =>
      cases hcomp
      rfl
  | succ n ih =>
      cases hcomp with
      | succ hstep hrest =>
          cases toTuringMachine_step_to_stepConfig hc hstep with
          | intro d hd =>
              cases hd.right
              have hdBound : d.state < D.stateCount :=
                stepConfig_state_bound hD hd.left
              have ihd := ih hdBound hrest
              change _ = D.toTMConfig
                (match D.stepConfig c with
                | none => c
                | some next => D.runConfig n next)
              rw [hd.left]
              exact ihd

/-!
## Output semantics for descriptions
-/

def HaltsWithOutputIn (D : MachineDescription)
    (n : Nat) (w out : Word Bool) : Prop :=
  let final := D.runConfig n (D.initial w)
  final.state = D.halt ∧ Tape.normalizedOutput final.tape = out

def HaltsWithExactOutputIn (D : MachineDescription)
    (n : Nat) (w out : Word Bool) : Prop :=
  let final := D.runConfig n (D.initial w)
  final.state = D.halt ∧ final.tape = Tape.output out

def HaltsWithTapeIn (D : MachineDescription)
    (n : Nat) (w : Word Bool) (T : Tape Bool) : Prop :=
  let final := D.runConfig n (D.initial w)
  final.state = D.halt ∧ final.tape = T

def HaltsWithOutput (D : MachineDescription)
    (w out : Word Bool) : Prop :=
  exists n : Nat, D.HaltsWithOutputIn n w out

def HaltsWithExactOutput (D : MachineDescription)
    (w out : Word Bool) : Prop :=
  exists n : Nat, D.HaltsWithExactOutputIn n w out

def HaltsWithTape (D : MachineDescription)
    (w : Word Bool) (T : Tape Bool) : Prop :=
  exists n : Nat, D.HaltsWithTapeIn n w T

theorem haltsWithExactOutputIn_iff_haltsWithTapeIn_output
    {D : MachineDescription} {n : Nat} {w out : Word Bool} :
    D.HaltsWithExactOutputIn n w out <->
      D.HaltsWithTapeIn n w (Tape.output out) := by
  rfl

theorem haltsWithExactOutput_iff_haltsWithTape_output
    {D : MachineDescription} {w out : Word Bool} :
    D.HaltsWithExactOutput w out <->
      D.HaltsWithTape w (Tape.output out) := by
  rfl

theorem not_haltsWithExactOutput_empty_of_input_contextLength_pos
    {D : MachineDescription} {w : Word Bool}
    (hctx : 0 < Tape.contextLength (Tape.input w)) :
    ¬ D.HaltsWithExactOutput w [] := by
  intro hhalt
  rcases hhalt with ⟨n, hn⟩
  have hmono :=
    runConfig_contextLength_mono D n (D.initial w)
  have hfinalCtx :
      Tape.contextLength
          (D.runConfig n (D.initial w)).tape =
        0 := by
    simpa [HaltsWithExactOutputIn, Tape.output_empty,
      Tape.contextLength_blank] using congrArg
        (fun T : Tape Bool => Tape.contextLength T) hn.right
  have hinputCtx :
      Tape.contextLength (D.initial w).tape =
        Tape.contextLength (Tape.input w) := rfl
  omega

theorem haltsWithOutputIn_of_haltsWithExactOutputIn
    {D : MachineDescription} {n : Nat} {w out : Word Bool}
    (h : D.HaltsWithExactOutputIn n w out) :
    D.HaltsWithOutputIn n w out := by
  rcases h with ⟨hhalt, htape⟩
  exact ⟨hhalt, Tape.normalizedOutput_of_eq_output htape⟩

theorem haltsWithOutput_of_haltsWithExactOutput
    {D : MachineDescription} {w out : Word Bool}
    (h : D.HaltsWithExactOutput w out) :
    D.HaltsWithOutput w out := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, haltsWithOutputIn_of_haltsWithExactOutputIn hn⟩

def ExactOutputRealizes
    (D : MachineDescription) (f : Word Bool -> Word Bool) : Prop :=
  D.WellFormed ∧ forall w : Word Bool, D.HaltsWithExactOutput w (f w)

def ExactOutputComposable
    (A B C : MachineDescription) : Prop :=
  C.WellFormed ∧
    forall w mid out : Word Bool,
      A.HaltsWithExactOutput w mid ->
      B.HaltsWithExactOutput mid out ->
        C.HaltsWithExactOutput w out

theorem ExactOutputRealizes.toOutputRealizes
    {D : MachineDescription} {f : Word Bool -> Word Bool}
    (h : D.ExactOutputRealizes f) :
    D.WellFormed ∧ forall w : Word Bool, D.HaltsWithOutput w (f w) := by
  constructor
  · exact h.left
  · intro w
    exact haltsWithOutput_of_haltsWithExactOutput (h.right w)

theorem ExactOutputComposable.realizes_comp
    {A B C : MachineDescription}
    {f g : Word Bool -> Word Bool}
    (hcomp : ExactOutputComposable A B C)
    (hA : A.ExactOutputRealizes f)
    (hB : B.ExactOutputRealizes g) :
    C.ExactOutputRealizes (fun w => g (f w)) := by
  constructor
  · exact hcomp.left
  · intro w
    exact hcomp.right w (f w) (g (f w)) (hA.right w)
      (hB.right (f w))

def ExactIdentityDescription : MachineDescription where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem exactIdentityDescription_wellFormed :
    ExactIdentityDescription.WellFormed := by
  simp [ExactIdentityDescription, WellFormed, Deterministic]

theorem exactIdentityDescription_haltTransitionFree :
    ExactIdentityDescription.HaltTransitionFree := by
  intro t ht
  simp [ExactIdentityDescription] at ht

theorem exactIdentityDescription_haltsWithExactOutputIn
    (w : Word Bool) :
    ExactIdentityDescription.HaltsWithExactOutputIn 0 w w := by
  constructor
  · rfl
  · rfl

theorem exactIdentityDescription_exactOutputRealizes :
    ExactIdentityDescription.ExactOutputRealizes id := by
  constructor
  · exact exactIdentityDescription_wellFormed
  · intro w
    exact ⟨0, exactIdentityDescription_haltsWithExactOutputIn w⟩

theorem exactIdentityDescription_runConfig_initial
    (n : Nat) (w : Word Bool) :
    ExactIdentityDescription.runConfig n
        (ExactIdentityDescription.initial w) =
      ExactIdentityDescription.initial w := by
  cases n <;>
    simp [runConfig, stepConfig, lookupTransition,
      ExactIdentityDescription]

theorem exactIdentityDescription_haltsWithExactOutput_iff
    (w out : Word Bool) :
    ExactIdentityDescription.HaltsWithExactOutput w out <-> out = w := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    have htape : Tape.input w = Tape.output out := by
      simpa [HaltsWithExactOutputIn,
        exactIdentityDescription_runConfig_initial] using hn.right
    have hw : w = out := Tape.input_injective
      (by simpa [Tape.output] using htape)
    exact hw.symm
  · intro h
    rw [h]
    exact ⟨0, exactIdentityDescription_haltsWithExactOutputIn w⟩

/-!
## Normalized-output transducers

Exact tape-output compilation is too strict for destructive code-word
operations because the tape window remembers blank context.  The finite
transducers below target normalized output: they may leave blank context on the
tape, but the visible code word is exactly the desired output.
-/

def EraseRightDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 0 (some false) none Direction.right 0
    , transition 0 (some true) none Direction.right 0 ]

def eraseRightTape (erased : Nat) : Word Bool -> Tape Bool
  | [] =>
      { left := List.replicate erased none
        head := none
        right := [] }
  | b :: rest =>
      { left := List.replicate erased none
        head := some b
        right := rest.map some }

theorem eraseRightDescription_wellFormed :
    EraseRightDescription.WellFormed := by
  constructor
  · simp [EraseRightDescription]
  constructor
  · simp [EraseRightDescription]
  constructor
  · simp [EraseRightDescription]
  constructor
  · intro t ht
    simp [EraseRightDescription, transition,
      TransitionDescription.WellFormed] at ht ⊢
    rcases ht with rfl | rfl | rfl <;> simp
  · intro t u ht hu hkey
    simp [EraseRightDescription, transition] at ht hu
    rcases ht with rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl <;>
        simp [TransitionDescription.SameKey,
          TransitionDescription.SameAction] at hkey ⊢

theorem eraseRightDescription_haltTransitionFree :
    EraseRightDescription.HaltTransitionFree := by
  intro t ht
  simp [EraseRightDescription, transition] at ht
  rcases ht with rfl | rfl | rfl <;>
    simp [EraseRightDescription]

theorem eraseRightTape_move_nonempty
    (erased : Nat) (b : Bool) (rest : Word Bool) :
    Tape.move Direction.right
        (Tape.write none (eraseRightTape erased (b :: rest))) =
      eraseRightTape (erased + 1) rest := by
  cases rest with
  | nil =>
      simp [eraseRightTape, Tape.move, Tape.moveRight, Tape.write,
        List.replicate_succ]
  | cons c tail =>
      simp [eraseRightTape, Tape.move, Tape.moveRight, Tape.write,
        List.replicate_succ]

theorem eraseRightTape_move_empty (erased : Nat) :
    Tape.move Direction.right
        (Tape.write none (eraseRightTape erased [])) =
      eraseRightTape (erased + 1) [] := by
  simp [eraseRightTape, Tape.move, Tape.moveRight, Tape.write,
    List.replicate_succ]

theorem eraseRightTape_zero_eq_input (w : Word Bool) :
    eraseRightTape 0 w = Tape.input w := by
  cases w <;> rfl

theorem eraseRightDescription_step_nonempty
    (erased : Nat) (b : Bool) (rest : Word Bool) :
    EraseRightDescription.stepConfig
        { state := 0, tape := eraseRightTape erased (b :: rest) } =
      some { state := 0, tape := eraseRightTape (erased + 1) rest } := by
  cases b <;>
    cases rest <;>
      simp [EraseRightDescription, stepConfig, lookupTransition,
        Matches, transition, Tape.read, eraseRightTape,
        Tape.write, Tape.move, Tape.moveRight, List.replicate_succ]

theorem eraseRightDescription_step_empty
    (erased : Nat) :
    EraseRightDescription.stepConfig
        { state := 0, tape := eraseRightTape erased [] } =
      some { state := 1, tape := eraseRightTape (erased + 1) [] } := by
  simp [EraseRightDescription, stepConfig, lookupTransition,
    Matches, transition, Tape.read, eraseRightTape,
    Tape.write, Tape.move, Tape.moveRight, List.replicate_succ]

theorem eraseRightDescription_run_scan
    (erased : Nat) (w : Word Bool) :
    EraseRightDescription.runConfig w.length
        { state := 0, tape := eraseRightTape erased w } =
      { state := 0, tape := eraseRightTape (erased + w.length) [] } := by
  induction w generalizing erased with
  | nil =>
      simp [runConfig]
  | cons b rest ih =>
      simp [runConfig, eraseRightDescription_step_nonempty, ih,
        List.length_cons]
      have hlen :
          erased + 1 + rest.length =
            erased + (rest.length + 1) := by
        omega
      rw [hlen]

theorem eraseRightDescription_run_halt (w : Word Bool) :
    EraseRightDescription.runConfig (w.length + 1)
        (EraseRightDescription.initial w) =
      { state := 1, tape := eraseRightTape (w.length + 1) [] } := by
  rw [runConfig_add]
  have hscan :
      EraseRightDescription.runConfig w.length
          (EraseRightDescription.initial w) =
        { state := 0, tape := eraseRightTape w.length [] } := by
    simpa [initial, EraseRightDescription, eraseRightTape_zero_eq_input,
      Nat.zero_add] using
      eraseRightDescription_run_scan 0 w
  rw [hscan]
  simp [runConfig, eraseRightDescription_step_empty]

theorem eraseRightTape_normalizedOutput_empty (erased : Nat) :
    Tape.normalizedOutput (eraseRightTape erased []) = [] := by
  induction erased with
  | zero =>
      rfl
  | succ erased ih =>
    simp [eraseRightTape, Tape.normalizedOutput, Tape.cells,
        List.replicate_succ]

theorem eraseRightDescription_haltsWithOutput_empty
    (w : Word Bool) :
    EraseRightDescription.HaltsWithOutput w [] := by
  exists w.length + 1
  constructor
  · rw [eraseRightDescription_run_halt]
    simp [EraseRightDescription]
  · rw [eraseRightDescription_run_halt]
    exact eraseRightTape_normalizedOutput_empty (w.length + 1)

def BoolOutputDescription (b : Bool) : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none (some b) Direction.right 1
    , transition 0 (some false) none Direction.right 0
    , transition 0 (some true) none Direction.right 0 ]

theorem boolOutputDescription_wellFormed (b : Bool) :
    (BoolOutputDescription b).WellFormed := by
  constructor
  · simp [BoolOutputDescription]
  constructor
  · simp [BoolOutputDescription]
  constructor
  · simp [BoolOutputDescription]
  constructor
  · intro t ht
    simp [BoolOutputDescription, transition,
      TransitionDescription.WellFormed] at ht ⊢
    rcases ht with rfl | rfl | rfl <;> simp
  · intro t u ht hu hkey
    simp [BoolOutputDescription, transition] at ht hu
    rcases ht with rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl <;>
        simp [TransitionDescription.SameKey,
          TransitionDescription.SameAction] at hkey ⊢

theorem boolOutputDescription_haltTransitionFree (b : Bool) :
    (BoolOutputDescription b).HaltTransitionFree := by
  intro t ht
  simp [BoolOutputDescription, transition] at ht
  rcases ht with rfl | rfl | rfl <;>
    simp [BoolOutputDescription]

theorem boolOutputDescription_step_nonempty
    (out : Bool) (erased : Nat) (b : Bool) (rest : Word Bool) :
    (BoolOutputDescription out).stepConfig
        { state := 0, tape := eraseRightTape erased (b :: rest) } =
      some { state := 0, tape := eraseRightTape (erased + 1) rest } := by
  cases b <;>
    cases rest <;>
      simp [BoolOutputDescription, stepConfig, lookupTransition,
        Matches, transition, Tape.read, eraseRightTape,
        Tape.write, Tape.move, Tape.moveRight, List.replicate_succ]

def boolOutputTape (erased : Nat) (b : Bool) : Tape Bool :=
  { left := some b :: List.replicate erased none
    head := none
    right := [] }

theorem boolOutputDescription_step_empty
    (out : Bool) (erased : Nat) :
    (BoolOutputDescription out).stepConfig
        { state := 0, tape := eraseRightTape erased [] } =
      some { state := 1, tape := boolOutputTape erased out } := by
  simp [BoolOutputDescription, stepConfig, lookupTransition,
    Matches, transition, Tape.read, eraseRightTape, boolOutputTape,
    Tape.write, Tape.move, Tape.moveRight]

theorem boolOutputDescription_run_scan
    (out : Bool) (erased : Nat) (w : Word Bool) :
    (BoolOutputDescription out).runConfig w.length
        { state := 0, tape := eraseRightTape erased w } =
      { state := 0, tape := eraseRightTape (erased + w.length) [] } := by
  induction w generalizing erased with
  | nil =>
      simp [runConfig]
  | cons b rest ih =>
    simp [runConfig, boolOutputDescription_step_nonempty, ih,
      List.length_cons]
    have hlen :
        erased + 1 + rest.length =
          erased + (rest.length + 1) := by
      omega
    rw [hlen]

theorem boolOutputDescription_run_halt
    (out : Bool) (w : Word Bool) :
    (BoolOutputDescription out).runConfig (w.length + 1)
        ((BoolOutputDescription out).initial w) =
      { state := 1, tape := boolOutputTape w.length out } := by
  rw [runConfig_add]
  have hscan :
      (BoolOutputDescription out).runConfig w.length
          ((BoolOutputDescription out).initial w) =
        { state := 0, tape := eraseRightTape w.length [] } := by
    simpa [initial, BoolOutputDescription, eraseRightTape_zero_eq_input,
      Nat.zero_add] using
      boolOutputDescription_run_scan out 0 w
  rw [hscan]
  simp [runConfig, boolOutputDescription_step_empty]

theorem boolOutputTape_normalizedOutput
    (erased : Nat) (b : Bool) :
    Tape.normalizedOutput (boolOutputTape erased b) = [b] := by
  induction erased with
  | zero =>
      rfl
  | succ erased ih =>
      simp [boolOutputTape, Tape.normalizedOutput, Tape.cells,
        List.replicate_succ]

theorem boolOutputDescription_haltsWithOutput
    (b : Bool) (w : Word Bool) :
    (BoolOutputDescription b).HaltsWithOutput w [b] := by
  exists w.length + 1
  constructor
  · rw [boolOutputDescription_run_halt]
    simp [BoolOutputDescription]
  · rw [boolOutputDescription_run_halt]
    exact boolOutputTape_normalizedOutput w.length b

/-!
## Code-symbol append transducers

The next finite machine is a first transition-level emitter for encoded
{lit}`MachineCodeSymbol` words. It scans to the first blank on the right of the
Boolean input, writes four fixed bits, and halts with the normalized output
extended by those bits.  Instantiating the four bits with
{name}`encodeCodeSymbolAsInput` realizes the one-symbol
{name}`MachineDescription.TapeCodePrimitive.append` primitive for one fixed
code symbol.
-/

def appendRightScanTape
    (leftRev remaining : Word Bool) : Tape Bool :=
  match remaining with
  | [] =>
      { left := leftRev.map some
        head := none
        right := [] }
  | b :: rest =>
      { left := leftRev.map some
        head := some b
        right := rest.map some }

def appendRightWriteTape
    (leftRev written : Word Bool) : Tape Bool :=
  { left := (List.append written.reverse leftRev).map some
    head := none
    right := [] }

def AppendFixedFourBitsRightDescription
    (b0 b1 b2 b3 : Bool) : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 none (some b0) Direction.right 1
    , transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 1 none (some b1) Direction.right 2
    , transition 2 none (some b2) Direction.right 3
    , transition 3 none (some b3) Direction.right 4 ]

def AppendCodeSymbolRightDescription
    (symbol : MachineCodeSymbol) : MachineDescription :=
  match MachineDescription.encodeCodeSymbolAsInput symbol with
  | [b0, b1, b2, b3] =>
      AppendFixedFourBitsRightDescription b0 b1 b2 b3
  | _ => ExactIdentityDescription

theorem appendFixedFourBitsRightDescription_wellFormed
    (b0 b1 b2 b3 : Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).WellFormed := by
  constructor
  · simp [AppendFixedFourBitsRightDescription]
  constructor
  · simp [AppendFixedFourBitsRightDescription]
  constructor
  · simp [AppendFixedFourBitsRightDescription]
  constructor
  · intro t ht
    simp [AppendFixedFourBitsRightDescription, transition,
      TransitionDescription.WellFormed] at ht ⊢
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro t u ht hu hkey
    simp [AppendFixedFourBitsRightDescription, transition] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [TransitionDescription.SameKey,
          TransitionDescription.SameAction] at hkey ⊢

theorem appendFixedFourBitsRightDescription_haltTransitionFree
    (b0 b1 b2 b3 : Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).HaltTransitionFree := by
  intro t ht
  simp [AppendFixedFourBitsRightDescription, transition] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AppendFixedFourBitsRightDescription]

theorem appendCodeSymbolRightDescription_wellFormed
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolRightDescription symbol).WellFormed := by
  cases symbol <;>
    exact appendFixedFourBitsRightDescription_wellFormed _ _ _ _

theorem appendCodeSymbolRightDescription_haltTransitionFree
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolRightDescription symbol).HaltTransitionFree := by
  cases symbol <;>
    exact appendFixedFourBitsRightDescription_haltTransitionFree _ _ _ _

theorem appendRightScanTape_nil_eq_input
    (w : Word Bool) :
    appendRightScanTape [] w = Tape.input w := by
  cases w <;> rfl

theorem appendFixedFourBitsRightDescription_step_scan_nonempty
    (b0 b1 b2 b3 : Bool)
    (leftRev : Word Bool) (b : Bool) (rest : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).stepConfig
        { state := 0, tape := appendRightScanTape leftRev (b :: rest) } =
      some { state := 0, tape := appendRightScanTape (b :: leftRev) rest } := by
  cases b <;>
    cases rest <;>
      simp [AppendFixedFourBitsRightDescription, stepConfig,
        lookupTransition, Matches, transition, Tape.read,
        appendRightScanTape, Tape.write, Tape.move, Tape.moveRight]

theorem appendFixedFourBitsRightDescription_step_scan_empty
    (b0 b1 b2 b3 : Bool) (leftRev : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).stepConfig
        { state := 0, tape := appendRightScanTape leftRev [] } =
      some { state := 1, tape := appendRightWriteTape leftRev [b0] } := by
  simp [AppendFixedFourBitsRightDescription, stepConfig,
    lookupTransition, Matches, transition, Tape.read,
    appendRightScanTape, appendRightWriteTape, Tape.write, Tape.move,
    Tape.moveRight]

theorem appendFixedFourBitsRightDescription_step_write_one
    (b0 b1 b2 b3 : Bool) (leftRev : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).stepConfig
        { state := 1, tape := appendRightWriteTape leftRev [b0] } =
      some { state := 2, tape := appendRightWriteTape leftRev [b0, b1] } := by
  simp [AppendFixedFourBitsRightDescription, stepConfig,
    lookupTransition, Matches, transition, Tape.read,
    appendRightWriteTape, Tape.write, Tape.move, Tape.moveRight]

theorem appendFixedFourBitsRightDescription_step_write_two
    (b0 b1 b2 b3 : Bool) (leftRev : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).stepConfig
        { state := 2, tape := appendRightWriteTape leftRev [b0, b1] } =
      some { state := 3, tape := appendRightWriteTape leftRev [b0, b1, b2] } := by
  simp [AppendFixedFourBitsRightDescription, stepConfig,
    lookupTransition, Matches, transition, Tape.read,
    appendRightWriteTape, Tape.write, Tape.move, Tape.moveRight]

theorem appendFixedFourBitsRightDescription_step_write_three
    (b0 b1 b2 b3 : Bool) (leftRev : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).stepConfig
        { state := 3, tape := appendRightWriteTape leftRev [b0, b1, b2] } =
      some
        { state := 4
          tape := appendRightWriteTape leftRev [b0, b1, b2, b3] } := by
  simp [AppendFixedFourBitsRightDescription, stepConfig,
    lookupTransition, Matches, transition, Tape.read,
    appendRightWriteTape, Tape.write, Tape.move, Tape.moveRight]

theorem appendFixedFourBitsRightDescription_run_scan
    (b0 b1 b2 b3 : Bool)
    (leftRev remaining : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).runConfig
        remaining.length
        { state := 0, tape := appendRightScanTape leftRev remaining } =
      { state := 0
        tape :=
          appendRightScanTape (List.append remaining.reverse leftRev) [] } := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [runConfig]
  | cons b rest ih =>
    simp [runConfig,
      appendFixedFourBitsRightDescription_step_scan_nonempty, ih,
      List.append_assoc]

theorem appendFixedFourBitsRightDescription_run_write
    (b0 b1 b2 b3 : Bool) (leftRev : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).runConfig 4
        { state := 0, tape := appendRightScanTape leftRev [] } =
      { state := 4
        tape := appendRightWriteTape leftRev [b0, b1, b2, b3] } := by
  simp [runConfig,
    appendFixedFourBitsRightDescription_step_scan_empty,
    appendFixedFourBitsRightDescription_step_write_one,
    appendFixedFourBitsRightDescription_step_write_two,
    appendFixedFourBitsRightDescription_step_write_three]

theorem appendFixedFourBitsRightDescription_run_halt
    (b0 b1 b2 b3 : Bool) (w : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).runConfig
        (w.length + 4)
        ((AppendFixedFourBitsRightDescription b0 b1 b2 b3).initial w) =
      { state := 4
        tape := appendRightWriteTape w.reverse [b0, b1, b2, b3] } := by
  rw [runConfig_add]
  have hscan :
      (AppendFixedFourBitsRightDescription b0 b1 b2 b3).runConfig
          w.length
          ((AppendFixedFourBitsRightDescription b0 b1 b2 b3).initial w) =
        { state := 0, tape := appendRightScanTape w.reverse [] } := by
    simpa [initial, AppendFixedFourBitsRightDescription,
      appendRightScanTape_nil_eq_input] using
      appendFixedFourBitsRightDescription_run_scan
        b0 b1 b2 b3 [] w
  rw [hscan]
  exact appendFixedFourBitsRightDescription_run_write b0 b1 b2 b3 w.reverse

theorem appendRightWriteTape_normalizedOutput
    (leftRev written : Word Bool) :
    Tape.normalizedOutput (appendRightWriteTape leftRev written) =
      List.append leftRev.reverse written := by
  have hfilter :
      forall xs : Word Bool,
        List.filterMap
            ((fun cell : Option Bool => cell) ∘
              (fun b : Bool => some b)) xs = xs := by
    intro xs
    induction xs with
    | nil =>
        rfl
    | cons b rest ih =>
        simp [Function.comp, ih]
  simp [appendRightWriteTape, Tape.normalizedOutput, Tape.cells,
    List.filterMap_append, List.reverse_append, hfilter]

theorem appendFixedFourBitsRightDescription_haltsWithOutput_append
    (b0 b1 b2 b3 : Bool) (w : Word Bool) :
    (AppendFixedFourBitsRightDescription b0 b1 b2 b3).HaltsWithOutput
        w (List.append w [b0, b1, b2, b3]) := by
  exists w.length + 4
  constructor
  · rw [appendFixedFourBitsRightDescription_run_halt]
    simp [AppendFixedFourBitsRightDescription]
  · rw [appendFixedFourBitsRightDescription_run_halt,
      appendRightWriteTape_normalizedOutput]
    simp

theorem appendCodeSymbolRightDescription_haltsWithOutput_append
    (symbol : MachineCodeSymbol) (w : Word Bool) :
    (AppendCodeSymbolRightDescription symbol).HaltsWithOutput
        w
        (List.append w
          (MachineDescription.encodeCodeSymbolAsInput symbol)) := by
  cases symbol
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := false) (b1 := false) (b2 := false) (b3 := false) w
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := false) (b1 := false) (b2 := false) (b3 := true) w
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := false) (b1 := false) (b2 := true) (b3 := false) w
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := false) (b1 := false) (b2 := true) (b3 := true) w
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := false) (b1 := true) (b2 := false) (b3 := false) w
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := false) (b1 := true) (b2 := false) (b3 := true) w
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := false) (b1 := true) (b2 := true) (b3 := false) w
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := false) (b1 := true) (b2 := true) (b3 := true) w
  · simpa [AppendCodeSymbolRightDescription,
      MachineDescription.encodeCodeSymbolAsInput] using
      appendFixedFourBitsRightDescription_haltsWithOutput_append
        (b0 := true) (b1 := false) (b2 := false) (b3 := false) w

theorem toTuringMachine_haltsOnInput_iff {D : MachineDescription}
    (hD : D.WellFormed) (w : Word Bool) :
    TuringMachine.HaltsOnInput D.toTuringMachine w <-> D.HaltsOnInput w := by
  constructor
  · intro htm
    cases htm with
    | intro final hfinal =>
        cases TuringMachine.computes_to_computesIn hfinal.left with
        | intro n hn =>
            have hrun := toTuringMachine_computesIn_to_runConfig
              (D := D) hD (n := n) (c := D.initial w)
              hD.right.left hn
            have hhalt := hfinal.right
            rw [hrun] at hhalt
            change D.stateOfNat (D.runConfig n (D.initial w)).state =
              D.stateOfNat D.halt at hhalt
            have hval := congrArg Fin.val hhalt
            rw [stateOfNat_val_of_lt
                (Nat.lt_trans
                  (runConfig_state_bound hD hD.right.left)
                  (Nat.lt_succ_self D.stateCount)),
              stateOfNat_val_of_lt
                (Nat.lt_trans hD.right.right.left
                  (Nat.lt_succ_self D.stateCount))] at hval
            exact Exists.intro n hval
  · intro hd
    cases hd with
    | intro n hn =>
        let final := D.runConfig n (D.initial w)
        exists D.toTMConfig final
        constructor
        · exact runConfig_toTuringMachine_computes
            (D := D) hD (n := n) (c := D.initial w) hD.right.left
        · change D.stateOfNat final.state = D.stateOfNat D.halt
          rw [hn]

theorem toTuringMachine_haltsWithOutput_iff {D : MachineDescription}
    (hD : D.WellFormed) (w out : Word Bool) :
    TuringMachine.HaltsWithOutput D.toTuringMachine w out <->
      D.HaltsWithOutput w out := by
  constructor
  · intro htm
    cases htm with
    | intro final hfinal =>
        cases TuringMachine.computes_to_computesIn hfinal.left with
        | intro n hn =>
            have hrun := toTuringMachine_computesIn_to_runConfig
              (D := D) hD (n := n) (c := D.initial w)
              hD.right.left hn
            have hhalt := hfinal.right.left
            have htape := hfinal.right.right
            rw [hrun] at hhalt htape
            change D.stateOfNat (D.runConfig n (D.initial w)).state =
              D.stateOfNat D.halt at hhalt
            have hval := congrArg Fin.val hhalt
            rw [stateOfNat_val_of_lt
                (Nat.lt_trans
                  (runConfig_state_bound hD hD.right.left)
                  (Nat.lt_succ_self D.stateCount)),
              stateOfNat_val_of_lt
                (Nat.lt_trans hD.right.right.left
                  (Nat.lt_succ_self D.stateCount))] at hval
            exact Exists.intro n (And.intro hval htape)
  · intro hd
    cases hd with
    | intro n hn =>
        let final := D.runConfig n (D.initial w)
        exists D.toTMConfig final
        constructor
        · exact runConfig_toTuringMachine_computes
            (D := D) hD (n := n) (c := D.initial w) hD.right.left
        · constructor
          · change D.stateOfNat final.state = D.stateOfNat D.halt
            rw [hn.left]
          · change Tape.normalizedOutput final.tape = out
            exact hn.right

end MachineDescription

/-!
## Description-backed language recognition and decision
-/

def MachineDescriptionAcceptsLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.WellFormed ∧ forall w : Word Bool, D.HaltsOnInput w <-> w ∈ L

def MachineDescriptionDecidesLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool,
      (w ∈ L -> D.HaltsWithOutput w [true]) ∧
        (¬ w ∈ L -> D.HaltsWithOutput w [false])

theorem machineDescriptionAcceptsLanguage_turingAcceptable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionAcceptsLanguage D L) :
    TuringAcceptable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  intro w
  rw [encodeWord_id]
  exact Iff.trans (MachineDescription.toTuringMachine_haltsOnInput_iff
    h.left w) (h.right w)

theorem machineDescriptionDecidesLanguage_turingDecidable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionDecidesLanguage D L) :
    TuringDecidable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  exists false
  exists true
  intro w
  constructor
  · intro hw
    rw [encodeWord_id]
    exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
      h.left w [true]).mpr ((h.right w).left hw)
  · intro hw
    rw [encodeWord_id]
    exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
      h.left w [false]).mpr ((h.right w).right hw)

/-!
## Staged-program compiler predicates
-/

def ProgramCompiledByDescription
    (P : StagedProgram Bool Unit) (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool,
      D.HaltsOnInput w <-> ProgramHaltsWithOutput P w []

theorem programCompiledByDescription_of_same_accepted_language
    {P Q : StagedProgram Bool Unit} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramAcceptsLanguage P L)
    (hQ : ProgramAcceptsLanguage Q L)
    (hcompile : ProgramCompiledByDescription P D) :
    ProgramCompiledByDescription Q D := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w)
      (Iff.trans (hP w) (Iff.symm (hQ w)))

def BoolProgramCompiledByDescription
    (P : StagedProgram Bool Bool) (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      D.HaltsWithOutput w [b] <-> ProgramHaltsWithOutput P w [b]

def ProgramAcceptableByDescription (L : Language Bool) : Prop :=
  exists P : StagedProgram Bool Unit, exists D : MachineDescription,
    ProgramAcceptsLanguage P L ∧ ProgramCompiledByDescription P D

def ProgramBoolDecidableByDescription (L : Language Bool) : Prop :=
  exists P : StagedProgram Bool Bool, exists D : MachineDescription,
    ProgramBoolDecides P L ∧ BoolProgramCompiledByDescription P D

theorem programCompiledByDescription_acceptsLanguage
    {P : StagedProgram Bool Unit} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramAcceptsLanguage P L)
    (hcompile : ProgramCompiledByDescription P D) :
    MachineDescriptionAcceptsLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w) (hP w)

theorem boolProgramCompiledByDescription_decidesLanguage
    {P : StagedProgram Bool Bool} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramBoolDecides P L)
    (hcompile : BoolProgramCompiledByDescription P D) :
    MachineDescriptionDecidesLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    constructor
    · intro hw
      exact (hcompile.right w true).mpr ((hP.left w).mpr hw)
    · intro hw
      exact (hcompile.right w false).mpr ((hP.right w).mpr hw)

theorem programAcceptableByDescription_turingAcceptable
    {L : Language Bool}
    (h : ProgramAcceptableByDescription L) :
    TuringAcceptable L := by
  cases h with
  | intro P hP =>
      cases hP with
      | intro D hD =>
          exact machineDescriptionAcceptsLanguage_turingAcceptable
            (programCompiledByDescription_acceptsLanguage hD.left hD.right)

theorem programBoolDecidableByDescription_turingDecidable
    {L : Language Bool}
    (h : ProgramBoolDecidableByDescription L) :
    TuringDecidable L := by
  cases h with
  | intro P hP =>
      cases hP with
      | intro D hD =>
          exact machineDescriptionDecidesLanguage_turingDecidable
            (boolProgramCompiledByDescription_decidesLanguage hD.left hD.right)

def DescriptionProgramAcceptorCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Unit,
    exists D : MachineDescription, ProgramCompiledByDescription P D

/-
The next aliases separate semantic compiler assumptions from finite-source
compiler targets.  A semantic assumption quantifies over arbitrary Lean staged
programs or traces.  A finite-source construction has concrete finite data as
input, such as a supplied {name}`MachineDescription`.
-/

def SemanticDescriptionAcceptorCompilerAssumption : Prop :=
  DescriptionProgramAcceptorCompilationPrinciple

theorem programAcceptableByDescription_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple)
    {L : Language Bool}
    (h : ProgramAcceptable L) :
    ProgramAcceptableByDescription L := by
  rcases h with ⟨P, hP⟩
  rcases hcompile P with ⟨D, hD⟩
  exact ⟨P, D, hP, hD⟩

theorem recursivelyEnumerable_programAcceptableByDescription_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerable L) :
    ProgramAcceptableByDescription L :=
  programAcceptableByDescription_of_descriptionCompiler hcompile
    (recursivelyEnumerable_programAcceptable h)

def DescriptionProgramBoolDeciderCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Bool,
    exists D : MachineDescription, BoolProgramCompiledByDescription P D

def SemanticDescriptionBoolDeciderCompilerAssumption : Prop :=
  DescriptionProgramBoolDeciderCompilationPrinciple

def DovetailDescriptionCompilerPrinciple : Prop :=
  forall accept reject : Word Bool -> Nat -> Prop,
    exists D : MachineDescription,
      BoolProgramCompiledByDescription (DovetailProgram accept reject) D

def SemanticDovetailDescriptionCompilerAssumption : Prop :=
  DovetailDescriptionCompilerPrinciple

/-
The broad dovetail compiler above talks about arbitrary Lean traces.  The
paired-recognizer version below is the concrete Section 5.2 transition-level
handoff: both traces come from finite `MachineDescription` interpreters.
It is still a construction principle, but it names the exact uniform machine
description that a real dovetailing compiler must build.
-/

def PairedRecognizerDovetailDescriptionCompilerPrinciple : Prop :=
  forall accept reject : MachineDescription,
    exists D : MachineDescription,
      BoolProgramCompiledByDescription
        (DovetailProgram
          (fun w n => accept.HaltsIn n w)
          (fun w n => reject.HaltsIn n w)) D

def FiniteSourcePairedRecognizerDovetailCompilerConstruction : Prop :=
  PairedRecognizerDovetailDescriptionCompilerPrinciple

def PairedRecognizerBoundedDovetailTableRealizes
    (accept reject decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          MachineDescription.boundedDovetailOutput
            accept reject w limit = some [b]

def PairedRecognizerBoundedDovetailTableCompilerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def FiniteSourcePairedRecognizerBoundedDovetailTableCompilerConstruction :
    Prop :=
  PairedRecognizerBoundedDovetailTableCompilerConstruction

def FixedDescriptionBoundedSimulatorInput
    (L : MachineDescription.SimulatorLayout) : Word Bool :=
  MachineDescription.SimulatorLayout.asBoolInput L

def FixedDescriptionBoundedSimulatorOutput
    (D : MachineDescription)
    (L : MachineDescription.SimulatorLayout) : Word Bool :=
  MachineDescription.SimulatorLayout.asBoolInput
    (MachineDescription.SimulatorLayout.run D L.stage L)

def FixedDescriptionBoundedSimulatorTableRealizes
    (D simulator : MachineDescription) : Prop :=
  simulator.WellFormed ∧
    forall L : MachineDescription.SimulatorLayout,
      simulator.HaltsWithOutput
        (FixedDescriptionBoundedSimulatorInput L)
        (FixedDescriptionBoundedSimulatorOutput D L)

def FixedDescriptionBoundedSimulatorTableCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      FixedDescriptionBoundedSimulatorTableRealizes D simulator

structure MachineBoundedTraceSearchConstruction : Prop where
  haltsInBool_correct :
    forall D : MachineDescription, forall n : Nat, forall w : Word Bool,
      MachineDescription.haltsInBool D n w = true <-> D.HaltsIn n w
  hitsByBool_correct :
    forall D : MachineDescription, forall w : Word Bool, forall limit : Nat,
      MachineDescription.hitsByBool D w limit = true <->
        exists n : Nat, n ≤ limit ∧ D.HaltsIn n w
  boundedDovetailOutput_correct :
    forall accept reject : MachineDescription,
      forall w : Word Bool, forall limit : Nat,
        MachineDescription.boundedDovetailOutput accept reject w limit =
          (DovetailProgram
            (fun w n => accept.HaltsIn n w)
            (fun w n => reject.HaltsIn n w)).run w limit

structure EncodedConfigurationTraceSearchConstruction : Prop where
  checksEncodedRun_canonical :
    forall D : MachineDescription,
      forall c : MachineDescription.Configuration,
      forall steps : Nat,
        MachineDescription.checksEncodedRun D
          (MachineDescription.encodeConfiguration c)
          steps
          (MachineDescription.encodeConfiguration
            (D.runConfig steps c)) = true

structure BoundedTraceSearchConstruction : Prop where
  machine : MachineBoundedTraceSearchConstruction
  encodedConfiguration : EncodedConfigurationTraceSearchConstruction

theorem machineBoundedTraceSearchConstruction :
    MachineBoundedTraceSearchConstruction where
  haltsInBool_correct := MachineDescription.haltsInBool_eq_true_iff
  hitsByBool_correct := MachineDescription.hitsByBool_eq_true_iff
  boundedDovetailOutput_correct :=
    MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run

theorem encodedConfigurationTraceSearchConstruction :
    EncodedConfigurationTraceSearchConstruction where
  checksEncodedRun_canonical := by
    intro D c steps
    exact MachineDescription.checksEncodedRun_encodeConfiguration D steps c

theorem boundedTraceSearchConstruction :
    BoundedTraceSearchConstruction where
  machine := machineBoundedTraceSearchConstruction
  encodedConfiguration := encodedConfigurationTraceSearchConstruction

theorem fixedDescriptionBoundedSimulatorTableRealizes_wellFormed
    {D simulator : MachineDescription}
    (h : FixedDescriptionBoundedSimulatorTableRealizes D simulator) :
    simulator.WellFormed :=
  h.left

theorem fixedDescriptionBoundedSimulatorTableRealizes_output
    {D simulator : MachineDescription}
    (h : FixedDescriptionBoundedSimulatorTableRealizes D simulator)
    (L : MachineDescription.SimulatorLayout) :
    simulator.HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L) :=
  h.right L

theorem fixedDescriptionBoundedSimulatorOutput_run_hit
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (MachineDescription.SimulatorLayout.run D L.stage L).hit = true <->
      L.hit = true ∨
        exists n : Nat, n ≤ L.stage ∧
          (D.runConfig n L.config).state = D.halt :=
  MachineDescription.SimulatorLayout.run_hit_eq_true_iff D L.stage L

def FixedDescriptionBoundedSimulatorCode
    (D : MachineDescription) : MachineDescription.TapeCodePrimitive :=
  MachineDescription.SimulatorLayout.runCodePrimitive D

def FixedDescriptionBoundedSimulatorCodeRealizes
    (D : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    P.transform (MachineDescription.SimulatorLayout.encode L) =
      some
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L))

theorem fixedDescriptionBoundedSimulatorCode_encode
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (FixedDescriptionBoundedSimulatorCode D).transform
        (MachineDescription.SimulatorLayout.encode L) =
      some
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L)) :=
  MachineDescription.SimulatorLayout.runCodePrimitive_encode D L

theorem fixedDescriptionBoundedSimulatorCode_realizes
    (D : MachineDescription) :
    FixedDescriptionBoundedSimulatorCodeRealizes
      D (FixedDescriptionBoundedSimulatorCode D) := by
  intro L
  exact fixedDescriptionBoundedSimulatorCode_encode D L

theorem fixedDescriptionBoundedSimulatorCode_boolOutput
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    Option.map MachineDescription.encodeCodeWordAsInput
        ((FixedDescriptionBoundedSimulatorCode D).transform
          (MachineDescription.SimulatorLayout.encode L)) =
      some (FixedDescriptionBoundedSimulatorOutput D L) := by
  simp [fixedDescriptionBoundedSimulatorCode_encode,
    FixedDescriptionBoundedSimulatorOutput,
    MachineDescription.SimulatorLayout.asBoolInput]

def FixedDescriptionStepCode
    (D : MachineDescription) : MachineDescription.TapeCodePrimitive :=
  MachineDescription.stepConfigurationCodePrimitive D

def FixedDescriptionStepCodeRealizes
    (D : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall c : MachineDescription.Configuration,
    P.transform (MachineDescription.encodeConfiguration c) =
      some (MachineDescription.encodeConfiguration (D.runConfig 1 c))

theorem fixedDescriptionStepCode_encode
    (D : MachineDescription) (c : MachineDescription.Configuration) :
    (FixedDescriptionStepCode D).transform
        (MachineDescription.encodeConfiguration c) =
      some (MachineDescription.encodeConfiguration (D.runConfig 1 c)) :=
  MachineDescription.stepConfigurationCodePrimitive_encodeConfiguration D c

theorem fixedDescriptionStepCode_realizes
    (D : MachineDescription) :
    FixedDescriptionStepCodeRealizes D (FixedDescriptionStepCode D) := by
  intro c
  exact fixedDescriptionStepCode_encode D c

def PairedRecognizerDovetailLayoutCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.runCodePrimitive accept reject

def PairedRecognizerDovetailLayoutCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    P.transform (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.run
            accept reject L.stage L))

theorem pairedRecognizerDovetailLayoutCode_encode
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    (PairedRecognizerDovetailLayoutCode accept reject).transform
        (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.run
            accept reject L.stage L)) :=
  MachineDescription.DovetailLayout.runCodePrimitive_encode
    accept reject L

theorem pairedRecognizerDovetailLayoutCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailLayoutCodeRealizes
      accept reject
      (PairedRecognizerDovetailLayoutCode accept reject) := by
  intro L
  exact pairedRecognizerDovetailLayoutCode_encode accept reject L

theorem pairedRecognizerDovetailLayout_initial_output
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    MachineDescription.DovetailLayout.outputFromHits
        (MachineDescription.DovetailLayout.run accept reject limit
          (MachineDescription.DovetailLayout.initial
            accept reject w limit)) =
      MachineDescription.boundedDovetailOutput accept reject w limit :=
  MachineDescription.DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput
    accept reject w limit

def TapeCodePrimitiveCompiledByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      D.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out

def TapeCodePrimitiveOutputRealizedByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      P.transform code = some out ->
        D.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)

def TapeCodePrimitiveOutputSubroutineRealizedByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  TapeCodePrimitiveOutputRealizedByDescription P D ∧
    D.HaltTransitionFree

theorem tapeCodePrimitiveOutputRealizedByDescription_of_exact
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveCompiledByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D := by
  constructor
  · exact h.left
  · intro code out hp
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
      ((h.right code out).mpr hp)

theorem tapeCodePrimitiveOutputRealizedByDescription_of_subroutine
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D :=
  h.left

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left.left, h.right⟩

theorem tapeCodePrimitiveCompiledByDescription_identity :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput code :=
        (MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)).mp h
      have hout : out = code :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.identity, hout]
    · intro h
      simp [MachineDescription.TapeCodePrimitive.identity] at h
      rw [← h]
      exact
        (MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputRealizedByDescription_identity :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  tapeCodePrimitiveOutputRealizedByDescription_of_exact
    tapeCodePrimitiveCompiledByDescription_identity

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_identity :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_identity,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_erase :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription := by
  constructor
  · exact MachineDescription.eraseRightDescription_wellFormed
  · intro code out h
    simp [MachineDescription.TapeCodePrimitive.erase] at h
    rw [← h]
    exact MachineDescription.eraseRightDescription_haltsWithOutput_empty
      (MachineDescription.encodeCodeWordAsInput code)

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_erase :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_erase,
    MachineDescription.eraseRightDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputRealizedByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) := by
  constructor
  · exact MachineDescription.appendCodeSymbolRightDescription_wellFormed
      symbol
  · intro code out h
    simp [MachineDescription.TapeCodePrimitive.append] at h
    rw [← h]
    have hencoded :
        MachineDescription.encodeCodeWordAsInput
            (List.append code [symbol]) =
          List.append (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeSymbolAsInput symbol) := by
      rw [MachineDescription.encodeCodeWordAsInput_append,
        MachineDescription.encodeCodeWordAsInput_singleton]
    change
      (MachineDescription.AppendCodeSymbolRightDescription symbol).HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput
          (List.append code [symbol]))
    rw [hencoded]
    exact
      MachineDescription.appendCodeSymbolRightDescription_haltsWithOutput_append
        symbol (MachineDescription.encodeCodeWordAsInput code)

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_append_singleton symbol,
    MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
      symbol⟩

theorem not_tapeCodePrimitiveCompiledByDescription_erase :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        MachineDescription.TapeCodePrimitive.erase D := by
  intro h
  rcases h with ⟨D, hD⟩
  have herase :
      D.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput
          [MachineCodeSymbol.header])
        (MachineDescription.encodeCodeWordAsInput []) := by
    exact (hD.right [MachineCodeSymbol.header] []).mpr rfl
  have hctx :
      0 <
        Tape.contextLength
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput
              [MachineCodeSymbol.header])) := by
    simp [MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput, Tape.input,
      Tape.contextLength]
  simpa [MachineDescription.encodeCodeWordAsInput] using
    MachineDescription.not_haltsWithExactOutput_empty_of_input_contextLength_pos
      (D := D)
      (w := MachineDescription.encodeCodeWordAsInput
        [MachineCodeSymbol.header])
      hctx herase

structure MachineDescriptionPrimitiveCompilerCore where
  identityCompiled :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  identityOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  eraseOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription
  eraseNotExactlyCompiled :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        MachineDescription.TapeCodePrimitive.erase D
  appendSingletonOutputRealized :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputRealizedByDescription
        (MachineDescription.TapeCodePrimitive.append [symbol])
        (MachineDescription.AppendCodeSymbolRightDescription symbol)

def machineDescriptionPrimitiveCompilerCore :
    MachineDescriptionPrimitiveCompilerCore where
  identityCompiled := tapeCodePrimitiveCompiledByDescription_identity
  identityOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_identity
  eraseOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_erase
  eraseNotExactlyCompiled :=
    not_tapeCodePrimitiveCompiledByDescription_erase
  appendSingletonOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_append_singleton

structure MachineDescriptionPrimitiveSubroutineCore where
  identityReady :
    MachineDescription.SubroutineReady
      MachineDescription.ExactIdentityDescription
  eraseReady :
    MachineDescription.SubroutineReady
      MachineDescription.EraseRightDescription
  boolOutputReady :
    forall b : Bool,
      MachineDescription.SubroutineReady
        (MachineDescription.BoolOutputDescription b)
  appendSingletonReady :
    forall symbol : MachineCodeSymbol,
      MachineDescription.SubroutineReady
        (MachineDescription.AppendCodeSymbolRightDescription symbol)

def machineDescriptionPrimitiveSubroutineCore :
    MachineDescriptionPrimitiveSubroutineCore where
  identityReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  eraseReady :=
    ⟨MachineDescription.eraseRightDescription_wellFormed,
      MachineDescription.eraseRightDescription_haltTransitionFree⟩
  boolOutputReady := by
    intro b
    exact
      ⟨MachineDescription.boolOutputDescription_wellFormed b,
        MachineDescription.boolOutputDescription_haltTransitionFree b⟩
  appendSingletonReady := by
    intro symbol
    exact
      ⟨MachineDescription.appendCodeSymbolRightDescription_wellFormed symbol,
        MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
          symbol⟩

def MachineDescriptionTapeCodeExactCompilerConstruction : Prop :=
  forall P : MachineDescription.TapeCodePrimitive,
    exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription P D

def MachineDescriptionTapeCodeOutputCompilerConstruction : Prop :=
  forall P : MachineDescription.TapeCodePrimitive,
    exists D : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription P D

theorem not_machineDescriptionTapeCodeExactCompilerConstruction :
    ¬ MachineDescriptionTapeCodeExactCompilerConstruction := by
  intro hcompile
  rcases hcompile MachineDescription.TapeCodePrimitive.erase with
    ⟨D, hD⟩
  exact not_tapeCodePrimitiveCompiledByDescription_erase ⟨D, hD⟩

theorem machineDescriptionTapeCodeOutputCompiler_realizes
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (P : MachineDescription.TapeCodePrimitive) :
    exists D : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription P D :=
  hcompile P

def TapeCodePrimitiveCodeComposition
    (A B C : MachineDescription) : Prop :=
  C.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      C.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
        exists mid : Word MachineCodeSymbol,
          A.HaltsWithExactOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput mid) ∧
            B.HaltsWithExactOutput
              (MachineDescription.encodeCodeWordAsInput mid)
              (MachineDescription.encodeCodeWordAsInput out)

theorem tapeCodePrimitiveCompiledByDescription_compose
    {P Q : MachineDescription.TapeCodePrimitive}
    {A B C : MachineDescription}
    (hcomp : TapeCodePrimitiveCodeComposition A B C)
    (hP : TapeCodePrimitiveCompiledByDescription P A)
    (hQ : TapeCodePrimitiveCompiledByDescription Q B) :
    TapeCodePrimitiveCompiledByDescription
      (MachineDescription.TapeCodePrimitive.compose P Q) C := by
  constructor
  · exact hcomp.left
  · intro code out
    constructor
    · intro h
      rcases (hcomp.right code out).mp h with
        ⟨mid, hA, hB⟩
      have hPmid : P.transform code = some mid :=
        (hP.right code mid).mp hA
      have hQout : Q.transform mid = some out :=
        (hQ.right mid out).mp hB
      exact
        MachineDescription.TapeCodePrimitive.compose_transform_some
          hPmid hQout
    · intro h
      unfold MachineDescription.TapeCodePrimitive.compose at h
      cases hPcode : P.transform code with
      | none =>
          simp [hPcode] at h
      | some mid =>
          have hQout : Q.transform mid = some out := by
            simpa [hPcode] using h
          apply (hcomp.right code out).mpr
          exists mid
          constructor
          · exact (hP.right code mid).mpr hPcode
          · exact (hQ.right mid out).mpr hQout

def FixedDescriptionBoundedSimulatorCodeCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionStepCodeCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (FixedDescriptionStepCode D) stepper

def FixedDescriptionStepCodeOutputRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (FixedDescriptionStepCode D) stepper

def FixedDescriptionStepCodeConfigurationRealizes
    (D stepper : MachineDescription) : Prop :=
  stepper.WellFormed ∧
    forall c : MachineDescription.Configuration,
      stepper.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration c))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration (D.runConfig 1 c)))

def FixedDescriptionStepCodeConfigurationRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      FixedDescriptionStepCodeConfigurationRealizes D stepper

def PairedRecognizerDovetailLayoutCodeCompilerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputSubroutineRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailSearchDriverCompilerConstruction : Prop :=
  forall accept reject runner : MachineDescription,
    TapeCodePrimitiveOutputRealizedByDescription
      (PairedRecognizerDovetailLayoutCode accept reject) runner ->
      exists decider : MachineDescription,
        PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject runner : MachineDescription,
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      (PairedRecognizerDovetailLayoutCode accept reject) runner ->
      exists decider : MachineDescription,
        PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def PairedRecognizerDovetailRunnerSearchDriverRealizes
    (accept reject runner decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          runner.HaltsWithOutput
            (MachineDescription.DovetailLayout.asBoolInput
              (MachineDescription.DovetailLayout.initial
                accept reject w limit))
            (MachineDescription.DovetailLayout.asBoolInput
              (MachineDescription.DovetailLayout.run accept reject limit
                (MachineDescription.DovetailLayout.initial
                  accept reject w limit))) ∧
          MachineDescription.DovetailLayout.outputFromHits
              (MachineDescription.DovetailLayout.run accept reject limit
                (MachineDescription.DovetailLayout.initial
                  accept reject w limit)) =
            some [b]

def PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction : Prop :=
  forall accept reject runner : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerDovetailRunnerSearchDriverRealizes
        accept reject runner decider

def PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject runner : MachineDescription,
    runner.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailRunnerSearchDriverRealizes
          accept reject runner decider

theorem fixedDescriptionBoundedSimulatorCodeOutputRealizer_of_codeCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeCompilerConstruction) :
    FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction := by
  intro D
  rcases hcompile D with ⟨simulator, hsimulator⟩
  exact ⟨simulator,
    tapeCodePrimitiveOutputRealizedByDescription_of_exact hsimulator⟩

theorem fixedDescriptionStepCodeOutputRealizer_of_codeCompiler
    (hcompile : FixedDescriptionStepCodeCompilerConstruction) :
    FixedDescriptionStepCodeOutputRealizerConstruction := by
  intro D
  rcases hcompile D with ⟨stepper, hstepper⟩
  exact ⟨stepper,
    tapeCodePrimitiveOutputRealizedByDescription_of_exact hstepper⟩

theorem fixedDescriptionStepCodeOutputRealizer_of_configurationRealizer
    {D stepper : MachineDescription}
    (hstepper :
      FixedDescriptionStepCodeConfigurationRealizes D stepper) :
    TapeCodePrimitiveOutputRealizedByDescription
      (FixedDescriptionStepCode D) stepper := by
  constructor
  · exact hstepper.left
  · intro code out hcode
    unfold FixedDescriptionStepCode at hcode
    simp [MachineDescription.stepConfigurationCodePrimitive,
      MachineDescription.stepConfigurationCode] at hcode
    cases hdecode : MachineDescription.decodeConfiguration code with
    | none =>
        simp [hdecode] at hcode
    | some parsed =>
        cases parsed with
        | mk c suffix =>
            cases suffix with
            | nil =>
                simp [hdecode] at hcode
                have hcanonical :
                    code = MachineDescription.encodeConfiguration c :=
                  MachineDescription.decodeConfiguration_eq_some_encodeConfiguration
                    hdecode
                rw [hcanonical, ← hcode]
                exact hstepper.right c
            | cons _ _ =>
                simp [hdecode] at hcode

theorem fixedDescriptionStepCodeOutputRealizerConstruction_of_configurationRealizerConstruction
    (hcompile :
      FixedDescriptionStepCodeConfigurationRealizerConstruction) :
    FixedDescriptionStepCodeOutputRealizerConstruction := by
  intro D
  rcases hcompile D with ⟨stepper, hstepper⟩
  exact ⟨stepper,
    fixedDescriptionStepCodeOutputRealizer_of_configurationRealizer
      hstepper⟩

theorem fixedDescriptionStepCodeConfigurationRealizer_of_outputRealizer
    {D stepper : MachineDescription}
    (hstepper :
      TapeCodePrimitiveOutputRealizedByDescription
        (FixedDescriptionStepCode D) stepper) :
    FixedDescriptionStepCodeConfigurationRealizes D stepper := by
  constructor
  · exact hstepper.left
  · intro c
    exact hstepper.right
      (MachineDescription.encodeConfiguration c)
      (MachineDescription.encodeConfiguration (D.runConfig 1 c))
      (fixedDescriptionStepCode_encode D c)

theorem fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
    (hcompile :
      FixedDescriptionStepCodeOutputRealizerConstruction) :
    FixedDescriptionStepCodeConfigurationRealizerConstruction := by
  intro D
  rcases hcompile D with ⟨stepper, hstepper⟩
  exact ⟨stepper,
    fixedDescriptionStepCodeConfigurationRealizer_of_outputRealizer
      hstepper⟩

theorem fixedDescriptionStepCodeConfigurationRealizerConstruction_iff_outputRealizerConstruction :
    FixedDescriptionStepCodeConfigurationRealizerConstruction <->
      FixedDescriptionStepCodeOutputRealizerConstruction := by
  constructor
  · exact
      fixedDescriptionStepCodeOutputRealizerConstruction_of_configurationRealizerConstruction
  · exact
      fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction

theorem fixedDescriptionStepCodeConfigurationRealizes_of_runConfig_one_eq_id
    {D stepper : MachineDescription}
    (hstepper :
      TapeCodePrimitiveOutputRealizedByDescription
        MachineDescription.TapeCodePrimitive.identity stepper)
    (hD : forall c : MachineDescription.Configuration,
      D.runConfig 1 c = c) :
    FixedDescriptionStepCodeConfigurationRealizes D stepper := by
  constructor
  · exact hstepper.left
  · intro c
    rw [hD c]
    exact hstepper.right
      (MachineDescription.encodeConfiguration c)
      (MachineDescription.encodeConfiguration c)
      rfl

theorem runConfig_one_eq_id_of_transitions_nil
    {D : MachineDescription}
    (hD : D.transitions = []) :
    forall c : MachineDescription.Configuration, D.runConfig 1 c = c := by
  intro c
  cases c
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, hD]

theorem fixedDescriptionStepCodeConfigurationRealizes_transitionless
    {D : MachineDescription}
    (hD : D.transitions = []) :
    FixedDescriptionStepCodeConfigurationRealizes
      D MachineDescription.ExactIdentityDescription :=
  fixedDescriptionStepCodeConfigurationRealizes_of_runConfig_one_eq_id
    tapeCodePrimitiveOutputRealizedByDescription_identity
    (runConfig_one_eq_id_of_transitions_nil hD)

theorem fixedDescriptionStepCodeConfigurationRealizes_exactIdentityDescription :
    FixedDescriptionStepCodeConfigurationRealizes
      MachineDescription.ExactIdentityDescription
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro c
    have hrun :
        MachineDescription.ExactIdentityDescription.runConfig 1 c = c := by
      cases c
      simp [MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.ExactIdentityDescription]
    rw [hrun]
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
      ((MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration c))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration c))).mpr rfl)

theorem pairedRecognizerDovetailLayoutCodeOutputRealizer_of_codeCompiler
    (hcompile :
      PairedRecognizerDovetailLayoutCodeCompilerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨runner, hrunner⟩
  exact ⟨runner,
    tapeCodePrimitiveOutputRealizedByDescription_of_exact hrunner⟩

theorem pairedRecognizerDovetailLayoutCodeOutputRealizer_of_subroutineRealizer
    (hcompile :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨runner, hrunner⟩
  exact ⟨runner,
    tapeCodePrimitiveOutputRealizedByDescription_of_subroutine hrunner⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hrunner accept reject with ⟨runner, hrunnerRealizes⟩
  exact hdriver accept reject runner hrunnerRealizes

theorem pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hrunner accept reject with ⟨runner, hrunnerRealizes⟩
  exact hdriver accept reject runner hrunnerRealizes

theorem pairedRecognizerBoundedDovetailTableRealizes_of_runnerSearchDriverRealizes
    {accept reject runner decider : MachineDescription}
    (hrunner :
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner)
    (hdecider :
      PairedRecognizerDovetailRunnerSearchDriverRealizes
        accept reject runner decider) :
    PairedRecognizerBoundedDovetailTableRealizes accept reject decider := by
  constructor
  · exact hdecider.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdecider.right w b).mp hhalt with
        ⟨limit, _hrunnerHalts, hout⟩
      exact ⟨limit, by
        simpa [pairedRecognizerDovetailLayout_initial_output] using hout⟩
    · intro hbounded
      rcases hbounded with ⟨limit, hout⟩
      apply (hdecider.right w b).mpr
      refine ⟨limit, ?_, ?_⟩
      · exact
          hrunner.right
            (MachineDescription.DovetailLayout.encode
              (MachineDescription.DovetailLayout.initial
                accept reject w limit))
            (MachineDescription.DovetailLayout.encode
              (MachineDescription.DovetailLayout.run accept reject limit
                (MachineDescription.DovetailLayout.initial
                  accept reject w limit)))
            (pairedRecognizerDovetailLayoutCode_encode
              accept reject
              (MachineDescription.DovetailLayout.initial
                accept reject w limit))
      · simpa [pairedRecognizerDovetailLayout_initial_output] using hout

theorem pairedRecognizerDovetailSearchDriverCompiler_of_runnerSearchDriverCompiler
    (hcompile :
      PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailSearchDriverCompilerConstruction := by
  intro accept reject runner hrunner
  rcases hcompile accept reject runner with ⟨decider, hdecider⟩
  exact ⟨decider,
    pairedRecognizerBoundedDovetailTableRealizes_of_runnerSearchDriverRealizes
      hrunner hdecider⟩

theorem pairedRecognizerDovetailSubroutineSearchDriverCompiler_of_subroutineRunnerSearchDriverCompiler
    (hcompile :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction := by
  intro accept reject runner hrunner
  rcases hcompile accept reject runner
      (tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
        hrunner) with
    ⟨decider, hdecider⟩
  exact ⟨decider,
    pairedRecognizerBoundedDovetailTableRealizes_of_runnerSearchDriverRealizes
      (tapeCodePrimitiveOutputRealizedByDescription_of_subroutine hrunner)
      hdecider⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
    hrunner
    (pairedRecognizerDovetailSubroutineSearchDriverCompiler_of_subroutineRunnerSearchDriverCompiler
      hdriver)

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_codeCompiler
    {D simulator : MachineDescription}
    (hcompile : TapeCodePrimitiveCompiledByDescription
      (FixedDescriptionBoundedSimulatorCode D) simulator) :
    FixedDescriptionBoundedSimulatorTableRealizes D simulator := by
  constructor
  · exact hcompile.left
  · intro L
    have hExact :
        simulator.HaltsWithExactOutput
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorOutput D L) := by
      have hcode := (hcompile.right
        (MachineDescription.SimulatorLayout.encode L)
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L))).mpr
          (fixedDescriptionBoundedSimulatorCode_encode D L)
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorOutput,
        MachineDescription.SimulatorLayout.asBoolInput] using hcode
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput hExact

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_codeCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨simulator, hsimulator⟩
  exact ⟨simulator,
    fixedDescriptionBoundedSimulatorTableRealizes_of_codeCompiler
      hsimulator⟩

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_codeOutputRealizer
    {D simulator : MachineDescription}
    (hcompile : TapeCodePrimitiveOutputRealizedByDescription
      (FixedDescriptionBoundedSimulatorCode D) simulator) :
    FixedDescriptionBoundedSimulatorTableRealizes D simulator := by
  constructor
  · exact hcompile.left
  · intro L
    exact hcompile.right
      (MachineDescription.SimulatorLayout.encode L)
      (MachineDescription.SimulatorLayout.encode
        (MachineDescription.SimulatorLayout.run D L.stage L))
      (fixedDescriptionBoundedSimulatorCode_encode D L)

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨simulator, hsimulator⟩
  exact ⟨simulator,
    fixedDescriptionBoundedSimulatorTableRealizes_of_codeOutputRealizer
      hsimulator⟩

structure MachineDescriptionCompilerCloseout where
  stepCodeOutput :
    FixedDescriptionStepCodeOutputRealizerConstruction
  stepConfiguration :
    FixedDescriptionStepCodeConfigurationRealizerConstruction
  boundedSimulatorCodeOutput :
    FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction
  boundedSimulatorTable :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction
  dovetailLayoutCodeOutput :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction

def machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    MachineDescriptionCompilerCloseout where
  stepCodeOutput := by
    intro D
    exact hcompile (FixedDescriptionStepCode D)
  stepConfiguration :=
    fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
      (by
        intro D
        exact hcompile (FixedDescriptionStepCode D))
  boundedSimulatorCodeOutput := by
    intro D
    exact hcompile (FixedDescriptionBoundedSimulatorCode D)
  boundedSimulatorTable :=
    fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer
      (by
        intro D
        exact hcompile (FixedDescriptionBoundedSimulatorCode D))
  dovetailLayoutCodeOutput := by
    intro accept reject
    exact hcompile (PairedRecognizerDovetailLayoutCode accept reject)

theorem fixedDescriptionStepCodeConfigurationRealizerConstruction_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    FixedDescriptionStepCodeConfigurationRealizerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).stepConfiguration

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).boundedSimulatorTable

theorem pairedRecognizerDovetailLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).dovetailLayoutCodeOutput

structure FixedDescriptionBoundedSimulatorPhaseTargets
    (D : MachineDescription) where
  decodeLayout :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  simulateStep :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  repeatControl :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  emitLayout :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  pipeline_correct :
    forall L : MachineDescription.SimulatorLayout,
      emitLayout (repeatControl (simulateStep (decodeLayout L))) =
        MachineDescription.SimulatorLayout.run D L.stage L

namespace FixedDescriptionBoundedSimulatorPhaseTargets

def canonical (D : MachineDescription) :
    FixedDescriptionBoundedSimulatorPhaseTargets D where
  decodeLayout := id
  simulateStep := fun L =>
    MachineDescription.SimulatorLayout.run D L.stage L
  repeatControl := id
  emitLayout := id
  pipeline_correct := by
    intro L
    rfl

theorem canonical_pipeline_correct
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (canonical D).emitLayout
        ((canonical D).repeatControl
          ((canonical D).simulateStep ((canonical D).decodeLayout L))) =
      MachineDescription.SimulatorLayout.run D L.stage L :=
  (canonical D).pipeline_correct L

end FixedDescriptionBoundedSimulatorPhaseTargets

def FixedDescriptionBoundedSimulatorLayoutTape
    (L : MachineDescription.SimulatorLayout) : Tape Bool :=
  MachineDescription.SimulatorLayout.tape L

def FixedDescriptionBoundedSimulatorHandoffTape
    (handoffMove : Direction)
    (L : MachineDescription.SimulatorLayout) : Tape Bool :=
  Tape.move handoffMove (FixedDescriptionBoundedSimulatorLayoutTape L)

def FixedDescriptionBoundedSimulatorFragmentReaches
    (entryTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool)
    (phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout)
    (fragment : MachineDescription.Fragment)
    (L : MachineDescription.SimulatorLayout) : Prop :=
  exists n : Nat,
    fragment.toDescription.runConfig n
        { state := fragment.entry, tape := entryTape L } =
      { state := fragment.exit, tape := exitTape (phase L) } ∧
      forall k : Nat,
        k < n ->
          (fragment.toDescription.runConfig k
            { state := fragment.entry, tape := entryTape L }).state ≠
            fragment.exit

def FixedDescriptionBoundedSimulatorFragmentRealizes
    (entryTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool)
    (phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout)
    (fragment : MachineDescription.Fragment) : Prop :=
  fragment.WellFormed ∧
    forall L : MachineDescription.SimulatorLayout,
      FixedDescriptionBoundedSimulatorFragmentReaches
        entryTape exitTape phase fragment L

abbrev FixedDescriptionBoundedSimulatorPhaseRealizes :=
  FixedDescriptionBoundedSimulatorFragmentRealizes

theorem fixedDescriptionBoundedSimulatorPhaseRealizes_standard_output
    {phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout}
    {fragment : MachineDescription.Fragment}
    (h :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        phase fragment) :
    fragment.WellFormed ∧
      forall L : MachineDescription.SimulatorLayout,
        fragment.toDescription.HaltsWithOutput
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorInput (phase L)) := by
  constructor
  · exact h.left
  · intro L
    rcases h.right L with ⟨n, hn, _hminimal⟩
    exists n
    have hstate :
        (fragment.toDescription.runConfig n
          (fragment.toDescription.initial
            (FixedDescriptionBoundedSimulatorInput L))).state =
          fragment.exit := by
      simpa [MachineDescription.Fragment.toDescription,
        FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorLayoutTape,
        MachineDescription.SimulatorLayout.tape] using congrArg
          (fun c : MachineDescription.Configuration => c.state) hn
    have htape :
        (fragment.toDescription.runConfig n
          (fragment.toDescription.initial
            (FixedDescriptionBoundedSimulatorInput L))).tape =
          FixedDescriptionBoundedSimulatorLayoutTape (phase L) := by
      simpa [MachineDescription.Fragment.toDescription,
        FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorLayoutTape,
        MachineDescription.SimulatorLayout.tape] using congrArg
          (fun c : MachineDescription.Configuration => c.tape) hn
    constructor
    · simpa [MachineDescription.Fragment.toDescription] using hstate
    · rw [htape]
      exact MachineDescription.SimulatorLayout.tape_normalizedOutput
        (phase L)

theorem fixedDescriptionBoundedSimulatorHandoffPhaseRealizes
    (move : Direction) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      FixedDescriptionBoundedSimulatorLayoutTape
      (FixedDescriptionBoundedSimulatorHandoffTape move)
      id
      (MachineDescription.Fragment.handoff move) := by
  constructor
  · exact MachineDescription.Fragment.handoff_wellFormed move
  · intro L
    simpa [FixedDescriptionBoundedSimulatorLayoutTape,
      FixedDescriptionBoundedSimulatorHandoffTape] using
      MachineDescription.Fragment.handoff_firstReaches move
        (FixedDescriptionBoundedSimulatorLayoutTape L)

theorem fixedDescriptionBoundedSimulatorHaltPhaseRealizes
    (tape : MachineDescription.SimulatorLayout -> Tape Bool) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      tape tape id MachineDescription.Fragment.halt := by
  constructor
  · exact MachineDescription.Fragment.halt_wellFormed
  · intro L
    exists 0
    constructor
    · rfl
    · intro k hk
      omega

namespace MachineDescription
namespace Fragment

theorem lookup_seq_left
    {A B : Fragment} {handoffMove : Direction}
    (hB : B.WellFormed)
    {state : Nat} {cell : Option Bool}
    (hstate : state < A.stateCount)
    (hnotExit : state ≠ A.exit) :
    (seq A B handoffMove).toDescription.lookupTransition state cell =
      A.toDescription.lookupTransition state cell := by
  unfold MachineDescription.lookupTransition
  simp [MachineDescription.Fragment.seq,
    MachineDescription.Fragment.toDescription, List.find?_append]
  cases hfindA :
      List.find? (MachineDescription.Matches state cell)
        A.transitions with
  | some t =>
      simp
  | none =>
      have hfindH :
          List.find? (MachineDescription.Matches state cell)
            (handoffTransitions A.exit
              (A.stateCount + B.entry) handoffMove) = none := by
        rw [List.find?_eq_none]
        intro t ht hmatch
        simp [handoffTransitions, branchOnCell,
          preserveTransition, transition] at ht
        rcases ht with rfl | rfl | rfl
        · rcases (by
            simpa [MachineDescription.Matches] using hmatch) with
            ⟨hsource, _hread⟩
          exact hnotExit hsource.symm
        · rcases (by
            simpa [MachineDescription.Matches] using hmatch) with
            ⟨hsource, _hread⟩
          exact hnotExit hsource.symm
        · rcases (by
            simpa [MachineDescription.Matches] using hmatch) with
            ⟨hsource, _hread⟩
          exact hnotExit hsource.symm
      have hfindB :
          List.find? (MachineDescription.Matches state cell)
            (B.transitions.map
              (TransitionDescription.offsetStates A.stateCount)) =
            none := by
        apply (List.find?_eq_none).mpr
        intro t ht hmatch
        rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
        have hbaseSource :
            base.source < B.stateCount :=
          (hB.right.right.right.left base hbase).left
        have hmatchPair :
            A.stateCount + base.source = state ∧ base.read = cell := by
          simpa [MachineDescription.Matches,
            TransitionDescription.offsetStates] using hmatch
        have hsource :
            A.stateCount + base.source = state :=
          hmatchPair.left
        omega
      simpa [hfindA, hfindH, List.find?_eq_none] using hfindB

theorem stepConfig_seq_left
    {A B : Fragment} {handoffMove : Direction}
    (hB : B.WellFormed)
    {c : MachineDescription.Configuration}
    (hstate : c.state < A.stateCount)
    (hnotExit : c.state ≠ A.exit) :
    (seq A B handoffMove).toDescription.stepConfig c =
      A.toDescription.stepConfig c := by
  simp [MachineDescription.stepConfig,
    lookup_seq_left hB hstate hnotExit]

theorem runConfig_seq_left_of_no_exit
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {n : Nat} {c : MachineDescription.Configuration}
    (hstate : c.state < A.stateCount)
    (hnoExit : forall k : Nat,
      k < n ->
        (A.toDescription.runConfig k c).state ≠ A.exit) :
    (seq A B handoffMove).toDescription.runConfig n c =
      A.toDescription.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hcNotExit : c.state ≠ A.exit := by
        simpa [MachineDescription.runConfig] using
          hnoExit 0 (Nat.succ_pos n)
      have hstepSeq :
          (seq A B handoffMove).toDescription.stepConfig c =
            A.toDescription.stepConfig c :=
        stepConfig_seq_left hB hstate hcNotExit
      cases hstepA : A.toDescription.stepConfig c with
      | none =>
          simp [MachineDescription.runConfig, hstepSeq, hstepA]
      | some cnext =>
          have hnextState : cnext.state < A.stateCount := by
            have hbound :=
              MachineDescription.stepConfig_state_bound
                (D := A.toDescription)
                (Fragment.toDescription_wellFormed hA)
                hstepA
            simpa [Fragment.toDescription] using hbound
          have hnextNoExit : forall k : Nat,
              k < n ->
                (A.toDescription.runConfig k cnext).state ≠
                  A.exit := by
            intro k hk
            have hno := hnoExit (k + 1) (Nat.succ_lt_succ hk)
            simpa [MachineDescription.runConfig, hstepA] using hno
          simp [MachineDescription.runConfig, hstepSeq, hstepA,
            ih hnextState hnextNoExit]

theorem stepConfig_seq_handoff
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed)
    (T : Tape Bool) :
    (seq A B handoffMove).toDescription.stepConfig
        { state := A.exit, tape := T } =
      some
        { state := A.stateCount + B.entry
          tape := Tape.move handoffMove T } := by
  have hfindA :
      List.find? (MachineDescription.Matches A.exit (Tape.read T))
        A.transitions = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    have hmatchPair : t.source = A.exit ∧ t.read = Tape.read T := by
      simpa [MachineDescription.Matches] using hmatch
    have hsource : t.source = A.exit :=
      hmatchPair.left
    exact hA.right.right.right.right.right t ht hsource
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          have hfindA' :
              List.find? (MachineDescription.Matches A.exit none)
                A.transitions = none := by
            simpa [Tape.read] using hfindA
          cases handoffMove <;>
            simp [MachineDescription.stepConfig,
              MachineDescription.lookupTransition, Fragment.seq,
              Fragment.toDescription, List.find?_append, hfindA',
              handoffTransitions, branchOnCell,
              preserveTransition, transition, preserveCell,
              MachineDescription.Matches, Tape.read, Tape.write,
              Tape.move, Tape.moveLeft, Tape.moveRight]
      | some b =>
          cases b
          · have hfindA' :
                List.find?
                    (MachineDescription.Matches A.exit (some false))
                    A.transitions = none := by
              simpa [Tape.read] using hfindA
            cases handoffMove <;>
              simp [MachineDescription.stepConfig,
                MachineDescription.lookupTransition, Fragment.seq,
                Fragment.toDescription, List.find?_append, hfindA',
                handoffTransitions, branchOnCell,
                preserveTransition, transition, preserveCell,
                MachineDescription.Matches, Tape.read, Tape.write,
                Tape.move, Tape.moveLeft, Tape.moveRight]
          · have hfindA' :
                List.find?
                    (MachineDescription.Matches A.exit (some true))
                    A.transitions = none := by
              simpa [Tape.read] using hfindA
            cases handoffMove <;>
              simp [MachineDescription.stepConfig,
                MachineDescription.lookupTransition, Fragment.seq,
                Fragment.toDescription, List.find?_append, hfindA',
                handoffTransitions, branchOnCell,
                preserveTransition, transition, preserveCell,
                MachineDescription.Matches, Tape.read, Tape.write,
                Tape.move, Tape.moveLeft, Tape.moveRight]

def offsetConfiguration
    (offset : Nat) (c : MachineDescription.Configuration) :
    MachineDescription.Configuration :=
  { state := offset + c.state, tape := c.tape }

theorem lookup_seq_right
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed)
    {state : Nat} {cell : Option Bool} :
    (seq A B handoffMove).toDescription.lookupTransition
        (A.stateCount + state) cell =
      Option.map (TransitionDescription.offsetStates A.stateCount)
        (B.toDescription.lookupTransition state cell) := by
  unfold MachineDescription.lookupTransition
  have hfindA :
      List.find? (MachineDescription.Matches
          (A.stateCount + state) cell) A.transitions = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    have htSource : t.source < A.stateCount :=
      (hA.right.right.right.left t ht).left
    have hsource : t.source = A.stateCount + state := by
      have hmatchPair :
          t.source = A.stateCount + state ∧ t.read = cell := by
        simpa [MachineDescription.Matches] using hmatch
      exact hmatchPair.left
    omega
  have hfindH :
      List.find? (MachineDescription.Matches
          (A.stateCount + state) cell)
        (handoffTransitions A.exit
          (A.stateCount + B.entry) handoffMove) = none := by
    apply (List.find?_eq_none).mpr
    intro t ht hmatch
    simp [handoffTransitions, branchOnCell,
      preserveTransition, transition] at ht
    rcases ht with rfl | rfl | rfl
    · have hsource : A.exit = A.stateCount + state := by
        have hmatchPair :
            A.exit = A.stateCount + state ∧ none = cell := by
          simpa [MachineDescription.Matches] using hmatch
        exact hmatchPair.left
      have hAexit : A.exit < A.stateCount := hA.right.right.left
      omega
    · have hsource : A.exit = A.stateCount + state := by
        have hmatchPair :
            A.exit = A.stateCount + state ∧ some false = cell := by
          simpa [MachineDescription.Matches] using hmatch
        exact hmatchPair.left
      have hAexit : A.exit < A.stateCount := hA.right.right.left
      omega
    · have hsource : A.exit = A.stateCount + state := by
        have hmatchPair :
            A.exit = A.stateCount + state ∧ some true = cell := by
          simpa [MachineDescription.Matches] using hmatch
        exact hmatchPair.left
      have hAexit : A.exit < A.stateCount := hA.right.right.left
      omega
  have hpredicate :
      (MachineDescription.Matches (A.stateCount + state) cell ∘
          TransitionDescription.offsetStates A.stateCount) =
        MachineDescription.Matches state cell := by
    funext t
    have hsourceBeq :
        (A.stateCount + t.source == A.stateCount + state) =
          (t.source == state) := by
      by_cases hsource : t.source = state
      · have hoffset :
            A.stateCount + t.source = A.stateCount + state := by
          omega
        have hleft :
            (A.stateCount + t.source == A.stateCount + state) =
              true := by
          rw [beq_iff_eq]
          exact hoffset
        have hright : (t.source == state) = true := by
          rw [beq_iff_eq]
          exact hsource
        rw [hleft, hright]
      · have hoffset :
            A.stateCount + t.source ≠ A.stateCount + state := by
          omega
        have hleft :
            (A.stateCount + t.source == A.stateCount + state) =
              false := by
          rw [beq_eq_false_iff_ne]
          exact hoffset
        have hright : (t.source == state) = false := by
          rw [beq_eq_false_iff_ne]
          exact hsource
        rw [hleft, hright]
    simp [Function.comp, MachineDescription.Matches,
      TransitionDescription.offsetStates, hsourceBeq]
  simp [Fragment.seq, Fragment.toDescription, List.find?_append,
    hfindA, hfindH, List.find?_map, hpredicate]

theorem stepConfig_seq_right
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed)
    (c : MachineDescription.Configuration) :
    (seq A B handoffMove).toDescription.stepConfig
        (offsetConfiguration A.stateCount c) =
      Option.map (offsetConfiguration A.stateCount)
        (B.toDescription.stepConfig c) := by
  cases c with
  | mk state tape =>
      simp [MachineDescription.stepConfig, offsetConfiguration,
        lookup_seq_right (A := A) (B := B)
          (handoffMove := handoffMove) hA]
      cases hlookup :
          B.toDescription.lookupTransition state (Tape.read tape) with
      | none =>
          simp
      | some t =>
          simp [TransitionDescription.offsetStates, offsetConfiguration]

theorem runConfig_seq_right
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed)
    (n : Nat) (c : MachineDescription.Configuration) :
    (seq A B handoffMove).toDescription.runConfig n
        (offsetConfiguration A.stateCount c) =
      offsetConfiguration A.stateCount
        (B.toDescription.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      simp [MachineDescription.runConfig,
        stepConfig_seq_right (A := A) (B := B)
          (handoffMove := handoffMove) hA c]
      cases hstep : B.toDescription.stepConfig c with
      | none =>
          simp [offsetConfiguration]
      | some next =>
          simp [ih next]

theorem seq_runConfig_reaches
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {nA nB : Nat} {Tin Tmid Tout : Tape Bool}
    (hArun :
      A.toDescription.runConfig nA
          { state := A.entry, tape := Tin } =
        { state := A.exit, tape := Tmid })
    (hAnoExit :
      forall k : Nat,
        k < nA ->
          (A.toDescription.runConfig k
            { state := A.entry, tape := Tin }).state ≠ A.exit)
    (hBrun :
      B.toDescription.runConfig nB
          { state := B.entry,
            tape := Tape.move handoffMove Tmid } =
        { state := B.exit, tape := Tout }) :
    (seq A B handoffMove).toDescription.runConfig
        (nA + (1 + nB))
        { state := (seq A B handoffMove).entry, tape := Tin } =
      { state := (seq A B handoffMove).exit, tape := Tout } := by
  have hseqA :
      (seq A B handoffMove).toDescription.runConfig nA
          { state := (seq A B handoffMove).entry, tape := Tin } =
        { state := A.exit, tape := Tmid } := by
    calc
      (seq A B handoffMove).toDescription.runConfig nA
          { state := (seq A B handoffMove).entry, tape := Tin } =
        A.toDescription.runConfig nA
          { state := A.entry, tape := Tin } := by
          simpa [Fragment.seq] using
            runConfig_seq_left_of_no_exit
              (A := A) (B := B) (handoffMove := handoffMove)
              hA hB (n := nA)
              (c := { state := A.entry, tape := Tin })
              hA.right.left hAnoExit
      _ = { state := A.exit, tape := Tmid } := hArun
  calc
    (seq A B handoffMove).toDescription.runConfig
        (nA + (1 + nB))
        { state := (seq A B handoffMove).entry, tape := Tin }
        =
      (seq A B handoffMove).toDescription.runConfig
        (1 + nB)
        ((seq A B handoffMove).toDescription.runConfig nA
          { state := (seq A B handoffMove).entry, tape := Tin }) := by
        rw [MachineDescription.runConfig_add]
    _ =
      (seq A B handoffMove).toDescription.runConfig
        (1 + nB)
        { state := A.exit, tape := Tmid } := by
        rw [hseqA]
    _ =
      (seq A B handoffMove).toDescription.runConfig nB
        { state := A.stateCount + B.entry,
          tape := Tape.move handoffMove Tmid } := by
        rw [Nat.add_comm 1 nB]
        change
          (match
            (seq A B handoffMove).toDescription.stepConfig
              { state := A.exit, tape := Tmid } with
          | none => { state := A.exit, tape := Tmid }
          | some next =>
              (seq A B handoffMove).toDescription.runConfig nB next) =
            (seq A B handoffMove).toDescription.runConfig nB
              { state := A.stateCount + B.entry,
                tape := Tape.move handoffMove Tmid }
        rw [stepConfig_seq_handoff
          (A := A) (B := B) (handoffMove := handoffMove) hA Tmid]
    _ =
      offsetConfiguration A.stateCount
        (B.toDescription.runConfig nB
          { state := B.entry,
            tape := Tape.move handoffMove Tmid }) := by
        exact runConfig_seq_right
          (A := A) (B := B) (handoffMove := handoffMove)
          hA nB
          { state := B.entry,
            tape := Tape.move handoffMove Tmid }
    _ =
      offsetConfiguration A.stateCount
        { state := B.exit, tape := Tout } := by
        rw [hBrun]
    _ =
      { state := (seq A B handoffMove).exit, tape := Tout } := by
        rfl

theorem seq_reaches
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {Tin Tmid Tout : Tape Bool}
    (hAReach :
      exists nA : Nat,
        A.toDescription.runConfig nA
            { state := A.entry, tape := Tin } =
          { state := A.exit, tape := Tmid } ∧
          forall k : Nat,
            k < nA ->
              (A.toDescription.runConfig k
                { state := A.entry, tape := Tin }).state ≠ A.exit)
    (hBReach :
      exists nB : Nat,
        B.toDescription.runConfig nB
            { state := B.entry,
              tape := Tape.move handoffMove Tmid } =
          { state := B.exit, tape := Tout }) :
    exists n : Nat,
      (seq A B handoffMove).toDescription.runConfig n
          { state := (seq A B handoffMove).entry, tape := Tin } =
        { state := (seq A B handoffMove).exit, tape := Tout } := by
  rcases hAReach with ⟨nA, hArun, hAnoExit⟩
  rcases hBReach with ⟨nB, hBrun⟩
  exists nA + (1 + nB)
  exact seq_runConfig_reaches
    (A := A) (B := B) (handoffMove := handoffMove)
    hA hB hArun hAnoExit hBrun

theorem seq_firstReaches
    {A B : Fragment} {handoffMove : Direction}
    (hA : A.WellFormed) (hB : B.WellFormed)
    {Tin Tmid Tout : Tape Bool}
    (hAReach :
      exists nA : Nat,
        A.toDescription.runConfig nA
            { state := A.entry, tape := Tin } =
          { state := A.exit, tape := Tmid } ∧
          forall k : Nat,
            k < nA ->
              (A.toDescription.runConfig k
                { state := A.entry, tape := Tin }).state ≠ A.exit)
    (hBReach :
      exists nB : Nat,
        B.toDescription.runConfig nB
            { state := B.entry,
              tape := Tape.move handoffMove Tmid } =
          { state := B.exit, tape := Tout } ∧
          forall k : Nat,
            k < nB ->
              (B.toDescription.runConfig k
                { state := B.entry,
                  tape := Tape.move handoffMove Tmid }).state ≠ B.exit) :
    exists n : Nat,
      (seq A B handoffMove).toDescription.runConfig n
          { state := (seq A B handoffMove).entry, tape := Tin } =
        { state := (seq A B handoffMove).exit, tape := Tout } ∧
      forall k : Nat,
        k < n ->
          ((seq A B handoffMove).toDescription.runConfig k
            { state := (seq A B handoffMove).entry,
              tape := Tin }).state ≠
            (seq A B handoffMove).exit := by
  rcases hAReach with ⟨nA, hArun, hAnoExit⟩
  rcases hBReach with ⟨nB, hBrun, hBnoExit⟩
  let startSeq : MachineDescription.Configuration :=
    { state := (seq A B handoffMove).entry, tape := Tin }
  let startA : MachineDescription.Configuration :=
    { state := A.entry, tape := Tin }
  let startB : MachineDescription.Configuration :=
    { state := B.entry, tape := Tape.move handoffMove Tmid }
  have hseqA :
      (seq A B handoffMove).toDescription.runConfig nA startSeq =
        { state := A.exit, tape := Tmid } := by
    calc
      (seq A B handoffMove).toDescription.runConfig nA startSeq =
        A.toDescription.runConfig nA startA := by
          simpa [startSeq, startA, Fragment.seq] using
            runConfig_seq_left_of_no_exit
              (A := A) (B := B) (handoffMove := handoffMove)
              hA hB (n := nA)
              (c := { state := A.entry, tape := Tin })
              hA.right.left hAnoExit
      _ = { state := A.exit, tape := Tmid } := hArun
  exists nA + (1 + nB)
  constructor
  · simpa [startSeq] using
      seq_runConfig_reaches
        (A := A) (B := B) (handoffMove := handoffMove)
        hA hB hArun hAnoExit hBrun
  · intro k hk
    intro hfinal
    have hfinalSeq :
        ((seq A B handoffMove).toDescription.runConfig k
          startSeq).state =
          (seq A B handoffMove).exit := by
      simpa [startSeq] using hfinal
    by_cases hkLeft : k < nA
    · have hseqk :
          (seq A B handoffMove).toDescription.runConfig k startSeq =
            A.toDescription.runConfig k startA := by
        simpa [startSeq, startA, Fragment.seq] using
          runConfig_seq_left_of_no_exit
            (A := A) (B := B) (handoffMove := handoffMove)
            hA hB (n := k)
            (c := { state := A.entry, tape := Tin })
            hA.right.left
            (fun j hj => hAnoExit j (Nat.lt_trans hj hkLeft))
      have hstateBound :
          ((seq A B handoffMove).toDescription.runConfig k
            startSeq).state < A.stateCount := by
        rw [hseqk]
        exact MachineDescription.runConfig_state_bound
          (MachineDescription.Fragment.toDescription_wellFormed hA)
          hA.right.left
      have hexitBound :
          (seq A B handoffMove).exit < A.stateCount := by
        rw [hfinalSeq] at hstateBound
        exact hstateBound
      have hbad :
          A.stateCount + B.exit < A.stateCount := by
        simpa [Fragment.seq] using hexitBound
      omega
    · have hnA_le_k : nA ≤ k := Nat.le_of_not_gt hkLeft
      let d : Nat := k - nA
      have hk_eq : k = nA + d := by
        omega
      have hd_bound : d < 1 + nB := by
        omega
      cases hd : d with
      | zero =>
          have hk_nA : k = nA := by
            omega
          have hstateBound :
              ((seq A B handoffMove).toDescription.runConfig k
                startSeq).state < A.stateCount := by
            rw [hk_nA, hseqA]
            exact hA.right.right.left
          have hexitBound :
              (seq A B handoffMove).exit < A.stateCount := by
            rw [hfinalSeq] at hstateBound
            exact hstateBound
          have hbad :
              A.stateCount + B.exit < A.stateCount := by
            simpa [Fragment.seq] using hexitBound
          omega
      | succ j =>
          have hj_bound : j < nB := by
            omega
          have hk_succ : k = nA + (1 + j) := by
            omega
          have hseqk :
              (seq A B handoffMove).toDescription.runConfig k
                  startSeq =
                offsetConfiguration A.stateCount
                  (B.toDescription.runConfig j startB) := by
            calc
              (seq A B handoffMove).toDescription.runConfig k
                  startSeq =
                (seq A B handoffMove).toDescription.runConfig
                    (nA + (1 + j)) startSeq := by
                    rw [hk_succ]
              _ =
                (seq A B handoffMove).toDescription.runConfig
                    (1 + j)
                    ((seq A B handoffMove).toDescription.runConfig nA
                      startSeq) := by
                    rw [MachineDescription.runConfig_add]
              _ =
                (seq A B handoffMove).toDescription.runConfig
                    (1 + j)
                    { state := A.exit, tape := Tmid } := by
                    rw [hseqA]
              _ =
                (seq A B handoffMove).toDescription.runConfig j
                    { state := A.stateCount + B.entry,
                      tape := Tape.move handoffMove Tmid } := by
                    rw [Nat.add_comm 1 j]
                    change
                      (match
                        (seq A B handoffMove).toDescription.stepConfig
                          { state := A.exit, tape := Tmid } with
                      | none => { state := A.exit, tape := Tmid }
                      | some next =>
                          (seq A B handoffMove).toDescription.runConfig
                            j next) =
                        (seq A B handoffMove).toDescription.runConfig j
                          { state := A.stateCount + B.entry,
                            tape := Tape.move handoffMove Tmid }
                    rw [stepConfig_seq_handoff
                      (A := A) (B := B) (handoffMove := handoffMove)
                      hA Tmid]
              _ =
                offsetConfiguration A.stateCount
                  (B.toDescription.runConfig j startB) := by
                    simpa [startB] using
                      runConfig_seq_right
                        (A := A) (B := B)
                        (handoffMove := handoffMove)
                        hA j
                        { state := B.entry,
                          tape := Tape.move handoffMove Tmid }
          have hstateEq :
              (offsetConfiguration A.stateCount
                (B.toDescription.runConfig j startB)).state =
                (seq A B handoffMove).exit := by
            simpa [hseqk] using hfinalSeq
          have hBexit :
              (B.toDescription.runConfig j startB).state = B.exit := by
            apply Nat.add_left_cancel (n := A.stateCount)
            simpa [offsetConfiguration, Fragment.seq] using hstateEq
          exact hBnoExit j hj_bound hBexit

end Fragment

theorem seqSubroutine_reaches
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAReach :
      exists nA : Nat,
        A.runConfig nA { state := A.start, tape := Tin } =
          { state := A.halt, tape := Tmid } ∧
        forall k : Nat,
          k < nA ->
            (A.runConfig k
              { state := A.start, tape := Tin }).state ≠ A.halt)
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start,
              tape := Tape.move handoffMove Tmid } =
          { state := B.halt, tape := Tout }) :
    exists n : Nat,
      (seqSubroutine A B handoffMove).runConfig n
          { state := (seqSubroutine A B handoffMove).start,
            tape := Tin } =
        { state := (seqSubroutine A B handoffMove).halt,
          tape := Tout } := by
  simpa [seqSubroutine, asFragment] using
    Fragment.seq_reaches
      (A := A.asFragment) (B := B.asFragment)
      (handoffMove := handoffMove)
      (asFragment_wellFormed hA) (asFragment_wellFormed hB)
      hAReach hBReach

theorem seqSubroutine_reaches_of_runConfig_eq
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {nA : Nat} {Tin Tmid Tout : Tape Bool}
    (hArun :
      A.runConfig nA { state := A.start, tape := Tin } =
        { state := A.halt, tape := Tmid })
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start,
              tape := Tape.move handoffMove Tmid } =
          { state := B.halt, tape := Tout }) :
    exists n : Nat,
      (seqSubroutine A B handoffMove).runConfig n
          { state := (seqSubroutine A B handoffMove).start,
            tape := Tin } =
        { state := (seqSubroutine A B handoffMove).halt,
          tape := Tout } := by
  rcases firstReaches_halt_of_runConfig_eq hA.right hArun with
    ⟨m, _hmle, hmrun, hmfirst⟩
  exact seqSubroutine_reaches hA hB
    ⟨m, hmrun, hmfirst⟩ hBReach

end MachineDescription

theorem fixedDescriptionBoundedSimulatorPhaseRealizes_seq
    {entryTape midTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool}
    {phaseA phaseB :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout}
    {A B : MachineDescription.Fragment} {handoffMove : Direction}
    (hA :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        entryTape midTape phaseA A)
    (hB :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (fun L => Tape.move handoffMove (midTape L))
        exitTape phaseB B) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      entryTape exitTape (fun L => phaseB (phaseA L))
      (MachineDescription.Fragment.seq A B handoffMove) := by
  constructor
  · exact MachineDescription.Fragment.seq_wellFormed hA.left hB.left
  · intro L
    simpa [FixedDescriptionBoundedSimulatorFragmentReaches] using
      MachineDescription.Fragment.seq_firstReaches
        (A := A) (B := B) (handoffMove := handoffMove)
        hA.left hB.left
        (Tin := entryTape L)
        (Tmid := midTape (phaseA L))
        (Tout := exitTape (phaseB (phaseA L)))
        (hA.right L)
        (hB.right (phaseA L))

structure FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction)
    (targets : FixedDescriptionBoundedSimulatorPhaseTargets D) :
    Prop where
  decodeLayout :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      FixedDescriptionBoundedSimulatorLayoutTape
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.decodeLayout S.decodeLayout
  simulateStep :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.simulateStep S.simulateStep
  repeatControl :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.repeatControl S.repeatControl
  emitLayout :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.emitLayout S.emitLayout

def FixedDescriptionBoundedSimulatorSkeletonRealizes
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    (S.toDescription handoffMove).HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L)

def FixedDescriptionBoundedSimulatorSkeletonRealizesExact
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    (S.toDescription handoffMove).HaltsWithExactOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L)

theorem fixedDescriptionBoundedSimulatorSkeletonRealizes_of_exact
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizesExact
      D S handoffMove) :
    FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove := by
  intro L
  exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
    (h L)

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizes
      D S handoffMove) :
    FixedDescriptionBoundedSimulatorTableRealizes
      D (S.toDescription handoffMove) := by
  constructor
  · exact
      MachineDescription.FixedSimulatorTableSkeleton.toDescription_wellFormed
        S handoffMove
  · exact h

theorem fixedDescriptionBoundedSimulatorSkeletonRealizes_output
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizes
      D S handoffMove)
    (L : MachineDescription.SimulatorLayout) :
    (S.toDescription handoffMove).HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L) :=
  h L

def FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists S : MachineDescription.FixedSimulatorTableSkeleton,
      exists handoffMove : Direction,
        FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨S, handoffMove, hS⟩
  exact ⟨S.toDescription handoffMove,
    fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes hS⟩

def FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction : Prop :=
  forall D : MachineDescription,
    exists S : MachineDescription.FixedSimulatorTableSkeleton,
      exists handoffMove : Direction,
      exists targets : FixedDescriptionBoundedSimulatorPhaseTargets D,
        FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
          D S handoffMove targets

def FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness : Prop :=
  forall D : MachineDescription,
    forall S : MachineDescription.FixedSimulatorTableSkeleton,
    forall handoffMove : Direction,
    forall targets : FixedDescriptionBoundedSimulatorPhaseTargets D,
      FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
        D S handoffMove targets ->
      FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseSoundness :
    FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness := by
  intro D S handoffMove targets htargets
  have hDecodeSim :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => targets.simulateStep (targets.decodeLayout L))
        (MachineDescription.Fragment.seq
          S.decodeLayout S.simulateStep handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := targets.decodeLayout)
      (phaseB := targets.simulateStep)
      (A := S.decodeLayout)
      (B := S.simulateStep)
      (handoffMove := handoffMove)
      htargets.decodeLayout htargets.simulateStep
  have hDecodeSimRepeat :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L =>
          targets.repeatControl
            (targets.simulateStep (targets.decodeLayout L)))
        (MachineDescription.Fragment.seq
          (MachineDescription.Fragment.seq
            S.decodeLayout S.simulateStep handoffMove)
          S.repeatControl handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := fun L =>
        targets.simulateStep (targets.decodeLayout L))
      (phaseB := targets.repeatControl)
      (A := MachineDescription.Fragment.seq
        S.decodeLayout S.simulateStep handoffMove)
      (B := S.repeatControl)
      (handoffMove := handoffMove)
      hDecodeSim htargets.repeatControl
  have hAllPhases :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L =>
          targets.emitLayout
            (targets.repeatControl
              (targets.simulateStep (targets.decodeLayout L))))
        (MachineDescription.Fragment.seq
          (MachineDescription.Fragment.seq
            (MachineDescription.Fragment.seq
              S.decodeLayout S.simulateStep handoffMove)
            S.repeatControl handoffMove)
          S.emitLayout handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := fun L =>
        targets.repeatControl
          (targets.simulateStep (targets.decodeLayout L)))
      (phaseB := targets.emitLayout)
      (A := MachineDescription.Fragment.seq
        (MachineDescription.Fragment.seq
          S.decodeLayout S.simulateStep handoffMove)
        S.repeatControl handoffMove)
      (B := S.emitLayout)
      (handoffMove := handoffMove)
      hDecodeSimRepeat htargets.emitLayout
  intro L
  have hOutput :=
    (fixedDescriptionBoundedSimulatorPhaseRealizes_standard_output
      hAllPhases).right L
  have hpipeline :
      targets.emitLayout
          (targets.repeatControl
            (targets.simulateStep (targets.decodeLayout L))) =
        MachineDescription.SimulatorLayout.run D L.stage L :=
    targets.pipeline_correct L
  simpa [MachineDescription.FixedSimulatorTableSkeleton.toDescription,
    MachineDescription.FixedSimulatorTableSkeleton.toFragment,
    FixedDescriptionBoundedSimulatorOutput, hpipeline] using hOutput

theorem fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨S, handoffMove, targets, htargets⟩
  exact ⟨S, handoffMove,
    hsound D S handoffMove targets htargets⟩

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
      hsound hcompile)

theorem pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile
    (fun w n => accept.HaltsIn n w)
    (fun w n => reject.HaltsIn n w)

theorem pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (hcompile :
      PairedRecognizerBoundedDovetailTableCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  cases hcompile accept reject with
  | intro decider hdecider =>
      exists decider
      constructor
      · exact hdecider.left
      · intro w b
        constructor
        · intro hhalt
          cases (hdecider.right w b).mp hhalt with
          | intro limit hlimit =>
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
                at hlimit
        · intro hprog
          cases hprog with
          | intro limit hlimit =>
              apply (hdecider.right w b).mpr
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]

theorem pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler
    (hcompile : PairedRecognizerDovetailDescriptionCompilerPrinciple) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdecider.right w b).mp hhalt with ⟨limit, hlimit⟩
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using hlimit⟩
    · intro hlimit
      rcases hlimit with ⟨limit, hlimit⟩
      apply (hdecider.right w b).mpr
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using hlimit⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_iff_pairedRecognizerDovetailDescriptionCompiler :
    PairedRecognizerBoundedDovetailTableCompilerConstruction <->
      PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  ⟨pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler,
    pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler⟩

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputRealizer_and_searchDriver
      hrunner hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
      hrunner hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
      hrunner hdriver)

theorem dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    DovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile (DovetailProgram accept reject)

theorem pairedRecognizerDovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler hcompile)

theorem programAcceptorCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    ProgramAcceptorCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programAcceptableByDescription_turingAcceptable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem programBoolDeciderCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    ProgramBoolDeciderCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programBoolDecidableByDescription_turingDecidable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    {accept reject : Word Bool -> Nat -> Prop}
    (htraces : ComplementaryAcceptanceTraces accept reject L) :
    TuringDecidable L := by
  cases hcompile accept reject with
  | intro D hD =>
      exact programBoolDecidableByDescription_turingDecidable
        (Exists.intro (DovetailProgram accept reject)
          (Exists.intro D (And.intro (dovetailProgram_decides htraces) hD)))

theorem reCoRe_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerableWithComplement L) :
    TuringDecidable L := by
  cases recursivelyEnumerable_with_complement_has_complementaryTraces h with
  | intro accept haccept =>
      cases haccept with
      | intro reject htraces =>
          exact complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
            hcompile htraces

theorem reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    ReCoReToDecidablePrinciple Bool := by
  intro L h
  exact reCoRe_turingDecidable_of_dovetailDescriptionCompiler hcompile h

/-!
## Encoded input languages and universal runners

Section 5.3 encodes machine descriptions and their inputs over the common
{name}`MachineCodeSymbol` alphabet, while concrete descriptions still execute
on Boolean tapes. The next predicates isolate the exact compiler and runner
obligations needed for a concrete universal machine.
-/

def MachineDescriptionAcceptsEncodedInputLanguage
    (D : MachineDescription)
    (L : Language MachineCodeSymbol) : Prop :=
  D.WellFormed ∧ Language.Equal (MachineDescription.EncodedInputLanguage D) L

def EncodedInputProgramCompiledByDescription
    (P : StagedProgram MachineCodeSymbol Unit)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word MachineCodeSymbol,
      D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput w) <->
        ProgramHaltsWithOutput P w []

def EncodedInputProgramAcceptorCompilationPrinciple : Prop :=
  forall P : StagedProgram MachineCodeSymbol Unit,
    exists D : MachineDescription,
      EncodedInputProgramCompiledByDescription P D

def EncodedInputDescriptionCompilerPrinciple : Prop :=
  forall L : Language MachineCodeSymbol,
    RecursivelyEnumerable L ->
      exists D : MachineDescription,
        MachineDescriptionAcceptsEncodedInputLanguage D L

def CodeUniversalMachineSpec
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall machine input : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input) <->
        MachineDescription.CodeAccepts machine input

def ImmediateHaltingDescription : MachineDescription where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem immediateHaltingDescription_haltsOnInput
    (input : Word Bool) :
    ImmediateHaltingDescription.HaltsOnInput input := by
  exact ⟨0, rfl⟩

theorem codeAccepts_empty_false
    (input : Word MachineCodeSymbol) :
    ¬ MachineDescription.CodeAccepts [] input := by
  intro h
  rcases h with ⟨D, hdecode, _⟩
  simp [MachineDescription.decodeDescription] at hdecode

theorem codeUniversalMachineSpec_rawConcat_inconsistent
    (universal : TuringMachine MachineCodeSymbol state) :
    ¬ CodeUniversalMachineSpec universal := by
  intro hspec
  let D := ImmediateHaltingDescription
  have haccept :
      MachineDescription.CodeAccepts
        (MachineDescription.encodeDescription D) [] :=
    MachineDescription.codeAccepts_of_encodeDescription
      (immediateHaltingDescription_haltsOnInput [])
  have hhalts :
      TuringMachine.HaltsOnInput universal
        (Languages.Word.Concat (MachineDescription.encodeDescription D) []) :=
    (hspec (MachineDescription.encodeDescription D) []).mpr haccept
  have hhaltsEmpty :
      TuringMachine.HaltsOnInput universal
        (Languages.Word.Concat [] (MachineDescription.encodeDescription D)) := by
    simpa [Languages.Word.Concat] using hhalts
  have hfalse :
      MachineDescription.CodeAccepts []
        (MachineDescription.encodeDescription D) :=
    (hspec [] (MachineDescription.encodeDescription D)).mp hhaltsEmpty
  exact codeAccepts_empty_false (MachineDescription.encodeDescription D) hfalse

def CodeUniversalPrefixMachineSpec
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall encoded : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput universal encoded <->
      MachineDescription.CodePrefixAccepts encoded

def CodeUniversalPrefixMachineRowLanguage
    (universal : TuringMachine MachineCodeSymbol state)
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => TuringMachine.HaltsOnInput universal
    (Languages.Word.Concat machine input)

def CodeUniversalPrefixRowsCoverAcceptableLanguages
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall L : Language MachineCodeSymbol, RecursivelyEnumerable L ->
    exists machine : Word MachineCodeSymbol,
      Language.Equal
        (CodeUniversalPrefixMachineRowLanguage universal machine) L

def CodeUniversalPrefixRunnerConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalPrefixMachineSpec universal

def CodeUniversalPrefixRowsCoverConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalPrefixMachineSpec universal ∧
        CodeUniversalPrefixRowsCoverAcceptableLanguages universal

structure CodeUniversalPrefixSection53Closeout where
  encodedInputProgramCompiler : EncodedInputProgramAcceptorCompilationPrinciple
  universalRunner : CodeUniversalPrefixRunnerConstruction

theorem codeUniversalPrefixMachine_halts_on_encoded_description_iff
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat (MachineDescription.encodeDescription D) input) <->
        D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput input) := by
  exact Iff.trans
    (hspec (Languages.Word.Concat (MachineDescription.encodeDescription D) input))
    (MachineDescription.codePrefixAccepts_encodeDescription_append_iff D input)

theorem codeUniversalPrefixMachine_rowLanguage_equal_encodedInputLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (D : MachineDescription) :
    Language.Equal
      (CodeUniversalPrefixMachineRowLanguage universal
        (MachineDescription.encodeDescription D))
      (MachineDescription.EncodedInputLanguage D) :=
  codeUniversalPrefixMachine_halts_on_encoded_description_iff hspec D

theorem codeUniversalPrefixRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (hcompile : EncodedInputDescriptionCompilerPrinciple) :
    CodeUniversalPrefixRowsCoverAcceptableLanguages universal := by
  intro L hL
  cases hcompile L hL with
  | intro D hD =>
      exists MachineDescription.encodeDescription D
      exact Language.equal_trans
        (codeUniversalPrefixMachine_rowLanguage_equal_encodedInputLanguage
          hspec D)
        hD.right

theorem codeUniversalPrefixRowsCoverConstruction_of_constructions
    (hcompile : EncodedInputDescriptionCompilerPrinciple)
    (hrunner : CodeUniversalPrefixRunnerConstruction) :
    CodeUniversalPrefixRowsCoverConstruction := by
  unfold CodeUniversalPrefixRunnerConstruction at hrunner
  rcases hrunner with ⟨state, universal, hspec⟩
  exact
    ⟨state, universal,
      hspec,
      codeUniversalPrefixRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
        hspec hcompile⟩

def CodeUniversalMachineRowLanguage
    (universal : TuringMachine MachineCodeSymbol state)
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => TuringMachine.HaltsOnInput universal
    (Languages.Word.Concat machine input)

def CodeUniversalRowsCoverAcceptableLanguages
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall L : Language MachineCodeSymbol, RecursivelyEnumerable L ->
    exists machine : Word MachineCodeSymbol,
      Language.Equal (CodeUniversalMachineRowLanguage universal machine) L

def CodeUniversalRunnerConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalMachineSpec universal

theorem not_codeUniversalRunnerConstruction :
    ¬ CodeUniversalRunnerConstruction := by
  intro h
  unfold CodeUniversalRunnerConstruction at h
  rcases h with ⟨state, universal, hspec⟩
  exact codeUniversalMachineSpec_rawConcat_inconsistent universal hspec

def CodeUniversalRowsCoverConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalMachineSpec universal ∧
        CodeUniversalRowsCoverAcceptableLanguages universal

structure CodeUniversalSection53Closeout where
  encodedInputProgramCompiler : EncodedInputProgramAcceptorCompilationPrinciple
  universalRunner : CodeUniversalRunnerConstruction

theorem not_codeUniversalSection53Closeout :
    ¬ CodeUniversalSection53Closeout := by
  intro hclose
  exact not_codeUniversalRunnerConstruction hclose.universalRunner

theorem encodedInputProgramCompiledByDescription_acceptsLanguage
    {P : StagedProgram MachineCodeSymbol Unit}
    {D : MachineDescription}
    {L : Language MachineCodeSymbol}
    (hP : ProgramAcceptsLanguage P L)
    (hcompile : EncodedInputProgramCompiledByDescription P D) :
    MachineDescriptionAcceptsEncodedInputLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w) (hP w)

theorem encodedInputDescriptionCompilerPrinciple_of_programCompiler
    (hcompile : EncodedInputProgramAcceptorCompilationPrinciple) :
    EncodedInputDescriptionCompilerPrinciple := by
  intro L hL
  cases recursivelyEnumerable_has_acceptanceTrace hL with
  | intro trace htrace =>
      cases hcompile (TraceRecognizerProgram trace) with
      | intro D hD =>
          exists D
          exact encodedInputProgramCompiledByDescription_acceptsLanguage
            (traceRecognizerProgram_acceptsLanguage htrace) hD

theorem codeUniversalMachineRowLanguage_equal_codeAcceptedLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (machine : Word MachineCodeSymbol) :
    Language.Equal
      (CodeUniversalMachineRowLanguage universal machine)
      (MachineDescription.CodeAcceptedLanguage machine) :=
  hspec machine

theorem codeUniversalMachineRowLanguage_equal_encodedInputLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (D : MachineDescription) :
    Language.Equal
      (CodeUniversalMachineRowLanguage universal
        (MachineDescription.encodeDescription D))
      (MachineDescription.EncodedInputLanguage D) := by
  intro input
  exact Iff.trans
    (codeUniversalMachineRowLanguage_equal_codeAcceptedLanguage
      hspec (MachineDescription.encodeDescription D) input)
    (MachineDescription.codeAccepts_encodeDescription_iff D input)

theorem codeUniversalRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (hcompile : EncodedInputDescriptionCompilerPrinciple) :
    CodeUniversalRowsCoverAcceptableLanguages universal := by
  intro L hL
  cases hcompile L hL with
  | intro D hD =>
      exists MachineDescription.encodeDescription D
      exact Language.equal_trans
        (codeUniversalMachineRowLanguage_equal_encodedInputLanguage hspec D)
        hD.right

theorem codeUniversalRowsCoverConstruction_of_constructions
    (hcompile : EncodedInputDescriptionCompilerPrinciple)
    (hrunner : CodeUniversalRunnerConstruction) :
    CodeUniversalRowsCoverConstruction := by
  cases hrunner with
  | intro state hstate =>
      cases hstate with
      | intro universal hspec =>
          exact
            Exists.intro state
              (Exists.intro universal
                (And.intro hspec
                  (codeUniversalRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
                    hspec hcompile)))

theorem encodedInputDescriptionCompilerPrinciple_of_section53Closeout
    (hclose : CodeUniversalSection53Closeout) :
    EncodedInputDescriptionCompilerPrinciple :=
  encodedInputDescriptionCompilerPrinciple_of_programCompiler
    hclose.encodedInputProgramCompiler

theorem codeUniversalPrefixRowsCoverConstruction_of_section53Closeout
    (hclose : CodeUniversalPrefixSection53Closeout) :
    CodeUniversalPrefixRowsCoverConstruction :=
  codeUniversalPrefixRowsCoverConstruction_of_constructions
    (encodedInputDescriptionCompilerPrinciple_of_programCompiler
      hclose.encodedInputProgramCompiler)
    hclose.universalRunner

theorem codeUniversalRowsCoverConstruction_of_section53Closeout
    (hclose : CodeUniversalSection53Closeout) :
    CodeUniversalRowsCoverConstruction :=
  codeUniversalRowsCoverConstruction_of_constructions
    (encodedInputDescriptionCompilerPrinciple_of_section53Closeout hclose)
    hclose.universalRunner

/-!
## Compiled partial-function ranges
-/

def PartialFunctionCompiledByDescription
    (f : Word input -> Option (Word Bool))
    (encodeInput : input -> Bool)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word input,
      match f w with
      | some out => D.HaltsWithOutput (EncodeWord encodeInput w) out
      | none => ¬ D.HaltsOnInput (EncodeWord encodeInput w)

theorem partialFunctionCompiledByDescription_turingComputablePartial
    {f : Word input -> Option (Word Bool)}
    {encodeInput : input -> Bool}
    {D : MachineDescription}
    (h : PartialFunctionCompiledByDescription f encodeInput D) :
    TuringComputablePartial f := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists encodeInput
  exists fun b : Bool => b
  intro w
  cases hf : f w with
  | none =>
      have hnone := h.right w
      rw [hf] at hnone
      intro hhalt
      exact hnone ((MachineDescription.toTuringMachine_haltsOnInput_iff
        h.left (EncodeWord encodeInput w)).mp hhalt)
  | some out =>
      have hsome := h.right w
      rw [hf] at hsome
      simp at hsome
      simpa [encodeWord_id] using
        (MachineDescription.toTuringMachine_haltsWithOutput_iff
          h.left (EncodeWord encodeInput w) out).mpr hsome

def PartialUnaryTuringComputableRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool),
    TuringComputablePartial f ∧ Language.Equal (PartialRangeLanguage f) L

def CompiledPartialUnaryRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool), exists D : MachineDescription,
    PartialFunctionCompiledByDescription f (fun _ : Unit => true) D ∧
      Language.Equal (PartialRangeLanguage f) L

def CompiledPartialUnaryFunctionProgramRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool), exists D : MachineDescription,
    PartialFunctionCompiledByDescription f (fun _ : Unit => true) D ∧
      Language.Equal (ProgramRangeLanguage (PartialFunctionProgram f)) L

def PartialUnaryRangeDescriptionCompilerPrinciple : Prop :=
  forall f : Word Unit -> Option (Word Bool),
    exists D : MachineDescription,
      PartialFunctionCompiledByDescription f (fun _ : Unit => true) D

def SemanticPartialUnaryRangeCompilerAssumption : Prop :=
  PartialUnaryRangeDescriptionCompilerPrinciple

/-!
The partial-unary compiler principle is intentionally strong: its source is an
arbitrary semantic Lean partial function, not a finite program syntax.  The
following consequences make that strength explicit.  Concrete closeouts should
therefore keep this principle as a named construction boundary unless a finite
source syntax is supplied.
-/

theorem partialUnaryRangeDescriptionCompilerPrinciple_turingComputablePartial
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (f : Word Unit -> Option (Word Bool)) :
    TuringComputablePartial f := by
  rcases hcompile f with ⟨D, hD⟩
  exact partialFunctionCompiledByDescription_turingComputablePartial hD

theorem partialUnaryRangeDescriptionCompilerPrinciple_compiledRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (f : Word Unit -> Option (Word Bool)) :
    CompiledPartialUnaryRange (PartialRangeLanguage f) := by
  rcases hcompile f with ⟨D, hD⟩
  exact ⟨f, D, hD, Language.equal_refl (PartialRangeLanguage f)⟩

theorem partialUnaryRangeDescriptionCompilerPrinciple_compiledProgramRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (f : Word Unit -> Option (Word Bool)) :
    CompiledPartialUnaryFunctionProgramRange
      (ProgramRangeLanguage (PartialFunctionProgram f)) := by
  rcases hcompile f with ⟨D, hD⟩
  exact ⟨f, D, hD,
    Language.equal_refl
      (ProgramRangeLanguage (PartialFunctionProgram f))⟩

theorem compiledPartialUnaryRange_partialRangeOfUnaryFunction
    {L : Language Bool}
    (h : CompiledPartialUnaryRange L) :
    PartialRangeOfUnaryFunction L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro _ hD =>
          exists f
          exact hD.right

theorem compiledPartialUnaryRange_turingComputableRange
    {L : Language Bool}
    (h : CompiledPartialUnaryRange L) :
    PartialUnaryTuringComputableRange L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro D hD =>
          exists f
          constructor
          · exact partialFunctionCompiledByDescription_turingComputablePartial
              hD.left
          · exact hD.right

theorem compiledPartialUnaryFunctionProgramRange_compiledRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    CompiledPartialUnaryRange L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro D hD =>
          exists f
          exists D
          constructor
          · exact hD.left
          · exact Language.equal_trans
              (Language.equal_symm (partialFunctionProgram_range f))
              hD.right

theorem compiledPartialUnaryFunctionProgramRange_turingComputableRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    PartialUnaryTuringComputableRange L :=
  compiledPartialUnaryRange_turingComputableRange
    (compiledPartialUnaryFunctionProgramRange_compiledRange h)

theorem compiledPartialUnaryFunctionProgramRange_partialRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    PartialRangeOfUnaryFunction L :=
  compiledPartialUnaryRange_partialRangeOfUnaryFunction
    (compiledPartialUnaryFunctionProgramRange_compiledRange h)

theorem compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartialRangeOfUnaryFunction L) :
    CompiledPartialUnaryRange L := by
  cases h with
  | intro f hf =>
      cases hcompile f with
      | intro D hD =>
          exact Exists.intro f (Exists.intro D (And.intro hD hf))

theorem compiledPartialUnaryRange_of_partiallyListable
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartiallyListable L) :
    CompiledPartialUnaryRange L :=
  compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    hcompile (partiallyListable_partialRangeOfUnaryFunction h)

theorem compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartialRangeOfUnaryFunction L) :
    CompiledPartialUnaryFunctionProgramRange L := by
  cases h with
  | intro f hf =>
      cases hcompile f with
      | intro D hD =>
          exact Exists.intro f
            (Exists.intro D
              (And.intro hD
                (Language.equal_trans (partialFunctionProgram_range f) hf)))

theorem compiledPartialUnaryFunctionProgramRange_of_partiallyListable
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartiallyListable L) :
    CompiledPartialUnaryFunctionProgramRange L :=
  compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    hcompile (partiallyListable_partialRangeOfUnaryFunction h)

theorem compiledPartialUnaryRange_of_unaryProgramRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (P : StagedProgram Unit Bool) :
    CompiledPartialUnaryRange (ProgramRangeLanguage P) :=
  compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    hcompile (programRange_partialRangeOfUnaryFunction P)

theorem compiledPartialUnaryFunctionProgramRange_of_unaryProgramRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (P : StagedProgram Unit Bool) :
    CompiledPartialUnaryFunctionProgramRange (ProgramRangeLanguage P) :=
  compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    hcompile (programRange_partialRangeOfUnaryFunction P)

end Computability
end FoC
