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

def HaltsFromTapeIn (D : MachineDescription)
    (n : Nat) (Tin Tout : Tape Bool) : Prop :=
  let final := D.runConfig n { state := D.start, tape := Tin }
  final.state = D.halt ∧ final.tape = Tout

def HaltsFromTape (D : MachineDescription)
    (Tin Tout : Tape Bool) : Prop :=
  exists n : Nat, D.HaltsFromTapeIn n Tin Tout

theorem haltsWithOutput_of_haltsWithTape
    {D : MachineDescription} {w : Word Bool} {T : Tape Bool}
    (h : D.HaltsWithTape w T) :
    D.HaltsWithOutput w (Tape.normalizedOutput T) := by
  rcases h with ⟨n, hn⟩
  rcases hn with ⟨hstate, htape⟩
  exact ⟨n, ⟨hstate, by rw [htape]⟩⟩

theorem runConfig_eq_halt_of_haltsWithTape
    {D : MachineDescription} {w : Word Bool} {T : Tape Bool}
    (h : D.HaltsWithTape w T) :
    exists n : Nat,
      D.runConfig n { state := D.start, tape := Tape.input w } =
        { state := D.halt, tape := T } := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  change D.runConfig n (D.initial w) = { state := D.halt, tape := T }
  cases hfinal : D.runConfig n (D.initial w) with
  | mk state tape =>
      rcases hn with ⟨hstate, htape⟩
      simp [hfinal] at hstate htape
      simp [hstate, htape]

theorem runConfig_eq_halt_of_haltsFromTape
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    exists n : Nat,
      D.runConfig n { state := D.start, tape := Tin } =
        { state := D.halt, tape := Tout } := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  change D.runConfig n { state := D.start, tape := Tin } = { state := D.halt, tape := Tout }
  cases hfinal : D.runConfig n { state := D.start, tape := Tin } with
  | mk state tape =>
      rcases hn with ⟨hstate, htape⟩
      simp [hfinal] at hstate htape
      simp [hstate, htape]

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

theorem haltsWithOutput_functional_of_haltTransitionFree
    {D : MachineDescription} {w out₁ out₂ : Word Bool}
    (hD : D.HaltTransitionFree)
    (h₁ : D.HaltsWithOutput w out₁)
    (h₂ : D.HaltsWithOutput w out₂) :
    out₁ = out₂ := by
  rcases h₁ with ⟨n₁, h₁⟩
  rcases h₂ with ⟨n₂, h₂⟩
  let c₀ := D.initial w
  have hordered :
      forall {n m : Nat} {outn outm : Word Bool},
        n ≤ m ->
        D.HaltsWithOutputIn n w outn ->
        D.HaltsWithOutputIn m w outm ->
          outn = outm := by
    intro n m outn outm hle hn hm
    let d := m - n
    have hm_eq : m = n + d := by
      omega
    have hconfig_n :
        D.runConfig n c₀ =
          { state := D.halt, tape := (D.runConfig n c₀).tape } := by
      cases hfinal : D.runConfig n c₀ with
      | mk state tape =>
          have hstate : state = D.halt := by
            simpa [HaltsWithOutputIn, c₀, hfinal] using hn.left
          simp [hstate]
    have hrunm :
        D.runConfig m c₀ = D.runConfig d (D.runConfig n c₀) := by
      rw [hm_eq, runConfig_add]
    have hstay :
        D.runConfig d (D.runConfig n c₀) =
          D.runConfig n c₀ := by
      rw [hconfig_n]
      exact MachineDescription.runConfig_halt
        hD (D.runConfig n c₀).tape d
    have htapes :
        (D.runConfig m c₀).tape = (D.runConfig n c₀).tape := by
      rw [hrunm, hstay]
    have hnout :
        Tape.normalizedOutput (D.runConfig n c₀).tape = outn := by
      simpa [HaltsWithOutputIn, c₀] using hn.right
    have hmout :
        Tape.normalizedOutput (D.runConfig m c₀).tape = outm := by
      simpa [HaltsWithOutputIn, c₀] using hm.right
    rw [htapes, hnout] at hmout
    exact hmout
  by_cases hle : n₁ ≤ n₂
  · exact hordered hle h₁ h₂
  · have hle' : n₂ ≤ n₁ := by omega
    exact (hordered hle' h₂ h₁).symm

theorem haltsWithTape_functional_of_haltTransitionFree
    {D : MachineDescription} {w : Word Bool} {T₁ T₂ : Tape Bool}
    (hD : D.HaltTransitionFree)
    (h₁ : D.HaltsWithTape w T₁)
    (h₂ : D.HaltsWithTape w T₂) :
    T₁ = T₂ := by
  rcases h₁ with ⟨n₁, h₁⟩
  rcases h₂ with ⟨n₂, h₂⟩
  let c₀ := D.initial w
  have hordered :
      forall {n m : Nat} {Tn Tm : Tape Bool},
        n ≤ m ->
        D.HaltsWithTapeIn n w Tn ->
        D.HaltsWithTapeIn m w Tm ->
          Tn = Tm := by
    intro n m Tn Tm hle hn hm
    let d := m - n
    have hm_eq : m = n + d := by
      omega
    have hconfig_n :
        D.runConfig n c₀ =
          { state := D.halt, tape := Tn } := by
      cases hfinal : D.runConfig n c₀ with
      | mk state tape =>
          have hstate : state = D.halt := by
            simpa [HaltsWithTapeIn, c₀, hfinal] using hn.left
          have htape : tape = Tn := by
            simpa [HaltsWithTapeIn, c₀, hfinal] using hn.right
          simp [hstate, htape]
    have hrunm :
        D.runConfig m c₀ = D.runConfig d (D.runConfig n c₀) := by
      rw [hm_eq, runConfig_add]
    have hstay :
        D.runConfig d (D.runConfig n c₀) =
          D.runConfig n c₀ := by
      rw [hconfig_n]
      exact MachineDescription.runConfig_halt hD Tn d
    have htape_m :
        (D.runConfig m c₀).tape = Tn := by
      rw [hrunm, hstay, hconfig_n]
    have htm : (D.runConfig m c₀).tape = Tm := by
      simpa [HaltsWithTapeIn, c₀] using hm.right
    rw [htm] at htape_m
    exact htape_m.symm
  by_cases hle : n₁ ≤ n₂
  · exact hordered hle h₁ h₂
  · have hle' : n₂ ≤ n₁ := by omega
    exact (hordered hle' h₂ h₁).symm

theorem haltsFromTape_functional_of_haltTransitionFree
    {D : MachineDescription} {Tin T₁ T₂ : Tape Bool}
    (hD : D.HaltTransitionFree)
    (h₁ : D.HaltsFromTape Tin T₁)
    (h₂ : D.HaltsFromTape Tin T₂) :
    T₁ = T₂ := by
  rcases h₁ with ⟨n₁, h₁⟩
  rcases h₂ with ⟨n₂, h₂⟩
  let c₀ := { state := D.start, tape := Tin : MachineDescription.Configuration }
  have hordered :
      forall {n m : Nat} {Tn Tm : Tape Bool},
        n ≤ m ->
        D.HaltsFromTapeIn n Tin Tn ->
        D.HaltsFromTapeIn m Tin Tm ->
          Tn = Tm := by
    intro n m Tn Tm hle hn hm
    let d := m - n
    have hm_eq : m = n + d := by
      omega
    have hconfig_n :
        D.runConfig n c₀ =
          { state := D.halt, tape := Tn } := by
      cases hfinal : D.runConfig n c₀ with
      | mk state tape =>
          have hstate : state = D.halt := by
            simpa [HaltsFromTapeIn, c₀, hfinal] using hn.left
          have htape : tape = Tn := by
            simpa [HaltsFromTapeIn, c₀, hfinal] using hn.right
          simp [hstate, htape]
    have hrunm :
        D.runConfig m c₀ = D.runConfig d (D.runConfig n c₀) := by
      rw [hm_eq, runConfig_add]
    have hstay :
        D.runConfig d (D.runConfig n c₀) =
          D.runConfig n c₀ := by
      rw [hconfig_n]
      exact MachineDescription.runConfig_halt hD Tn d
    have htape_m :
        (D.runConfig m c₀).tape = Tn := by
      rw [hrunm, hstay, hconfig_n]
    have htm : (D.runConfig m c₀).tape = Tm := by
      simpa [HaltsFromTapeIn, c₀] using hm.right
    rw [htm] at htape_m
    exact htape_m.symm
  by_cases hle : n₁ ≤ n₂
  · exact hordered hle h₁ h₂
  · have hle' : n₂ ≤ n₁ := by omega
    exact (hordered hle' h₂ h₁).symm

theorem runConfig_halt_tape_functional_of_haltTransitionFree
    {D : MachineDescription} {c : Configuration}
    {n₁ n₂ : Nat} {T₁ T₂ : Tape Bool}
    (hD : D.HaltTransitionFree)
    (h₁ : D.runConfig n₁ c = { state := D.halt, tape := T₁ })
    (h₂ : D.runConfig n₂ c = { state := D.halt, tape := T₂ }) :
    T₁ = T₂ := by
  have hordered :
      forall {n m : Nat} {Tn Tm : Tape Bool},
        n ≤ m ->
        D.runConfig n c = { state := D.halt, tape := Tn } ->
        D.runConfig m c = { state := D.halt, tape := Tm } ->
          Tn = Tm := by
    intro n m Tn Tm hle hn hm
    let d := m - n
    have hm_eq : m = n + d := by
      omega
    have hrunm :
        D.runConfig m c = D.runConfig d (D.runConfig n c) := by
      rw [hm_eq, runConfig_add]
    have hstay :
        D.runConfig d (D.runConfig n c) =
          D.runConfig n c := by
      rw [hn]
      exact MachineDescription.runConfig_halt hD Tn d
    have htape_m :
        (D.runConfig m c).tape = Tn := by
      rw [hrunm, hstay, hn]
    have htm : (D.runConfig m c).tape = Tm := by
      rw [hm]
    rw [htm] at htape_m
    exact htape_m.symm
  by_cases hle : n₁ ≤ n₂
  · exact hordered hle h₁ h₂
  · have hle' : n₂ ≤ n₁ := by omega
    exact (hordered hle' h₂ h₁).symm

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
  intro t
  simp [ExactIdentityDescription]

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

theorem exactIdentityDescription_haltsWithOutput_iff
    (w out : Word Bool) :
    ExactIdentityDescription.HaltsWithOutput w out <-> out = w := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    have hout : Tape.normalizedOutput (Tape.input w) = out := by
      simpa [HaltsWithOutputIn,
        exactIdentityDescription_runConfig_initial] using hn.right
    have hw : Tape.normalizedOutput (Tape.input w) = w := by
      simpa [Tape.output] using (Tape.normalizedOutput_output w)
    exact hout.symm.trans hw
  · intro h
    rw [h]
    exact haltsWithOutput_of_haltsWithExactOutput
      ((exactIdentityDescription_haltsWithExactOutput_iff w w).mpr rfl)

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
  refine ⟨by simp [EraseRightDescription], by simp [EraseRightDescription],
    by simp [EraseRightDescription], ?_, ?_⟩
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
  refine ⟨by simp [BoolOutputDescription], by simp [BoolOutputDescription],
    by simp [BoolOutputDescription], ?_, ?_⟩
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

theorem boolOutputDescription_haltsWithOutput_iff
    (b : Bool) (w out : Word Bool) :
    (BoolOutputDescription b).HaltsWithOutput w out <-> out = [b] := by
  constructor
  · intro h
    exact haltsWithOutput_functional_of_haltTransitionFree
      (boolOutputDescription_haltTransitionFree b) h
      (boolOutputDescription_haltsWithOutput b w)
  · intro h
    rw [h]
    exact boolOutputDescription_haltsWithOutput b w

/-!
## Code-word chunk recognizer

The shared parser base for the remaining finite transducers is a table that
checks the fixed-width Boolean expansion of {name}`MachineCodeSymbol` words.
At a chunk boundary it accepts blank input, scans all chunks whose first bit is
{lit}`0`, and permits the only {lit}`1`-headed code word, namely {lit}`1000`.
The table preserves cells while scanning; invalid or incomplete chunks stop in
a non-halt state.
-/

def EncodedCodeWordRecognizerDescription : MachineDescription where
  stateCount := 8
  start := 0
  halt := 7
  transitions :=
    [ transition 0 none none Direction.right 7
    , transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 4
    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 2
    , transition 2 (some false) (some false) Direction.right 3
    , transition 2 (some true) (some true) Direction.right 3
    , transition 3 (some false) (some false) Direction.right 0
    , transition 3 (some true) (some true) Direction.right 0
    , transition 4 (some false) (some false) Direction.right 5
    , transition 5 (some false) (some false) Direction.right 6
    , transition 6 (some false) (some false) Direction.right 0 ]

theorem encodedCodeWordRecognizerDescription_wellFormed :
    EncodedCodeWordRecognizerDescription.WellFormed := by
  refine ⟨by simp [EncodedCodeWordRecognizerDescription],
    by simp [EncodedCodeWordRecognizerDescription],
    by simp [EncodedCodeWordRecognizerDescription], ?_, ?_⟩
  · intro t ht
    simp [EncodedCodeWordRecognizerDescription, transition,
      TransitionDescription.WellFormed] at ht ⊢
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · intro t u ht hu hkey
    simp [EncodedCodeWordRecognizerDescription, transition] at ht hu
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rcases hu with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp [TransitionDescription.SameKey,
          TransitionDescription.SameAction] at hkey ⊢

theorem encodedCodeWordRecognizerDescription_haltTransitionFree :
    EncodedCodeWordRecognizerDescription.HaltTransitionFree := by
  intro t ht
  simp [EncodedCodeWordRecognizerDescription, transition] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [EncodedCodeWordRecognizerDescription]

theorem encodedCodeWordRecognizerDescription_subroutineReady :
    EncodedCodeWordRecognizerDescription.SubroutineReady :=
  ⟨encodedCodeWordRecognizerDescription_wellFormed,
    encodedCodeWordRecognizerDescription_haltTransitionFree⟩

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
  refine ⟨by simp [AppendFixedFourBitsRightDescription],
    by simp [AppendFixedFourBitsRightDescription],
    by simp [AppendFixedFourBitsRightDescription], ?_, ?_⟩
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

theorem stepConfig_equiv
    {D : MachineDescription} {c d : MachineDescription.Configuration}
    (htape : Tape.Equiv c.tape d.tape)
    (hstate : c.state = d.state) :
  match D.stepConfig c, D.stepConfig d with
  | none, none => True
  | some c', some d' =>
      c'.state = d'.state /\ Tape.Equiv c'.tape d'.tape
  | _, _ => False := by
  simp [stepConfig, hstate, Tape.Equiv.read_eq htape]
  cases D.lookupTransition d.state (Tape.read d.tape)
  · trivial
  · next t =>
    constructor
    · rfl
    · exact Tape.Equiv.move (Tape.Equiv.write htape t.write) t.move

theorem runConfig_equiv
    (D : MachineDescription) (n : Nat)
    {c d : MachineDescription.Configuration}
    (hstate : c.state = d.state)
    (htape : Tape.Equiv c.tape d.tape) :
  (D.runConfig n c).state = (D.runConfig n d).state /\
    Tape.Equiv (D.runConfig n c).tape (D.runConfig n d).tape := by
  induction n generalizing c d with
  | zero => exact ⟨hstate, htape⟩
  | succ n ih =>
    unfold runConfig
    have hstep := stepConfig_equiv (D := D) htape hstate
    cases hc : stepConfig D c
    · cases hd : stepConfig D d
      · exact ⟨hstate, htape⟩
      · rw [hc, hd] at hstep; contradiction
    · next c' =>
      cases hd : stepConfig D d
      · rw [hc, hd] at hstep; contradiction
      · next d' =>
        rw [hc, hd] at hstep
        exact ih hstep.1 hstep.2

def HaltsWithTapeEquiv (D : MachineDescription)
    (w : Languages.Word Bool) (T : Tape Bool) : Prop :=
  exists Tactual : Tape Bool,
    D.HaltsWithTape w Tactual /\ Tape.Equiv Tactual T

def HaltsFromTapeEquiv (D : MachineDescription)
    (Tin Tout : Tape Bool) : Prop :=
  exists Tactual : Tape Bool,
    D.HaltsFromTape Tin Tactual /\ Tape.Equiv Tactual Tout

def ClosedFromTapeEquiv (D : MachineDescription)
    (Tin Tout : Tape Bool) : Prop :=
  forall T, D.HaltsFromTape Tin T -> Tape.Equiv T Tout

theorem HaltsWithTape.toEquiv {D : MachineDescription} {w : Languages.Word Bool} {T : Tape Bool}
    (h : D.HaltsWithTape w T) : D.HaltsWithTapeEquiv w T :=
  ⟨T, h, Tape.Equiv.refl T⟩

theorem HaltsFromTape.toEquiv {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) : D.HaltsFromTapeEquiv Tin Tout :=
  ⟨Tout, h, Tape.Equiv.refl Tout⟩

theorem HaltsFromTapeEquiv_of_input_equiv {D : MachineDescription} {Tin Tin' Tout : Tape Bool}
    (hin : Tape.Equiv Tin Tin')
    (h : D.HaltsFromTape Tin Tout) :
  D.HaltsFromTapeEquiv Tin' Tout := by
  rcases h with ⟨n, hn⟩
  have hrun := runConfig_equiv D n (c := { state := D.start, tape := Tin }) (d := { state := D.start, tape := Tin' }) rfl hin
  exists (D.runConfig n { state := D.start, tape := Tin' }).tape
  constructor
  · exists n
    change (D.runConfig n { state := D.start, tape := Tin' }).state = D.halt ∧ _ = _
    change (D.runConfig n { state := D.start, tape := Tin }).state = D.halt ∧ _ = Tout at hn
    constructor
    · rw [← hrun.1]
      exact hn.1
    · rfl
  · rw [← hn.2]
    exact Tape.Equiv.symm hrun.2

theorem haltsWithOutput_of_haltsWithTapeEquiv
    {D : MachineDescription} {w : Word Bool} {T : Tape Bool}
    (h : D.HaltsWithTapeEquiv w T) :
    D.HaltsWithOutput w (Tape.normalizedOutput T) := by
  rcases h with ⟨Tactual, h_halt, h_equiv⟩
  have h_output := haltsWithOutput_of_haltsWithTape h_halt
  rw [Tape.Equiv.normalizedOutput_eq h_equiv] at h_output
  exact h_output

end MachineDescription

end Computability
end FoC
