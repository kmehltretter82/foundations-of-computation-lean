import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.InitialLayout

set_option doc.verso true

/-!
# Protected exact-fuel layout code runner

Interface between the raw stage-program materializer and the protected layout
runner.  The assembly theorem here keeps the public stage-program code-machine
construction independent from the concrete implementation details of either
phase.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel

/--
Semantic code recognizer for protected exact-fuel layouts.  A concrete finite
table should realize this predicate by parsing the encoded layout and running
the selected finite transition table for the protected fuel.
-/
def layoutCodeRun {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match Layout.decode stateCount tokens with
  | none => none
  | some (L, suffix) =>
      match suffix with
      | [] =>
          if TuringMachine.HaltsFromIn M L.fuel L.config then
            some ([] : Word MachineCodeSymbol)
          else
            none
      | _ :: _ => none

/--
Semantic one-step transformer for protected exact-fuel layouts.  This is the
code-level target for the eventual finite table that parses one encoded layout,
performs one selected-machine step, decrements the protected fuel, and emits
the next encoded layout.
-/
def layoutStepCode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match Layout.decode stateCount tokens with
  | none => none
  | some (L, suffix) =>
      match suffix with
      | [] =>
          match Layout.step M L with
          | none => none
          | some L' => some (Layout.encode L')
      | _ :: _ => none

def layoutFuelLoopFrom {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Nat -> Layout stateCount -> Option (Layout stateCount)
  | 0, L => some L
  | fuel + 1, L =>
      match Layout.step M L with
      | none => none
      | some L' => layoutFuelLoopFrom M fuel L'

def layoutFuelLoopCode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match Layout.decode stateCount tokens with
  | none => none
  | some (L, suffix) =>
      match suffix with
      | [] =>
          match layoutFuelLoopFrom M L.fuel L with
          | none => none
          | some final =>
              if final.state = M.halt then
                some ([] : Word MachineCodeSymbol)
              else
                none
      | _ :: _ => none

def layoutCodeRunPrimitive {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    MachineDescription.TapeCodePrimitive where
  transform := layoutCodeRun M

def layoutStepCodePrimitive {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    MachineDescription.TapeCodePrimitive where
  transform := layoutStepCode M

def layoutFuelLoopCodePrimitive {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    MachineDescription.TapeCodePrimitive where
  transform := layoutFuelLoopCode M

/--
Executable primitive contract for the protected layout recognizer.  A concrete
finite table realizing this primitive is exactly the remaining layout-code
machine leaf.
-/
def LayoutCodeRunPrimitiveSpec {stateCount : Nat}
    (primitive : MachineDescription.TapeCodePrimitive)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  primitive.Realizes (layoutCodeRun M)

/--
Executable primitive contract for one protected layout step.  This isolates
the future finite stepper from the outer fuel-induction recognizer.
-/
def LayoutStepCodePrimitiveSpec {stateCount : Nat}
    (primitive : MachineDescription.TapeCodePrimitive)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  primitive.Realizes (layoutStepCode M)

def LayoutFuelLoopCodePrimitiveSpec {stateCount : Nat}
    (primitive : MachineDescription.TapeCodePrimitive)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  primitive.Realizes (layoutFuelLoopCode M)

theorem layoutCodeRunPrimitive_realizes {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    LayoutCodeRunPrimitiveSpec (layoutCodeRunPrimitive M) M := by
  intro tokens
  rfl

theorem layoutStepCodePrimitive_realizes {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    LayoutStepCodePrimitiveSpec (layoutStepCodePrimitive M) M := by
  intro tokens
  rfl

theorem layoutFuelLoopCodePrimitive_realizes {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    LayoutFuelLoopCodePrimitiveSpec (layoutFuelLoopCodePrimitive M) M := by
  intro tokens
  rfl

theorem layoutFuelLoopFrom_accepts_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) (fuel : Nat)
    (hfuel : L.fuel = fuel) :
    (exists final : Layout stateCount,
      layoutFuelLoopFrom M fuel L = some final /\
        TuringMachine.Halted M final.config) <->
      Layout.accepts M L := by
  induction fuel generalizing L with
  | zero =>
      cases L with
      | mk layoutFuel state left head right =>
          cases hfuel
          constructor
          · intro h
            rcases h with ⟨final, hloop, hhalt⟩
            simp [layoutFuelLoopFrom] at hloop
            cases hloop
            exact
              (Layout.accepts_zero_iff M
                ({ fuel := 0
                   state := state
                   left := left
                   head := head
                   right := right } : Layout stateCount)).mpr
                hhalt
          · intro haccepts
            refine
              ⟨{ fuel := 0
                 state := state
                 left := left
                 head := head
                 right := right }, rfl, ?_⟩
            exact
              (Layout.accepts_zero_iff M
                ({ fuel := 0
                   state := state
                   left := left
                   head := head
                   right := right } : Layout stateCount)).mp
                haccepts
  | succ fuel ih =>
      constructor
      · intro h
        rcases h with ⟨final, hloop, hhalt⟩
        cases hstep : Layout.step M L with
        | none =>
            simp [layoutFuelLoopFrom, hstep] at hloop
        | some L' =>
            have hloop' :
                layoutFuelLoopFrom M fuel L' = some final := by
              simpa [layoutFuelLoopFrom, hstep] using hloop
            have hfuel' : L'.fuel = fuel :=
              Layout.step_fuel_eq_of_eq_some hfuel hstep
            have haccepts' : Layout.accepts M L' :=
              (ih L' hfuel').mp ⟨final, hloop', hhalt⟩
            exact
              (Layout.accepts_succ_iff_step
                (M := M) L fuel hfuel).mpr
                ⟨L', hstep, haccepts'⟩
      · intro haccepts
        rcases
            (Layout.accepts_succ_iff_step
              (M := M) L fuel hfuel).mp haccepts with
          ⟨L', hstep, haccepts'⟩
        have hfuel' : L'.fuel = fuel :=
          Layout.step_fuel_eq_of_eq_some hfuel hstep
        rcases (ih L' hfuel').mpr haccepts' with
          ⟨final, hloop', hhalt⟩
        refine ⟨final, ?_, hhalt⟩
        simp [layoutFuelLoopFrom, hstep, hloop']

theorem layoutFuelLoopCode_encode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) :
    layoutFuelLoopCode M (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      Layout.accepts M L := by
  constructor
  · intro hloopCode
    unfold layoutFuelLoopCode at hloopCode
    simp [Layout.decode_encode] at hloopCode
    cases hloop : layoutFuelLoopFrom M L.fuel L with
    | none =>
        simp [hloop] at hloopCode
    | some final =>
        by_cases hstate : final.state = M.halt
        · have hhalt : TuringMachine.Halted M final.config := by
            simpa [TuringMachine.Halted, Layout.config] using hstate
          exact
            (layoutFuelLoopFrom_accepts_iff M L L.fuel rfl).mp
              ⟨final, hloop, hhalt⟩
        · simp [hloop, hstate] at hloopCode
  · intro haccepts
    rcases
        (layoutFuelLoopFrom_accepts_iff M L L.fuel rfl).mpr
          haccepts with
      ⟨final, hloop, hhalt⟩
    have hstate : final.state = M.halt := by
      simpa [TuringMachine.Halted, Layout.config] using hhalt
    simp [layoutFuelLoopCode, Layout.decode_encode, hloop, hstate]
    rfl

theorem layoutFuelLoopCodePrimitive_encode_eq_some_iff
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) :
    (layoutFuelLoopCodePrimitive M).transform (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      Layout.accepts M L := by
  exact layoutFuelLoopCode_encode_eq_some_iff M L

theorem layoutFuelLoopCode_encode_initial_eq_some_iff
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    layoutFuelLoopCode M
        (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input := by
  exact Iff.trans
    (layoutFuelLoopCode_encode_eq_some_iff M
      (Layout.initial M input fuel))
    (Layout.accepts_initial_iff_haltsOnInputIn M input fuel)

theorem layoutFuelLoopCodePrimitive_encode_initial_eq_some_iff
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (layoutFuelLoopCodePrimitive M).transform
        (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input := by
  exact layoutFuelLoopCode_encode_initial_eq_some_iff M input fuel

theorem layoutCodeRun_eq_some_iff_decode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    layoutCodeRun M tokens = some ([] : Word MachineCodeSymbol) <->
      exists L : Layout stateCount,
        Layout.decode stateCount tokens = some (L, []) /\
          Layout.accepts M L := by
  constructor
  · intro hrun
    unfold layoutCodeRun at hrun
    cases hdecode : Layout.decode stateCount tokens with
    | none =>
        rw [hdecode] at hrun
        cases hrun
    | some decoded =>
        rcases decoded with ⟨L, suffix⟩
        cases suffix with
        | nil =>
            by_cases hhalt :
                TuringMachine.HaltsFromIn M L.fuel L.config
            · exact
                ⟨L, rfl, by
                  simpa [Layout.accepts] using hhalt⟩
            · simp [hdecode, hhalt] at hrun
        | cons _ _ =>
            simp [hdecode] at hrun
  · intro h
    rcases h with ⟨L, hdecode, haccepts⟩
    unfold layoutCodeRun
    rw [hdecode]
    have hhalt :
        TuringMachine.HaltsFromIn M L.fuel L.config := by
      simpa [Layout.accepts] using haccepts
    simp [hhalt]
    rfl

theorem layoutFuelLoopCode_eq_some_iff_decode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    layoutFuelLoopCode M tokens = some ([] : Word MachineCodeSymbol) <->
      exists L : Layout stateCount,
        Layout.decode stateCount tokens = some (L, []) /\
          Layout.accepts M L := by
  constructor
  · intro hloopCode
    unfold layoutFuelLoopCode at hloopCode
    cases hdecode : Layout.decode stateCount tokens with
    | none =>
        rw [hdecode] at hloopCode
        cases hloopCode
    | some decoded =>
        rcases decoded with ⟨L, suffix⟩
        cases suffix with
        | nil =>
            cases hloop : layoutFuelLoopFrom M L.fuel L with
            | none =>
                simp [hdecode, hloop] at hloopCode
            | some final =>
                by_cases hstate : final.state = M.halt
                · have hhalt :
                      TuringMachine.Halted M final.config := by
                    simpa [TuringMachine.Halted, Layout.config]
                      using hstate
                  have haccepts : Layout.accepts M L :=
                    (layoutFuelLoopFrom_accepts_iff
                      M L L.fuel rfl).mp
                      ⟨final, hloop, hhalt⟩
                  exact ⟨L, rfl, haccepts⟩
                · simp [hdecode, hloop, hstate] at hloopCode
        | cons _ _ =>
            simp [hdecode] at hloopCode
  · intro h
    rcases h with ⟨L, hdecode, haccepts⟩
    unfold layoutFuelLoopCode
    rw [hdecode]
    rcases
        (layoutFuelLoopFrom_accepts_iff
          M L L.fuel rfl).mpr haccepts with
      ⟨final, hloop, hhalt⟩
    have hstate : final.state = M.halt := by
      simpa [TuringMachine.Halted, Layout.config] using hhalt
    simp [hloop, hstate]
    rfl

theorem layoutFuelLoopCode_eq_layoutCodeRun_on_empty_output
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    layoutFuelLoopCode M tokens = some ([] : Word MachineCodeSymbol) <->
      layoutCodeRun M tokens = some ([] : Word MachineCodeSymbol) := by
  exact Iff.trans
    (layoutFuelLoopCode_eq_some_iff_decode M tokens)
    (Iff.symm (layoutCodeRun_eq_some_iff_decode M tokens))

theorem layoutCodeRun_encode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) :
    layoutCodeRun M (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      Layout.accepts M L := by
  constructor
  · intro hrun
    by_cases hhalt : TuringMachine.HaltsFromIn M L.fuel L.config
    · simpa [Layout.accepts] using hhalt
    · simp [layoutCodeRun, Layout.decode_encode, hhalt] at hrun
  · intro haccepts
    have hhalt : TuringMachine.HaltsFromIn M L.fuel L.config := by
      simpa [Layout.accepts] using haccepts
    simp [layoutCodeRun, Layout.decode_encode, hhalt]
    rfl

theorem layoutCodeRunPrimitive_encode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) :
    (layoutCodeRunPrimitive M).transform (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      Layout.accepts M L := by
  exact layoutCodeRun_encode_eq_some_iff M L

theorem layoutCodeRun_encode_initial_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    layoutCodeRun M (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input := by
  exact Iff.trans
    (layoutCodeRun_encode_eq_some_iff M
      (Layout.initial M input fuel))
    (Layout.accepts_initial_iff_haltsOnInputIn M input fuel)

theorem layoutCodeRunPrimitive_encode_initial_eq_some_iff
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (layoutCodeRunPrimitive M).transform
        (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input := by
  exact layoutCodeRun_encode_initial_eq_some_iff M input fuel

theorem layoutStepCode_encode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) (output : Word MachineCodeSymbol) :
    layoutStepCode M (Layout.encode L) = some output <->
      exists L' : Layout stateCount,
        Layout.step M L = some L' /\ output = Layout.encode L' := by
  constructor
  · intro hstepCode
    unfold layoutStepCode at hstepCode
    simp [Layout.decode_encode] at hstepCode
    cases hstep : Layout.step M L with
    | none =>
        simp [hstep] at hstepCode
    | some L' =>
        simp [hstep] at hstepCode
        exact ⟨L', rfl, hstepCode.symm⟩
  · intro h
    rcases h with ⟨L', hstep, houtput⟩
    subst output
    simp [layoutStepCode, Layout.decode_encode, hstep]

theorem layoutStepCodePrimitive_encode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) (output : Word MachineCodeSymbol) :
    (layoutStepCodePrimitive M).transform (Layout.encode L) =
        some output <->
      exists L' : Layout stateCount,
        Layout.step M L = some L' /\ output = Layout.encode L' := by
  exact layoutStepCode_encode_eq_some_iff M L output

theorem layoutStepCode_eq_some_iff_decode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens output : Word MachineCodeSymbol) :
    layoutStepCode M tokens = some output <->
      exists L : Layout stateCount,
      exists L' : Layout stateCount,
        Layout.decode stateCount tokens = some (L, []) /\
          Layout.step M L = some L' /\
            output = Layout.encode L' := by
  constructor
  · intro hstepCode
    unfold layoutStepCode at hstepCode
    cases hdecode : Layout.decode stateCount tokens with
    | none =>
        rw [hdecode] at hstepCode
        cases hstepCode
    | some decoded =>
        rcases decoded with ⟨L, suffix⟩
        cases suffix with
        | nil =>
            cases hstep : Layout.step M L with
            | none =>
                simp [hdecode, hstep] at hstepCode
            | some L' =>
                simp [hdecode, hstep] at hstepCode
                exact ⟨L, L', rfl, hstep, hstepCode.symm⟩
        | cons _ _ =>
            simp [hdecode] at hstepCode
  · intro h
    rcases h with ⟨L, L', hdecode, hstep, houtput⟩
    subst output
    simp [layoutStepCode, hdecode, hstep]

theorem layoutStepCodePrimitive_eq_some_iff_decode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens output : Word MachineCodeSymbol) :
    (layoutStepCodePrimitive M).transform tokens = some output <->
      exists L : Layout stateCount,
      exists L' : Layout stateCount,
        Layout.decode stateCount tokens = some (L, []) /\
          Layout.step M L = some L' /\
            output = Layout.encode L' := by
  exact layoutStepCode_eq_some_iff_decode M tokens output

theorem layoutCodeRun_encode_succ_iff_step {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) (fuel : Nat)
    (hfuel : L.fuel = fuel + 1) :
    layoutCodeRun M (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      exists L' : Layout stateCount,
        Layout.step M L = some L' /\
          layoutCodeRun M (Layout.encode L') =
            some ([] : Word MachineCodeSymbol) := by
  rw [layoutCodeRun_encode_eq_some_iff]
  constructor
  · intro haccepts
    rcases
        (Layout.accepts_succ_iff_step
          (M := M) L fuel hfuel).mp haccepts with
      ⟨L', hstep, htail⟩
    exact
      ⟨L', hstep,
        (layoutCodeRun_encode_eq_some_iff M L').mpr htail⟩
  · intro h
    rcases h with ⟨L', hstep, htailRun⟩
    have htail :
        Layout.accepts M L' :=
      (layoutCodeRun_encode_eq_some_iff M L').mp htailRun
    exact
      (Layout.accepts_succ_iff_step
        (M := M) L fuel hfuel).mpr
        ⟨L', hstep, htail⟩

theorem layoutFuelLoopCode_encode_zero_iff_halted {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount)
    (hfuel : L.fuel = 0) :
    layoutFuelLoopCode M (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.Halted M L.config := by
  cases L with
  | mk layoutFuel state left head right =>
      cases hfuel
      exact
        Iff.trans
          (layoutFuelLoopCode_encode_eq_some_iff M
            ({ fuel := 0
               state := state
               left := left
               head := head
               right := right } : Layout stateCount))
          (Layout.accepts_zero_iff M
            ({ fuel := 0
               state := state
               left := left
               head := head
               right := right } : Layout stateCount))

theorem layoutFuelLoopCode_encode_succ_iff_step {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) (fuel : Nat)
    (hfuel : L.fuel = fuel + 1) :
    layoutFuelLoopCode M (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      exists L' : Layout stateCount,
        Layout.step M L = some L' /\
          layoutFuelLoopCode M (Layout.encode L') =
            some ([] : Word MachineCodeSymbol) := by
  constructor
  · intro hloop
    have hrun :
        layoutCodeRun M (Layout.encode L) =
          some ([] : Word MachineCodeSymbol) :=
      (layoutFuelLoopCode_eq_layoutCodeRun_on_empty_output
        M (Layout.encode L)).mp hloop
    rcases
        (layoutCodeRun_encode_succ_iff_step
          M L fuel hfuel).mp hrun with
      ⟨L', hstep, htailRun⟩
    exact
      ⟨L', hstep,
        (layoutFuelLoopCode_eq_layoutCodeRun_on_empty_output
          M (Layout.encode L')).mpr htailRun⟩
  · intro h
    rcases h with ⟨L', hstep, htailLoop⟩
    have htailRun :
        layoutCodeRun M (Layout.encode L') =
          some ([] : Word MachineCodeSymbol) :=
      (layoutFuelLoopCode_eq_layoutCodeRun_on_empty_output
        M (Layout.encode L')).mp htailLoop
    have hrun :
        layoutCodeRun M (Layout.encode L) =
          some ([] : Word MachineCodeSymbol) :=
      (layoutCodeRun_encode_succ_iff_step M L fuel hfuel).mpr
        ⟨L', hstep, htailRun⟩
    exact
      (layoutFuelLoopCode_eq_layoutCodeRun_on_empty_output
        M (Layout.encode L)).mpr hrun

def LayoutCodeMachineSpec {stateCount : Nat}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      layoutCodeRun M tokens = some ([] : Word MachineCodeSymbol)

def LayoutFuelLoopCodeMachineSpec {stateCount : Nat}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      layoutFuelLoopCode M tokens = some ([] : Word MachineCodeSymbol)

def LayoutCodeMachineConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    LayoutCodeMachineSpec runner M

def LayoutFuelLoopCodeMachineConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    LayoutFuelLoopCodeMachineSpec runner M

/--
Exact-output finite-machine target for the executable protected-layout fuel
loop primitive.  Since this primitive only succeeds with empty output, an
exact-output realizer is also an ordinary recognizer for
{name}`layoutFuelLoopCode`.
-/
def LayoutFuelLoopExactOutputPrimitiveConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    StageProgram.ExactOutputSpec runner
        (layoutFuelLoopCodePrimitive M).transform ∧
      StageProgram.ExactOutputCanonicalSpec runner
        (layoutFuelLoopCodePrimitive M).transform ∧
      TuringMachine.HaltingTransitionsDisabled runner

theorem layoutFuelLoopCode_eq_some_empty_of_eq_some
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    {tokens output : Word MachineCodeSymbol}
    (h :
      layoutFuelLoopCode M tokens = some output) :
    output = ([] : Word MachineCodeSymbol) := by
  unfold layoutFuelLoopCode at h
  cases hdecode : Layout.decode stateCount tokens with
  | none =>
      simp [hdecode] at h
  | some decoded =>
      rcases decoded with ⟨L, suffix⟩
      cases suffix with
      | nil =>
          cases hloop : layoutFuelLoopFrom M L.fuel L with
          | none =>
              simp [hdecode, hloop] at h
          | some final =>
              by_cases hstate : final.state = M.halt
              · have hsome :
                    output = ([] : Word MachineCodeSymbol) := by
                  simpa [hdecode, hloop, hstate] using h.symm
                exact hsome
              · simp [hdecode, hloop, hstate] at h
      | cons _ _ =>
          simp [hdecode] at h

theorem layoutFuelLoopCodeMachineConstruction_of_exactOutputPrimitive
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hprimitive : LayoutFuelLoopExactOutputPrimitiveConstruction M) :
    LayoutFuelLoopCodeMachineConstruction M := by
  rcases hprimitive with
    ⟨runnerState, runner, hexact, hcanonical, _hstop⟩
  refine ⟨runnerState, runner, ?_⟩
  intro tokens
  simpa [layoutFuelLoopCodePrimitive] using
    (StageProgram.haltsOnInput_iff_some_empty_of_exactOutput
      hexact hcanonical
      (by
        intro tokens output houtput
        exact layoutFuelLoopCode_eq_some_empty_of_eq_some
          M (by
            simpa [layoutFuelLoopCodePrimitive] using houtput))
      tokens)

def FinStateLayoutCodeMachineConstruction : Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    LayoutCodeMachineConstruction M

def FinStateLayoutFuelLoopCodeMachineConstruction : Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    LayoutFuelLoopCodeMachineConstruction M

theorem layoutCodeMachineSpec_of_fuelLoopCodeMachineSpec
    {stateCount : Nat} {runnerState : Type}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hrunner : LayoutFuelLoopCodeMachineSpec runner M) :
    LayoutCodeMachineSpec runner M := by
  intro tokens
  exact Iff.trans (hrunner tokens)
    (layoutFuelLoopCode_eq_layoutCodeRun_on_empty_output M tokens)

theorem layoutCodeMachineConstruction_of_fuelLoopCodeMachine
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hloop : LayoutFuelLoopCodeMachineConstruction M) :
    LayoutCodeMachineConstruction M := by
  rcases hloop with ⟨runnerState, runner, hrunner⟩
  exact
    ⟨runnerState, runner,
      layoutCodeMachineSpec_of_fuelLoopCodeMachineSpec hrunner⟩

def LayoutCodeRunnerSpec {stateCount : Nat}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall L : Layout stateCount,
    TuringMachine.HaltsOnInput runner (Layout.encode L) <->
      Layout.accepts M L

def LayoutCodeRunnerConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    LayoutCodeRunnerSpec runner M

theorem layoutCodeRunnerSpec_of_codeMachineSpec {stateCount : Nat}
    {runnerState : Type}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hrunner : LayoutCodeMachineSpec runner M) :
    LayoutCodeRunnerSpec runner M := by
  intro L
  exact Iff.trans (hrunner (Layout.encode L))
    (layoutCodeRun_encode_eq_some_iff M L)

theorem layoutCodeRunnerConstruction_of_codeMachine
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcode : LayoutCodeMachineConstruction M) :
    LayoutCodeRunnerConstruction M := by
  rcases hcode with ⟨runnerState, runner, hrunner⟩
  exact
    ⟨runnerState, runner,
      layoutCodeRunnerSpec_of_codeMachineSpec hrunner⟩

namespace StageProgram

def CodePrimitiveEmptySpec {stateCount : Nat}
    (primitive : MachineDescription.TapeCodePrimitive)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    primitive.transform tokens = some ([] : Word MachineCodeSymbol) <->
      run M tokens = some ([] : Word MachineCodeSymbol)

def stageProgramFuelLoopCodePrimitive {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    (initialLayoutMaterializerCodePrimitive M)
    (layoutFuelLoopCodePrimitive M)

theorem stageProgramFuelLoopCodePrimitive_eq_some_empty_iff
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    (stageProgramFuelLoopCodePrimitive M).transform tokens =
        some ([] : Word MachineCodeSymbol) <->
      run M tokens = some ([] : Word MachineCodeSymbol) := by
  constructor
  · intro h
    change
      (match (initialLayoutMaterializerCodePrimitive M).transform tokens with
      | none => none
      | some mid => (layoutFuelLoopCodePrimitive M).transform mid) =
        some ([] : Word MachineCodeSymbol) at h
    cases hmat :
        (initialLayoutMaterializerCodePrimitive M).transform tokens with
    | none =>
        rw [hmat] at h
        cases h
    | some mid =>
        rw [hmat] at h
        have hmat' :
            Layout.stageCodeToInitialLayoutCode M tokens = some mid := by
          simpa [initialLayoutMaterializerCodePrimitive] using hmat
        have hloop :
            layoutFuelLoopCode M mid =
              some ([] : Word MachineCodeSymbol) := by
          simpa [layoutFuelLoopCodePrimitive] using h
        rcases
            (stageCodeToInitialLayoutCode_eq_some_iff
              M tokens mid).mp hmat' with
          ⟨input, fuel, htokens, hmid⟩
        subst tokens
        subst mid
        have hhalt :
            TuringMachine.HaltsOnInputIn M fuel input :=
          (layoutFuelLoopCode_encode_initial_eq_some_iff
            M input fuel).mp hloop
        exact (run_stageCode_eq_some_iff M input fuel).mpr hhalt
  · intro hrun
    rcases (run_eq_some_iff_decodeNat M tokens).mp hrun with
      ⟨fuel, input, hdecode, hhalt⟩
    have hmat :
        (initialLayoutMaterializerCodePrimitive M).transform tokens =
          some (Layout.encode (Layout.initial M input fuel)) := by
      have hcode :
          Layout.stageCodeToInitialLayoutCode M tokens =
            some (Layout.encode (Layout.initial M input fuel)) := by
        simp [Layout.stageCodeToInitialLayoutCode, hdecode]
      simpa [initialLayoutMaterializerCodePrimitive] using hcode
    have hloop :
        (layoutFuelLoopCodePrimitive M).transform
            (Layout.encode (Layout.initial M input fuel)) =
          some ([] : Word MachineCodeSymbol) := by
      simpa [layoutFuelLoopCodePrimitive] using
        (layoutFuelLoopCode_encode_initial_eq_some_iff
          M input fuel).mpr hhalt
    change
      (match (initialLayoutMaterializerCodePrimitive M).transform tokens with
      | none => none
      | some mid => (layoutFuelLoopCodePrimitive M).transform mid) =
        some ([] : Word MachineCodeSymbol)
    rw [hmat]
    exact hloop

theorem stageProgramFuelLoopCodePrimitive_emptySpec
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    CodePrimitiveEmptySpec
      (stageProgramFuelLoopCodePrimitive M) M := by
  intro tokens
  exact stageProgramFuelLoopCodePrimitive_eq_some_empty_iff M tokens

/--
Direct exact-output finite-machine target for the normalized exact-fuel stage
program.  This combines unary parsing, initial-layout materialization, and the
protected fuel loop behind one concrete backend boundary.
-/
def ExactOutputPrimitiveConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    ExactOutputSpec runner
        (stageProgramFuelLoopCodePrimitive M).transform ∧
      ExactOutputCanonicalSpec runner
        (stageProgramFuelLoopCodePrimitive M).transform ∧
      TuringMachine.HaltingTransitionsDisabled runner

theorem stageProgramFuelLoopCodePrimitive_eq_some_empty_of_eq_some
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    {tokens output : Word MachineCodeSymbol}
    (h :
      (stageProgramFuelLoopCodePrimitive M).transform tokens =
        some output) :
    output = ([] : Word MachineCodeSymbol) := by
  change
    (match (initialLayoutMaterializerCodePrimitive M).transform tokens with
    | none => none
    | some mid => (layoutFuelLoopCodePrimitive M).transform mid) =
      some output at h
  cases hmat :
      (initialLayoutMaterializerCodePrimitive M).transform tokens with
  | none =>
      rw [hmat] at h
      cases h
  | some mid =>
      rw [hmat] at h
      have hloop :
          layoutFuelLoopCode M mid = some output := by
        simpa [layoutFuelLoopCodePrimitive] using h
      exact layoutFuelLoopCode_eq_some_empty_of_eq_some M hloop

theorem exactOutputPrimitiveConstruction_of_exactMaterializer_layoutFuelLoop
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hmaterializer : InitialLayoutExactOutputPrimitiveConstruction M)
    (hlayout : LayoutFuelLoopExactOutputPrimitiveConstruction M) :
    ExactOutputPrimitiveConstruction M := by
  rcases hmaterializer with
    ⟨materializerState, materializer, hmaterializer,
      hmaterializerCanonical, hmaterializerStop⟩
  rcases hlayout with
    ⟨layoutState, layoutRunner, hlayout,
      hlayoutCanonical, hlayoutStop⟩
  refine
    ⟨OutputThenRecognizeState materializerState layoutState,
      outputThenRecognizePipeline materializer layoutRunner,
      ?_, ?_, ?_⟩
  · simpa [stageProgramFuelLoopCodePrimitive,
      initialLayoutMaterializerCodePrimitive,
      layoutFuelLoopCodePrimitive,
      MachineDescription.TapeCodePrimitive.compose] using
      (outputThenRecognizePipeline_compose_exactOutputSpec
        hmaterializerStop hmaterializer hmaterializerCanonical
        hlayoutStop hlayout
        (by
          intro tokens output houtput
          exact
            outputThenRecognizeHandoffTape_stageCodeToInitialLayoutCode
              M (by
                simpa [initialLayoutMaterializerCodePrimitive] using
                  houtput)))
  · simpa [stageProgramFuelLoopCodePrimitive,
      initialLayoutMaterializerCodePrimitive,
      layoutFuelLoopCodePrimitive,
      MachineDescription.TapeCodePrimitive.compose] using
      (outputThenRecognizePipeline_compose_exactOutputCanonicalSpec
        hmaterializerStop hmaterializerCanonical
        hlayoutStop hlayoutCanonical
        (by
          intro tokens output houtput
          exact
            outputThenRecognizeHandoffTape_stageCodeToInitialLayoutCode
              M (by
                simpa [initialLayoutMaterializerCodePrimitive] using
                  houtput)))
  · exact
      outputThenRecognizePipeline_haltingTransitionsDisabled
        (producer := materializer) hlayoutStop

theorem codeMachineConstruction_of_exactOutputPrimitive
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hprimitive : ExactOutputPrimitiveConstruction M) :
    CodeMachineConstruction M := by
  rcases hprimitive with
    ⟨runnerState, runner, hexact, hcanonical, _hstop⟩
  refine ⟨runnerState, runner, ?_⟩
  intro tokens
  exact Iff.trans
    (haltsOnInput_iff_some_empty_of_exactOutput
      hexact hcanonical
      (by
        intro tokens output houtput
        exact stageProgramFuelLoopCodePrimitive_eq_some_empty_of_eq_some
          M houtput)
      tokens)
    (stageProgramFuelLoopCodePrimitive_emptySpec M tokens)

theorem codeMachineConstruction_of_materializer_layoutRunner_compose
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcompose : OutputThenRecognizeConstruction)
    (hmaterializer : InitialLayoutMaterializerConstruction M)
    (hlayout : LayoutCodeRunnerConstruction M) :
    CodeMachineConstruction M := by
  rcases hmaterializer with
    ⟨materializerState, materializer, hmaterializer⟩
  rcases hlayout with ⟨layoutState, layoutRunner, hlayoutRunner⟩
  let P : Word MachineCodeSymbol -> Prop :=
    fun output => TuringMachine.HaltsOnInput layoutRunner output
  have hrecognizes : FiniteRecognizer.Recognizes layoutRunner P := by
    intro output
    rfl
  rcases
      hcompose materializer layoutRunner
        (Layout.stageCodeToInitialLayoutCode M) P
        hmaterializer hrecognizes with
    ⟨pipelineState, pipeline, hpipeline⟩
  refine ⟨pipelineState, pipeline, ?_⟩
  intro tokens
  exact Iff.trans (hpipeline tokens) (by
    rw [run_eq_some_iff_decodeNat M tokens]
    constructor
    · intro h
      rcases h with ⟨output, houtput, hrunner⟩
      unfold Layout.stageCodeToInitialLayoutCode at houtput
      cases hdecode : MachineDescription.decodeNat tokens with
      | none =>
          rw [hdecode] at houtput
          cases houtput
      | some decoded =>
          rcases decoded with ⟨fuel, input⟩
          rw [hdecode] at houtput
          cases houtput
          have haccept :
              Layout.accepts M (Layout.initial M input fuel) :=
            (hlayoutRunner (Layout.initial M input fuel)).mp hrunner
          have hhalt :
              TuringMachine.HaltsOnInputIn M fuel input :=
            (Layout.accepts_initial_iff_haltsOnInputIn
              M input fuel).mp haccept
          exact ⟨fuel, input, rfl, hhalt⟩
    · intro h
      rcases h with ⟨fuel, input, hdecode, hhalt⟩
      refine
        ⟨Layout.encode (Layout.initial M input fuel), ?_, ?_⟩
      · simp [Layout.stageCodeToInitialLayoutCode, hdecode]
      · exact
          (hlayoutRunner (Layout.initial M input fuel)).mpr
            ((Layout.accepts_initial_iff_haltsOnInputIn
              M input fuel).mpr hhalt))

theorem codeMachineConstruction_of_materializer_layoutCodeMachine_compose
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcompose : OutputThenRecognizeConstruction)
    (hmaterializer : InitialLayoutMaterializerConstruction M)
    (hlayout : LayoutCodeMachineConstruction M) :
    CodeMachineConstruction M :=
  codeMachineConstruction_of_materializer_layoutRunner_compose
    hcompose hmaterializer
    (layoutCodeRunnerConstruction_of_codeMachine hlayout)

theorem codeMachineConstruction_of_exactMaterializer_layoutRunner_compose_normalized
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcompose : OutputThenRecognizeConstruction)
    (hmaterializer : InitialLayoutExactMaterializerConstruction M)
    (hlayout : LayoutCodeRunnerConstruction M) :
    CodeMachineConstruction M :=
  codeMachineConstruction_of_materializer_layoutRunner_compose
    hcompose
    (initialLayoutMaterializerConstruction_of_exact hmaterializer)
    hlayout

theorem codeMachineConstruction_of_exactMaterializer_layoutCodeMachine_compose_normalized
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcompose : OutputThenRecognizeConstruction)
    (hmaterializer : InitialLayoutExactMaterializerConstruction M)
    (hlayout : LayoutCodeMachineConstruction M) :
    CodeMachineConstruction M :=
  codeMachineConstruction_of_exactMaterializer_layoutRunner_compose_normalized
    hcompose hmaterializer
    (layoutCodeRunnerConstruction_of_codeMachine hlayout)

theorem codeMachineConstruction_of_exactMaterializer_layoutRunner_compose
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcompose : ExactOutputThenRecognizeConstruction)
    (hmaterializer : InitialLayoutExactMaterializerConstruction M)
    (hlayout : LayoutCodeRunnerConstruction M) :
    CodeMachineConstruction M := by
  rcases hmaterializer with
    ⟨materializerState, materializer, hmaterializer,
      hmaterializerCanonical, hmaterializerStop⟩
  rcases hlayout with ⟨layoutState, layoutRunner, hlayoutRunner⟩
  let P : Word MachineCodeSymbol -> Prop :=
    fun output => TuringMachine.HaltsOnInput layoutRunner output
  have hrecognizes : FiniteRecognizer.Recognizes layoutRunner P := by
    intro output
    rfl
  rcases
      hcompose materializer layoutRunner
        (Layout.stageCodeToInitialLayoutCode M) P
        hmaterializer hmaterializerCanonical hmaterializerStop
        hrecognizes with
    ⟨pipelineState, pipeline, hpipeline⟩
  refine ⟨pipelineState, pipeline, ?_⟩
  intro tokens
  exact Iff.trans (hpipeline tokens) (by
    rw [run_eq_some_iff_decodeNat M tokens]
    constructor
    · intro h
      rcases h with ⟨output, houtput, hrunner⟩
      unfold Layout.stageCodeToInitialLayoutCode at houtput
      cases hdecode : MachineDescription.decodeNat tokens with
      | none =>
          rw [hdecode] at houtput
          cases houtput
      | some decoded =>
          rcases decoded with ⟨fuel, input⟩
          rw [hdecode] at houtput
          cases houtput
          have haccept :
              Layout.accepts M (Layout.initial M input fuel) :=
            (hlayoutRunner (Layout.initial M input fuel)).mp hrunner
          have hhalt :
              TuringMachine.HaltsOnInputIn M fuel input :=
            (Layout.accepts_initial_iff_haltsOnInputIn
              M input fuel).mp haccept
          exact ⟨fuel, input, rfl, hhalt⟩
    · intro h
      rcases h with ⟨fuel, input, hdecode, hhalt⟩
      refine
        ⟨Layout.encode (Layout.initial M input fuel), ?_, ?_⟩
      · simp [Layout.stageCodeToInitialLayoutCode, hdecode]
      · exact
          (hlayoutRunner (Layout.initial M input fuel)).mpr
            ((Layout.accepts_initial_iff_haltsOnInputIn
              M input fuel).mpr hhalt))

theorem codeMachineConstruction_of_exactMaterializer_layoutCodeMachine_compose
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcompose : ExactOutputThenRecognizeConstruction)
    (hmaterializer : InitialLayoutExactMaterializerConstruction M)
    (hlayout : LayoutCodeMachineConstruction M) :
    CodeMachineConstruction M :=
  codeMachineConstruction_of_exactMaterializer_layoutRunner_compose
    hcompose hmaterializer
    (layoutCodeRunnerConstruction_of_codeMachine hlayout)

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
