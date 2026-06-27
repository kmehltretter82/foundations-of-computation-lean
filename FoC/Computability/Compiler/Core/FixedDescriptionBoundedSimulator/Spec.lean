import FoC.Computability.Compiler.Core.BoundedTrace

set_option doc.verso true

/-!
# Canonical fixed-description bounded simulator contract

The existing table-realizer contract for fixed-description simulators records
only normalized output.  Bounded-layout runner phases need a stronger
canonical tape contract: the simulator starts on a canonical
{name}`FoC.Computability.MachineDescription.SimulatorLayout` tape, halts on the canonical tape
for the bounded run, and has no other halting tape on canonical inputs.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

def FixedDescriptionBoundedSimulatorCanonicalOutputTape
    (D : MachineDescription)
    (L : SimulatorLayout) : Tape Bool :=
  SimulatorLayout.tape
    (SimulatorLayout.run D L.stage L)

def FixedDescriptionBoundedSimulatorPaddedTape
    (w : Word Bool) (padding : Nat) : Tape Bool :=
  match w with
  | [] =>
      { left := []
        head := none
        right := List.replicate padding none }
  | bit :: rest =>
      { left := []
        head := some bit
        right := rest.map some ++ List.replicate padding none }

theorem fixedDescriptionBoundedSimulator_dropTrailingNone_append_none
    {symbol : Type u} (xs : List (Option symbol)) :
    Tape.dropTrailingNone (xs ++ [none]) =
      Tape.dropTrailingNone xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.cons_append, Tape.dropTrailingNone_cons,
        Tape.dropTrailingNone_cons, ih]

theorem fixedDescriptionBoundedSimulator_dropTrailingNone_replicate_none
    (padding : Nat) :
    Tape.dropTrailingNone
        (List.replicate padding (none : Option Bool)) = [] := by
  induction padding with
  | zero =>
      rfl
  | succ padding ih =>
      simp [List.replicate, Tape.dropTrailingNone, ih]

theorem fixedDescriptionBoundedSimulator_dropTrailingNone_append_replicate_none
    (xs : List (Option Bool)) (padding : Nat) :
    Tape.dropTrailingNone
        (xs ++ List.replicate padding (none : Option Bool)) =
      Tape.dropTrailingNone xs := by
  induction padding generalizing xs with
  | zero =>
      simp
  | succ padding ih =>
      calc
        Tape.dropTrailingNone
            (xs ++ List.replicate (padding + 1) (none : Option Bool)) =
          Tape.dropTrailingNone
            ((xs ++ [none]) ++
              List.replicate padding (none : Option Bool)) := by
            simp [List.replicate_succ, List.append_assoc]
        _ = Tape.dropTrailingNone (xs ++ [none]) :=
          ih (xs ++ [none])
        _ = Tape.dropTrailingNone xs :=
          fixedDescriptionBoundedSimulator_dropTrailingNone_append_none xs

theorem FixedDescriptionBoundedSimulatorPaddedTape_equiv_input
    (w : Word Bool) (padding : Nat) :
    Tape.Equiv (FixedDescriptionBoundedSimulatorPaddedTape w padding)
      (Tape.input w) := by
  cases w with
  | nil =>
      constructor
      · rfl
      · constructor
        · rfl
        · exact
            fixedDescriptionBoundedSimulator_dropTrailingNone_replicate_none
              padding
  | cons bit rest =>
      constructor
      · rfl
      · constructor
        · rfl
        · exact
            fixedDescriptionBoundedSimulator_dropTrailingNone_append_replicate_none
              (rest.map some) padding

theorem FixedDescriptionBoundedSimulatorPaddedTape_normalizedOutput
    (w : Word Bool) (padding : Nat) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedTape w padding) = w := by
  have hequiv :=
    FixedDescriptionBoundedSimulatorPaddedTape_equiv_input w padding
  rw [Tape.Equiv.normalizedOutput_eq hequiv]
  simpa [Tape.output] using Tape.normalizedOutput_output w

theorem FixedDescriptionBoundedSimulatorPaddedTape_contextLength_ge_padding
    (w : Word Bool) (padding : Nat) :
    padding <=
      Tape.contextLength
        (FixedDescriptionBoundedSimulatorPaddedTape w padding) := by
  cases w <;>
    simp [FixedDescriptionBoundedSimulatorPaddedTape,
      Tape.contextLength, List.length_append] <;>
    omega

def FixedDescriptionBoundedSimulatorPaddedOutputTape
    (D : MachineDescription)
    (L : SimulatorLayout) : Tape Bool :=
  FixedDescriptionBoundedSimulatorPaddedTape
    (FixedDescriptionBoundedSimulatorOutput D L)
    (Tape.contextLength
      (Tape.input (FixedDescriptionBoundedSimulatorInput L)))

theorem FixedDescriptionBoundedSimulatorPaddedOutputTape_equiv_canonical
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.Equiv
      (FixedDescriptionBoundedSimulatorPaddedOutputTape D L)
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) := by
  simpa [FixedDescriptionBoundedSimulatorPaddedOutputTape,
    FixedDescriptionBoundedSimulatorCanonicalOutputTape,
    FixedDescriptionBoundedSimulatorOutput,
    SimulatorLayout.tape] using
    FixedDescriptionBoundedSimulatorPaddedTape_equiv_input
      (FixedDescriptionBoundedSimulatorOutput D L)
      (Tape.contextLength
        (Tape.input (FixedDescriptionBoundedSimulatorInput L)))

theorem FixedDescriptionBoundedSimulatorPaddedOutputTape_normalizedOutput
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedOutputTape D L) =
      FixedDescriptionBoundedSimulatorOutput D L := by
  simpa [FixedDescriptionBoundedSimulatorPaddedOutputTape] using
    FixedDescriptionBoundedSimulatorPaddedTape_normalizedOutput
      (FixedDescriptionBoundedSimulatorOutput D L)
      (Tape.contextLength
        (Tape.input (FixedDescriptionBoundedSimulatorInput L)))

theorem FixedDescriptionBoundedSimulatorPaddedOutputTape_contextLength_ge_input
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.contextLength
        (Tape.input (FixedDescriptionBoundedSimulatorInput L)) <=
      Tape.contextLength
        (FixedDescriptionBoundedSimulatorPaddedOutputTape D L) := by
  simpa [FixedDescriptionBoundedSimulatorPaddedOutputTape] using
    FixedDescriptionBoundedSimulatorPaddedTape_contextLength_ge_padding
      (FixedDescriptionBoundedSimulatorOutput D L)
      (Tape.contextLength
        (Tape.input (FixedDescriptionBoundedSimulatorInput L)))

def FixedDescriptionBoundedSimulatorCanonicalForwardSpec
    (D sim : MachineDescription) : Prop :=
  forall L : SimulatorLayout,
    sim.HaltsWithTape
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L)

def FixedDescriptionBoundedSimulatorCanonicalClosedSpec
    (D sim : MachineDescription) : Prop :=
  forall L : SimulatorLayout,
  forall T : Tape Bool,
    sim.HaltsWithTape (FixedDescriptionBoundedSimulatorInput L) T ->
      T = FixedDescriptionBoundedSimulatorCanonicalOutputTape D L

def FixedDescriptionBoundedSimulatorCanonicalSpec
    (D sim : MachineDescription) : Prop :=
  sim.SubroutineReady ∧
    FixedDescriptionBoundedSimulatorCanonicalForwardSpec D sim ∧
      FixedDescriptionBoundedSimulatorCanonicalClosedSpec D sim

def FixedDescriptionBoundedSimulatorCanonicalConstruction : Prop :=
  forall D : MachineDescription,
    exists sim : MachineDescription,
      FixedDescriptionBoundedSimulatorCanonicalSpec D sim

def FixedDescriptionBoundedSimulatorEquivForwardSpec
    (D sim : MachineDescription) : Prop :=
  forall L : SimulatorLayout,
    sim.HaltsWithTapeEquiv
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L)

def FixedDescriptionBoundedSimulatorEquivClosedSpec
    (D sim : MachineDescription) : Prop :=
  forall L : SimulatorLayout,
  forall T : Tape Bool,
    sim.HaltsWithTape (FixedDescriptionBoundedSimulatorInput L) T ->
      Tape.Equiv T (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L)

def FixedDescriptionBoundedSimulatorEquivSpec
    (D sim : MachineDescription) : Prop :=
  sim.SubroutineReady ∧
    FixedDescriptionBoundedSimulatorEquivForwardSpec D sim ∧
      FixedDescriptionBoundedSimulatorEquivClosedSpec D sim

def FixedDescriptionBoundedSimulatorEquivConstruction : Prop :=
  forall D : MachineDescription,
    exists sim : MachineDescription,
      FixedDescriptionBoundedSimulatorEquivSpec D sim

def FixedDescriptionBoundedSimulatorPaddedForwardSpec
    (D sim : MachineDescription) : Prop :=
  forall L : SimulatorLayout,
    sim.HaltsWithTape
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorPaddedOutputTape D L)

def FixedDescriptionBoundedSimulatorPaddedClosedSpec
    (D sim : MachineDescription) : Prop :=
  forall L : SimulatorLayout,
  forall T : Tape Bool,
    sim.HaltsWithTape (FixedDescriptionBoundedSimulatorInput L) T ->
      T = FixedDescriptionBoundedSimulatorPaddedOutputTape D L

def FixedDescriptionBoundedSimulatorPaddedSpec
    (D sim : MachineDescription) : Prop :=
  sim.SubroutineReady ∧
    FixedDescriptionBoundedSimulatorPaddedForwardSpec D sim ∧
      FixedDescriptionBoundedSimulatorPaddedClosedSpec D sim

def FixedDescriptionBoundedSimulatorPaddedConstruction : Prop :=
  forall D : MachineDescription,
    exists sim : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedSpec D sim

theorem fixedDescriptionBoundedSimulatorEquivSpec_of_canonicalSpec
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorCanonicalSpec D sim) :
    FixedDescriptionBoundedSimulatorEquivSpec D sim := by
  constructor
  · exact hsim.left
  constructor
  · intro L
    exact HaltsWithTape.toEquiv
      (hsim.right.left L)
  · intro L T hhalt
    rw [hsim.right.right L T hhalt]
    exact Tape.Equiv.refl _

theorem fixedDescriptionBoundedSimulatorEquivConstruction_of_canonical
    (hcanonical : FixedDescriptionBoundedSimulatorCanonicalConstruction) :
    FixedDescriptionBoundedSimulatorEquivConstruction := by
  intro D
  rcases hcanonical D with ⟨sim, hsim⟩
  exact
    ⟨sim, fixedDescriptionBoundedSimulatorEquivSpec_of_canonicalSpec hsim⟩

theorem fixedDescriptionBoundedSimulatorEquivSpec_of_paddedSpec
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorPaddedSpec D sim) :
    FixedDescriptionBoundedSimulatorEquivSpec D sim := by
  constructor
  · exact hsim.left
  constructor
  · intro L
    exact
      ⟨FixedDescriptionBoundedSimulatorPaddedOutputTape D L,
        hsim.right.left L,
        FixedDescriptionBoundedSimulatorPaddedOutputTape_equiv_canonical
          D L⟩
  · intro L T hhalt
    rw [hsim.right.right L T hhalt]
    exact
      FixedDescriptionBoundedSimulatorPaddedOutputTape_equiv_canonical
        D L

theorem fixedDescriptionBoundedSimulatorEquivConstruction_of_padded
    (hpadded : FixedDescriptionBoundedSimulatorPaddedConstruction) :
    FixedDescriptionBoundedSimulatorEquivConstruction := by
  intro D
  rcases hpadded D with ⟨sim, hsim⟩
  exact
    ⟨sim, fixedDescriptionBoundedSimulatorEquivSpec_of_paddedSpec hsim⟩

theorem FixedDescriptionBoundedSimulatorEquivSpec.haltsFromTapeEquiv
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorEquivSpec D sim)
    (L : SimulatorLayout) :
    sim.HaltsFromTapeEquiv
      (SimulatorLayout.tape L)
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) := by
  rcases hsim.right.left L with ⟨Tactual, hhalt, hequiv⟩
  refine ⟨Tactual, ?_, hequiv⟩
  rcases hhalt with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [HaltsWithTapeIn,
    HaltsFromTapeIn,
    initial,
    FixedDescriptionBoundedSimulatorInput,
    SimulatorLayout.tape] using hn

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_canonicalSpec
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorCanonicalSpec D sim) :
    FixedDescriptionBoundedSimulatorTableRealizes D sim := by
  constructor
  · exact hsim.left.left
  · intro L
    simpa [FixedDescriptionBoundedSimulatorCanonicalOutputTape,
      FixedDescriptionBoundedSimulatorOutput,
      SimulatorLayout.tape_normalizedOutput,
      SimulatorLayout.asBoolInput] using
      haltsWithOutput_of_haltsWithTape
        (hsim.right.left L)

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_equivSpec
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorEquivSpec D sim) :
    FixedDescriptionBoundedSimulatorTableRealizes D sim := by
  constructor
  · exact hsim.left.left
  · intro L
    simpa [FixedDescriptionBoundedSimulatorCanonicalOutputTape,
      FixedDescriptionBoundedSimulatorOutput,
      SimulatorLayout.tape_normalizedOutput,
      SimulatorLayout.asBoolInput] using
      haltsWithOutput_of_haltsWithTapeEquiv
        (hsim.right.left L)

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_equivConstruction
    (hcompile :
      FixedDescriptionBoundedSimulatorEquivConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fun D =>
    Exists.elim (hcompile D) fun sim hsim =>
      ⟨sim,
      fixedDescriptionBoundedSimulatorTableRealizes_of_equivSpec hsim⟩

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_canonicalConstruction
    (hcompile :
      FixedDescriptionBoundedSimulatorCanonicalConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fun D =>
    Exists.elim (hcompile D) fun sim hsim =>
      ⟨sim,
      fixedDescriptionBoundedSimulatorTableRealizes_of_canonicalSpec hsim⟩

end Computability
end FoC
