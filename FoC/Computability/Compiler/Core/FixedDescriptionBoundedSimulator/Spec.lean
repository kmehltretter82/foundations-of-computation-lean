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

def FixedDescriptionBoundedSimulatorCanonicalOutputTape
    (D : MachineDescription)
    (L : MachineDescription.SimulatorLayout) : Tape Bool :=
  MachineDescription.SimulatorLayout.tape
    (MachineDescription.SimulatorLayout.run D L.stage L)

def FixedDescriptionBoundedSimulatorCanonicalForwardSpec
    (D sim : MachineDescription) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    sim.HaltsWithTape
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L)

def FixedDescriptionBoundedSimulatorCanonicalClosedSpec
    (D sim : MachineDescription) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
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

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_canonicalSpec
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorCanonicalSpec D sim) :
    FixedDescriptionBoundedSimulatorTableRealizes D sim := by
  constructor
  · exact hsim.left.left
  · intro L
    have hhalt := hsim.right.left L
    have houtput :
        Tape.normalizedOutput
            (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) =
          FixedDescriptionBoundedSimulatorOutput D L := by
      simp [FixedDescriptionBoundedSimulatorCanonicalOutputTape,
        FixedDescriptionBoundedSimulatorOutput,
        MachineDescription.SimulatorLayout.tape_normalizedOutput,
        MachineDescription.SimulatorLayout.asBoolInput]
    rw [← houtput]
    exact MachineDescription.haltsWithOutput_of_haltsWithTape hhalt

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_canonicalConstruction
    (hcompile :
      FixedDescriptionBoundedSimulatorCanonicalConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨sim, hsim⟩
  exact
    ⟨sim,
      fixedDescriptionBoundedSimulatorTableRealizes_of_canonicalSpec hsim⟩

end Computability
end FoC
