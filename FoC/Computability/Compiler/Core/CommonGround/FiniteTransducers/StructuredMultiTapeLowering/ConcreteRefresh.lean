import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.SelectedSeparatorRefreshRuns
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.RunsStructuredSingleton3

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

def concreteStructuredSingletonRefresh3Description : MachineDescription :=
  concreteHeadStructuredSegmentRefresh3Description
    selectedShapeRefreshDescription
    selectedShapeRefreshDescription

theorem concreteStructuredSingletonRefresh3Description_contract :
    StructuredSingletonGuardSlackRefresh3Contract
      concreteStructuredSingletonRefresh3Description := by
  simpa [concreteStructuredSingletonRefresh3Description] using
    concreteHeadStructuredSegmentRefresh3Description_contract
      (selectedShapeRefreshDescription_contract 1)
      (selectedShapeRefreshDescription_contract 2)

def concreteStructuredSingletonRefresh3Prerequisites
    (D : Description) (hD : D.WellFormed)
    (hrows : SupportsReadWriteRows3 D) :
    StaticLoweringWithStructuredSingleton3RefreshPrerequisites D where
  wellFormed := hD
  rows := hrows
  refresh := concreteStructuredSingletonRefresh3Description
  refreshContract := concreteStructuredSingletonRefresh3Description_contract

def concreteStructuredSingletonRefresh3PrerequisitesOfSupports
    (D : Description) (hD : D.WellFormed)
    (hrows : supportsReadWriteRows3 D = true) :
    StaticLoweringWithStructuredSingleton3RefreshPrerequisites D :=
  concreteStructuredSingletonRefresh3Prerequisites D hD
    (supportedReadWriteRows3_of_supports_eq_true hrows)

def concreteStructuredSingleton3TraceDescription
    (D : Description) :
    Nat -> Configuration -> MachineDescription :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh D
    concreteStructuredSingletonRefresh3Description

theorem concreteStructuredSingleton3TraceDescription_subroutineReady
    {D : Description} (hrows : SupportsReadWriteRows3 D)
    (n : Nat) (c : Configuration) :
    (concreteStructuredSingleton3TraceDescription D n c).SubroutineReady :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_subroutineReady
    hrows concreteStructuredSingletonRefresh3Description_contract n c

theorem concreteStructuredSingleton3TraceDescription_simulates_runConfig
    {D : Description} (hrows : SupportsReadWriteRows3 D)
    (n : Nat) (c : Configuration)
    (hc : c.tapes.length = D.tapeCount) :
    (concreteStructuredSingleton3TraceDescription D n c).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes c.tapes)
      (encodedGuardedStructuredTapes (D.runConfig n c).tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_runConfig
    hrows concreteStructuredSingletonRefresh3Description_contract n c hc

theorem concreteStructuredSingleton3TraceDescription_simulates_initial_runConfig
    {D : Description} (hrows : SupportsReadWriteRows3 D)
    (n : Nat) (inputs : List (Word Bool)) :
    (concreteStructuredSingleton3TraceDescription D n
      (D.initial inputs)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_runConfig
    hrows concreteStructuredSingletonRefresh3Description_contract n inputs

theorem concreteStructuredSingleton3TraceDescription_simulates_initial_haltsWithTapes
    {D : Description} (hrows : SupportsReadWriteRows3 D)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (concreteStructuredSingleton3TraceDescription D n
        (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_haltsWithTapes
    hrows concreteStructuredSingletonRefresh3Description_contract hhalts

theorem concreteStructuredSingleton3TraceDescription_simulates_initial_haltsFromConfig
    {D : Description} (hrows : SupportsReadWriteRows3 D)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (concreteStructuredSingleton3TraceDescription D n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_haltsFromConfig
    hrows concreteStructuredSingletonRefresh3Description_contract hhalts

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
