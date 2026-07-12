import FoC.Computability.Compiler.Structured.HeadRoutes.ContractGuardrails

set_option doc.verso true

/-!
# Endpoint tape-2 projector machines

The live endpoint family contains canonical Boolean-word tapes and the
one-step-right handoff form.  The machines below erase the two unused guarded
segments, retain a two-bit metadata prefix, stream-decode the selected segment
into a contiguous Boolean word, and finally remove the metadata while restoring
the requested head position.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace Tape2Projector

def prefixEraserDescription : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ transition 0 none (some false) Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 1 (some false) none Direction.right 1
    , transition 1 (some true) none Direction.right 1
    , transition 2 none none Direction.right 3
    , transition 2 (some false) none Direction.right 2
    , transition 2 (some true) none Direction.right 2 ]

theorem prefixEraserDescription_wellFormed :
    prefixEraserDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := prefixEraserDescription.transitions)
      (stateCount := prefixEraserDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := prefixEraserDescription.transitions)
      (by decide)

theorem prefixEraserDescription_haltTransitionFree :
    prefixEraserDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := prefixEraserDescription.transitions)
    (state := prefixEraserDescription.halt)
    (by decide)

theorem prefixEraserDescription_subroutineReady :
    prefixEraserDescription.SubroutineReady :=
  ⟨prefixEraserDescription_wellFormed,
    prefixEraserDescription_haltTransitionFree⟩

def parserDescription : MachineDescription where
  stateCount := 30
  start := 0
  halt := 29
  transitions :=
    [ transition 0 (some false) none Direction.right 1
    , transition 1 (some false) none Direction.right 2
    , transition 2 (some false) none Direction.right 3
    , transition 2 (some true) none Direction.right 4
    , transition 3 (some true) none Direction.right 5
    , transition 4 (some true) none Direction.left 10
    , transition 4 (some false) none Direction.right 6
    , transition 5 (some true) none Direction.right 7
    , transition 6 (some true) none Direction.right 8
    , transition 7 (some true) none Direction.left 11
    , transition 8 (some true) none Direction.left 12
    , transition 10 none none Direction.left 10
    , transition 10 (some false) (some false) Direction.right 13
    , transition 11 none none Direction.left 11
    , transition 11 (some false) (some false) Direction.right 14
    , transition 12 none none Direction.left 12
    , transition 12 (some false) (some false) Direction.right 15
    , transition 13 none (some false) Direction.right 16
    , transition 14 none (some true) Direction.right 17
    , transition 15 none (some true) Direction.right 18
    , transition 16 none none Direction.right 20
    , transition 17 none (some false) Direction.right 20
    , transition 18 none (some true) Direction.right 20
    , transition 20 none none Direction.right 20
    , transition 20 (some false) (some false) Direction.right 21
    , transition 20 (some true) (some true) Direction.right 21
    , transition 21 none (some false) Direction.left 22
    , transition 21 (some false) (some false) Direction.right 21
    , transition 21 (some true) (some true) Direction.right 21
    , transition 22 none none Direction.right 29
    , transition 22 (some false) (some false) Direction.left 22
    , transition 22 (some true) (some true) Direction.left 22 ]

theorem parserDescription_wellFormed :
    parserDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := parserDescription.transitions)
      (stateCount := parserDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := parserDescription.transitions)
      (by decide)

theorem parserDescription_haltTransitionFree :
    parserDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := parserDescription.transitions)
    (state := parserDescription.halt)
    (by decide)

theorem parserDescription_subroutineReady :
    parserDescription.SubroutineReady :=
  ⟨parserDescription_wellFormed,
    parserDescription_haltTransitionFree⟩

def decoderDescription : MachineDescription where
  stateCount := 21
  start := 0
  halt := 20
  transitions :=
    [ transition 0 none none Direction.right 0
    , transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 2
    , transition 1 none none Direction.left 3
    , transition 1 (some false) none Direction.left 4
    , transition 1 (some true) none Direction.left 5
    , transition 2 none none Direction.left 3
    , transition 2 (some false) none Direction.left 6
    , transition 3 (some false) none Direction.right 20
    , transition 3 (some true) none Direction.right 20
    , transition 4 (some false) none Direction.left 7
    , transition 4 (some true) none Direction.left 7
    , transition 5 (some false) none Direction.left 8
    , transition 5 (some true) none Direction.left 8
    , transition 6 (some false) none Direction.left 9
    , transition 6 (some true) none Direction.left 9
    , transition 7 none none Direction.left 7
    , transition 7 (some false) (some false) Direction.right 0
    , transition 7 (some true) (some true) Direction.right 0
    , transition 8 none none Direction.left 8
    , transition 8 (some false) (some false) Direction.right 10
    , transition 8 (some true) (some true) Direction.right 10
    , transition 9 none none Direction.left 9
    , transition 9 (some false) (some false) Direction.right 11
    , transition 9 (some true) (some true) Direction.right 11
    , transition 10 none (some false) Direction.right 0
    , transition 11 none (some true) Direction.right 0 ]

theorem decoderDescription_wellFormed :
    decoderDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := decoderDescription.transitions)
      (stateCount := decoderDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := decoderDescription.transitions)
      (by decide)

theorem decoderDescription_haltTransitionFree :
    decoderDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := decoderDescription.transitions)
    (state := decoderDescription.halt)
    (by decide)

theorem decoderDescription_subroutineReady :
    decoderDescription.SubroutineReady :=
  ⟨decoderDescription_wellFormed,
    decoderDescription_haltTransitionFree⟩

def finalizerDescription : MachineDescription where
  stateCount := 26
  start := 0
  halt := 25
  transitions :=
    [ transition 0 none none Direction.left 0
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.right 2
    , transition 1 (some false) (some false) Direction.left 1
    , transition 1 (some true) (some true) Direction.left 1
    , transition 2 (some false) none Direction.right 3
    , transition 3 (some false) none Direction.right 4
    , transition 3 (some true) none Direction.right 6
    , transition 4 none none Direction.left 25
    , transition 4 (some false) none Direction.left 8
    , transition 4 (some true) none Direction.left 9
    , transition 5 none none Direction.left 20
    , transition 5 (some false) none Direction.left 8
    , transition 5 (some true) none Direction.left 9
    , transition 6 none none Direction.left 25
    , transition 6 (some false) none Direction.left 10
    , transition 6 (some true) none Direction.left 11
    , transition 7 none none Direction.left 21
    , transition 7 (some false) none Direction.left 10
    , transition 7 (some true) none Direction.left 11
    , transition 8 none none Direction.left 12
    , transition 9 none none Direction.left 13
    , transition 10 none none Direction.left 14
    , transition 11 none none Direction.left 15
    , transition 12 none (some false) Direction.right 16
    , transition 13 none (some true) Direction.right 16
    , transition 14 none (some false) Direction.right 17
    , transition 15 none (some true) Direction.right 17
    , transition 16 none none Direction.right 18
    , transition 17 none none Direction.right 19
    , transition 18 none none Direction.right 5
    , transition 19 none none Direction.right 7
    , transition 20 none none Direction.left 20
    , transition 20 (some false) (some false) Direction.left 22
    , transition 20 (some true) (some true) Direction.left 22
    , transition 21 none none Direction.left 21
    , transition 21 (some false) (some false) Direction.left 23
    , transition 21 (some true) (some true) Direction.left 23
    , transition 22 none none Direction.right 25
    , transition 22 (some false) (some false) Direction.left 22
    , transition 22 (some true) (some true) Direction.left 22
    , transition 23 none none Direction.right 24
    , transition 23 (some false) (some false) Direction.left 23
    , transition 23 (some true) (some true) Direction.left 23
    , transition 24 (some false) (some false) Direction.right 25
    , transition 24 (some true) (some true) Direction.right 25 ]

theorem finalizerDescription_wellFormed :
    finalizerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := finalizerDescription.transitions)
      (stateCount := finalizerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := finalizerDescription.transitions)
      (by decide)

theorem finalizerDescription_haltTransitionFree :
    finalizerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := finalizerDescription.transitions)
    (state := finalizerDescription.halt)
    (by decide)

theorem finalizerDescription_subroutineReady :
    finalizerDescription.SubroutineReady :=
  ⟨finalizerDescription_wellFormed,
    finalizerDescription_haltTransitionFree⟩

end Tape2Projector
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
