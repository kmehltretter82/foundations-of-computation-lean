import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerOutput

set_option doc.verso true

/-!
# Direct joined source-rest endpoint contracts

These are the retained inner finish contracts shared by the direct joined
endpoint and the public source-rest wrappers.  Keeping them below the concrete
construction avoids an import cycle through the retired separated
emitter/joiner route.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

def MixedParserStackSourceRestFinishAssemblyEquivSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeEquiv
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishTargetTape
          w sourceRestBits stage)

def MixedParserStackSourceRestFinishAssemblyEquivConstruction : Prop :=
  exists finish : MachineDescription,
    MixedParserStackSourceRestFinishAssemblyEquivSpec finish

def MixedParserStackSourceRestFinishAssemblyOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishJoinedOutput
          w sourceRestBits stage)

def MixedParserStackSourceRestFinishAssemblyOutputConstruction : Prop :=
  exists finish : MachineDescription,
    MixedParserStackSourceRestFinishAssemblyOutputSpec finish

theorem MixedParserStackSourceRestFinishAssemblyOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackSourceRestFinishAssemblyOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedParserStackSourceRestFinishAssemblyOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackSourceRestFinishAssemblyOutputSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (assemblySourceRestFinishJoinedOutput
        w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
