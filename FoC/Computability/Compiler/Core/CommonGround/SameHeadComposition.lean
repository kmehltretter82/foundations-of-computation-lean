import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition

set_option doc.verso true

/-!
# Same-head sequential composition helpers

These wrappers compose two subroutines while returning the head to the same
physical cell between phases.  They are useful when ordinary
{name (full := FoC.Computability.MachineDescription.seqSubroutine)}`seqSubroutine`'s
mandatory handoff move is an implementation detail rather than part of the
logical phase boundary.
-/

namespace FoC
namespace Computability

open MachineDescription

namespace CommonGround
namespace SameHeadComposition

def leftRightSeqDescription
    (A B : MachineDescription) : MachineDescription :=
  seqSubroutine
    (seqSubroutine A ExactIdentityDescription Direction.left)
    B Direction.right

theorem leftRightSeqDescription_subroutineReady
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (leftRightSeqDescription A B).SubroutineReady := by
  exact
    seqSubroutine_subroutineReady
      (seqSubroutine_subroutineReady hA
        CommonGround.Identity.exactIdentityDescription_subroutineReady)
      hB

theorem leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tnext Tout : Tape Bool}
    (hAhalts : A.HaltsFromTape Tin Tmid)
    (hbridge :
      Tape.move Direction.right (Tape.move Direction.left Tmid) =
        Tnext)
    (hBhalts : B.HaltsFromTape Tnext Tout) :
    (leftRightSeqDescription A B).HaltsFromTape Tin Tout := by
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hAid :
      (seqSubroutine A ExactIdentityDescription Direction.left).HaltsFromTape
        Tin (Tape.move Direction.left Tmid) :=
    SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      hA hid hAhalts rfl
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (Tape.move Direction.left Tmid))
  exact
    SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (seqSubroutine_subroutineReady hA hid)
      hB hAid hbridge hBhalts

theorem leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tnext Tout : Tape Bool}
    (hAhalts : A.HaltsFromTapeEquiv Tin Tmid)
    (hbridge :
      Tape.move Direction.right (Tape.move Direction.left Tmid) =
        Tnext)
    (hBhalts : B.HaltsFromTapeEquiv Tnext Tout) :
    (leftRightSeqDescription A B).HaltsFromTapeEquiv Tin Tout := by
  rcases hAhalts with ⟨TmidActual, hAactual, hTmidEquiv⟩
  rcases hBhalts with ⟨ToutBActual, hBactual, hToutBEquiv⟩
  let TnextActual :=
    Tape.move Direction.right (Tape.move Direction.left TmidActual)
  have hTnextEquiv : Tape.Equiv Tnext TnextActual := by
    rw [← hbridge]
    exact
      Tape.Equiv.symm
        (Tape.Equiv.moveRight
          (Tape.Equiv.moveLeft hTmidEquiv))
  have hBfromActual :=
    HaltsFromTapeEquiv_of_input_equiv
      (D := B)
      (Tin := Tnext)
      (Tin' := TnextActual)
      (Tout := ToutBActual)
      hTnextEquiv
      hBactual
  rcases hBfromActual with
    ⟨ToutActual, hBactualFromActual, hToutActualEquiv⟩
  exact
    ⟨ToutActual,
      leftRightSeqDescription_haltsFromTape_of_haltsFromTape
        hA hB hAactual rfl hBactualFromActual,
      Tape.Equiv.trans hToutActualEquiv hToutBEquiv⟩

theorem leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tnext Tout : Tape Bool}
    (hAhalts : A.HaltsFromTape Tin Tmid)
    (hbridge :
      Tape.move Direction.right (Tape.move Direction.left Tmid) =
        Tnext)
    (hBhalts : B.HaltsFromTapeEquiv Tnext Tout) :
    (leftRightSeqDescription A B).HaltsFromTapeEquiv Tin Tout :=
  leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
    hA hB hAhalts.toEquiv hbridge hBhalts

theorem leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv_haltsFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tnext Tout : Tape Bool}
    (hAhalts : A.HaltsFromTapeEquiv Tin Tmid)
    (hbridge :
      Tape.move Direction.right (Tape.move Direction.left Tmid) =
        Tnext)
    (hBhalts : B.HaltsFromTape Tnext Tout) :
    (leftRightSeqDescription A B).HaltsFromTapeEquiv Tin Tout :=
  leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
    hA hB hAhalts hbridge hBhalts.toEquiv

end SameHeadComposition
end CommonGround

end Computability
end FoC
