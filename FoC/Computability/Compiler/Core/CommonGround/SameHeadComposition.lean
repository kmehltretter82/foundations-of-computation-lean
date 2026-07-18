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

/-- Exact closed inversion of a same-head sequence. -/
theorem leftRightSeqDescription_haltsFromTape_inv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input output : Tape Bool}
    (hseq : (leftRightSeqDescription A B).HaltsFromTape input output) :
    exists middle : Tape Bool,
      A.HaltsFromTape input middle ∧
        B.HaltsFromTape
          (Tape.move Direction.right (Tape.move Direction.left middle))
          output := by
  let identity := ExactIdentityDescription
  have hidentity : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hseq' : (seqSubroutine
      (seqSubroutine A identity Direction.left) B Direction.right).HaltsFromTape
      input output := by
    simpa [leftRightSeqDescription, identity] using hseq
  rcases seqSubroutine_haltsFromTape_closed_exists_mid
      (seqSubroutine_subroutineReady hA hidentity) hB hseq' with
    ⟨identityOutput, hAIdentity, hBhalt⟩
  rcases seqSubroutine_haltsFromTape_closed_exists_mid
      hA hidentity hAIdentity with ⟨middle, hAhalt, hIdentityHalt⟩
  have hcanonical :=
    CommonGround.Identity.exactIdentityDescription_haltsFromTape
      (Tape.move Direction.left middle)
  have hout : identityOutput = Tape.move Direction.left middle :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hidentity.2 hIdentityHalt hcanonical
  subst identityOutput
  exact ⟨middle, hAhalt, hBhalt⟩

/-- A left-phase stuck run is preserved by same-head sequencing. -/
theorem leftRightSeqDescription_stuckFromTape_of_left
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input stuck : Tape Bool} (hstuck : A.StuckFromTape input stuck) :
    (leftRightSeqDescription A B).StuckFromTape input stuck := by
  have hid := CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hinner := seqSubroutine_stuckFromTape_of_left
    (handoffMove := Direction.left) hA hid hstuck
  exact seqSubroutine_stuckFromTape_of_left
    (handoffMove := Direction.right)
    (seqSubroutine_subroutineReady hA hid) hB hinner

/-- A right-phase stuck run lifts after an exact same-head handoff. -/
theorem leftRightSeqDescription_stuckFromTape_of_right
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input middle next stuck : Tape Bool}
    (hAhalts : A.HaltsFromTape input middle)
    (hbridge : Tape.move Direction.right (Tape.move Direction.left middle) = next)
    (hBstuck : B.StuckFromTape next stuck) :
    (leftRightSeqDescription A B).StuckFromTape input stuck := by
  have hid := CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hinner : (seqSubroutine A ExactIdentityDescription Direction.left).HaltsFromTape
      input (Tape.move Direction.left middle) :=
    SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      hA hid hAhalts rfl
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (Tape.move Direction.left middle))
  have hBstuck' : B.StuckFromTape
      (Tape.move Direction.right (Tape.move Direction.left middle)) stuck := by
    simpa [hbridge] using hBstuck
  exact seqSubroutine_stuckFromTape_of_right
    (seqSubroutine_subroutineReady hA hid) hB hinner hBstuck'

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
