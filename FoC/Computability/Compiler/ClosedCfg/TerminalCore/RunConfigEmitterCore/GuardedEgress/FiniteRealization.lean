import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.PaddedIdentity

set_option doc.verso true

/-!
# Finite realization frontier for guarded #18 egress

The parent module proves an executable exact decoder for the guarded tape-0
payload, an executable metadata/scratch/witness decoder for tape 2, and exact
assembly of the required right-scratch target.  This module isolates the one
remaining implementation question: realize that checked transform by a finite
one-tape description while accepting every far-edge-padded representative of
the guarded source.

The concrete navigation prefix below is already closed.  It reaches the raw
tape-0 payload in one step, or the raw tape-2 payload through the verified
two-segment seeker.  Neither route invokes the lossy selected-segment decoder,
the shared selected-head endpoint, or its open footprint compactor.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress
namespace FiniteRealization

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-!
## Realization contract for the checked transform
-/

/-- A finite normalizer realizes every successful result of the checked
parse-and-assemble transform on every equivalent physical representative. -/
def Spec (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (i : Index) (actual target : Tape Bool),
      Tape.Equiv actual i.source ->
        SemanticAssembly.assembleTarget
            (SemanticAssembly.tape0Payload i) i.doneWitnessTape =
          some target ->
        normalizer.HaltsFromTape actual target

def Construction : Prop :=
  exists normalizer : MachineDescription, Spec normalizer

theorem guardedEgressSpec_of_spec
    {normalizer : MachineDescription} (hspec : Spec normalizer) :
    GuardedEgress.Spec normalizer := by
  constructor
  · exact hspec.left
  · intro i actual hequiv
    exact hspec.right i actual i.target hequiv
      (SemanticAssembly.assembleTarget_index i)

theorem spec_of_guardedEgressSpec
    {normalizer : MachineDescription}
    (hspec : GuardedEgress.Spec normalizer) : Spec normalizer := by
  constructor
  · exact hspec.left
  · intro i actual target hequiv htarget
    rw [SemanticAssembly.assembleTarget_index] at htarget
    cases htarget
    exact hspec.right i actual hequiv

theorem guardedEgressConstruction_of_construction
    (hconstruction : Construction) : GuardedEgress.Construction := by
  rcases hconstruction with ⟨normalizer, hnormalizer⟩
  exact ⟨normalizer, guardedEgressSpec_of_spec hnormalizer⟩

theorem construction_of_guardedEgressConstruction
    (hconstruction : GuardedEgress.Construction) : Construction := by
  rcases hconstruction with ⟨normalizer, hnormalizer⟩
  exact ⟨normalizer, spec_of_guardedEgressSpec hnormalizer⟩

/-!
## Exact raw-segment ingress
-/

/-- Physical cursor one cell right of the opening tape-0 separator.  Its head
is the first raw bit of the guarded tape-0 payload. -/
def tape0PayloadHead (i : Index) : Tape Bool :=
  Tape.move Direction.right i.source

/-- A blank-delimited raw Boolean payload starts under the physical head;
both physical contexts remain explicit so a later parser can preserve them. -/
def RawPayloadAtHead (payload : Word Bool) (physical : Tape Bool) : Prop :=
  exists left suffix : List (Option Bool),
    physical =
      tapeAtCells left
        (List.append (payload.map some) (none :: suffix))

/-- Physical cells following the tape-0 closing separator. -/
def tape0PayloadPadding (i : Index) : List (Option Bool) :=
  List.append
    (logicalTapeCode (guardLogicalTape i.consumedStageTape))
    (List.append tapeSeparatorCells
      (List.append
        (logicalTapeCode (guardLogicalTape i.doneWitnessTape))
        tapeSeparatorCells))

/-- Exact suffix following the guarded tape-0 payload.  Keeping this suffix
opaque lets later raw parsers state their ingress without unfolding the two
unrelated logical tapes. -/
def tape0PayloadSuffix (i : Index) : List (Option Bool) :=
  none :: tape0PayloadPadding i

private theorem logicalTapeCode_exists_cons (T : Tape Bool) :
    exists first : Option Bool, exists rest : List (Option Bool),
      logicalTapeCode T = first :: rest := by
  cases hleft : T.left.reverse with
  | nil =>
      refine
        ⟨some true,
          some true ::
            List.append (logicalCellCode T.head)
              (logicalCellListCode T.right), ?_⟩
      simp only [logicalTapeCode, hleft, logicalCellListCode_nil,
        headMarkerCells]
      rfl
  | cons cell cells =>
      cases cell with
      | none =>
          refine
            ⟨some false,
              some false ::
                List.append (logicalCellListCode cells)
                  (List.append headMarkerCells
                    (List.append (logicalCellCode T.head)
                      (logicalCellListCode T.right))), ?_⟩
          simp only [logicalTapeCode, hleft, logicalCellListCode_cons,
            logicalCellCode_none]
          rfl
      | some bit =>
          cases bit with
          | false =>
              refine
                ⟨some false,
                  some true ::
                    List.append (logicalCellListCode cells)
                      (List.append headMarkerCells
                        (List.append (logicalCellCode T.head)
                          (logicalCellListCode T.right))), ?_⟩
              simp only [logicalTapeCode, hleft, logicalCellListCode_cons,
                logicalCellCode_some_false]
              rfl
          | true =>
              refine
                ⟨some true,
                  some false ::
                    List.append (logicalCellListCode cells)
                      (List.append headMarkerCells
                        (List.append (logicalCellCode T.head)
                          (logicalCellListCode T.right))), ?_⟩
              simp only [logicalTapeCode, hleft, logicalCellListCode_cons,
                logicalCellCode_some_true]
              rfl

private theorem moveRight_encodedGuardedStructured3Tapes
    (T0 T1 T2 : Tape Bool) :
    Tape.move Direction.right
        (encodedGuardedStructuredTapes [T0, T1, T2]) =
      tapeAtCells [none]
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode (guardLogicalTape T2))
                  tapeSeparatorCells))))) := by
  rcases logicalTapeCode_exists_cons (guardLogicalTape T0) with
    ⟨first, rest, hcode⟩
  simp [encodedGuardedStructuredTapes, encodedStructuredTapes,
    guardLogicalTapes, encodedStructuredTapeCells, tapeSeparatorCells,
    hcode, Tape.move, Tape.moveRight, tapeAtCells]

theorem tape0PayloadHead_eq (i : Index) :
    tape0PayloadHead i =
      tapeAtCells [none]
        (List.append
          (logicalTapeCode (guardLogicalTape i.finalTape))
          (tape0PayloadSuffix i)) := by
  change
    Tape.move Direction.right
        (encodedGuardedStructuredTapes
          [i.finalTape, i.consumedStageTape, i.doneWitnessTape]) = _
  simpa [tape0PayloadSuffix, tape0PayloadPadding,
    tapeSeparatorCells, List.append_assoc] using
    moveRight_encodedGuardedStructured3Tapes
      i.finalTape i.consumedStageTape i.doneWitnessTape

theorem tape0PayloadHead_rawShape (i : Index) :
    RawPayloadAtHead
      (logicalTapeBits (guardLogicalTape i.finalTape))
      (tape0PayloadHead i) := by
  refine
    ⟨[none], tape0PayloadPadding i, ?_⟩
  rw [tape0PayloadHead_eq]
  simp [tape0PayloadSuffix, tape0PayloadPadding, tapeSeparatorCells,
    logicalTapeCode_eq_map_some]

/-- Exact endpoint after scanning the complete guarded tape-0 raw payload. -/
def tape0PayloadScanEnd (i : Index) : Tape Bool :=
  rightEdgeScanTargetTapeFromLeft [none]
    (logicalTapeBits (guardLogicalTape i.finalTape))
    (tape0PayloadPadding i)

theorem rightEdgeScanDescription_haltsFrom_tape0Payload (i : Index) :
    rightEdgeScanDescription.HaltsFromTape
      (tape0PayloadHead i) (tape0PayloadScanEnd i) := by
  rw [tape0PayloadHead_eq]
  simpa [tape0PayloadScanEnd, tape0PayloadSuffix,
    rightEdgeScanSourceTapeFromLeft,
    logicalTapeCode_eq_map_some] using
    rightEdgeScanDescription_haltsFromTape
      [none]
      (logicalTapeBits (guardLogicalTape i.finalTape))
      (tape0PayloadPadding i)

/-- Enter tape 0 from its opening separator and scan its full raw payload. -/
def scanTape0PayloadDescription : MachineDescription :=
  seqSubroutine ExactIdentityDescription rightEdgeScanDescription
    Direction.right

theorem scanTape0PayloadDescription_subroutineReady :
    scanTape0PayloadDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    CommonGround.Identity.exactIdentityDescription_subroutineReady
    rightEdgeScanDescription_subroutineReady

theorem scanTape0PayloadDescription_haltsFromTape (i : Index) :
    scanTape0PayloadDescription.HaltsFromTape
      i.source (tape0PayloadScanEnd i) := by
  unfold scanTape0PayloadDescription
  exact CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
    CommonGround.Identity.exactIdentityDescription_subroutineReady
    rightEdgeScanDescription_subroutineReady
    (CommonGround.Identity.exactIdentityDescription_haltsFromTape i.source)
    rfl
    (rightEdgeScanDescription_haltsFrom_tape0Payload i)

theorem scanTape0PayloadDescription_haltsFromTapeEquiv
    (i : Index) (actual : Tape Bool)
    (hequiv : Tape.Equiv actual i.source) :
    scanTape0PayloadDescription.HaltsFromTapeEquiv
      actual (tape0PayloadScanEnd i) := by
  exact MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tape.Equiv.symm hequiv)
    (scanTape0PayloadDescription_haltsFromTape i)

theorem rightMoveOnceDescription_haltsFrom_tape0Payload
    (i : Index) :
    rightMoveOnceDescription.HaltsFromTape
      i.source (tape0PayloadHead i) := by
  exact rightMoveOnceDescription_haltsFromTape i.source

theorem rightMoveOnceDescription_haltsFrom_tape0PayloadEquiv
    (i : Index) (actual : Tape Bool)
    (hequiv : Tape.Equiv actual i.source) :
    rightMoveOnceDescription.HaltsFromTapeEquiv
      actual (tape0PayloadHead i) := by
  exact MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tape.Equiv.symm hequiv)
    (rightMoveOnceDescription_haltsFrom_tape0Payload i)

/-- Canonical guarded logical list used by both seeker proofs. -/
def guardedLogical (i : Index) : List (Tape Bool) :=
  guardLogicalTapes
    [i.finalTape, i.consumedStageTape, i.doneWitnessTape]

/-- Exact physical cursor at the opening separator of logical tape 1, after a
complete non-mutating traversal of the raw tape-0 payload. -/
def tape1Separator (i : Index) : Tape Bool :=
  tapeAtEncodedSplit
    (encodedPrefixBeforeTape (guardedLogical i) 1)
    (encodedSuffixFromTape (guardedLogical i) 1)

theorem seekTape1Description_haltsFrom_separator (i : Index) :
    seekTape1Description.HaltsFromTape i.source (tape1Separator i) := by
  have hsource :
      AtExistingTapeSeparator (guardedLogical i) 0 i.source := by
    constructor
    · simpa [Index.source, Index.logicalTapes, guardedLogical,
        encodedGuardedStructuredTapes,
        loopDispatcherDoneWitnessTapes, Index.finalTape,
        Index.finalLayout, Index.consumedStageTape,
        Index.doneWitnessTape, AtEncodedBlockStart] using
        atEncodedBlockStart_self (guardedLogical i)
    · exact
        ⟨guardLogicalTape i.finalTape,
          [guardLogicalTape i.consumedStageTape,
            guardLogicalTape i.doneWitnessTape], rfl⟩
  rcases seekTape1Description_contract.realizes
      (guardedLogical i) i.source hsource with
    ⟨physical, hseek, _hindex, hphysical⟩
  rw [hphysical] at hseek
  exact hseek

theorem seekTape1Description_haltsFrom_separatorEquiv
    (i : Index) (actual : Tape Bool)
    (hequiv : Tape.Equiv actual i.source) :
    seekTape1Description.HaltsFromTapeEquiv
      actual (tape1Separator i) := by
  exact MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tape.Equiv.symm hequiv)
    (seekTape1Description_haltsFrom_separator i)

/-- Exact physical cursor at the opening separator of logical tape 2. -/
def tape2Separator (i : Index) : Tape Bool :=
  tapeAtEncodedSplit
    (encodedPrefixBeforeTape (guardedLogical i) 2)
    (encodedSuffixFromTape (guardedLogical i) 2)

theorem seekTape2Description_haltsFrom_separator (i : Index) :
    seekTape2Description.HaltsFromTape i.source (tape2Separator i) := by
  have hsource :
      exists T : Tape Bool, exists U : Tape Bool, exists V : Tape Bool,
        guardedLogical i = [T, U, V] ∧
          AtEncodedBlockStart (guardedLogical i) i.source := by
    refine
      ⟨guardLogicalTape i.finalTape,
        guardLogicalTape i.consumedStageTape,
        guardLogicalTape i.doneWitnessTape, ?_, ?_⟩
    · rfl
    · simpa [Index.source, Index.logicalTapes, guardedLogical,
        encodedGuardedStructuredTapes,
        loopDispatcherDoneWitnessTapes, Index.finalTape,
        Index.finalLayout, Index.consumedStageTape,
        Index.doneWitnessTape] using
        atEncodedBlockStart_self (guardedLogical i)
  rcases seekTape2Description_contract_three.realizes
      (guardedLogical i) i.source hsource with
    ⟨physical, hseek, _hindex, hphysical⟩
  rw [hphysical] at hseek
  exact hseek

/-- Physical cursor on the first raw bit of the guarded tape-2 payload. -/
def tape2PayloadHead (i : Index) : Tape Bool :=
  Tape.move Direction.right (tape2Separator i)

private theorem moveRight_tapeAtEncodedSplit_separator
    (encodedLeft : List (Option Bool)) (T : Tape Bool) :
    Tape.move Direction.right
        (tapeAtEncodedSplit encodedLeft
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode T) tapeSeparatorCells))) =
      tapeAtCells (none :: encodedLeft.reverse)
        (List.append (logicalTapeCode T) tapeSeparatorCells) := by
  rcases logicalTapeCode_exists_cons T with ⟨first, rest, hcode⟩
  simp [tapeAtEncodedSplit, tapeSeparatorCells, hcode,
    Tape.move, Tape.moveRight, tapeAtCells]

theorem tape2PayloadHead_eq (i : Index) :
    tape2PayloadHead i =
      tapeAtCells
        (none ::
          (encodedPrefixBeforeTape (guardedLogical i) 2).reverse)
        (List.append
          (logicalTapeCode (guardLogicalTape i.doneWitnessTape))
          tapeSeparatorCells) := by
  rw [tape2PayloadHead, tape2Separator]
  have hsuffix :
      encodedSuffixFromTape (guardedLogical i) 2 =
        List.append tapeSeparatorCells
          (List.append
            (logicalTapeCode (guardLogicalTape i.doneWitnessTape))
            tapeSeparatorCells) := by
    simp [encodedSuffixFromTape, guardedLogical, guardLogicalTapes,
      encodedStructuredTapeCells]
  rw [hsuffix]
  exact moveRight_tapeAtEncodedSplit_separator _ _

theorem tape2PayloadHead_rawShape (i : Index) :
    RawPayloadAtHead
      (logicalTapeBits (guardLogicalTape i.doneWitnessTape))
      (tape2PayloadHead i) := by
  refine
    ⟨none ::
        (encodedPrefixBeforeTape (guardedLogical i) 2).reverse,
      [], ?_⟩
  rw [tape2PayloadHead_eq]
  simp [tapeSeparatorCells, logicalTapeCode_eq_map_some]

/-- Exact endpoint after scanning the complete guarded tape-2 raw payload. -/
def tape2PayloadScanEnd (i : Index) : Tape Bool :=
  rightEdgeScanTargetTapeFromLeft
    (none ::
      (encodedPrefixBeforeTape (guardedLogical i) 2).reverse)
    (logicalTapeBits (guardLogicalTape i.doneWitnessTape)) []

theorem rightEdgeScanDescription_haltsFrom_tape2Payload (i : Index) :
    rightEdgeScanDescription.HaltsFromTape
      (tape2PayloadHead i) (tape2PayloadScanEnd i) := by
  rw [tape2PayloadHead_eq]
  simpa [tape2PayloadScanEnd, rightEdgeScanSourceTapeFromLeft,
    tapeSeparatorCells, logicalTapeCode_eq_map_some] using
    rightEdgeScanDescription_haltsFromTape
      (none ::
        (encodedPrefixBeforeTape (guardedLogical i) 2).reverse)
      (logicalTapeBits (guardLogicalTape i.doneWitnessTape)) []

/-- Seek logical tape 2 and scan its complete raw payload. -/
def scanTape2PayloadDescription : MachineDescription :=
  seqSubroutine seekTape2Description rightEdgeScanDescription
    Direction.right

theorem scanTape2PayloadDescription_subroutineReady :
    scanTape2PayloadDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    seekTape2Description_subroutineReady
    rightEdgeScanDescription_subroutineReady

theorem scanTape2PayloadDescription_haltsFromTape (i : Index) :
    scanTape2PayloadDescription.HaltsFromTape
      i.source (tape2PayloadScanEnd i) := by
  unfold scanTape2PayloadDescription
  exact CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
    seekTape2Description_subroutineReady
    rightEdgeScanDescription_subroutineReady
    (seekTape2Description_haltsFrom_separator i)
    rfl
    (rightEdgeScanDescription_haltsFrom_tape2Payload i)

theorem scanTape2PayloadDescription_haltsFromTapeEquiv
    (i : Index) (actual : Tape Bool)
    (hequiv : Tape.Equiv actual i.source) :
    scanTape2PayloadDescription.HaltsFromTapeEquiv
      actual (tape2PayloadScanEnd i) := by
  exact MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tape.Equiv.symm hequiv)
    (scanTape2PayloadDescription_haltsFromTape i)

/-- Concrete seeker followed by the ordinary sequential handoff into an exact
identity subroutine. -/
def seekTape2PayloadDescription : MachineDescription :=
  seqSubroutine seekTape2Description ExactIdentityDescription Direction.right

theorem seekTape2PayloadDescription_subroutineReady :
    seekTape2PayloadDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    seekTape2Description_subroutineReady
    CommonGround.Identity.exactIdentityDescription_subroutineReady

theorem seekTape2PayloadDescription_haltsFromTape (i : Index) :
    seekTape2PayloadDescription.HaltsFromTape
      i.source (tape2PayloadHead i) := by
  unfold seekTape2PayloadDescription tape2PayloadHead
  exact CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
    seekTape2Description_subroutineReady
    CommonGround.Identity.exactIdentityDescription_subroutineReady
    (seekTape2Description_haltsFrom_separator i)
    rfl
    (CommonGround.Identity.exactIdentityDescription_haltsFromTape
      (Tape.move Direction.right (tape2Separator i)))

theorem seekTape2PayloadDescription_haltsFromTapeEquiv
    (i : Index) (actual : Tape Bool)
    (hequiv : Tape.Equiv actual i.source) :
    seekTape2PayloadDescription.HaltsFromTapeEquiv
      actual (tape2PayloadHead i) := by
  exact MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tape.Equiv.symm hequiv)
    (seekTape2PayloadDescription_haltsFromTape i)

/-!
## Narrow remaining machine leaf
-/

/-- Machine-level parser/assembler after the clean raw-segment ingress.  The
implementation must retain exact pair alignment and head-marker position,
decode tape-2 metadata and witness fields, and normalize all outer padding to
the exact target. -/
def RawGuardedParserAssemblerConstruction : Prop := Construction

theorem construction_of_rawGuardedParserAssembler
    (hparser : RawGuardedParserAssemblerConstruction) : Construction :=
  hparser

end FiniteRealization
end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
