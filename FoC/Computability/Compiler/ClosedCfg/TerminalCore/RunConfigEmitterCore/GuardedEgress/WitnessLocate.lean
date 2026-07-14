import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.TapeSerializer

set_option doc.verso true

/-!
# Locate the guarded metadata/witness tape

The corrected tape-field serializer halts on the blank reservoir immediately
to the right of the emitted tape field.  Its preserved suffix consists of the
nonempty encoded consumed-stage tape, one physical separator, and the encoded
metadata/witness tape.  This finite phase erases that exhausted first segment
and halts on the first cell of the metadata/witness tape.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessBridgeLocate

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open GuardedEgress.RawPairQuoter

/-- Scan the serializer's blank reservoir, cross the first encoded logical
tape, and step across its closing separator. -/
def description : MachineDescription where
  stateCount := 3
  start := 1
  halt := 0
  transitions :=
    [ transition 1 none none Direction.right 1
    , transition 1 (some false) none Direction.right 2
    , transition 1 (some true) none Direction.right 2
    , transition 2 (some false) none Direction.right 2
    , transition 2 (some true) none Direction.right 2
    , transition 2 none none Direction.right 0 ]

theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def sourceTape (left : List (Option Bool)) (gap : Nat)
    (firstSegment : List Bool) (suffix : List (Option Bool)) : Tape Bool :=
  tapeAtCells left
    (List.append (List.replicate gap (none : Option Bool))
      (List.append (firstSegment.map some) (none :: suffix)))

def targetTape (left : List (Option Bool)) (gap : Nat)
    (firstSegment : List Bool) (suffix : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (firstSegment.length + gap + 1)
        (none : Option Bool)) left)
    suffix

private theorem run_blank_prefix (n : Nat)
    (left right : List (Option Bool)) :
    description.runConfig n
        { state := description.start
          tape := tapeAtCells left
            (List.append (List.replicate n (none : Option Bool)) right) } =
      { state := description.start
        tape := tapeAtCells
          (List.append (List.replicate n (none : Option Bool)) left)
          right } := by
  induction n generalizing left with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n + 1 = 1 + n by lia]
      rw [runConfig_add]
      rw [show List.replicate (1 + n) (none : Option Bool) =
          none :: List.replicate n none by
        rw [show 1 + n = Nat.succ n by lia]
        rfl]
      have hstep :
          description.runConfig 1
              { state := description.start
                tape := tapeAtCells left
                  (none ::
                    List.append (List.replicate n none) right) } =
            { state := description.start
              tape := tapeAtCells (none :: left)
                (List.append (List.replicate n none) right) } := by
        cases hrest : List.append (List.replicate n
            (none : Option Bool)) right <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
      change description.runConfig n
          (description.runConfig 1
            { state := description.start
              tape := tapeAtCells left
                (none ::
                  List.append (List.replicate n none) right) }) = _
      rw [hstep]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rfl

private theorem run_present_prefix (bits : List Bool)
    (left suffix : List (Option Bool)) :
    description.runConfig bits.length
        { state := 2
          tape := tapeAtCells left
            (List.append (bits.map some) (none :: suffix)) } =
      { state := 2
        tape := tapeAtCells
          (List.append
            (List.replicate bits.length (none : Option Bool)) left)
          (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 2
                tape := tapeAtCells left
                  (some bit ::
                    List.append (rest.map some) (none :: suffix)) } =
            { state := 2
              tape := tapeAtCells (none :: left)
                (List.append (rest.map some) (none :: suffix)) } := by
        cases bit <;>
          cases hrest : List.append (rest.map some) (none :: suffix) <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
      change description.runConfig rest.length
          (description.runConfig 1
            { state := 2
              tape := tapeAtCells left
                (some bit ::
                  List.append (rest.map some) (none :: suffix)) }) = _
      rw [hstep]
      rw [ih (none :: left)]
      rw [show List.append
          (List.replicate rest.length (none : Option Bool))
          (none :: left) =
        List.append (List.replicate (1 + rest.length) none) left by
          rw [show 1 + rest.length = rest.length + 1 by lia]
          rw [List.replicate_succ]
          exact replicate_none_append_none_cons rest.length left]

private theorem run_cross_separator
    (left suffix : List (Option Bool)) :
    description.runConfig 1
        { state := 2
          tape := tapeAtCells left (none :: suffix) } =
      { state := description.halt
        tape := tapeAtCells (none :: left) suffix } := by
  cases suffix <;>
    simp [description, runConfig, stepConfig, lookupTransition,
      Matches, transition, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem description_haltsFromTape
    (left : List (Option Bool)) (gap : Nat)
    (firstSegment : List Bool) (suffix : List (Option Bool))
    (hsegment : firstSegment ≠ []) :
    description.HaltsFromTape
      (sourceTape left gap firstSegment suffix)
      (targetTape left gap firstSegment suffix) := by
  cases hbits : firstSegment with
  | nil =>
      exact False.elim (hsegment hbits)
  | cons first rest =>
      have hblank := run_blank_prefix gap left
        (List.append ((first :: rest).map some) (none :: suffix))
      have hfirst :
          description.runConfig 1
              { state := description.start
                tape := tapeAtCells
                  (List.append (List.replicate gap none) left)
                  (some first ::
                    List.append (rest.map some) (none :: suffix)) } =
            { state := 2
              tape := tapeAtCells
                (none ::
                  List.append (List.replicate gap none) left)
                (List.append (rest.map some) (none :: suffix)) } := by
        cases first <;>
          cases hrest : List.append (rest.map some) (none :: suffix) <;>
          simp [description, runConfig, stepConfig, lookupTransition,
            Matches, transition, tapeAtCells, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
      have hrest := run_present_prefix rest
        (none ::
          List.append (List.replicate gap none) left) suffix
      have hseparator := run_cross_separator
        (List.append (List.replicate rest.length none)
          (none ::
            List.append (List.replicate gap none) left)) suffix
      refine ⟨gap + 1 + rest.length + 1, ?_⟩
      constructor
      .
        rw [show gap + 1 + rest.length + 1 =
            gap + (1 + rest.length + 1) by lia]
        rw [runConfig_add]
        unfold sourceTape
        rw [hblank]
        rw [show 1 + rest.length + 1 = 1 + (rest.length + 1) by lia]
        rw [runConfig_add]
        rw [show List.map some (first :: rest) =
          some first :: rest.map some by rfl]
        rw [show List.append
            (some first :: rest.map some) (none :: suffix) =
          some first :: List.append (rest.map some) (none :: suffix) by
            rfl]
        rw [hfirst]
        rw [show rest.length + 1 = rest.length + 1 by rfl]
        rw [runConfig_add]
        rw [hrest]
        rw [hseparator]
      .
        rw [show gap + 1 + rest.length + 1 =
            gap + (1 + rest.length + 1) by lia]
        rw [runConfig_add]
        unfold sourceTape
        rw [hblank]
        rw [show 1 + rest.length + 1 = 1 + (rest.length + 1) by lia]
        rw [runConfig_add]
        rw [show List.map some (first :: rest) =
          some first :: rest.map some by rfl]
        rw [show List.append
            (some first :: rest.map some) (none :: suffix) =
          some first :: List.append (rest.map some) (none :: suffix) by
            rfl]
        rw [hfirst]
        rw [show rest.length + 1 = rest.length + 1 by rfl]
        rw [runConfig_add]
        rw [hrest]
        rw [hseparator]
        unfold targetTape
        change tapeAtCells
            (none ::
              List.append (List.replicate rest.length none)
                (none ::
                  List.append (List.replicate gap none) left)) suffix =
          tapeAtCells
            (List.append
              (List.replicate (rest.length + 1 + gap + 1) none) left)
            suffix
        have hleft :
            none ::
                List.append (List.replicate rest.length none)
                  (none ::
                    List.append (List.replicate gap none) left) =
              List.append
                (List.replicate
                  ((rest.length + 1) + (gap + 1)) none) left := by
          calc
            none ::
                List.append (List.replicate rest.length none)
                  (none ::
                    List.append (List.replicate gap none) left) =
              List.append (List.replicate (rest.length + 1) none)
                (List.append (List.replicate (gap + 1) none) left) := by
                  rw [List.replicate_succ, List.replicate_succ]
                  rfl
            _ = List.append
                (List.replicate
                  ((rest.length + 1) + (gap + 1)) none) left :=
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool) (rest.length + 1) (gap + 1) left).symm
        rw [hleft]
        congr 3

/-!
## Corrected serializer specialization
-/

/-- Left stack of the corrected serializer endpoint, normalized to the exact
tape-field currency. -/
def serializerLeft (i : Index) : List (Option Bool) :=
  none :: none ::
    (LengthAssembly.exactTapeFieldBits i.finalTape []).reverse.map some

/-- Blank suffix retained after right-field serialization. -/
def rightResidual (i : Index) : Nat :=
  (RawPairDecoder.decoderGap i + 1 + (RawPairQuoter.rawBits i).length) -
    (4 * (guardLogicalTape i.finalTape).right.length + 3)

/-- Exact number of blanks between the serialized tape field and the first
preserved logical-tape segment. -/
def serializerGap (i : Index) : Nat :=
  TapeFieldSerializer.correctedHeadScratch i.finalTape + 11 + rightResidual i

/-- Physical suffix beginning at the first bit of the metadata/witness tape. -/
def tape2Suffix (i : Index) : List (Option Bool) :=
  List.append (logicalTapeCode (guardLogicalTape i.doneWitnessTape))
    tapeSeparatorCells

/-- Exact endpoint of the locator, with the erased logical-tape-1 footprint
retained as blank left workspace. -/
def locatedTape (i : Index) : Tape Bool :=
  targetTape (serializerLeft i) (serializerGap i)
    (logicalTapeBits (guardLogicalTape i.consumedStageTape))
    (tape2Suffix i)

private theorem serializerPadding_eq (i : Index) :
    sentinelGapCompactorFinalPadding
        (TapeFieldSerializer.correctedHeadScratch i.finalTape) 2
        (none :: TapeFieldSerializer.correctedRightPaddingTail i) =
      List.append
        (List.replicate (serializerGap i) (none : Option Bool))
        (RawPairQuoter.suffixCells i) := by
  rw [sentinelGapCompactorFinalPadding_eq_replicate_append
    (TapeFieldSerializer.correctedHeadScratch i.finalTape) 1]
  unfold TapeFieldSerializer.correctedRightPaddingTail
  unfold RightLengthCopy.rightAssemblyPaddingTail
  change
    List.append
        (List.replicate
          (2 + TapeFieldSerializer.correctedHeadScratch i.finalTape) none)
        (none ::
          List.append (List.replicate 8 none)
            (List.append (List.replicate (rightResidual i) none)
              (RawPairQuoter.suffixCells i))) = _
  calc
    List.append
        (List.replicate
          (2 + TapeFieldSerializer.correctedHeadScratch i.finalTape) none)
        (none ::
          List.append (List.replicate 8 none)
            (List.append (List.replicate (rightResidual i) none)
              (RawPairQuoter.suffixCells i))) =
      List.append
        (List.replicate
          (2 + TapeFieldSerializer.correctedHeadScratch i.finalTape + 1)
          none)
        (List.append (List.replicate 8 none)
          (List.append (List.replicate (rightResidual i) none)
            (RawPairQuoter.suffixCells i))) := by
        exact FoC.Computability.list_replicate_append_self
          (none : Option Bool)
          (2 + TapeFieldSerializer.correctedHeadScratch i.finalTape)
          (List.append (List.replicate 8 none)
            (List.append (List.replicate (rightResidual i) none)
              (RawPairQuoter.suffixCells i)))
    _ = List.append
        (List.replicate
          ((2 + TapeFieldSerializer.correctedHeadScratch i.finalTape + 1) + 8)
          none)
        (List.append (List.replicate (rightResidual i) none)
          (RawPairQuoter.suffixCells i)) := by
        exact (FoC.Computability.list_replicate_add_append
          (none : Option Bool)
          (2 + TapeFieldSerializer.correctedHeadScratch i.finalTape + 1) 8
          (List.append (List.replicate (rightResidual i) none)
            (RawPairQuoter.suffixCells i))).symm
    _ = List.append
        (List.replicate
          (((2 + TapeFieldSerializer.correctedHeadScratch i.finalTape + 1) + 8) +
            rightResidual i) none)
        (RawPairQuoter.suffixCells i) := by
        exact (FoC.Computability.list_replicate_add_append
          (none : Option Bool)
          ((2 + TapeFieldSerializer.correctedHeadScratch i.finalTape + 1) + 8)
          (rightResidual i) (RawPairQuoter.suffixCells i)).symm
    _ = List.append
        (List.replicate (serializerGap i) none)
        (RawPairQuoter.suffixCells i) := by
        congr 2
        unfold serializerGap
        lia

private theorem serializerLeft_eq (i : Index) :
    none :: none ::
        List.append
          ((RightLengthCopy.compactedPayloadBits
            (i.finalTape.right.map logicalCellPair)).reverse.map some)
          ((TapeFieldSerializer.leftHeadFieldBits i.finalTape).reverse.map
            some) =
      serializerLeft i := by
  unfold serializerLeft
  have hfields :=
    TapeFieldSerializer.leftHead_compactedRight_eq_exactTapeFieldBits
      i.finalTape
  have hreverse := congrArg (fun w : Word Bool => w.reverse) hfields
  have hmapped := congrArg (fun w : Word Bool => w.map some) hreverse
  simpa [List.reverse_append, List.map_append] using hmapped

theorem correctedSerializedTapeFieldTarget_eq_sourceTape (i : Index) :
    TapeFieldSerializer.correctedSerializedTapeFieldTarget i =
      sourceTape (serializerLeft i) (serializerGap i)
        (logicalTapeBits (guardLogicalTape i.consumedStageTape))
        (tape2Suffix i) := by
  unfold TapeFieldSerializer.correctedSerializedTapeFieldTarget
  unfold leadingBlankLeftShiftTargetTapeWithPadding
  unfold sourceTape
  rw [serializerPadding_eq]
  rw [serializerLeft_eq]
  unfold RawPairQuoter.suffixCells tape2Suffix
  rw [logicalTapeCode_eq_map_some]
  simp [tapeSeparatorCells]

theorem consumedStageBits_ne_nil (i : Index) :
    logicalTapeBits (guardLogicalTape i.consumedStageTape) ≠ [] := by
  rcases logicalTapeBits_exists_cons
      (guardLogicalTape i.consumedStageTape) with ⟨bit, rest, hbits⟩
  rw [hbits]
  simp

theorem description_haltsFrom_serializerTarget (i : Index) :
    description.HaltsFromTape
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)
      (locatedTape i) := by
  rw [correctedSerializedTapeFieldTarget_eq_sourceTape]
  exact description_haltsFromTape
    (serializerLeft i) (serializerGap i)
    (logicalTapeBits (guardLogicalTape i.consumedStageTape))
    (tape2Suffix i) (consumedStageBits_ne_nil i)

theorem description_haltsFromTapeEquiv
    (i : Index) (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    description.HaltsFromTapeEquiv actual (locatedTape i) := by
  exact MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tape.Equiv.symm hactual)
    (description_haltsFrom_serializerTarget i)

end GuardedEgress.MetadataWitnessBridgeLocate
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
