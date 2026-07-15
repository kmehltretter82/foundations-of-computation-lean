import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.AcceptBranch

set_option doc.verso true

/-!
Accepting-route completion and internal-marker phases.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace AcceptFinish

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch

theorem replicate_none_append_cons
    (n : Nat) (left : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool)) (none :: left) =
      List.append (List.replicate (n + 1) (none : Option Bool)) left := by
  exact list_replicate_append_self (none : Option Bool) n left

theorem replicate_none_append_replicate (n m : Nat) :
    List.append
        (List.replicate n (none : Option Bool))
        (List.replicate m (none : Option Bool)) =
      List.replicate (n + m) (none : Option Bool) := by
  exact
    FoC.Computability.CommonGround.FiniteTransducers.replicate_none_append_replicate_none
      n m
theorem replicate_none_append_none_marked (n m : Nat) :
    List.append
        (List.replicate n (none : Option Bool))
        (none :: List.append (List.replicate m none) [some true]) =
      List.append (List.replicate (n + 1 + m) none) [some true] := by
  rw [show none :: List.append (List.replicate m none) [some true] =
      List.append (List.replicate (m + 1) none) [some true] by
        rw [List.replicate_succ]
        rfl]
  calc
    List.append (List.replicate n none)
        (List.append (List.replicate (m + 1) none) [some true]) =
      List.append
        (List.append (List.replicate n none)
          (List.replicate (m + 1) none)) [some true] :=
            (List.append_assoc _ _ _).symm
    _ = List.append (List.replicate (n + (m + 1)) none) [some true] := by
      rw [replicate_none_append_replicate]
    _ = List.append (List.replicate (n + 1 + m) none) [some true] := by
      congr 2
      lia

theorem reverse_map_some_append (a b : List Bool) :
    (List.append a b).reverse.map some =
      List.append (b.reverse.map some) (a.reverse.map some) := by
  calc
    _ = (List.append b.reverse a.reverse).map some :=
      congrArg (List.map some) (List.reverse_append)
    _ = _ := List.map_append

theorem append_seven_regroup {alpha : Type}
    (a b c d e f g : List alpha) :
    List.append
        (List.append
          (List.append
            (List.append (List.append a (List.append b c)) d) e) f) g =
      List.append a
        (List.append b
          (List.append (List.append c d)
            (List.append (List.append e f) g))) := by
  calc
    _ = List.append
        (List.append
          (List.append (List.append a (List.append b c)) d) e)
        (List.append f g) := List.append_assoc _ _ _
    _ = List.append
        (List.append (List.append a (List.append b c)) d)
        (List.append e (List.append f g)) := List.append_assoc _ _ _
    _ = List.append (List.append a (List.append b c))
        (List.append d (List.append e (List.append f g))) :=
      List.append_assoc _ _ _
    _ = List.append a
        (List.append (List.append b c)
          (List.append d (List.append e (List.append f g)))) :=
      List.append_assoc _ _ _
    _ = List.append a
        (List.append b
          (List.append c
            (List.append d (List.append e (List.append f g))))) :=
      congrArg (List.append a) (List.append_assoc _ _ _)
    _ = _ := by
      apply congrArg (List.append a)
      apply congrArg (List.append b)
      calc
        _ = List.append (List.append c d)
            (List.append e (List.append f g)) :=
          (List.append_assoc _ _ _).symm
        _ = _ := congrArg (List.append (List.append c d))
          (List.append_assoc _ _ _).symm
theorem eraseRight_one
    (bit : Bool) (bits : List Bool) (left : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.write none
          (tapeAtCells left
            (List.append ((bit :: bits).map some) [none]))) =
      tapeAtCells (none :: left)
        (List.append (bits.map some) [none]) := by
  cases bits <;> rfl

theorem eraseRight_tapeAtCells
    (n : Nat) (bits : List Bool) (left : List (Option Bool)) :
    Components.eraseRight n
        (tapeAtCells left (List.append (bits.map some) [none])) =
      tapeAtCells
        (List.append (List.replicate n (none : Option Bool)) left)
        (List.append ((bits.drop n).map some) [none]) := by
  induction n generalizing bits left with
  | zero => rfl
  | succ n ih =>
      cases bits with
      | nil =>
          simp only [List.map, List.nil_append, List.drop]
          rw [Components.eraseRight]
          change Components.eraseRight n
              (tapeAtCells (none :: left) [none]) = _
          calc
            Components.eraseRight n
                (tapeAtCells (none :: left) [none]) =
              tapeAtCells
                (List.append (List.replicate n (none : Option Bool))
                  (none :: left)) [none] := by
                    simpa using ih ([] : List Bool) (none :: left)
            _ = tapeAtCells
                (List.append (List.replicate (n + 1) (none : Option Bool))
                  left) [none] := by
                    rw [replicate_none_append_cons]
      | cons bit bits =>
          simp only [List.drop_succ_cons]
          rw [Components.eraseRight]
          rw [eraseRight_one]
          calc
            Components.eraseRight n
                (tapeAtCells (none :: left)
                  (List.append (bits.map some) [none])) =
              tapeAtCells
                (List.append (List.replicate n (none : Option Bool))
                  (none :: left))
                (List.append ((bits.drop n).map some) [none]) :=
                  ih bits (none :: left)
            _ = tapeAtCells
                (List.append (List.replicate (n + 1) (none : Option Bool))
                  left)
                (List.append ((bits.drop n).map some) [none]) := by
                    rw [replicate_none_append_cons]

def gapOldTailBits (L : DovetailLayout) : List Bool :=
  (stageCounterBits L).drop
    (directScratchBlankDriverBits true L).length
theorem remainingBits_add_four_eq_direct_length (L : DovetailLayout) :
    (remainingBits L).length + 4 =
      (directScratchBlankDriverBits true L).length := by
  have hle := acceptCounterBits_length_le_dataBits L
  rw [remainingBits, List.length_drop]
  rw [dataBits_accept_decomp]
  simp [inputStageBits, acceptBits, rejectBits, acceptHitBits,
    rejectHitBits, acceptCounterBits, directScratchBlankDriverBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    boolFieldBits_nil_length] at hle ⊢
  lia

theorem counterBaseTail_eq_marked_replicate (L : DovetailLayout) :
    counterBaseTail L =
      List.append
        (List.replicate ((ParsedLayoutBits L).length - 1)
          (none : Option Bool))
        [some true] := by
  have hpos : 0 < (ParsedLayoutBits L).length := by
    rw [parsedLayoutBits_fieldDecomp]
    simp [transitionPrefixBits_length]
    lia
  cases hlen : (ParsedLayoutBits L).length with
  | zero => simp [hlen] at hpos
  | succ n =>
      simp only [counterBaseTail, counterBaseLeft, hlen,
        List.replicate_succ]
      simp

theorem writeWordRight_append
    (u v : List Bool) (T : Tape Bool) :
    writeWordRight v (writeWordRight u T) =
      writeWordRight (List.append u v) T := by
  induction u generalizing T with
  | nil => rfl
  | cons bit u ih =>
      rw [writeWordRight]
      rw [ih]
      rfl
theorem stagePrefix_append_remaining_eq_liveBits (L : DovetailLayout) :
    List.append
        (StagePrefixForward.bits (L.stage = 0))
        (remainingLiveBits L) =
      liveBits L := by
  cases hstage : L.stage with
  | zero =>
      simp [StagePrefixForward.bits, remainingLiveBits, liveBits,
        configHitBits, acceptBits, rejectBits, acceptHitBits, rejectHitBits,
        hstage,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits]
  | succ stage =>
      simp [StagePrefixForward.bits, remainingLiveBits, liveBits,
        configHitBits, acceptBits, rejectBits, acceptHitBits, rejectHitBits,
        hstage,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        List.append_assoc]

theorem gapOldTailBits_length_lt_liveBits (L : DovetailLayout) :
    (gapOldTailBits L).length < (liveBits L).length := by
  have haccept := configurationFieldBits_length_pos L.acceptConfig
  have hdrop :
      (gapOldTailBits L).length <= (stageCounterBits L).length := by
    rw [gapOldTailBits, List.length_drop]
    exact Nat.sub_le _ _
  simp [gapOldTailBits, stageCounterBits, acceptCounterBits, liveBits,
    acceptBits, rejectBits, acceptHitBits, rejectHitBits,
    boolFieldBits_nil_length] at hdrop ⊢
  lia

def keptLiveBits (L : DovetailLayout) : List Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)
    (List.append (acceptBits L)
      (List.append (rejectBits L) (acceptHitBits L)))
theorem liveBits_eq_kept_append_rejectHit (L : DovetailLayout) :
    liveBits L = List.append (keptLiveBits L) (rejectHitBits L) := by
  simp [liveBits, keptLiveBits, List.append_assoc]

def moveLeftFour (T : Tape Bool) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.left
      (Tape.move Direction.left (Tape.move Direction.left T)))

namespace MoveLeftFour

def s0 : Nat := 0
def s1 : Nat := 1
def s2 : Nat := 2
def s3 : Nat := 3
def halt : Nat := 4
def rowsForRead (source target : Nat) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads3 fun read0 read1 read2 =>
    row source read0 read1 read2 keepS keepS keepL target

def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  [ rowsForRead s0 s1, rowsForRead s1 s2,
    rowsForRead s2 s3, rowsForRead s3 halt ].flatten

def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 5 s0 halt rows

syntax "move_left_four_cases" ident ident ident : tactic

macro_rules
  | `(tactic| move_left_four_cases $T0:ident $T1:ident $T2:ident) =>
      `(tactic|
        cases h0 : ($T0:ident).head with
        | none =>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, halt, allReads3, allReads2,
                    allReadCells, List.find?, h0, h1, h2]
                | some b => cases b <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, halt, allReads3, allReads2,
                      allReadCells, List.find?, h0, h1, h2]
            | some b1 => cases b1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, halt, allReads3, allReads2,
                    allReadCells, List.find?, h0, h1, h2]
                | some b2 => cases b2 <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, halt, allReads3, allReads2,
                      allReadCells, List.find?, h0, h1, h2]
        | some b0 => cases b0 <;>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, halt, allReads3, allReads2,
                    allReadCells, List.find?, h0, h1, h2]
                | some b => cases b <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, halt, allReads3, allReads2,
                      allReadCells, List.find?, h0, h1, h2]
            | some b1 => cases b1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, halt, allReads3, allReads2,
                    allReadCells, List.find?, h0, h1, h2]
                | some b2 => cases b2 <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, halt, allReads3, allReads2,
                      allReadCells, List.find?, h0, h1, h2])
theorem step0 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config s0 T0 T1 T2) =
      config s1 T0 T1 (keepL.apply T2) := by
  move_left_four_cases T0 T1 T2

theorem step1 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config s1 T0 T1 T2) =
      config s2 T0 T1 (keepL.apply T2) := by
  move_left_four_cases T0 T1 T2

theorem step2 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config s2 T0 T1 T2) =
      config s3 T0 T1 (keepL.apply T2) := by
  move_left_four_cases T0 T1 T2
theorem step3 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config s3 T0 T1 T2) =
      config halt T0 T1 (keepL.apply T2) := by
  move_left_four_cases T0 T1 T2

theorem run (T0 T1 T2 : Tape Bool) :
    description.runConfig 4 (config s0 T0 T1 T2) =
      config halt T0 T1 (moveLeftFour T2) := by
  rw [show 4 = 1 + (1 + (1 + 1)) by rfl]
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [step0]
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [step1]
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [step2, step3]
  rfl

end MoveLeftFour

namespace MoveRightOne

def start : Nat := 0
def halt : Nat := 1
def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads3 fun read0 read1 read2 =>
    row start read0 read1 read2 keepS keepS keepR halt

def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 2 start halt rows

theorem run (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config start T0 T1 T2) =
      config halt T0 T1 (keepR.apply T2) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          cases h2 : T2.head with
          | none => three_tape_step [description, rows, start, halt,
              allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
          | some b => cases b <;>
              three_tape_step [description, rows, start, halt,
                allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
      | some b1 => cases b1 <;>
          cases h2 : T2.head with
          | none => three_tape_step [description, rows, start, halt,
              allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
          | some b2 => cases b2 <;>
              three_tape_step [description, rows, start, halt,
                allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
  | some b0 => cases b0 <;>
      cases h1 : T1.head with
      | none =>
          cases h2 : T2.head with
          | none => three_tape_step [description, rows, start, halt,
              allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
          | some b => cases b <;>
              three_tape_step [description, rows, start, halt,
                allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
      | some b1 => cases b1 <;>
          cases h2 : T2.head with
          | none => three_tape_step [description, rows, start, halt,
              allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]
          | some b2 => cases b2 <;>
              three_tape_step [description, rows, start, halt,
                allReads3, allReads2, allReadCells, List.find?, h0, h1, h2]

end MoveRightOne
def moveLeftFourDescription : MachineDescription :=
  lowerStructured3Description MoveLeftFour.description

def moveRightOneDescription : MachineDescription :=
  lowerStructured3Description MoveRightOne.description

theorem moveLeftFour_ready : MoveLeftFour.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool MoveLeftFour.description
    (by decide)
theorem moveLeftFour_supports : SupportsReadWriteRows3 MoveLeftFour.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem moveRightOne_ready : MoveRightOne.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool MoveRightOne.description
    (by decide)

theorem moveRightOne_supports : SupportsReadWriteRows3 MoveRightOne.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem moveLeftFourDescription_ready :
    moveLeftFourDescription.SubroutineReady := by
  simpa [moveLeftFourDescription] using
    lowerStructured3Description_subroutineReady moveLeftFour_ready.left
      moveLeftFour_supports

theorem moveRightOneDescription_ready :
    moveRightOneDescription.SubroutineReady := by
  simpa [moveRightOneDescription] using
    lowerStructured3Description_subroutineReady moveRightOne_ready.left
      moveRightOne_supports

theorem moveLeftFourDescription_realizes (T0 T2 : Tape Bool) :
    moveLeftFourDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank (moveLeftFour T2)) := by
  simpa [moveLeftFourDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      moveLeftFour_ready.left moveLeftFour_ready.right moveLeftFour_supports
      (c := config MoveLeftFour.s0 T0 Tape.blank T2)
      (tapes := [T0, Tape.blank, moveLeftFour T2])
      rfl rfl ⟨4, MoveLeftFour.run T0 Tape.blank T2⟩
theorem moveRightOneDescription_realizes (T0 T2 : Tape Bool) :
    moveRightOneDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank (keepR.apply T2)) := by
  simpa [moveRightOneDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      moveRightOne_ready.left moveRightOne_ready.right moveRightOne_supports
      (c := config MoveRightOne.start T0 Tape.blank T2)
      (tapes := [T0, Tape.blank, keepR.apply T2])
      rfl rfl ⟨1, MoveRightOne.run T0 Tape.blank T2⟩

def moveEraseDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveLeftFourDescription
    AcceptBranch.eraseFourDescription

def cleanupDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveEraseDescription
    moveRightOneDescription
theorem moveEraseDescription_ready : moveEraseDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    moveLeftFourDescription_ready
    AcceptBranch.eraseFourDescription_ready

theorem cleanupDescription_ready : cleanupDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    moveEraseDescription_ready moveRightOneDescription_ready

theorem cleanupDescription_realizes (T0 T2 : Tape Bool) :
    cleanupDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (keepR.apply
          (Components.eraseRight 4 (moveLeftFour T2)))) := by
  have hl := moveLeftFourDescription_realizes T0 T2
  have he := AcceptBranch.eraseFourDescription_realizes
    T0 (moveLeftFour T2)
  have hle := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    moveLeftFourDescription_ready
    AcceptBranch.eraseFourDescription_ready hl he
  have hr := moveRightOneDescription_realizes T0
    (Components.eraseRight 4 (moveLeftFour T2))
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    moveEraseDescription_ready moveRightOneDescription_ready hle hr
  simpa [cleanupDescription, moveEraseDescription] using h
theorem afterLiveCopyTape0_eq_atBoundaryTape0 (L : DovetailLayout) :
    afterLiveCopyTape0 L = atBoundaryTape0 L := by
  rw [atBoundaryTape0_eq_rewindSource]
  unfold afterLiveCopyTape0 afterFirstStageLeft postPrefixLeft
  have hraw := rawBoundaryRest_eq_false_false_drop L
  cases hstage : L.stage with
  | zero =>
      simp [remainingLiveBits, hstage, configHitBits,
        wrappedBits_parsedLayoutBits,
        Components.wrappedNatTokens,
        List.reverse_append, List.map_append, List.append_assoc]
      apply congrArg (scanTape _)
      exact hraw.symm
  | succ stage =>
      have hsplit :
          AcceptConfigCopy.wrappedBits
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                (configHitBits L)) =
            List.append (Components.wrappedNatTokens stage)
              (AcceptConfigCopy.wrappedBits (configHitBits L)) := by
        rw [wrappedBits_append, wrappedBits_stageNatBits]
      let base : List (Option Bool) :=
        List.append
          (List.append ((wrappedKind .tick).reverse.map some)
            ((Components.wrappedCellTokens L.input).reverse.map some))
          (List.append
            (List.append
              ((Components.wrappedNatTokens L.input.length).reverse.map some)
              ((wrappedKind .transition).reverse.map some))
            (none :: primaryMarkerBaseLeft L))
      have hleft :
          List.append
              ((AcceptConfigCopy.wrappedBits
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage)
                  (configHitBits L))).reverse.map some)
              base =
            List.append
              ((AcceptConfigCopy.wrappedBits (configHitBits L)).reverse.map some)
              (List.append
                ((Components.wrappedNatTokens stage).reverse.map some) base) := by
        have hrev :
            (AcceptConfigCopy.wrappedBits
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage)
                  (configHitBits L))).reverse.map some =
              List.append
                ((AcceptConfigCopy.wrappedBits (configHitBits L)).reverse.map some)
                ((Components.wrappedNatTokens stage).reverse.map some) := by
          calc
            _ = (List.append (Components.wrappedNatTokens stage)
                  (AcceptConfigCopy.wrappedBits (configHitBits L))).reverse.map some :=
                congrArg
                  (fun xs => (xs.reverse.map some : List (Option Bool))) hsplit
            _ = _ := reverse_map_some_append
              (Components.wrappedNatTokens stage)
              (AcceptConfigCopy.wrappedBits (configHitBits L))
        rw [hrev]
        exact List.append_assoc _ _ _
      simp only [remainingLiveBits, hstage, List.reverse_append,
        List.map_append, List.append_assoc, reverse_map_some_append]
      rw [hleft]
      rw [wrappedBits_parsedLayoutBits, hstage]
      have hnat :
          Components.wrappedNatTokens (stage + 1) =
            List.append (wrappedKind .tick)
              (Components.wrappedNatTokens stage) := by
        rfl
      rw [hnat]
      simp only [List.reverse_append,
        List.map_append, List.append_assoc, reverse_map_some_append]
      rw [append_seven_regroup]
      apply congrArg (scanTape _)
      exact hraw.symm

end AcceptFinish
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC


namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace AcceptInternalMarker

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch AcceptFinish

namespace FirstCellMarker

def start : Nat := 0
def halt : Nat := 1

def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads2 fun read1 read2 =>
    row start (some false) read1 read2 (writeS none) keepS keepS halt
def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 2 start halt rows

theorem run
    (bit : Bool) (left rest : List (Option Bool))
    (T1 T2 : Tape Bool) :
    description.runConfig 1
        (config start
          (MarkedErase.scanOptionTape left
            (List.append (MarkedErase.wrappedOptions bit) rest))
          T1 T2) =
      config halt
        (MarkedErase.scanOptionTape left
          (List.append (MarkedErase.markedOptions bit) rest))
        T1 T2 := by
  cases bit <;> cases rest <;>
    cases h1 : T1.head with
    | none =>
        cases h2 : T2.head with
        | none =>
            three_tape_step [description, rows, start, halt,
              allReads2, allReadCells, List.find?,
              MarkedErase.scanOptionTape, MarkedErase.wrappedOptions,
              MarkedErase.markedOptions, wrappedRawBit,
              cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, encodeCell, tapeAtCells, h1, h2]
        | some b => cases b <;>
            three_tape_step [description, rows, start, halt,
              allReads2, allReadCells, List.find?,
              MarkedErase.scanOptionTape, MarkedErase.wrappedOptions,
              MarkedErase.markedOptions, wrappedRawBit,
              cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, encodeCell, tapeAtCells, h1, h2]
    | some b1 => cases b1 <;>
        cases h2 : T2.head with
        | none =>
            three_tape_step [description, rows, start, halt,
              allReads2, allReadCells, List.find?,
              MarkedErase.scanOptionTape, MarkedErase.wrappedOptions,
              MarkedErase.markedOptions, wrappedRawBit,
              cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, encodeCell, tapeAtCells, h1, h2]
        | some b2 => cases b2 <;>
            three_tape_step [description, rows, start, halt,
              allReads2, allReadCells, List.find?,
              MarkedErase.scanOptionTape, MarkedErase.wrappedOptions,
              MarkedErase.markedOptions, wrappedRawBit,
              cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, encodeCell, tapeAtCells, h1, h2]

end FirstCellMarker

def firstCellMarkerDescription : MachineDescription :=
  lowerStructured3Description FirstCellMarker.description
def markedEraseDescription : MachineDescription :=
  lowerStructured3Description MarkedErase.description

theorem firstCellMarker_ready : FirstCellMarker.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    FirstCellMarker.description (by decide)

theorem firstCellMarker_supports :
    SupportsReadWriteRows3 FirstCellMarker.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem markedErase_ready : MarkedErase.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    MarkedErase.description (by decide)

theorem markedErase_supports : SupportsReadWriteRows3 MarkedErase.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem firstCellMarkerDescription_ready :
    firstCellMarkerDescription.SubroutineReady := by
  simpa [firstCellMarkerDescription] using
    lowerStructured3Description_subroutineReady
      firstCellMarker_ready.left firstCellMarker_supports
theorem markedEraseDescription_ready :
    markedEraseDescription.SubroutineReady := by
  simpa [markedEraseDescription] using
    lowerStructured3Description_subroutineReady
      markedErase_ready.left markedErase_supports

theorem firstCellMarkerDescription_realizes
    (bit : Bool) (left rest : List (Option Bool))
    (T2 : Tape Bool) :
    firstCellMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (MarkedErase.scanOptionTape left
          (List.append (MarkedErase.wrappedOptions bit) rest))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (MarkedErase.scanOptionTape left
          (List.append (MarkedErase.markedOptions bit) rest))
        Tape.blank T2) := by
  simpa [firstCellMarkerDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      firstCellMarker_ready.left firstCellMarker_ready.right
      firstCellMarker_supports
      (c := config FirstCellMarker.start
        (MarkedErase.scanOptionTape left
          (List.append (MarkedErase.wrappedOptions bit) rest))
        Tape.blank T2)
      (tapes :=
        [ MarkedErase.scanOptionTape left
            (List.append (MarkedErase.markedOptions bit) rest)
        , Tape.blank, T2 ])
      rfl rfl ⟨1, FirstCellMarker.run bit left rest Tape.blank T2⟩

theorem markedEraseDescription_realizes
    (before after : List Bool) (markedBit : Bool)
    (left : List (Option Bool))
    (boundaryRest : List (Option Bool)) (T2 : Tape Bool) :
    markedEraseDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (MarkedErase.scanOptionTape left
          (List.append (MarkedErase.wrappedOptionsWord before)
            (List.append (MarkedErase.markedOptions markedBit)
              (List.append (MarkedErase.wrappedOptionsWord after)
                (some false :: some false :: boundaryRest)))))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (MarkedErase.scanOptionTape
          (List.append
            (List.append
              (List.append (MarkedErase.wrappedOptionsWord after).reverse
                (MarkedErase.wrappedOptions markedBit).reverse)
              (MarkedErase.wrappedOptionsWord before).reverse)
            left)
          (some false :: some false :: boundaryRest))
        Tape.blank
        (MarkedErase.eraseBits after
          ((writeBitR true).apply (MarkedErase.eraseBits before T2)))) := by
  simpa [markedEraseDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      markedErase_ready.left markedErase_ready.right markedErase_supports
      (c := config MarkedErase.loop
        (MarkedErase.scanOptionTape left
          (List.append (MarkedErase.wrappedOptionsWord before)
            (List.append (MarkedErase.markedOptions markedBit)
              (List.append (MarkedErase.wrappedOptionsWord after)
                (some false :: some false :: boundaryRest)))))
        Tape.blank T2)
      (tapes :=
        [ MarkedErase.scanOptionTape
            (List.append
              (List.append
                (List.append (MarkedErase.wrappedOptionsWord after).reverse
                  (MarkedErase.wrappedOptions markedBit).reverse)
                (MarkedErase.wrappedOptionsWord before).reverse)
              left)
            (some false :: some false :: boundaryRest)
        , Tape.blank
        , MarkedErase.eraseBits after
            ((writeBitR true).apply (MarkedErase.eraseBits before T2)) ])
      rfl rfl ⟨MarkedErase.markedFuel before after,
        MarkedErase.run before after markedBit left boundaryRest T2⟩
theorem remainingBits_length_formula (L : DovetailLayout) :
    (remainingBits L).length =
      (inputStageBits L).length + (acceptBits L).length +
        (rejectHitBits L).length := by
  have hle := acceptCounterBits_length_le_dataBits L
  rw [remainingBits, List.length_drop]
  rw [dataBits_accept_decomp]
  simp [acceptCounterBits]
  lia

theorem remainingBits_ne_nil (L : DovetailLayout) :
    remainingBits L ≠ [] := by
  have haccept := configurationFieldBits_length_pos L.acceptConfig
  intro hnil
  have hzero : (remainingBits L).length = 0 := by simp [hnil]
  rw [remainingBits_length_formula] at hzero
  change 0 < (acceptBits L).length at haccept
  lia

def pairLeft (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((AcceptConfigCopy.wrappedBits
      ((dataBits L).take (acceptCounterBits L).length)).reverse.map some)
    (commonEndpointLeft L)
def boundaryOptions (L : DovetailLayout) : List (Option Bool) :=
  ((rawBoundaryRest true L).drop 2).map some

def armedPairTape0 (L : DovetailLayout) : Tape Bool :=
  match remainingBits L with
  | [] => afterPairTape0 L
  | bit :: bits =>
      MarkedErase.scanOptionTape (pairLeft L)
        (List.append (MarkedErase.markedOptions bit)
          (List.append (MarkedErase.wrappedOptionsWord bits)
            (some false :: some false :: boundaryOptions L)))

def markedErasedTape2 (L : DovetailLayout) : Tape Bool :=
  match remainingBits L with
  | [] => afterRewindTape2 L
  | _bit :: bits =>
      MarkedErase.eraseBits bits ((writeBitR true).apply (afterRewindTape2 L))
def markedGapTape2 (L : DovetailLayout) : Tape Bool :=
  Components.eraseRight 4 (markedErasedTape2 L)

theorem afterPairTape0_eq_normal_options (L : DovetailLayout) :
    afterPairTape0 L =
      MarkedErase.scanOptionTape (pairLeft L)
        (List.append (MarkedErase.wrappedOptionsWord (remainingBits L))
          (some false :: some false :: boundaryOptions L)) := by
  unfold afterPairTape0
  rw [rawBoundaryRest_eq_false_false_drop]
  simp [pairLeft, remainingBits, boundaryOptions,
    MarkedErase.scanOptionTape, MarkedErase.wrappedOptionsWord,
    scanTape, List.map_append, List.append_assoc]

theorem markFirstAtRewind_realizes (L : DovetailLayout) :
    firstCellMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterPairTape0 L) Tape.blank (afterRewindTape2 L))
      (encodedGuardedStructured3Tapes
        (armedPairTape0 L) Tape.blank (afterRewindTape2 L)) := by
  rw [afterPairTape0_eq_normal_options]
  cases hbits : remainingBits L with
  | nil => exact (remainingBits_ne_nil L hbits).elim
  | cons bit bits =>
      simpa [armedPairTape0, hbits,
        MarkedErase.wrappedOptionsWord,
        AcceptConfigCopy.wrappedBits,
        AcceptConfigCopy.wrappedBit,
        MarkedErase.wrappedOptions, List.append_assoc] using
        firstCellMarkerDescription_realizes bit (pairLeft L)
          (List.append (MarkedErase.wrappedOptionsWord bits)
            (some false :: some false :: boundaryOptions L))
          (afterRewindTape2 L)
theorem markedEraseAtArmed_realizes (L : DovetailLayout) :
    markedEraseDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (armedPairTape0 L) Tape.blank (afterRewindTape2 L))
      (encodedGuardedStructured3Tapes
        (atBoundaryTape0 L) Tape.blank (markedErasedTape2 L)) := by
  cases hbits : remainingBits L with
  | nil => exact (remainingBits_ne_nil L hbits).elim
  | cons bit bits =>
      have h := markedEraseDescription_realizes
        ([] : List Bool) bits bit (pairLeft L) (boundaryOptions L)
        (afterRewindTape2 L)
      have hboundary :
          some false :: some false :: boundaryOptions L =
            (rawBoundaryRest true L).map some := by
        rw [rawBoundaryRest_eq_false_false_drop]
        rfl
      simpa [armedPairTape0, markedErasedTape2, hbits,
        atBoundaryTape0, pairLeft, commonEndpointLeft,
        MarkedErase.wrappedOptionsWord, MarkedErase.wrappedOptions,
        AcceptConfigCopy.wrappedBits, AcceptConfigCopy.wrappedBit,
        wrappedRawBit, scanTape, MarkedErase.scanOptionTape,
        MarkedErase.eraseBits,
        List.reverse_append, List.map_append, List.append_assoc,
        hboundary] using h

theorem eraseFourAtMarked_realizes (L : DovetailLayout) :
    eraseFourDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (atBoundaryTape0 L) Tape.blank (markedErasedTape2 L))
      (encodedGuardedStructured3Tapes
        (atBoundaryTape0 L) Tape.blank (markedGapTape2 L)) := by
  exact eraseFourDescription_realizes
    (atBoundaryTape0 L) (markedErasedTape2 L)

def markEraseGapDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription firstCellMarkerDescription
      markedEraseDescription)
    eraseFourDescription
theorem markEraseGapDescription_ready :
    markEraseGapDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      firstCellMarkerDescription_ready markedEraseDescription_ready)
    eraseFourDescription_ready

theorem markEraseGapDescription_realizes (L : DovetailLayout) :
    markEraseGapDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterPairTape0 L) Tape.blank (afterRewindTape2 L))
      (encodedGuardedStructured3Tapes
        (atBoundaryTape0 L) Tape.blank (markedGapTape2 L)) := by
  have hm := markFirstAtRewind_realizes L
  have he := markedEraseAtArmed_realizes L
  have hme := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    firstCellMarkerDescription_ready markedEraseDescription_ready hm he
  have hf := eraseFourAtMarked_realizes L
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    (canonicalPrimitiveSeqDescription_subroutineReady
      firstCellMarkerDescription_ready markedEraseDescription_ready)
    eraseFourDescription_ready hme hf
  simpa [markEraseGapDescription] using h

theorem eraseBits_eq_eraseRight
    (bits : List Bool) (T : Tape Bool) :
    MarkedErase.eraseBits bits T = Components.eraseRight bits.length T := by
  induction bits generalizing T with
  | nil => rfl
  | cons bit bits ih =>
      simp only [MarkedErase.eraseBits, List.length_cons]
      rw [Components.eraseRight]
      exact ih (eraseR.apply T)
theorem writeBitR_true_targetTape_cons
    (first : Bool) (rest : List Bool)
    (baseLeft : List (Option Bool)) :
    (writeBitR true).apply
        (Tape2Rewinder.targetTapeWithContext baseLeft (first :: rest) []) =
      tapeAtCells (some true :: none :: baseLeft)
        (List.append (rest.map some) [none]) := by
  cases rest <;> rfl

theorem markedGapTape2_shape (L : DovetailLayout) :
    markedGapTape2 L =
      tapeAtCells
        (List.append
          (List.replicate ((remainingBits L).length + 3)
            (none : Option Bool))
          (some true :: none :: counterBaseTail L))
        (List.append
          (((stageCounterBits L).drop
            ((remainingBits L).length + 4)).map some)
          [none]) := by
  rcases stageNatBits_cons_false L.stage with ⟨stageTail, hstage⟩
  have hcounter :
      stageCounterBits L =
        false :: List.append stageTail (acceptCounterBits L) := by
    rw [stageCounterBits, hstage]
    rfl
  cases hbits : remainingBits L with
  | nil => exact (remainingBits_ne_nil L hbits).elim
  | cons bit bits =>
      simp only [markedGapTape2, markedErasedTape2, hbits]
      rw [eraseBits_eq_eraseRight]
      unfold afterRewindTape2
      rw [hcounter]
      rw [writeBitR_true_targetTape_cons]
      rw [eraseRight_comp]
      rw [eraseRight_tapeAtCells]
      simp only [List.length_cons, List.drop_succ_cons]

theorem markedGap_blank_count (L : DovetailLayout) :
    (remainingBits L).length + 3 =
      (inputStageBits L).length + (acceptBits L).length + 7 := by
  rw [remainingBits_length_formula]
  have hhit : (rejectHitBits L).length = 4 := by
    simp [rejectHitBits, boolFieldBits_nil_length]
  rw [hhit]

end AcceptInternalMarker
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
