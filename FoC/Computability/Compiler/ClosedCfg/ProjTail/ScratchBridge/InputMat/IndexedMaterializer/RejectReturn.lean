import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.RejectPadding

set_option doc.verso true

/-!
Rejecting-route gap-copy return and final tape-2 rewind.
-/

set_option linter.unusedSimpArgs false

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectTape0Padding

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open AcceptBranch RejectBranchShapes

namespace GapCopy

def scan : Nat := 0
def gap2 : Nat := 1
def gap3 : Nat := 2
def gap4 : Nat := 3
def hit1 : Nat := 4
def hit2 : Nat := 5
def hit3 : Nat := 6
def hit4 : Nat := 7
def extra : Nat := 8
def halt : Nat := 9

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action0 action2 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 action0 keepS action2 target
def rowsForAllReads
    (source : Nat) (action0 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads3 fun read0 read1 read2 =>
    row source read0 read1 read2 action0 keepS action2 target

def copyRows (source target : Nat) : List Transition :=
  List.append
    (rowsForTape2Read source (some false) (writeR (some false)) keepR target)
    (rowsForTape2Read source (some true) (writeR (some true)) keepR target)

def rows : List Transition :=
  [ rowsForTape2Read scan (some false) keepS keepR scan
  , rowsForTape2Read scan (some true) keepS keepR scan
  , rowsForTape2Read scan none keepS keepR gap2
  , rowsForTape2Read gap2 none keepS keepR gap3
  , rowsForTape2Read gap3 none keepS keepR gap4
  , rowsForTape2Read gap4 none keepS keepR hit1
  , copyRows hit1 hit2
  , copyRows hit2 hit3
  , copyRows hit3 hit4
  , copyRows hit4 extra
  , rowsForAllReads extra (writeR none) keepS halt ].flatten
def description : Description :=
  ThreeTape.description 10 scan halt rows

theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

syntax "gap_copy_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| gap_copy_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape2Read,
          rowsForAllReads, copyRows, scan, gap2, gap3, gap4,
          hit1, hit2, hit3, hit4, extra, halt,
          allReads3, allReads2, allReadCells, List.find?, tapeAtCells,
          $lemmas,*])
theorem scan_step
    (T0 T1 : Tape Bool) (left right : List (Option Bool))
    (bit : Bool) :
    description.runConfig 1
        (config scan T0 T1
          (tapeAtCells left (some bit :: right))) =
      config scan T0 T1
        (tapeAtCells (some bit :: left) right) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => cases bit <;> gap_copy_step [h0, h1] <;> cases right <;> rfl
      | some b1 => cases b1 <;> cases bit <;>
          gap_copy_step [h0, h1] <;> cases right <;> rfl
  | some b0 => cases b0 <;>
      cases h1 : T1.head with
      | none => cases bit <;> gap_copy_step [h0, h1] <;> cases right <;> rfl
      | some b1 => cases b1 <;> cases bit <;>
          gap_copy_step [h0, h1] <;> cases right <;> rfl

theorem cons_cells_append
    (bit : Bool) (bits : List Bool)
    (right : List (Option Bool)) :
    List.append ((bit :: bits).map some) right =
      some bit :: List.append (bits.map some) right := by
  rfl

theorem scan_run
    (bits : List Bool) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig bits.length
        (config scan T0 T1
          (tapeAtCells left
            (List.append (bits.map some) right))) =
      config scan T0 T1
        (tapeAtCells
          (List.append (bits.reverse.map some) left)
          right) := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit bits ih =>
      rw [List.length_cons]
      rw [show bits.length + 1 = 1 + bits.length by lia]
      rw [Description.runConfig_add]
      rw [cons_cells_append]
      rw [scan_step]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]
theorem fixed_tail_run
    (hit : Bool) (T1 : Tape Bool)
    (left0 left2 : List (Option Bool)) :
    description.runConfig 9
        (config scan (tapeAtCells left0 []) T1
          (tapeAtCells left2
            (List.append (List.replicate 4 none)
              (List.append ((boolFieldBits hit []).map some)
                [none, none])))) =
      config halt
        (tapeAtCells
          (none ::
            List.append ((boolFieldBits hit []).reverse.map some) left0)
          [])
        T1
        (tapeAtCells
          (List.append ((boolFieldBits hit []).reverse.map some)
            (List.append (List.replicate 4 none) left2))
          [none, none]) := by
  cases h1 : T1.head with
  | none => cases hit <;>
      gap_copy_step [h1, boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
        List.append_assoc] <;> rfl
  | some bit1 => cases bit1 <;> cases hit <;>
      gap_copy_step [h1, boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
        List.append_assoc] <;> rfl

def fuel (data : List Bool) : Nat := data.length + 9

theorem run
    (data : List Bool) (hit : Bool) (T1 : Tape Bool)
    (left0 left2 : List (Option Bool)) :
    description.runConfig (fuel data)
        (config scan (tapeAtCells left0 []) T1
          (tapeAtCells left2
            (List.append (data.map some)
              (List.append (List.replicate 4 none)
                (List.append ((boolFieldBits hit []).map some)
                  [none, none]))))) =
      config halt
        (tapeAtCells
          (none ::
            List.append ((boolFieldBits hit []).reverse.map some) left0)
          [])
        T1
        (tapeAtCells
          (List.append ((boolFieldBits hit []).reverse.map some)
            (List.append (List.replicate 4 none)
              (List.append (data.reverse.map some) left2)))
          [none, none]) := by
  rw [show fuel data = data.length + 9 by rfl]
  rw [Description.runConfig_add]
  rw [scan_run]
  rw [fixed_tail_run]
def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_ready : loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady ready.left supports

theorem loweredDescription_realizes
    (data : List Bool) (hit : Bool) (T1 : Tape Bool)
    (left0 left2 : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (tapeAtCells left0 []) T1
        (tapeAtCells left2
          (List.append (data.map some)
            (List.append (List.replicate 4 none)
              (List.append ((boolFieldBits hit []).map some)
                [none, none])))))
      (encodedGuardedStructured3Tapes
        (tapeAtCells
          (none ::
            List.append ((boolFieldBits hit []).reverse.map some) left0)
          [])
        T1
        (tapeAtCells
          (List.append ((boolFieldBits hit []).reverse.map some)
            (List.append (List.replicate 4 none)
              (List.append (data.reverse.map some) left2)))
          [none, none])) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      ready.left ready.right supports
      (c := config scan (tapeAtCells left0 []) T1
        (tapeAtCells left2
          (List.append (data.map some)
            (List.append (List.replicate 4 none)
              (List.append ((boolFieldBits hit []).map some)
                [none, none])))))
      (tapes :=
        [ tapeAtCells
            (none ::
              List.append ((boolFieldBits hit []).reverse.map some) left0)
            []
        , T1
        , tapeAtCells
            (List.append ((boolFieldBits hit []).reverse.map some)
              (List.append (List.replicate 4 none)
                (List.append (data.reverse.map some) left2)))
            [none, none] ])
      rfl rfl ⟨fuel data, run data hit T1 left0 left2⟩

end GapCopy

open AfterAcceptCountRuns
def gapCopyData (L : DovetailLayout) : List Bool :=
  List.append (countedAcceptBits L) (AcceptBranch.rejectBits L)

def gapCopyTape0Left (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate ((countedAcceptBits L).length + 3) none)
    (some true :: rightEdgeBase0 L)

def gapCopyTape2Left (L : DovetailLayout) : List (Option Bool) :=
  some true :: RejectTape0Padding.acceptScanBaseLeft L
def afterGapCopyTape0 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        ((boolFieldBits L.rejectHit []).reverse.map some)
        (gapCopyTape0Left L))
    []

def afterGapCopyTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (List.append
      ((boolFieldBits L.rejectHit []).reverse.map some)
      (List.append (List.replicate 4 none)
        (List.append ((gapCopyData L).reverse.map some)
          (gapCopyTape2Left L))))
    [none, none]

theorem afterAcceptCountTape0_eq_gapCopySourceTape0
    (L : DovetailLayout) :
    afterAcceptCountTape0 L =
      tapeAtCells (gapCopyTape0Left L) [] := by
  rfl
theorem gapCopyData_eq_accept_rejectTail (L : DovetailLayout) :
    gapCopyData L =
      List.append (countedAcceptBits L)
        (false :: RejectTape0Padding.rejectConfigTail L) := by
  rw [gapCopyData]
  rw [RejectTape0Padding.rejectBits_eq_false_cons_tail]

theorem gapCopyData_cells_eq (L : DovetailLayout) :
    (gapCopyData L).map some =
      List.append ((countedAcceptBits L).map some)
        ((false :: RejectTape0Padding.rejectConfigTail L).map some) := by
  exact Eq.trans
    (congrArg (fun bits : List Bool => bits.map some)
      (gapCopyData_eq_accept_rejectTail L))
    (List.map_append
      (f := some)
      (l₁ := countedAcceptBits L)
      (l₂ := false :: RejectTape0Padding.rejectConfigTail L))

theorem rejectHitBits_eq_boolFieldBits (L : DovetailLayout) :
    RejectBranchShapes.rejectHitBits L =
      boolFieldBits L.rejectHit [] := by
  rfl
theorem afterAcceptCountTape2_eq_gapCopySourceTape2
    (L : DovetailLayout) :
    afterAcceptCountTape2 L =
      tapeAtCells (gapCopyTape2Left L)
        (List.append ((gapCopyData L).map some)
          (List.append (List.replicate 4 none)
            (List.append ((boolFieldBits L.rejectHit []).map some)
              [none, none]))) := by
  unfold afterAcceptCountTape2 restoredTape2 countedSuffixTail
    RejectTape0Padding.rejectRightPadding
    gapCopyTape2Left countedAcceptBits
  rw [rejectHitBits_eq_boolFieldBits]
  let acceptCells : List (Option Bool) :=
    (configurationFieldBits L.acceptConfig []).map some
  let rejectCells : List (Option Bool) :=
    (false :: RejectTape0Padding.rejectConfigTail L).map some
  let padding : List (Option Bool) :=
    List.append (List.replicate 4 none)
      (List.append ((boolFieldBits L.rejectHit []).map some) [none, none])
  apply congrArg (tapeAtCells (some true :: acceptScanBaseLeft L))
  exact Eq.trans
    (List.append_assoc acceptCells rejectCells padding).symm
    (congrArg (fun cells => List.append cells padding)
      (gapCopyData_cells_eq L).symm)

theorem gapCopyDescription_realizes (L : DovetailLayout) :
    GapCopy.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterAcceptCountTape0 L) Tape.blank (afterAcceptCountTape2 L))
      (encodedGuardedStructured3Tapes
        (afterGapCopyTape0 L) Tape.blank (afterGapCopyTape2 L)) := by
  rw [afterAcceptCountTape0_eq_gapCopySourceTape0]
  rw [afterAcceptCountTape2_eq_gapCopySourceTape2]
  exact GapCopy.loweredDescription_realizes
    (gapCopyData L) L.rejectHit Tape.blank
    (gapCopyTape0Left L) (gapCopyTape2Left L)

end RejectTape0Padding
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
namespace RejectTape0Padding
namespace GapCopyReturnRuns

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

namespace FixedBack

def start : Nat := 0
def back2 : Nat := 1
def back3 : Nat := 2
def back4 : Nat := 3
def back5 : Nat := 4
def back6 : Nat := 5
def back7 : Nat := 6
def back8 : Nat := 7
def back9 : Nat := 8
def halt : Nat := 9
def rowsForAllReads
    (source : Nat) (action0 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads3 fun read0 read1 read2 =>
    row source read0 read1 read2 action0 keepS action2 target

def rows : List Transition :=
  [ rowsForAllReads start keepL keepL back2
  , rowsForAllReads back2 keepL keepL back3
  , rowsForAllReads back3 keepL keepL back4
  , rowsForAllReads back4 keepL keepL back5
  , rowsForAllReads back5 keepL keepL back6
  , rowsForAllReads back6 keepL keepL back7
  , rowsForAllReads back7 keepL keepL back8
  , rowsForAllReads back8 keepL keepL back9
  , rowsForAllReads back9 keepL keepS halt ].flatten

def description : Description :=
  ThreeTape.description 10 start halt rows
theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

syntax "fixed_back_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| fixed_back_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForAllReads,
          start, back2, back3, back4, back5, back6, back7,
          back8, back9, halt, allReads3, allReadCells, List.find?,
          tapeAtCells, $lemmas,*])

theorem run
    (hit : Bool) (T1 : Tape Bool)
    (left0 left2 : List (Option Bool)) :
    description.runConfig 9
        (config start
          (tapeAtCells
            (none ::
              List.append ((boolFieldBits hit []).reverse.map some)
                (List.append (List.replicate 4 none) left0))
            [])
          T1
          (tapeAtCells
            (List.append ((boolFieldBits hit []).reverse.map some)
              (List.append (List.replicate 4 none) left2))
            [none, none])) =
      config halt
        (tapeAtCells left0
          (List.append (List.replicate 4 none)
            (List.append ((boolFieldBits hit []).map some)
              [none, none])))
        T1
        (tapeAtCells left2
          (List.append (List.replicate 4 none)
            (List.append ((boolFieldBits hit []).map some)
              [none, none]))) := by
  cases h1 : T1.head with
  | none => cases hit <;>
      fixed_back_step [h1, boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
        List.append_assoc] <;> rfl
  | some bit1 => cases bit1 <;> cases hit <;>
      fixed_back_step [h1, boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
        List.append_assoc] <;> rfl
def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_ready : loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady ready.left supports

theorem loweredDescription_realizes
    (hit : Bool) (T1 : Tape Bool)
    (left0 left2 : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (tapeAtCells
          (none ::
            List.append ((boolFieldBits hit []).reverse.map some)
              (List.append (List.replicate 4 none) left0))
          [])
        T1
        (tapeAtCells
          (List.append ((boolFieldBits hit []).reverse.map some)
            (List.append (List.replicate 4 none) left2))
          [none, none]))
      (encodedGuardedStructured3Tapes
        (tapeAtCells left0
          (List.append (List.replicate 4 none)
            (List.append ((boolFieldBits hit []).map some)
              [none, none])))
        T1
        (tapeAtCells left2
          (List.append (List.replicate 4 none)
            (List.append ((boolFieldBits hit []).map some)
              [none, none])))) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      ready.left ready.right supports
      (c := config start
        (tapeAtCells
          (none ::
            List.append ((boolFieldBits hit []).reverse.map some)
              (List.append (List.replicate 4 none) left0))
          [])
        T1
        (tapeAtCells
          (List.append ((boolFieldBits hit []).reverse.map some)
            (List.append (List.replicate 4 none) left2))
          [none, none]))
      (tapes :=
        [ tapeAtCells left0
            (List.append (List.replicate 4 none)
              (List.append ((boolFieldBits hit []).map some)
                [none, none]))
        , T1
        , tapeAtCells left2
            (List.append (List.replicate 4 none)
              (List.append ((boolFieldBits hit []).map some)
                [none, none])) ])
      rfl rfl ⟨9, run hit T1 left0 left2⟩

end FixedBack
def fixedBackBase0 (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate ((AfterAcceptCountRuns.countedAcceptBits L).length - 1)
      none)
    (some true :: AfterAcceptCountRuns.rightEdgeBase0 L)

def fixedBackBase2 (L : DovetailLayout) : List (Option Bool) :=
  List.append ((gapCopyData L).reverse.map some) (gapCopyTape2Left L)

def fixedBackRight (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 4 none)
    (List.append ((boolFieldBits L.rejectHit []).map some) [none, none])
def afterFixedBackTape0 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells (fixedBackBase0 L) (fixedBackRight L)

def afterFixedBackTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells (fixedBackBase2 L) (fixedBackRight L)

theorem gapCopyTape0Left_eq_fixedBack_split (L : DovetailLayout) :
    gapCopyTape0Left L =
      List.append (List.replicate 4 none) (fixedBackBase0 L) := by
  have hpos := configurationFieldBits_length_pos L.acceptConfig
  have hcount :
      (AfterAcceptCountRuns.countedAcceptBits L).length + 3 =
        4 + ((AfterAcceptCountRuns.countedAcceptBits L).length - 1) := by
    have hpos' : 0 <
        (AfterAcceptCountRuns.countedAcceptBits L).length := by
      simpa [AfterAcceptCountRuns.countedAcceptBits] using hpos
    lia
  unfold gapCopyTape0Left fixedBackBase0
  rw [hcount]
  exact list_replicate_add_append
    (none : Option Bool) 4
    ((AfterAcceptCountRuns.countedAcceptBits L).length - 1)
    (some true :: AfterAcceptCountRuns.rightEdgeBase0 L)
theorem afterGapCopyTape0_eq_fixedBackSource (L : DovetailLayout) :
    afterGapCopyTape0 L =
      tapeAtCells
        (none ::
          List.append ((boolFieldBits L.rejectHit []).reverse.map some)
            (List.append (List.replicate 4 none) (fixedBackBase0 L)))
        [] := by
  unfold afterGapCopyTape0
  rw [gapCopyTape0Left_eq_fixedBack_split]

theorem afterGapCopyTape2_eq_fixedBackSource (L : DovetailLayout) :
    afterGapCopyTape2 L =
      tapeAtCells
        (List.append ((boolFieldBits L.rejectHit []).reverse.map some)
          (List.append (List.replicate 4 none) (fixedBackBase2 L)))
        [none, none] := by
  unfold afterGapCopyTape2 fixedBackBase2
  simp [List.append_assoc]

theorem fixedBackDescription_realizes (L : DovetailLayout) :
    FixedBack.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterGapCopyTape0 L) Tape.blank (afterGapCopyTape2 L))
      (encodedGuardedStructured3Tapes
        (afterFixedBackTape0 L) Tape.blank (afterFixedBackTape2 L)) := by
  rw [afterGapCopyTape0_eq_fixedBackSource]
  rw [afterGapCopyTape2_eq_fixedBackSource]
  simpa [afterFixedBackTape0, afterFixedBackTape2, fixedBackRight] using
    FixedBack.loweredDescription_realizes
      L.rejectHit Tape.blank (fixedBackBase0 L) (fixedBackBase2 L)

namespace MarkerReturn
def enter2 : Nat := 0
def scan2 : Nat := 1
def scan0 : Nat := 2
def halt : Nat := 3

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action2 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 keepS keepS action2 target

def rowsForTape0Read
    (source : Nat) (read0 : Option Bool)
    (action0 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read1 read2 =>
    row source read0 read1 read2 action0 keepS keepS target
def rows : List Transition :=
  [ rowsForTape2Read enter2 (some false) keepL scan2
  , rowsForTape2Read enter2 (some true) keepL scan2
  , rowsForTape2Read scan2 none keepL scan2
  , rowsForTape2Read scan2 (some true) (writeS none) scan0
  , rowsForTape0Read scan0 none keepL scan0
  , rowsForTape0Read scan0 (some true) (writeS none) halt ].flatten

def description : Description :=
  ThreeTape.description 4 enter2 halt rows

theorem ready : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)
theorem supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

syntax "marker_return_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| marker_return_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape2Read,
          rowsForTape0Read, enter2, scan2, scan0, halt,
          allReads2, allReadCells, List.find?, tapeAtCells, $lemmas,*])

theorem enter2_step
    (T0 T1 : Tape Bool) (stageHead : Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        (config enter2 T0 T1
          (tapeAtCells (none :: left) (some stageHead :: right))) =
      config scan2 T0 T1
        (tapeAtCells left (none :: some stageHead :: right)) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => cases stageHead <;> marker_return_step [h0, h1]
      | some bit1 => cases bit1 <;> cases stageHead <;>
          marker_return_step [h0, h1]
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => cases stageHead <;> marker_return_step [h0, h1]
      | some bit1 => cases bit1 <;> cases stageHead <;>
          marker_return_step [h0, h1]

theorem scan2_blank_step
    (T0 T1 : Tape Bool) (next : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        (config scan2 T0 T1
          (tapeAtCells (next :: left) (none :: right))) =
      config scan2 T0 T1
        (tapeAtCells left (next :: none :: right)) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => marker_return_step [h0, h1]
      | some bit1 => cases bit1 <;> marker_return_step [h0, h1]
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => marker_return_step [h0, h1]
      | some bit1 => cases bit1 <;> marker_return_step [h0, h1]
theorem scan2_marker_step
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        (config scan2 T0 T1
          (tapeAtCells left (some true :: right))) =
      config scan0 T0 T1 (tapeAtCells left (none :: right)) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => marker_return_step [h0, h1]
      | some bit1 => cases bit1 <;> marker_return_step [h0, h1]
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none => marker_return_step [h0, h1]
      | some bit1 => cases bit1 <;> marker_return_step [h0, h1]

theorem scan0_blank_step
    (T1 T2 : Tape Bool) (next : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        (config scan0
          (tapeAtCells (next :: left) (none :: right)) T1 T2) =
      config scan0
        (tapeAtCells left (next :: none :: right)) T1 T2 := by
  cases h1 : T1.head with
  | none =>
      cases h2 : T2.head with
      | none => marker_return_step [h1, h2]
      | some bit2 => cases bit2 <;> marker_return_step [h1, h2]
  | some bit1 => cases bit1 <;>
      cases h2 : T2.head with
      | none => marker_return_step [h1, h2]
      | some bit2 => cases bit2 <;> marker_return_step [h1, h2]

theorem scan0_marker_step
    (T1 T2 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        (config scan0 (tapeAtCells left (some true :: right)) T1 T2) =
      config halt (tapeAtCells left (none :: right)) T1 T2 := by
  cases h1 : T1.head with
  | none =>
      cases h2 : T2.head with
      | none => marker_return_step [h1, h2]
      | some bit2 => cases bit2 <;> marker_return_step [h1, h2]
  | some bit1 => cases bit1 <;>
      cases h2 : T2.head with
      | none => marker_return_step [h1, h2]
      | some bit2 => cases bit2 <;> marker_return_step [h1, h2]
theorem scan2_blanks_to_marker
    (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig (n + 2)
        (config scan2 T0 T1
          (tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (some true :: left))
            (none :: right))) =
      config scan0 T0 T1
        (tapeAtCells left
          (none :: List.append
            (List.replicate (n + 1) (none : Option Bool)) right)) := by
  induction n generalizing right with
  | zero =>
      rw [show 0 + 2 = 1 + 1 by rfl]
      rw [Description.runConfig_add]
      simp only [List.replicate_zero, List.append_eq, List.nil_append]
      rw [scan2_blank_step]
      rw [scan2_marker_step]
      rfl
  | succ n ih =>
      rw [show (n + 1) + 2 = 1 + (n + 2) by lia]
      rw [Description.runConfig_add]
      simp only [List.replicate_succ, List.append_eq, List.cons_append]
      rw [scan2_blank_step]
      have hih := ih (none :: right)
      simp only [List.append_eq] at hih
      rw [hih]
      have hshift :=
        FoC.Computability.CommonGround.FiniteTransducers.replicate_none_append_none_cons
          n right
      simp only [List.append_eq] at hshift
      simp only [List.replicate_succ, List.cons_append]
      rw [hshift]

theorem scan0_blanks_to_marker
    (n : Nat) (T1 T2 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig (n + 2)
        (config scan0
          (tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (some true :: left))
            (none :: right))
          T1 T2) =
      config halt
        (tapeAtCells left
          (none :: List.append
            (List.replicate (n + 1) (none : Option Bool)) right))
        T1 T2 := by
  induction n generalizing right with
  | zero =>
      rw [show 0 + 2 = 1 + 1 by rfl]
      rw [Description.runConfig_add]
      simp only [List.replicate_zero, List.append_eq, List.nil_append]
      rw [scan0_blank_step]
      rw [scan0_marker_step]
      rfl
  | succ n ih =>
      rw [show (n + 1) + 2 = 1 + (n + 2) by lia]
      rw [Description.runConfig_add]
      simp only [List.replicate_succ, List.append_eq, List.cons_append]
      rw [scan0_blank_step]
      have hih := ih (none :: right)
      simp only [List.append_eq] at hih
      rw [hih]
      have hshift :=
        FoC.Computability.CommonGround.FiniteTransducers.replicate_none_append_none_cons
          n right
      simp only [List.append_eq] at hshift
      simp only [List.replicate_succ, List.cons_append]
      rw [hshift]
def sourceTape0
    (base : List (Option Bool)) (n : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate n (none : Option Bool))
      (some true :: base))
    (none :: right)

def sourceTape2
    (base : List (Option Bool)) (n : Nat) (stageHead : Bool)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate (n + 1) (none : Option Bool))
      (some true :: base))
    (some stageHead :: right)

def targetTape0
    (base : List (Option Bool)) (n : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells base
    (none :: List.append
      (List.replicate (n + 1) (none : Option Bool)) right)
def targetTape2
    (base : List (Option Bool)) (n : Nat) (stageHead : Bool)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells base
    (none :: List.append
      (List.replicate (n + 1) (none : Option Bool))
      (some stageHead :: right))

def fuel (n0 n2 : Nat) : Nat := n0 + n2 + 5

theorem run
    (base0 base2 right0 right2 : List (Option Bool))
    (n0 n2 : Nat) (stageHead : Bool) (T1 : Tape Bool) :
    description.runConfig (fuel n0 n2)
        (config enter2 (sourceTape0 base0 n0 right0) T1
          (sourceTape2 base2 n2 stageHead right2)) =
      config halt (targetTape0 base0 n0 right0) T1
        (targetTape2 base2 n2 stageHead right2) := by
  rw [show fuel n0 n2 = 1 + ((n2 + 2) + (n0 + 2)) by
    unfold fuel
    lia]
  rw [Description.runConfig_add]
  unfold sourceTape2
  simp only [List.replicate_succ, List.append_eq, List.cons_append]
  rw [enter2_step]
  rw [Description.runConfig_add]
  have hscan2 :=
    scan2_blanks_to_marker n2 (sourceTape0 base0 n0 right0) T1
      base2 (some stageHead :: right2)
  simp only [List.append_eq] at hscan2
  rw [hscan2]
  unfold sourceTape0
  have hscan0 :=
    scan0_blanks_to_marker n0 T1
      (tapeAtCells base2
        (none :: List.append
          (List.replicate (n2 + 1) (none : Option Bool))
          (some stageHead :: right2)))
      base0 right0
  simpa [targetTape0, targetTape2] using hscan0
def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_ready : loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady ready.left supports

theorem loweredDescription_realizes
    (base0 base2 right0 right2 : List (Option Bool))
    (n0 n2 : Nat) (stageHead : Bool) (T1 : Tape Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (sourceTape0 base0 n0 right0) T1
        (sourceTape2 base2 n2 stageHead right2))
      (encodedGuardedStructured3Tapes
        (targetTape0 base0 n0 right0) T1
        (targetTape2 base2 n2 stageHead right2)) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      ready.left ready.right supports
      (c := config enter2 (sourceTape0 base0 n0 right0) T1
        (sourceTape2 base2 n2 stageHead right2))
      (tapes :=
        [ targetTape0 base0 n0 right0
        , T1
        , targetTape2 base2 n2 stageHead right2 ])
      rfl rfl ⟨fuel n0 n2,
        run base0 base2 right0 right2 n0 n2 stageHead T1⟩

end MarkerReturn

end GapCopyReturnRuns
end RejectTape0Padding
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
namespace RejectTape0Padding
namespace RejectRawRewind

open CanonicalLayouts.DovetailLayoutScanner GapCopyReturnRuns RejectBranchShapes
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
def rewindBits (L : DovetailLayout) : List Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)
    (gapCopyData L)

def rewindBase2 (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate
      ((ParsedLayoutBits L).length + markerOffset L + 6) none)
    [some true, none]

def rewindRightPadding (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 3 none)
    (List.append ((boolFieldBits L.rejectHit []).map some) [none, none])
theorem fixedBackBase2_eq_rewindSourceLeft (L : DovetailLayout) :
    GapCopyReturnRuns.fixedBackBase2 L =
      List.append ((rewindBits L).reverse.map some)
        (none :: rewindBase2 L) := by
  unfold GapCopyReturnRuns.fixedBackBase2 gapCopyTape2Left
    acceptScanBaseLeft rewindBits rewindBase2
  let beforeBits : List Bool :=
    show List Bool from LocateAccept.stageBeforeLastBits L.stage
  let stageBits : List Bool :=
    show List Bool from
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage
  change
    List.append ((gapCopyData L).reverse.map some)
        (some true ::
          List.append (beforeBits.reverse.map some)
            (List.append (List.replicate (locateLeadingPadding L) none)
              [some true, none])) =
      List.append
        ((List.append stageBits (gapCopyData L)).reverse.map some)
        (none ::
          List.append
            (List.replicate
              ((ParsedLayoutBits L).length + markerOffset L + 6) none)
            [some true, none])
  have hstage : stageBits = List.append beforeBits [true] :=
    LocateAccept.stageNatBits_eq_beforeLast_true L.stage
  rw [hstage]
  let parsedBits : List Bool := show List Bool from ParsedLayoutBits L
  change
    List.append ((gapCopyData L).reverse.map some)
        (some true ::
          List.append (beforeBits.reverse.map some)
            (List.append (List.replicate (locateLeadingPadding L) none)
              [some true, none])) =
      List.append
        ((List.append (List.append beforeBits [true])
          (gapCopyData L)).reverse.map some)
        (none ::
          List.append
            (List.replicate
              (parsedBits.length + markerOffset L + 6) none)
            [some true, none])
  have hrev :
      (List.append (List.append beforeBits [true])
        (gapCopyData L)).reverse =
        List.append (gapCopyData L).reverse
          (List.append beforeBits [true]).reverse :=
    List.reverse_append
  rw [hrev]
  have hmap :
      (List.append (gapCopyData L).reverse
        (List.append beforeBits [true]).reverse).map some =
        List.append ((gapCopyData L).reverse.map some)
          ((List.append beforeBits [true]).reverse.map some) :=
    List.map_append
  rw [hmap]
  have hbeforeRev :
      (List.append beforeBits [true]).reverse =
        true :: beforeBits.reverse := by
    exact Eq.trans List.reverse_append rfl
  rw [hbeforeRev]
  rw [List.map_cons]
  have hloc :
      locateLeadingPadding L = parsedBits.length + markerOffset L + 7 := by
    rfl
  rw [hloc]
  have hcount :
      parsedBits.length + markerOffset L + 7 =
        (parsedBits.length + markerOffset L + 6) + 1 := by
    lia
  rw [hcount]
  rw [List.replicate_succ]
  let dataCells : List (Option Bool) :=
    (gapCopyData L).reverse.map some
  let beforeCells : List (Option Bool) := beforeBits.reverse.map some
  let padding : List (Option Bool) :=
    List.replicate (parsedBits.length + markerOffset L + 6) none
  change
    List.append dataCells
        (some true ::
          List.append beforeCells
            (List.append (none :: padding) [some true, none])) =
      List.append (List.append dataCells (some true :: beforeCells))
        (none :: List.append padding [some true, none])
  exact
    (List.append_assoc dataCells (some true :: beforeCells)
      (none :: List.append padding [some true, none])).symm

def afterRawRewindTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.targetTapeWithContext
    (rewindBase2 L) (rewindBits L) (rewindRightPadding L)

theorem afterFixedBackTape2_eq_rawSource (L : DovetailLayout) :
    GapCopyReturnRuns.afterFixedBackTape2 L =
      Tape2Rewinder.sourceTapeWithContext
        (rewindBase2 L) (rewindBits L) (rewindRightPadding L) := by
  unfold GapCopyReturnRuns.afterFixedBackTape2
    Tape2Rewinder.sourceTapeWithContext
  rw [fixedBackBase2_eq_rewindSourceLeft]
  unfold GapCopyReturnRuns.fixedBackRight rewindRightPadding
  rfl
theorem rawRewindDescription_realizes (L : DovetailLayout) :
    Tape2Rewinder.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (GapCopyReturnRuns.afterFixedBackTape0 L) Tape.blank
        (GapCopyReturnRuns.afterFixedBackTape2 L))
      (encodedGuardedStructured3Tapes
        (GapCopyReturnRuns.afterFixedBackTape0 L) Tape.blank
        (afterRawRewindTape2 L)) := by
  rw [afterFixedBackTape2_eq_rawSource]
  unfold afterRawRewindTape2
  exact Tape2Rewinder.loweredDescription_realizes_withContext
    (rewindBase2 L) (rewindBits L) (rewindRightPadding L)
    (GapCopyReturnRuns.afterFixedBackTape0 L) Tape.blank

end RejectRawRewind
end RejectTape0Padding
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
