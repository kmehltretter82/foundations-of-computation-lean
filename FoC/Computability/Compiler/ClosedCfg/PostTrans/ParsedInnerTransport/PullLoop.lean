import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.Machines

set_option doc.verso true

/-!
# Parsed-inner transport pull lemmas

Run lemmas for the pull machines.  Every pull moves the rightmost bit of a
source field to the left edge of the block that grows leftward past the
cell-0 blank sentinel.  All lemmas are parametric in the interior runs, the
gap widths, and the right context.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace ParsedInnerTransport

theorem Reaches.of_eq {D : MachineDescription}
    {a b : Configuration} (h : a = b) : Reaches D a b :=
  ⟨0, h⟩

theorem replicate_none_comm (n : Nat) (X : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool)) (none :: X) =
      none :: List.append (List.replicate n (none : Option Bool)) X := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, List.append_eq] at *
      rw [ih]

theorem replicate_none_comm' (n : Nat) (X : List (Option Bool)) :
    (List.replicate n (none : Option Bool)) ++ (none :: X) =
      none :: ((List.replicate n (none : Option Bool)) ++ X) := by
  simpa [List.append_eq] using replicate_none_comm n X

/-- Step left over a bit, keeping it, from a state with uniform bit rows. -/
theorem stepBitLeftAny
    {D : MachineDescription} {s t : Nat}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left t))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left t))
    (y : Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s, tape := tapeSeenLeft (some y :: L) R }
      { state := t, tape := tapeSeenLeft L (some y :: R) } := by
  cases y with
  | false =>
      exact Reaches.of_run (by
        have := runConfig_one hF (tapeSeenLeft (some false :: L) R)
          (by cases L <;> rfl)
        rwa [move_left_write_tapeSeenLeft] at this)
  | true =>
      exact Reaches.of_run (by
        have := runConfig_one hT (tapeSeenLeft (some true :: L) R)
          (by cases L <;> rfl)
        rwa [move_left_write_tapeSeenLeft] at this)

/-- Step left over a blank. -/
theorem stepBlankLeft
    {D : MachineDescription} {s t : Nat}
    (h : D.lookupTransition s none =
      some (transition s none none Direction.left t))
    (L R : List (Option Bool)) :
    Reaches D
      { state := s, tape := tapeSeenLeft (none :: L) R }
      { state := t, tape := tapeSeenLeft L (none :: R) } :=
  Reaches.of_run (by
    have := runConfig_one h (tapeSeenLeft (none :: L) R)
      (by cases L <;> rfl)
    rwa [move_left_write_tapeSeenLeft] at this)

/--
Carry a pulled bit left across a field remainder, two gap/run pairs, and the
cell-0 sentinel, prepend it at the block's left edge, and park on the written
cell.  The carry starts just left of the erased source cell.
-/
theorem carryJ2_run
    {D : MachineDescription}
    {a0 aG2 aR2 aG1 aR1 aB aP aH : Nat} (x : Bool)
    (h0F : D.lookupTransition a0 (some false) =
      some (transition a0 (some false) (some false) Direction.left a0))
    (h0T : D.lookupTransition a0 (some true) =
      some (transition a0 (some true) (some true) Direction.left a0))
    (h0E : D.lookupTransition a0 none =
      some (transition a0 none none Direction.left aG2))
    (hG2N : D.lookupTransition aG2 none =
      some (transition aG2 none none Direction.left aG2))
    (hG2F : D.lookupTransition aG2 (some false) =
      some (transition aG2 (some false) (some false) Direction.left aR2))
    (hG2T : D.lookupTransition aG2 (some true) =
      some (transition aG2 (some true) (some true) Direction.left aR2))
    (hR2F : D.lookupTransition aR2 (some false) =
      some (transition aR2 (some false) (some false) Direction.left aR2))
    (hR2T : D.lookupTransition aR2 (some true) =
      some (transition aR2 (some true) (some true) Direction.left aR2))
    (hR2E : D.lookupTransition aR2 none =
      some (transition aR2 none none Direction.left aG1))
    (hG1N : D.lookupTransition aG1 none =
      some (transition aG1 none none Direction.left aG1))
    (hG1F : D.lookupTransition aG1 (some false) =
      some (transition aG1 (some false) (some false) Direction.left aR1))
    (hG1T : D.lookupTransition aG1 (some true) =
      some (transition aG1 (some true) (some true) Direction.left aR1))
    (hR1F : D.lookupTransition aR1 (some false) =
      some (transition aR1 (some false) (some false) Direction.left aR1))
    (hR1T : D.lookupTransition aR1 (some true) =
      some (transition aR1 (some true) (some true) Direction.left aR1))
    (hR1E : D.lookupTransition aR1 none =
      some (transition aR1 none none Direction.left aB))
    (hBF : D.lookupTransition aB (some false) =
      some (transition aB (some false) (some false) Direction.left aB))
    (hBT : D.lookupTransition aB (some true) =
      some (transition aB (some true) (some true) Direction.left aB))
    (hBE : D.lookupTransition aB none =
      some (transition aB none (some x) Direction.left aP))
    (hP : D.lookupTransition aP none =
      some (transition aP none none Direction.right aH))
    (fldRev run2Rev run1Rev blkRev : Word Bool) (g1 g2 : Nat)
    (hrun2 : run2Rev ≠ []) (hrun1 : run1Rev ≠ [])
    (R : List (Option Bool)) :
    Reaches D
      { state := a0
        tape := tapeSeenLeft
          (List.append (fldRev.map some)
            (none ::
              List.append (List.replicate g2 none)
                (List.append (run2Rev.map some)
                  (none ::
                    List.append (List.replicate g1 none)
                      (List.append (run1Rev.map some)
                        (none ::
                          List.append (blkRev.map some) (none :: []))))))) R }
      { state := aH
        tape := tapeAtCells [none]
          (some x ::
            List.append (blkRev.reverse.map some)
              (none ::
                List.append (run1Rev.reverse.map some)
                  (List.append (List.replicate g1 none)
                    (none ::
                      List.append (run2Rev.reverse.map some)
                        (List.append (List.replicate g2 none)
                          (none ::
                            List.append (fldRev.reverse.map some) R)))))) } := by
  have s1 := crossBitsLeftThenLeft (D := D) h0F h0T h0E fldRev
    (List.append (List.replicate g2 none)
      (List.append (run2Rev.map some)
        (none ::
          List.append (List.replicate g1 none)
            (List.append (run1Rev.map some)
              (none :: List.append (blkRev.map some) (none :: []))))))
    R
  have s2 := crossBlanksBitsLeftThenLeft (D := D)
    hG2N hG2F hG2T hR2F hR2T hR2E g2 run2Rev hrun2
    (List.append (List.replicate g1 none)
      (List.append (run1Rev.map some)
        (none :: List.append (blkRev.map some) (none :: []))))
    (none :: List.append (fldRev.reverse.map some) R)
  have s3 := crossBlanksBitsLeftThenLeft (D := D)
    hG1N hG1F hG1T hR1F hR1T hR1E g1 run1Rev hrun1
    (List.append (blkRev.map some) (none :: []))
    (none ::
      List.append (run2Rev.reverse.map some)
        (List.append (List.replicate g2 none)
          (none :: List.append (fldRev.reverse.map some) R)))
  have s4 := deliverLeft (D := D) (x := x) hBF hBT hBE blkRev []
    (none ::
      List.append (run1Rev.reverse.map some)
        (List.append (List.replicate g1 none)
          (none ::
            List.append (run2Rev.reverse.map some)
              (List.append (List.replicate g2 none)
                (none :: List.append (fldRev.reverse.map some) R)))))
  have s5 := parkRight (D := D) hP []
    (some x ::
      List.append (blkRev.reverse.map some)
        (none ::
          List.append (run1Rev.reverse.map some)
            (List.append (List.replicate g1 none)
              (none ::
                List.append (run2Rev.reverse.map some)
                  (List.append (List.replicate g2 none)
                    (none :: List.append (fldRev.reverse.map some) R))))))
  refine (s1.trans (s2.trans (s3.trans (s4.trans (Reaches.trans ?_ s5)))))
  exact Reaches.of_eq (by rfl)

/--
Carry a pulled bit left across a field remainder, one gap/run pair, and the
cell-0 sentinel, prepend it at the block's left edge, and park on the written
cell.
-/
theorem carryJ1_run
    {D : MachineDescription}
    {a0 aG1 aR1 aB aP aH : Nat} (x : Bool)
    (h0F : D.lookupTransition a0 (some false) =
      some (transition a0 (some false) (some false) Direction.left a0))
    (h0T : D.lookupTransition a0 (some true) =
      some (transition a0 (some true) (some true) Direction.left a0))
    (h0E : D.lookupTransition a0 none =
      some (transition a0 none none Direction.left aG1))
    (hG1N : D.lookupTransition aG1 none =
      some (transition aG1 none none Direction.left aG1))
    (hG1F : D.lookupTransition aG1 (some false) =
      some (transition aG1 (some false) (some false) Direction.left aR1))
    (hG1T : D.lookupTransition aG1 (some true) =
      some (transition aG1 (some true) (some true) Direction.left aR1))
    (hR1F : D.lookupTransition aR1 (some false) =
      some (transition aR1 (some false) (some false) Direction.left aR1))
    (hR1T : D.lookupTransition aR1 (some true) =
      some (transition aR1 (some true) (some true) Direction.left aR1))
    (hR1E : D.lookupTransition aR1 none =
      some (transition aR1 none none Direction.left aB))
    (hBF : D.lookupTransition aB (some false) =
      some (transition aB (some false) (some false) Direction.left aB))
    (hBT : D.lookupTransition aB (some true) =
      some (transition aB (some true) (some true) Direction.left aB))
    (hBE : D.lookupTransition aB none =
      some (transition aB none (some x) Direction.left aP))
    (hP : D.lookupTransition aP none =
      some (transition aP none none Direction.right aH))
    (fldRev run1Rev blkRev : Word Bool) (g1 : Nat)
    (hrun1 : run1Rev ≠ [])
    (R : List (Option Bool)) :
    Reaches D
      { state := a0
        tape := tapeSeenLeft
          (List.append (fldRev.map some)
            (none ::
              List.append (List.replicate g1 none)
                (List.append (run1Rev.map some)
                  (none ::
                    List.append (blkRev.map some) (none :: []))))) R }
      { state := aH
        tape := tapeAtCells [none]
          (some x ::
            List.append (blkRev.reverse.map some)
              (none ::
                List.append (run1Rev.reverse.map some)
                  (List.append (List.replicate g1 none)
                    (none ::
                      List.append (fldRev.reverse.map some) R)))) } := by
  have s1 := crossBitsLeftThenLeft (D := D) h0F h0T h0E fldRev
    (List.append (List.replicate g1 none)
      (List.append (run1Rev.map some)
        (none :: List.append (blkRev.map some) (none :: []))))
    R
  have s2 := crossBlanksBitsLeftThenLeft (D := D)
    hG1N hG1F hG1T hR1F hR1T hR1E g1 run1Rev hrun1
    (List.append (blkRev.map some) (none :: []))
    (none :: List.append (fldRev.reverse.map some) R)
  have s3 := deliverLeft (D := D) (x := x) hBF hBT hBE blkRev []
    (none ::
      List.append (run1Rev.reverse.map some)
        (List.append (List.replicate g1 none)
          (none :: List.append (fldRev.reverse.map some) R)))
  have s4 := parkRight (D := D) hP []
    (some x ::
      List.append (blkRev.reverse.map some)
        (none ::
          List.append (run1Rev.reverse.map some)
            (List.append (List.replicate g1 none)
              (none :: List.append (fldRev.reverse.map some) R))))
  refine s1.trans (s2.trans (s3.trans (Reaches.trans ?_ s4)))
  exact Reaches.of_eq (by rfl)

/-- Cross a blank run leftward without exiting. -/
theorem crossBlanksLeftNoExit
    {D : MachineDescription} {s : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.left s))
    (g : Nat) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeSeenLeft (List.append (List.replicate g none) L) R }
      { state := s
        tape := tapeSeenLeft L (List.append (List.replicate g none) R) } := by
  induction g generalizing R with
  | zero => exact Reaches.of_eq rfl
  | succ k ih =>
      have hstep : Reaches D
          { state := s
            tape := tapeSeenLeft
              (List.append (List.replicate (k + 1) none) L) R }
          { state := s
            tape := tapeSeenLeft
              (List.append (List.replicate k none) L) (none :: R) } := by
        have := stepBlankLeft (D := D) hN
          (List.append (List.replicate k none) L) R
        simpa [List.replicate_succ] using this
      refine hstep.trans ((ih (none :: R)).trans (Reaches.of_eq ?_))
      congr 1
      exact congrArg (tapeSeenLeft L)
        (by simpa [List.append_eq] using replicate_none_append_cons k R)

/--
Carry a pulled bit left across a field remainder and two gap/run pairs to an
empty block: the first delivery writes the block's first bit one cell left of
the cell-0 sentinel.
-/
theorem carryJ2First_run
    {D : MachineDescription}
    {a0 aG2 aR2 aG1 aR1 aB aP aH : Nat} (x : Bool)
    (h0F : D.lookupTransition a0 (some false) =
      some (transition a0 (some false) (some false) Direction.left a0))
    (h0T : D.lookupTransition a0 (some true) =
      some (transition a0 (some true) (some true) Direction.left a0))
    (h0E : D.lookupTransition a0 none =
      some (transition a0 none none Direction.left aG2))
    (hG2N : D.lookupTransition aG2 none =
      some (transition aG2 none none Direction.left aG2))
    (hG2F : D.lookupTransition aG2 (some false) =
      some (transition aG2 (some false) (some false) Direction.left aR2))
    (hG2T : D.lookupTransition aG2 (some true) =
      some (transition aG2 (some true) (some true) Direction.left aR2))
    (hR2F : D.lookupTransition aR2 (some false) =
      some (transition aR2 (some false) (some false) Direction.left aR2))
    (hR2T : D.lookupTransition aR2 (some true) =
      some (transition aR2 (some true) (some true) Direction.left aR2))
    (hR2E : D.lookupTransition aR2 none =
      some (transition aR2 none none Direction.left aG1))
    (hG1N : D.lookupTransition aG1 none =
      some (transition aG1 none none Direction.left aG1))
    (hG1F : D.lookupTransition aG1 (some false) =
      some (transition aG1 (some false) (some false) Direction.left aR1))
    (hG1T : D.lookupTransition aG1 (some true) =
      some (transition aG1 (some true) (some true) Direction.left aR1))
    (hR1F : D.lookupTransition aR1 (some false) =
      some (transition aR1 (some false) (some false) Direction.left aR1))
    (hR1T : D.lookupTransition aR1 (some true) =
      some (transition aR1 (some true) (some true) Direction.left aR1))
    (hR1E : D.lookupTransition aR1 none =
      some (transition aR1 none none Direction.left aB))
    (hBE : D.lookupTransition aB none =
      some (transition aB none (some x) Direction.left aP))
    (hP : D.lookupTransition aP none =
      some (transition aP none none Direction.right aH))
    (hBF : D.lookupTransition aB (some false) =
      some (transition aB (some false) (some false) Direction.left aB))
    (hBT : D.lookupTransition aB (some true) =
      some (transition aB (some true) (some true) Direction.left aB))
    (fldRev run2Rev run1Rev : Word Bool) (g1 g2 : Nat)
    (hrun2 : run2Rev ≠ []) (hrun1 : run1Rev ≠ [])
    (R : List (Option Bool)) :
    Reaches D
      { state := a0
        tape := tapeSeenLeft
          (List.append (fldRev.map some)
            (none ::
              List.append (List.replicate g2 none)
                (List.append (run2Rev.map some)
                  (none ::
                    List.append (List.replicate g1 none)
                      (List.append (run1Rev.map some) (none :: [])))))) R }
      { state := aH
        tape := tapeAtCells [none]
          (some x ::
            none ::
              List.append (run1Rev.reverse.map some)
                (List.append (List.replicate g1 none)
                  (none ::
                    List.append (run2Rev.reverse.map some)
                      (List.append (List.replicate g2 none)
                        (none ::
                          List.append (fldRev.reverse.map some) R))))) } := by
  have s1 := crossBitsLeftThenLeft (D := D) h0F h0T h0E fldRev
    (List.append (List.replicate g2 none)
      (List.append (run2Rev.map some)
        (none ::
          List.append (List.replicate g1 none)
            (List.append (run1Rev.map some) (none :: [])))))
    R
  have s2 := crossBlanksBitsLeftThenLeft (D := D)
    hG2N hG2F hG2T hR2F hR2T hR2E g2 run2Rev hrun2
    (List.append (List.replicate g1 none)
      (List.append (run1Rev.map some) (none :: [])))
    (none :: List.append (fldRev.reverse.map some) R)
  have s3 := crossBlanksBitsLeftThenLeft (D := D)
    hG1N hG1F hG1T hR1F hR1T hR1E g1 run1Rev hrun1
    []
    (none ::
      List.append (run2Rev.reverse.map some)
        (List.append (List.replicate g2 none)
          (none :: List.append (fldRev.reverse.map some) R)))
  have s4 := deliverLeft (D := D) (x := x) hBF hBT hBE ([] : Word Bool) []
    (none ::
      List.append (run1Rev.reverse.map some)
        (List.append (List.replicate g1 none)
          (none ::
            List.append (run2Rev.reverse.map some)
              (List.append (List.replicate g2 none)
                (none :: List.append (fldRev.reverse.map some) R)))))
  have s5 := parkRight (D := D) hP []
    (some x ::
      none ::
        List.append (run1Rev.reverse.map some)
          (List.append (List.replicate g1 none)
            (none ::
              List.append (run2Rev.reverse.map some)
                (List.append (List.replicate g2 none)
                  (none :: List.append (fldRev.reverse.map some) R)))))
  refine s1.trans (s2.trans (s3.trans (Reaches.trans (Reaches.of_eq ?_)
    (s4.trans (Reaches.trans (Reaches.of_eq ?_) s5))))) <;> rfl

/--
One pull across two interior runs, from the block's leftmost bit back to the
grown block's leftmost bit.
-/
theorem pullOneBitJ2_run
    (b1 : Bool) (blkT : Word Bool)
    (r1 : Bool) (run1T : Word Bool) (g1 : Nat)
    (r2 : Bool) (run2T : Word Bool) (g2 : Nat)
    (fld : Word Bool) (x : Bool) (R : List (Option Bool)) :
    Reaches pullOneBitJ2Description
      { state := 0
        tape := tapeAtCells [none]
          (List.append ((b1 :: blkT).map some)
            (none ::
              List.append ((r1 :: run1T).map some)
                (none ::
                  List.append (List.replicate g1 none)
                    (List.append ((r2 :: run2T).map some)
                      (none ::
                        List.append (List.replicate g2 none)
                          (List.append
                            ((List.append fld [x]).map some)
                            (none :: R))))))) }
      { state := 20
        tape := tapeAtCells [none]
          (some x ::
            List.append ((b1 :: blkT).map some)
              (none ::
                List.append ((r1 :: run1T).map some)
                  (List.append (List.replicate g1 none)
                    (none ::
                      List.append ((r2 :: run2T).map some)
                        (List.append (List.replicate g2 none)
                          (none ::
                            List.append (fld.map some)
                              (none :: none :: R))))))) } := by
  have s1 := crossBitsRightThenRight
    (D := pullOneBitJ2Description) (s := 0) (t := 1)
    (by decide) (by decide) (by decide)
    (b1 :: blkT) [none]
    (List.append ((r1 :: run1T).map some)
      (none ::
        List.append (List.replicate g1 none)
          (List.append ((r2 :: run2T).map some)
            (none ::
              List.append (List.replicate g2 none)
                (List.append ((List.append fld [x]).map some)
                  (none :: R))))))
  have s2 := crossBitsRightThenRight
    (D := pullOneBitJ2Description) (s := 1) (t := 2)
    (by decide) (by decide) (by decide)
    (r1 :: run1T)
    (none :: List.append ((b1 :: blkT).reverse.map some) [none])
    (List.append (List.replicate g1 none)
      (List.append ((r2 :: run2T).map some)
        (none ::
          List.append (List.replicate g2 none)
            (List.append ((List.append fld [x]).map some)
              (none :: R)))))
  have s3 := crossBlanksBitsRightThenRight
    (D := pullOneBitJ2Description) (s := 2) (s2 := 3) (t := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    g1 (r2 :: run2T) (by simp)
    (none ::
      List.append ((r1 :: run1T).reverse.map some)
        (none :: List.append ((b1 :: blkT).reverse.map some) [none]))
    (List.append (List.replicate g2 none)
      (List.append ((List.append fld [x]).map some)
        (none :: R)))
  have s4 := crossBlanksBitsRightThenLeft
    (D := pullOneBitJ2Description) (s := 4) (s2 := 5) (t := 6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    g2 (List.append fld [x]) (by cases fld <;> simp)
    (none ::
      List.append ((r2 :: run2T).reverse.map some)
        (List.append (List.replicate g1 none)
          (none ::
            List.append ((r1 :: run1T).reverse.map some)
              (none :: List.append ((b1 :: blkT).reverse.map some) [none]))))
    R
  -- expose the pulled bit at the head of the left context
  have s4' : Reaches pullOneBitJ2Description
      { state := 6
        tape := tapeSeenLeft
          (List.append ((List.append fld [x]).reverse.map some)
            (List.append (List.replicate g2 none)
              (none ::
                List.append ((r2 :: run2T).reverse.map some)
                  (List.append (List.replicate g1 none)
                    (none ::
                      List.append ((r1 :: run1T).reverse.map some)
                        (none ::
                          List.append ((b1 :: blkT).reverse.map some)
                            [none]))))))
          (none :: R) }
      { state := 6
        tape := tapeSeenLeft
          (some x ::
            List.append (fld.reverse.map some)
              (none ::
                List.append (List.replicate g2 none)
                  (List.append ((r2 :: run2T).reverse.map some)
                    (none ::
                      List.append (List.replicate g1 none)
                        (List.append ((r1 :: run1T).reverse.map some)
                          (none ::
                            List.append ((b1 :: blkT).reverse.map some)
                              (none :: [])))))))
          (none :: R) } := by
    refine Reaches.of_eq ?_
    simp only [Configuration.mk.injEq, true_and]
    congr 1
    simp [List.append_eq, List.reverse_append, List.append_assoc,
      replicate_none_comm']
  cases x with
  | false =>
      have s5 := pullStepLeft
        (D := pullOneBitJ2Description) (s := 6) (t := 7) (x := false)
        (by decide)
        (List.append (fld.reverse.map some)
          (none ::
            List.append (List.replicate g2 none)
              (List.append ((r2 :: run2T).reverse.map some)
                (none ::
                  List.append (List.replicate g1 none)
                    (List.append ((r1 :: run1T).reverse.map some)
                      (none ::
                        List.append ((b1 :: blkT).reverse.map some)
                          (none :: [])))))))
        (none :: R)
      have s6 := carryJ2_run
        (D := pullOneBitJ2Description)
        (a0 := 7) (aG2 := 9) (aR2 := 11) (aG1 := 13) (aR1 := 15)
        (aB := 17) (aP := 19) (aH := 20) (x := false)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        fld.reverse (r2 :: run2T).reverse (r1 :: run1T).reverse
        (b1 :: blkT).reverse g1 g2
        (by intro h; simpa using congrArg List.length h)
        (by intro h; simpa using congrArg List.length h)
        (none :: none :: R)
      refine (s1.trans (s2.trans (s3.trans (s4.trans (s4'.trans
        (s5.trans (Reaches.trans (Reaches.of_eq ?_) (s6.trans
          (Reaches.of_eq ?_))))))))) <;>
        first
          | rfl
          | (congr 1
             simp [List.append_eq, List.reverse_reverse, List.reverse_append,
               replicate_none_comm'])
  | true =>
      have s5 := pullStepLeft
        (D := pullOneBitJ2Description) (s := 6) (t := 8) (x := true)
        (by decide)
        (List.append (fld.reverse.map some)
          (none ::
            List.append (List.replicate g2 none)
              (List.append ((r2 :: run2T).reverse.map some)
                (none ::
                  List.append (List.replicate g1 none)
                    (List.append ((r1 :: run1T).reverse.map some)
                      (none ::
                        List.append ((b1 :: blkT).reverse.map some)
                          (none :: [])))))))
        (none :: R)
      have s6 := carryJ2_run
        (D := pullOneBitJ2Description)
        (a0 := 8) (aG2 := 10) (aR2 := 12) (aG1 := 14) (aR1 := 16)
        (aB := 18) (aP := 19) (aH := 20) (x := true)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        fld.reverse (r2 :: run2T).reverse (r1 :: run1T).reverse
        (b1 :: blkT).reverse g1 g2
        (by intro h; simpa using congrArg List.length h)
        (by intro h; simpa using congrArg List.length h)
        (none :: none :: R)
      refine (s1.trans (s2.trans (s3.trans (s4.trans (s4'.trans
        (s5.trans (Reaches.trans (Reaches.of_eq ?_) (s6.trans
          (Reaches.of_eq ?_))))))))) <;>
        first
          | rfl
          | (congr 1
             simp [List.append_eq, List.reverse_reverse, List.reverse_append,
               replicate_none_comm'])

/-- One pull across one interior run, from the block's leftmost bit. -/
theorem pullOneBitJ1_run
    (b1 : Bool) (blkT : Word Bool)
    (r1 : Bool) (run1T : Word Bool) (g1 : Nat)
    (fld : Word Bool) (x : Bool) (R : List (Option Bool)) :
    Reaches pullOneBitJ1Description
      { state := 0
        tape := tapeAtCells [none]
          (List.append ((b1 :: blkT).map some)
            (none ::
              List.append ((r1 :: run1T).map some)
                (none ::
                  List.append (List.replicate g1 none)
                    (List.append ((List.append fld [x]).map some)
                      (none :: R))))) }
      { state := 14
        tape := tapeAtCells [none]
          (some x ::
            List.append ((b1 :: blkT).map some)
              (none ::
                List.append ((r1 :: run1T).map some)
                  (List.append (List.replicate g1 none)
                    (none ::
                      List.append (fld.map some)
                        (none :: none :: R))))) } := by
  have s1 := crossBitsRightThenRight
    (D := pullOneBitJ1Description) (s := 0) (t := 1)
    (by decide) (by decide) (by decide)
    (b1 :: blkT) [none]
    (List.append ((r1 :: run1T).map some)
      (none ::
        List.append (List.replicate g1 none)
          (List.append ((List.append fld [x]).map some) (none :: R))))
  have s2 := crossBitsRightThenRight
    (D := pullOneBitJ1Description) (s := 1) (t := 2)
    (by decide) (by decide) (by decide)
    (r1 :: run1T)
    (none :: List.append ((b1 :: blkT).reverse.map some) [none])
    (List.append (List.replicate g1 none)
      (List.append ((List.append fld [x]).map some) (none :: R)))
  have s3 := crossBlanksBitsRightThenLeft
    (D := pullOneBitJ1Description) (s := 2) (s2 := 3) (t := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    g1 (List.append fld [x]) (by cases fld <;> simp)
    (none ::
      List.append ((r1 :: run1T).reverse.map some)
        (none :: List.append ((b1 :: blkT).reverse.map some) [none]))
    R
  have s3' : Reaches pullOneBitJ1Description
      { state := 4
        tape := tapeSeenLeft
          (List.append ((List.append fld [x]).reverse.map some)
            (List.append (List.replicate g1 none)
              (none ::
                List.append ((r1 :: run1T).reverse.map some)
                  (none ::
                    List.append ((b1 :: blkT).reverse.map some)
                      [none]))))
          (none :: R) }
      { state := 4
        tape := tapeSeenLeft
          (some x ::
            List.append (fld.reverse.map some)
              (none ::
                List.append (List.replicate g1 none)
                  (List.append ((r1 :: run1T).reverse.map some)
                    (none ::
                      List.append ((b1 :: blkT).reverse.map some)
                        (none :: [])))))
          (none :: R) } := by
    refine Reaches.of_eq ?_
    simp only [Configuration.mk.injEq, true_and]
    congr 1
    simp [List.append_eq, List.reverse_append, List.append_assoc,
      replicate_none_comm']
  cases x with
  | false =>
      have s4 := pullStepLeft
        (D := pullOneBitJ1Description) (s := 4) (t := 5) (x := false)
        (by decide)
        (List.append (fld.reverse.map some)
          (none ::
            List.append (List.replicate g1 none)
              (List.append ((r1 :: run1T).reverse.map some)
                (none ::
                  List.append ((b1 :: blkT).reverse.map some)
                    (none :: [])))))
        (none :: R)
      have s5 := carryJ1_run
        (D := pullOneBitJ1Description)
        (a0 := 5) (aG1 := 7) (aR1 := 9)
        (aB := 11) (aP := 13) (aH := 14) (x := false)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        fld.reverse (r1 :: run1T).reverse (b1 :: blkT).reverse g1
        (by intro h; simpa using congrArg List.length h)
        (none :: none :: R)
      refine (s1.trans (s2.trans (s3.trans (s3'.trans
        (s4.trans (Reaches.trans (Reaches.of_eq ?_) (s5.trans
          (Reaches.of_eq ?_)))))))) <;>
        first
          | rfl
          | (congr 1
             simp [List.append_eq, List.reverse_reverse, List.reverse_append,
               replicate_none_comm'])
  | true =>
      have s4 := pullStepLeft
        (D := pullOneBitJ1Description) (s := 4) (t := 6) (x := true)
        (by decide)
        (List.append (fld.reverse.map some)
          (none ::
            List.append (List.replicate g1 none)
              (List.append ((r1 :: run1T).reverse.map some)
                (none ::
                  List.append ((b1 :: blkT).reverse.map some)
                    (none :: [])))))
        (none :: R)
      have s5 := carryJ1_run
        (D := pullOneBitJ1Description)
        (a0 := 6) (aG1 := 8) (aR1 := 10)
        (aB := 12) (aP := 13) (aH := 14) (x := true)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        fld.reverse (r1 :: run1T).reverse (b1 :: blkT).reverse g1
        (by intro h; simpa using congrArg List.length h)
        (none :: none :: R)
      refine (s1.trans (s2.trans (s3.trans (s3'.trans
        (s4.trans (Reaches.trans (Reaches.of_eq ?_) (s5.trans
          (Reaches.of_eq ?_)))))))) <;>
        first
          | rfl
          | (congr 1
             simp [List.append_eq, List.reverse_reverse, List.reverse_append,
               replicate_none_comm'])

/-- Bit-run crossing leftward to the window edge, exiting on the phantom
blank beyond the leftmost cell. -/
theorem runConfig_bitsRun_exitBlank_left_edge
    {D : MachineDescription} {s : Nat}
    {w : Option Bool} {d : Direction} {t : Nat}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s))
    (hExit : D.lookupTransition s none =
      some (transition s none w d t))
    (revBits : Word Bool) (R : List (Option Bool)) :
    D.runConfig (revBits.length + 1)
        { state := s
          tape := tapeSeenLeft (revBits.map some) R } =
      { state := t
        tape := Tape.move d (Tape.write w
          (tapeSeenLeft []
            (List.append (revBits.reverse.map some) R))) } := by
  induction revBits generalizing R with
  | nil =>
      simpa [tapeSeenLeft] using
        runConfig_one hExit (tapeSeenLeft [] R) rfl
  | cons b rest ih =>
      have hstep :
          D.runConfig 1
              { state := s
                tape := tapeSeenLeft ((b :: rest).map some) R } =
            { state := s
              tape := tapeSeenLeft (rest.map some) (some b :: R) } := by
        cases b <;> cases rest <;>
          simp [MachineDescription.runConfig, MachineDescription.stepConfig,
            hF, hT, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, tapeSeenLeft]
      have hlen : ((b :: rest) : Word Bool).length + 1 =
          1 + (rest.length + 1) := by
        simp [List.length_cons]
        lia
      rw [hlen, MachineDescription.runConfig_add, hstep, ih (some b :: R)]
      simp [List.append_assoc]

/-- Delivery at the window edge, stepping further left onto the phantom. -/
theorem deliverLeftEdge
    {D : MachineDescription} {s t : Nat} {x : Bool}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s))
    (hExit : D.lookupTransition s none =
      some (transition s none (some x) Direction.left t))
    (revBits : Word Bool) (R : List (Option Bool)) :
    Reaches D
      { state := s, tape := tapeSeenLeft (revBits.map some) R }
      { state := t
        tape := tapeSeenLeft []
          (some x :: List.append (revBits.reverse.map some) R) } :=
  Reaches.of_run (by
    have := runConfig_bitsRun_exitBlank_left_edge hF hT hExit revBits R
    rwa [show Tape.move Direction.left (Tape.write (some x)
        (tapeSeenLeft [] (List.append (revBits.reverse.map some) R))) =
      tapeSeenLeft [] (some x :: List.append (revBits.reverse.map some) R)
      from rfl] at this)

/-- Delivery at the window edge, stepping back right onto the old block. -/
theorem deliverRightEdge
    {D : MachineDescription} {s t : Nat} {x : Bool}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s))
    (hExit : D.lookupTransition s none =
      some (transition s none (some x) Direction.right t))
    (revBits : Word Bool) (R : List (Option Bool)) :
    Reaches D
      { state := s, tape := tapeSeenLeft (revBits.map some) R }
      { state := t
        tape := tapeAtCells [some x]
          (List.append (revBits.reverse.map some) R) } :=
  Reaches.of_run (by
    have := runConfig_bitsRun_exitBlank_left_edge hF hT hExit revBits R
    rwa [show Tape.move Direction.right (Tape.write (some x)
        (tapeSeenLeft [] (List.append (revBits.reverse.map some) R))) =
      tapeAtCells [some x] (List.append (revBits.reverse.map some) R)
      from by cases hr : List.append (revBits.reverse.map some) R <;>
        simp [tapeSeenLeft, tapeAtCells, Tape.move, Tape.moveRight,
          Tape.write]] at this)

theorem replicate_none_append_cons' (n : Nat) (X : List (Option Bool)) :
    (List.replicate n (none : Option Bool)) ++ (none :: X) =
      (List.replicate (n + 1) (none : Option Bool)) ++ X := by
  simpa [List.append_eq] using replicate_none_append_cons n X

theorem none_cons_replicate_append (n : Nat) (X : List (Option Bool)) :
    (none :: (List.replicate n (none : Option Bool) ++ X)) =
      List.replicate (n + 1) (none : Option Bool) ++ X := by
  simp [List.replicate_succ]

/-- Bit-run crossing rightward whose exit steps back left onto the run's
last cell. -/
theorem crossBitsRightThenLeft
    {D : MachineDescription} {s t : Nat}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.right s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.right s))
    (hExit : D.lookupTransition s none =
      some (transition s none none Direction.left t))
    (bits : Word Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeAtCells L (List.append (bits.map some) (none :: R)) }
      { state := t
        tape := tapeSeenLeft
          (List.append (bits.reverse.map some) L) (none :: R) } :=
  Reaches.of_run (by
    have := runConfig_bitsRun_exitBlank_right hF hT hExit bits L R
    rwa [move_left_write_tapeAtCells] at this)

/--
Main loop of the one-interior-run pull machine, stated at the pull position
with the window edge immediately left of the block.
-/
theorem pullLoopJ1_loop
    (g1 : Nat) (run1Rev : Word Bool) (hrun1 : run1Rev ≠ [])
    (fldRev : Word Bool) :
    forall (x : Bool) (blkRev : Word Bool) (R : List (Option Bool)),
    Reaches pullLoopJ1Description
      { state := 4
        tape := tapeSeenLeft
          (some x ::
            List.append (fldRev.map some)
              (none ::
                List.append (List.replicate g1 none)
                  (List.append (run1Rev.map some)
                    (none :: blkRev.map some)))) R }
      { state := 26
        tape := tapeAtCells [none]
          (List.append (fldRev.reverse.map some)
            (some x ::
              List.append (blkRev.reverse.map some)
                (none ::
                  List.append (run1Rev.reverse.map some)
                    (List.append (List.replicate g1 none)
                      (none ::
                        List.append (List.replicate fldRev.length none)
                          (none :: R)))))) } := by
  induction fldRev with
  | nil =>
      intro x blkRev R
      have s1 := pullStepLeft
        (D := pullLoopJ1Description) (s := 4)
        (t := if x then 6 else 5) (x := x)
        (by cases x <;> decide)
        (List.append (List.map some [])
          (none ::
            List.append (List.replicate g1 none)
              (List.append (run1Rev.map some)
                (none :: blkRev.map some))))
        R
      have s2 := stepBlankLeft
        (D := pullLoopJ1Description) (s := if x then 6 else 5)
        (t := if x then 20 else 19)
        (by cases x <;> decide)
        (List.append (List.replicate g1 none)
          (List.append (run1Rev.map some)
            (none :: blkRev.map some)))
        (none :: R)
      have s3 := crossBlanksBitsLeftThenLeft
        (D := pullLoopJ1Description)
        (s := if x then 20 else 19) (s2 := if x then 22 else 21)
        (t := if x then 24 else 23)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide) (by cases x <;> decide)
        g1 run1Rev hrun1
        (blkRev.map some)
        (none :: none :: R)
      have s4 := deliverLeftEdge
        (D := pullLoopJ1Description)
        (s := if x then 24 else 23) (t := 25) (x := x)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide)
        blkRev
        (none ::
          List.append (run1Rev.reverse.map some)
            (List.append (List.replicate g1 none) (none :: none :: R)))
      have s5 := parkRight
        (D := pullLoopJ1Description) (s := 25) (t := 26)
        (by decide) []
        (some x ::
          List.append (blkRev.reverse.map some)
            (none ::
              List.append (run1Rev.reverse.map some)
                (List.append (List.replicate g1 none)
                  (none :: none :: R))))
      refine (Reaches.trans (Reaches.of_eq ?_)
        (s1.trans ((Reaches.trans (Reaches.of_eq ?_)
          (s2.trans (s3.trans (s4.trans
            (Reaches.trans (Reaches.of_eq ?_)
              (s5.trans (Reaches.of_eq ?_)))))))))) <;>
        first
          | rfl
          | (congr 1
             simp [List.append_eq, List.append_assoc])
  | cons y rest ih =>
      intro x blkRev R
      have s1 := pullStepLeft
        (D := pullLoopJ1Description) (s := 4)
        (t := if x then 6 else 5) (x := x)
        (by cases x <;> decide)
        (List.append ((y :: rest).map some)
          (none ::
            List.append (List.replicate g1 none)
              (List.append (run1Rev.map some)
                (none :: blkRev.map some))))
        R
      have s2 := stepBitLeftAny
        (D := pullLoopJ1Description) (s := if x then 6 else 5)
        (t := if x then 8 else 7)
        (by cases x <;> decide) (by cases x <;> decide)
        y
        (List.append (rest.map some)
          (none ::
            List.append (List.replicate g1 none)
              (List.append (run1Rev.map some)
                (none :: blkRev.map some))))
        (none :: R)
      have s3 := crossBitsLeftThenLeft
        (D := pullLoopJ1Description)
        (s := if x then 8 else 7) (t := if x then 10 else 9)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide)
        rest
        (List.append (List.replicate g1 none)
          (List.append (run1Rev.map some)
            (none :: blkRev.map some)))
        (some y :: none :: R)
      have s4 := crossBlanksBitsLeftThenLeft
        (D := pullLoopJ1Description)
        (s := if x then 10 else 9) (s2 := if x then 12 else 11)
        (t := if x then 14 else 13)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide) (by cases x <;> decide)
        g1 run1Rev hrun1
        (blkRev.map some)
        (none :: List.append (rest.reverse.map some) (some y :: none :: R))
      have s5 := deliverRightEdge
        (D := pullLoopJ1Description)
        (s := if x then 14 else 13) (t := 15) (x := x)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide)
        blkRev
        (none ::
          List.append (run1Rev.reverse.map some)
            (List.append (List.replicate g1 none)
              (none ::
                List.append (rest.reverse.map some)
                  (some y :: none :: R))))
      have s6 := crossBitsRightThenRight
        (D := pullLoopJ1Description) (s := 15) (t := 16)
        (by decide) (by decide) (by decide)
        blkRev.reverse [some x]
        (List.append (run1Rev.reverse.map some)
          (List.append (List.replicate g1 none)
            (none ::
              List.append (rest.reverse.map some)
                (some y :: none :: R))))
      have s7 := crossBitsRightThenRight
        (D := pullLoopJ1Description) (s := 16) (t := 17)
        (by decide) (by decide) (by decide)
        run1Rev.reverse
        (none :: List.append (blkRev.reverse.reverse.map some) [some x])
        (List.append (List.replicate g1 none)
          (List.append ((List.append rest.reverse [y]).map some)
            (none :: R)))
      have s8 := runConfig_blanksThenBits_exitBlank_right
        (D := pullLoopJ1Description) (s := 17) (s2 := 18)
        (w := none) (d := Direction.left) (t := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
        g1 (List.append rest.reverse [y])
        (by cases rest.reverse <;> simp)
        (none ::
          List.append (run1Rev.reverse.reverse.map some)
            (none ::
              List.append (blkRev.reverse.reverse.map some) [some x]))
        R
      have s8' : Reaches pullLoopJ1Description
          { state := 17
            tape := tapeAtCells
              (none ::
                List.append (run1Rev.reverse.reverse.map some)
                  (none ::
                    List.append (blkRev.reverse.reverse.map some) [some x]))
              (List.append (List.replicate g1 none)
                (List.append ((List.append rest.reverse [y]).map some)
                  (none :: R))) }
          { state := 4
            tape := tapeSeenLeft
              (List.append
                ((List.append rest.reverse [y]).reverse.map some)
                (List.append (List.replicate g1 none)
                  (none ::
                    List.append (run1Rev.reverse.reverse.map some)
                      (none ::
                        List.append (blkRev.reverse.reverse.map some)
                          [some x]))))
              (none :: R) } :=
        by
          rw [move_left_write_tapeAtCells] at s8
          exact Reaches.of_run s8
      have sloop := ih y (List.append blkRev [x]) (none :: R)
      refine s1.trans (Reaches.trans (Reaches.of_eq ?_)
        (s2.trans (s3.trans (s4.trans (s5.trans
          (Reaches.trans (Reaches.of_eq ?_)
            (s6.trans (Reaches.trans (Reaches.of_eq ?_)
              (s7.trans (s8'.trans (Reaches.trans (Reaches.of_eq ?_)
                (sloop.trans (Reaches.of_eq ?_))))))))))))) <;>
        first
          | rfl
          | (congr 1
             simp [List.append_eq, List.reverse_reverse, List.reverse_append,
               List.append_assoc, replicate_none_append_cons',
               none_cons_replicate_append])

/--
Full run of the one-interior-run pull loop machine: from the block's leftmost
bit, pull the entire field beyond {name}`run1` and prepend it to the block.  The
pulled field is presented through its reversed decomposition
{lean}`x0 :: y0 :: fldRest` (fields pulled by this machine always have at
least two bits).
-/
theorem pullLoopJ1_run
    (b1 : Bool) (blkT : Word Bool)
    (run1 : Word Bool) (hrun1 : run1 ≠ [])
    (g1 : Nat) (x0 y0 : Bool) (fldRest : Word Bool)
    (R : List (Option Bool)) :
    Reaches pullLoopJ1Description
      { state := 0
        tape := tapeAtCells [none]
          (List.append ((b1 :: blkT).map some)
            (none ::
              List.append (run1.map some)
                (none ::
                  List.append (List.replicate g1 none)
                    (List.append
                      (((x0 :: y0 :: fldRest).reverse).map some)
                      (none :: R))))) }
      { state := 26
        tape := tapeAtCells [none]
          (List.append (fldRest.reverse.map some)
            (some y0 :: some x0 ::
              List.append ((b1 :: blkT).map some)
                (none ::
                  List.append (run1.map some)
                    (List.append (List.replicate g1 none)
                      (none ::
                        List.append
                          (List.replicate (fldRest.length + 2) none)
                          (none :: R)))))) } := by
  have hrun1Rev : run1.reverse ≠ [] := by
    intro h
    apply hrun1
    unfold Word
    simpa using congrArg List.reverse h
  have s1 := crossBitsRightThenRight
    (D := pullLoopJ1Description) (s := 0) (t := 1)
    (by decide) (by decide) (by decide)
    (b1 :: blkT) [none]
    (List.append (run1.map some)
      (none ::
        List.append (List.replicate g1 none)
          (List.append (((x0 :: y0 :: fldRest).reverse).map some)
            (none :: R))))
  have s2 := crossBitsRightThenRight
    (D := pullLoopJ1Description) (s := 1) (t := 2)
    (by decide) (by decide) (by decide)
    run1
    (none :: List.append ((b1 :: blkT).reverse.map some) [none])
    (List.append (List.replicate g1 none)
      (List.append (((x0 :: y0 :: fldRest).reverse).map some)
        (none :: R)))
  have s3 := crossBlanksBitsRightThenLeft
    (D := pullLoopJ1Description) (s := 2) (s2 := 3) (t := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    g1 ((x0 :: y0 :: fldRest).reverse)
    (by intro h; simpa using congrArg List.length h)
    (none ::
      List.append (run1.reverse.map some)
        (none :: List.append ((b1 :: blkT).reverse.map some) [none]))
    R
  have s4 := pullStepLeft
    (D := pullLoopJ1Description) (s := 4)
    (t := if x0 then 6 else 5) (x := x0)
    (by cases x0 <;> decide)
    (List.append ((y0 :: fldRest).map some)
      (none ::
        List.append (List.replicate g1 none)
          (List.append (run1.reverse.map some)
            (none ::
              List.append ((b1 :: blkT).reverse.map some) (none :: [])))))
    (none :: R)
  have s5 := stepBitLeftAny
    (D := pullLoopJ1Description) (s := if x0 then 6 else 5)
    (t := if x0 then 8 else 7)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    y0
    (List.append (fldRest.map some)
      (none ::
        List.append (List.replicate g1 none)
          (List.append (run1.reverse.map some)
            (none ::
              List.append ((b1 :: blkT).reverse.map some) (none :: [])))))
    (none :: none :: R)
  have s6 := crossBitsLeftThenLeft
    (D := pullLoopJ1Description)
    (s := if x0 then 8 else 7) (t := if x0 then 10 else 9)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    (by cases x0 <;> decide)
    fldRest
    (List.append (List.replicate g1 none)
      (List.append (run1.reverse.map some)
        (none ::
          List.append ((b1 :: blkT).reverse.map some) (none :: []))))
    (some y0 :: none :: none :: R)
  have s7 := crossBlanksBitsLeftThenLeft
    (D := pullLoopJ1Description)
    (s := if x0 then 10 else 9) (s2 := if x0 then 12 else 11)
    (t := if x0 then 14 else 13)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    g1 run1.reverse hrun1Rev
    (List.append ((b1 :: blkT).reverse.map some) (none :: []))
    (none ::
      List.append (fldRest.reverse.map some)
        (some y0 :: none :: none :: R))
  have s8 := deliverRight
    (D := pullLoopJ1Description)
    (s := if x0 then 14 else 13) (t := 15) (x := x0)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    (by cases x0 <;> decide)
    ((b1 :: blkT).reverse) []
    (none ::
      List.append (run1.reverse.reverse.map some)
        (List.append (List.replicate g1 none)
          (none ::
            List.append (fldRest.reverse.map some)
              (some y0 :: none :: none :: R))))
  have s9 := crossBitsRightThenRight
    (D := pullLoopJ1Description) (s := 15) (t := 16)
    (by decide) (by decide) (by decide)
    (b1 :: blkT) [some x0]
    (List.append (run1.map some)
      (List.append (List.replicate g1 none)
        (none ::
          List.append (fldRest.reverse.map some)
            (some y0 :: none :: none :: R))))
  have s10 := crossBitsRightThenRight
    (D := pullLoopJ1Description) (s := 16) (t := 17)
    (by decide) (by decide) (by decide)
    run1
    (none :: List.append ((b1 :: blkT).reverse.map some) [some x0])
    (List.append (List.replicate g1 none)
      (List.append (((y0 :: fldRest).reverse).map some)
        (none :: none :: R)))
  have s11 := runConfig_blanksThenBits_exitBlank_right
    (D := pullLoopJ1Description) (s := 17) (s2 := 18)
    (w := none) (d := Direction.left) (t := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    g1 ((y0 :: fldRest).reverse)
    (by intro h; simpa using congrArg List.length h)
    (none ::
      List.append (run1.reverse.map some)
        (none :: List.append ((b1 :: blkT).reverse.map some) [some x0]))
    (none :: R)
  have s11' : Reaches pullLoopJ1Description
      { state := 17
        tape := tapeAtCells
          (none ::
            List.append (run1.reverse.map some)
              (none ::
                List.append ((b1 :: blkT).reverse.map some) [some x0]))
          (List.append (List.replicate g1 none)
            (List.append (((y0 :: fldRest).reverse).map some)
              (none :: none :: R))) }
      { state := 4
        tape := tapeSeenLeft
          (List.append (((y0 :: fldRest).reverse).reverse.map some)
            (List.append (List.replicate g1 none)
              (none ::
                List.append (run1.reverse.map some)
                  (none ::
                    List.append ((b1 :: blkT).reverse.map some)
                      [some x0]))))
          (none :: none :: R) } := by
    rw [move_left_write_tapeAtCells] at s11
    exact Reaches.of_run s11
  have sloop := pullLoopJ1_loop g1 run1.reverse hrun1Rev fldRest
    y0 (List.append ((b1 :: blkT).reverse) [x0]) (none :: none :: R)
  refine s1.trans (s2.trans (s3.trans (Reaches.trans (Reaches.of_eq ?_)
    (s4.trans (Reaches.trans (Reaches.of_eq ?_)
      (s5.trans (s6.trans (s7.trans (Reaches.trans (Reaches.of_eq ?_)
        (s8.trans (Reaches.trans (Reaches.of_eq ?_)
          (s9.trans (Reaches.trans (Reaches.of_eq ?_)
            (s10.trans (s11'.trans (Reaches.trans (Reaches.of_eq ?_)
              (sloop.trans (Reaches.of_eq ?_)))))))))))))))))) <;>
    first
      | rfl
      | (congr 1
         simp [List.append_eq, List.reverse_reverse, List.reverse_append,
           List.append_assoc, replicate_none_append_cons',
           none_cons_replicate_append])

/--
Main loop of the sentinel-adjacent pull machine, stated at the pull position
with the window edge immediately left of the block.
-/
theorem pullLoopJ0_loop
    (fldRev : Word Bool) :
    forall (x : Bool) (blkRev : Word Bool) (R : List (Option Bool)),
    Reaches pullLoopJ0Description
      { state := 2
        tape := tapeSeenLeft
          (some x ::
            List.append (fldRev.map some) (none :: blkRev.map some)) R }
      { state := 14
        tape := tapeAtCells [none]
          (List.append (fldRev.reverse.map some)
            (some x ::
              List.append (blkRev.reverse.map some)
                (none ::
                  List.append (List.replicate fldRev.length none)
                    (none :: R)))) } := by
  induction fldRev with
  | nil =>
      intro x blkRev R
      have s1 := pullStepLeft
        (D := pullLoopJ0Description) (s := 2)
        (t := if x then 4 else 3) (x := x)
        (by cases x <;> decide)
        (List.append (List.map some []) (none :: blkRev.map some))
        R
      have s2 := stepBlankLeft
        (D := pullLoopJ0Description) (s := if x then 4 else 3)
        (t := if x then 12 else 11)
        (by cases x <;> decide)
        (blkRev.map some)
        (none :: R)
      have s3 := deliverLeftEdge
        (D := pullLoopJ0Description)
        (s := if x then 12 else 11) (t := 13) (x := x)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide)
        blkRev
        (none :: none :: R)
      have s4 := parkRight
        (D := pullLoopJ0Description) (s := 13) (t := 14)
        (by decide) []
        (some x ::
          List.append (blkRev.reverse.map some) (none :: none :: R))
      refine s1.trans (Reaches.trans (Reaches.of_eq ?_)
        (s2.trans (s3.trans (Reaches.trans (Reaches.of_eq ?_)
          (s4.trans (Reaches.of_eq ?_)))))) <;>
        first
          | rfl
          | (congr 1
             simp [List.append_eq, List.append_assoc])
  | cons y rest ih =>
      intro x blkRev R
      have s1 := pullStepLeft
        (D := pullLoopJ0Description) (s := 2)
        (t := if x then 4 else 3) (x := x)
        (by cases x <;> decide)
        (List.append ((y :: rest).map some) (none :: blkRev.map some))
        R
      have s2 := stepBitLeftAny
        (D := pullLoopJ0Description) (s := if x then 4 else 3)
        (t := if x then 6 else 5)
        (by cases x <;> decide) (by cases x <;> decide)
        y
        (List.append (rest.map some) (none :: blkRev.map some))
        (none :: R)
      have s3 := crossBitsLeftThenLeft
        (D := pullLoopJ0Description)
        (s := if x then 6 else 5) (t := if x then 8 else 7)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide)
        rest
        (blkRev.map some)
        (some y :: none :: R)
      have s4 := deliverRightEdge
        (D := pullLoopJ0Description)
        (s := if x then 8 else 7) (t := 9) (x := x)
        (by cases x <;> decide) (by cases x <;> decide)
        (by cases x <;> decide)
        blkRev
        (none ::
          List.append (rest.reverse.map some) (some y :: none :: R))
      have s5 := crossBitsRightThenRight
        (D := pullLoopJ0Description) (s := 9) (t := 10)
        (by decide) (by decide) (by decide)
        blkRev.reverse [some x]
        (List.append (((y :: rest).reverse).map some) (none :: R))
      have s6 := crossBitsRightThenLeft
        (D := pullLoopJ0Description) (s := 10) (t := 2)
        (by decide) (by decide) (by decide)
        ((y :: rest).reverse)
        (none :: List.append (blkRev.reverse.reverse.map some) [some x])
        R
      have sloop := ih y (List.append blkRev [x]) (none :: R)
      refine s1.trans (Reaches.trans (Reaches.of_eq ?_)
        (s2.trans (s3.trans (s4.trans (Reaches.trans (Reaches.of_eq ?_)
          (s5.trans (Reaches.trans (Reaches.of_eq ?_)
            (s6.trans (Reaches.trans (Reaches.of_eq ?_)
              (sloop.trans (Reaches.of_eq ?_))))))))))) <;>
        first
          | rfl
          | (congr 1
             simp [List.append_eq, List.reverse_reverse, List.reverse_append,
               List.append_assoc, replicate_none_append_cons',
               none_cons_replicate_append])

/--
Full run of the sentinel-adjacent pull loop machine: from the block's
leftmost bit, pull the entire field between the cell-0 sentinel and the
erased region right of it, prepending it to the block.
-/
theorem pullLoopJ0_run
    (b1 : Bool) (blkT : Word Bool)
    (x0 y0 : Bool) (fldRest : Word Bool)
    (R : List (Option Bool)) :
    Reaches pullLoopJ0Description
      { state := 0
        tape := tapeAtCells [none]
          (List.append ((b1 :: blkT).map some)
            (none ::
              List.append (((x0 :: y0 :: fldRest).reverse).map some)
                (none :: R))) }
      { state := 14
        tape := tapeAtCells [none]
          (List.append (fldRest.reverse.map some)
            (some y0 :: some x0 ::
              List.append ((b1 :: blkT).map some)
                (none ::
                  List.append
                    (List.replicate (fldRest.length + 2) none)
                    (none :: R)))) } := by
  have s1 := crossBitsRightThenRight
    (D := pullLoopJ0Description) (s := 0) (t := 1)
    (by decide) (by decide) (by decide)
    (b1 :: blkT) [none]
    (List.append (((x0 :: y0 :: fldRest).reverse).map some)
      (none :: R))
  have s2 := crossBitsRightThenLeft
    (D := pullLoopJ0Description) (s := 1) (t := 2)
    (by decide) (by decide) (by decide)
    ((x0 :: y0 :: fldRest).reverse)
    (none :: List.append ((b1 :: blkT).reverse.map some) [none])
    R
  have s3 := pullStepLeft
    (D := pullLoopJ0Description) (s := 2)
    (t := if x0 then 4 else 3) (x := x0)
    (by cases x0 <;> decide)
    (List.append ((y0 :: fldRest).map some)
      (none ::
        List.append ((b1 :: blkT).reverse.map some) (none :: [])))
    (none :: R)
  have s4 := stepBitLeftAny
    (D := pullLoopJ0Description) (s := if x0 then 4 else 3)
    (t := if x0 then 6 else 5)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    y0
    (List.append (fldRest.map some)
      (none ::
        List.append ((b1 :: blkT).reverse.map some) (none :: [])))
    (none :: none :: R)
  have s5 := crossBitsLeftThenLeft
    (D := pullLoopJ0Description)
    (s := if x0 then 6 else 5) (t := if x0 then 8 else 7)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    (by cases x0 <;> decide)
    fldRest
    (List.append ((b1 :: blkT).reverse.map some) (none :: []))
    (some y0 :: none :: none :: R)
  have s6 := deliverRight
    (D := pullLoopJ0Description)
    (s := if x0 then 8 else 7) (t := 9) (x := x0)
    (by cases x0 <;> decide) (by cases x0 <;> decide)
    (by cases x0 <;> decide)
    ((b1 :: blkT).reverse) []
    (none ::
      List.append (fldRest.reverse.map some)
        (some y0 :: none :: none :: R))
  have s7 := crossBitsRightThenRight
    (D := pullLoopJ0Description) (s := 9) (t := 10)
    (by decide) (by decide) (by decide)
    (b1 :: blkT) [some x0]
    (List.append (((y0 :: fldRest).reverse).map some)
      (none :: none :: R))
  have s8 := crossBitsRightThenLeft
    (D := pullLoopJ0Description) (s := 10) (t := 2)
    (by decide) (by decide) (by decide)
    ((y0 :: fldRest).reverse)
    (none :: List.append ((b1 :: blkT).reverse.map some) [some x0])
    (none :: R)
  have sloop := pullLoopJ0_loop fldRest
    y0 (List.append ((b1 :: blkT).reverse) [x0]) (none :: none :: R)
  refine s1.trans (s2.trans (Reaches.trans (Reaches.of_eq ?_) (s3.trans (Reaches.trans (Reaches.of_eq ?_) (s4.trans (s5.trans (s6.trans (Reaches.trans (Reaches.of_eq ?_) (s7.trans (s8.trans (Reaches.trans (Reaches.of_eq ?_) (sloop.trans (Reaches.of_eq ?_))))))))))))) <;>
    first
      | rfl
      | (congr 1
         simp [List.append_eq, List.reverse_reverse, List.reverse_append,
           List.append_assoc, replicate_none_append_cons',
           none_cons_replicate_append])

/--
Reject-branch first pull: starting on the rightmost source bit, erase it and
deliver it as the block's first bit.
-/
theorem pullFirstReject_run
    (x : Bool) (fldRev : Word Bool)
    (g2 : Nat) (run2Rev : Word Bool) (hrun2 : run2Rev ≠ [])
    (g1 : Nat) (run1Rev : Word Bool) (hrun1 : run1Rev ≠ [])
    (R : List (Option Bool)) :
    Reaches pullFirstRejectDescription
      { state := 0
        tape := tapeSeenLeft
          (some x ::
            List.append (fldRev.map some)
              (none ::
                List.append (List.replicate g2 none)
                  (List.append (run2Rev.map some)
                    (none ::
                      List.append (List.replicate g1 none)
                        (List.append (run1Rev.map some) (none :: [])))))) R }
      { state := 14
        tape := tapeAtCells [none]
          (some x ::
            none ::
              List.append (run1Rev.reverse.map some)
                (List.append (List.replicate g1 none)
                  (none ::
                    List.append (run2Rev.reverse.map some)
                      (List.append (List.replicate g2 none)
                        (none ::
                          List.append (fldRev.reverse.map some)
                            (none :: R)))))) } := by
  have s1 := pullStepLeft
    (D := pullFirstRejectDescription) (s := 0)
    (t := if x then 2 else 1) (x := x)
    (by cases x <;> decide)
    (List.append (fldRev.map some)
      (none ::
        List.append (List.replicate g2 none)
          (List.append (run2Rev.map some)
            (none ::
              List.append (List.replicate g1 none)
                (List.append (run1Rev.map some) (none :: []))))))
    R
  cases x with
  | false =>
      have s2 := carryJ2First_run
        (D := pullFirstRejectDescription)
        (a0 := 1) (aG2 := 3) (aR2 := 5) (aG1 := 7) (aR1 := 9)
        (aB := 11) (aP := 13) (aH := 14) (x := false)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        fldRev run2Rev run1Rev g1 g2 hrun2 hrun1
        (none :: R)
      exact s1.trans s2
  | true =>
      have s2 := carryJ2First_run
        (D := pullFirstRejectDescription)
        (a0 := 2) (aG2 := 4) (aR2 := 6) (aG1 := 8) (aR1 := 10)
        (aB := 12) (aP := 13) (aH := 14) (x := true)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        fldRev run2Rev run1Rev g1 g2 hrun2 hrun1
        (none :: R)
      exact s1.trans s2

/--
Accept-branch first pull: from the rightmost source bit, walk left over that
run and the following gap, pull the last bit of the next field, and deliver
it as the block's first bit.
-/
theorem pullFirstAccept_run
    (ocohRev : Word Bool) (gC : Nat)
    (x : Bool) (fldRev : Word Bool)
    (g2 : Nat) (run2Rev : Word Bool) (hrun2 : run2Rev ≠ [])
    (g1 : Nat) (run1Rev : Word Bool) (hrun1 : run1Rev ≠ [])
    (R : List (Option Bool)) :
    Reaches pullFirstAcceptDescription
      { state := 0
        tape := tapeSeenLeft
          (List.append (ocohRev.map some)
            (none ::
              List.append (List.replicate gC none)
                (some x ::
                  List.append (fldRev.map some)
                    (none ::
                      List.append (List.replicate g2 none)
                        (List.append (run2Rev.map some)
                          (none ::
                            List.append (List.replicate g1 none)
                              (List.append (run1Rev.map some)
                                (none :: [])))))))) R }
      { state := 15
        tape := tapeAtCells [none]
          (some x ::
            none ::
              List.append (run1Rev.reverse.map some)
                (List.append (List.replicate g1 none)
                  (none ::
                    List.append (run2Rev.reverse.map some)
                      (List.append (List.replicate g2 none)
                        (none ::
                          List.append (fldRev.reverse.map some)
                            (none ::
                              List.append (List.replicate gC none)
                                (none ::
                                  List.append (ocohRev.reverse.map some)
                                    R))))))) } := by
  have s1 := crossBitsLeftThenLeft
    (D := pullFirstAcceptDescription) (s := 0) (t := 1)
    (by decide) (by decide) (by decide)
    ocohRev
    (List.append (List.replicate gC none)
      (some x ::
        List.append (fldRev.map some)
          (none ::
            List.append (List.replicate g2 none)
              (List.append (run2Rev.map some)
                (none ::
                  List.append (List.replicate g1 none)
                    (List.append (run1Rev.map some) (none :: [])))))))
    R
  have s2 := crossBlanksLeftNoExit
    (D := pullFirstAcceptDescription) (s := 1)
    (by decide)
    gC
    (some x ::
      List.append (fldRev.map some)
        (none ::
          List.append (List.replicate g2 none)
            (List.append (run2Rev.map some)
              (none ::
                List.append (List.replicate g1 none)
                  (List.append (run1Rev.map some) (none :: []))))))
    (none :: List.append (ocohRev.reverse.map some) R)
  have s3 := pullStepLeft
    (D := pullFirstAcceptDescription) (s := 1)
    (t := if x then 3 else 2) (x := x)
    (by cases x <;> decide)
    (List.append (fldRev.map some)
      (none ::
        List.append (List.replicate g2 none)
          (List.append (run2Rev.map some)
            (none ::
              List.append (List.replicate g1 none)
                (List.append (run1Rev.map some) (none :: []))))))
    (List.append (List.replicate gC none)
      (none :: List.append (ocohRev.reverse.map some) R))
  cases x with
  | false =>
      have s4 := carryJ2First_run
        (D := pullFirstAcceptDescription)
        (a0 := 2) (aG2 := 4) (aR2 := 6) (aG1 := 8) (aR1 := 10)
        (aB := 12) (aP := 14) (aH := 15) (x := false)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        fldRev run2Rev run1Rev g1 g2 hrun2 hrun1
        (none ::
          List.append (List.replicate gC none)
            (none :: List.append (ocohRev.reverse.map some) R))
      exact s1.trans (s2.trans (s3.trans (s4.trans (Reaches.of_eq rfl))))
  | true =>
      have s4 := carryJ2First_run
        (D := pullFirstAcceptDescription)
        (a0 := 3) (aG2 := 5) (aR2 := 7) (aG1 := 9) (aR1 := 11)
        (aB := 13) (aP := 14) (aH := 15) (x := true)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        fldRev run2Rev run1Rev g1 g2 hrun2 hrun1
        (none ::
          List.append (List.replicate gC none)
            (none :: List.append (ocohRev.reverse.map some) R))
      exact s1.trans (s2.trans (s3.trans (s4.trans (Reaches.of_eq rfl))))

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
