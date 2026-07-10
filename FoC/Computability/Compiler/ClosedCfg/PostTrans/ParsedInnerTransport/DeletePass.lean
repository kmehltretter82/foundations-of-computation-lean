import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.PullLoop
import FoC.Computability.Compiler.Core.DovetailInitLayout.StageInputMarkedScanner.Basic

set_option doc.verso true

/-!
# Parsed-inner transport deletion-pass lemmas

Run lemmas for the small machines of the deletion pre-pass: the entry
rewinder, the sentinel stash/restore pair around the boundary eraser, the
blank walker, and the two mid erasers.  Field-grammar traversal itself is
delegated to the already proved scanner machines; these lemmas only cover
blank/bit runs, fixed token windows, and unary nat fields.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

open CommonGround.FiniteTransducers
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncRewriters
namespace BoundedLayoutRunner
namespace ParsedInnerTransport

/-- Single step rightward through an explicit transition. -/
theorem stepRight
    {D : MachineDescription} {s t : Nat} {r w : Option Bool}
    (h : D.lookupTransition s r =
      some (transition s r w Direction.right t))
    (L R : List (Option Bool)) :
    Reaches D
      { state := s, tape := tapeAtCells L (r :: R) }
      { state := t, tape := tapeAtCells (w :: L) R } :=
  Reaches.of_run (by
    have := runConfig_one h (tapeAtCells L (r :: R)) (by cases R <;> rfl)
    rwa [move_right_write_tapeAtCells] at this)

/-- Single step leftward through an explicit transition. -/
theorem stepLeft
    {D : MachineDescription} {s t : Nat} {r w : Option Bool}
    (h : D.lookupTransition s r =
      some (transition s r w Direction.left t))
    (L R : List (Option Bool)) :
    Reaches D
      { state := s, tape := tapeSeenLeft (r :: L) R }
      { state := t, tape := tapeSeenLeft L (w :: R) } :=
  Reaches.of_run (by
    have := runConfig_one h (tapeSeenLeft (r :: L) R) (by cases L <;> rfl)
    rwa [move_left_write_tapeSeenLeft] at this)

/-- Bit-run crossing leftward whose exit steps back right. -/
theorem crossBitsLeftThenRight
    {D : MachineDescription} {s t : Nat}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s))
    (hExit : D.lookupTransition s none =
      some (transition s none none Direction.right t))
    (revBits : Word Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeSeenLeft
          (List.append (revBits.map some) (none :: L)) R }
      { state := t
        tape := tapeAtCells (none :: L)
          (List.append (revBits.reverse.map some) R) } :=
  Reaches.of_run (by
    have := runConfig_bitsRun_exitBlank_left hF hT hExit revBits L R
    rwa [move_right_write_tapeSeenLeft] at this)

/-- Blank-run crossing rightward whose exit steps back left onto the last
blank. -/
theorem crossBlanksRightThenLeft
    {D : MachineDescription} {s t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.right s))
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left t))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left t))
    (n : Nat) (b : Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeAtCells L
          (List.append (List.replicate n none) (some b :: R)) }
      { state := t
        tape := tapeSeenLeft
          (List.append (List.replicate n none) L) (some b :: R) } :=
  Reaches.of_run (by
    have := runConfig_blankRun_exitBit_right hN hF hT n b L R
    rwa [move_left_write_tapeAtCells] at this)

/-- Blank-run crossing rightward whose exit consumes the first bit. -/
theorem crossBlanksRightThenRight
    {D : MachineDescription} {s t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.right s))
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.right t))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.right t))
    (n : Nat) (b : Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeAtCells L
          (List.append (List.replicate n none) (some b :: R)) }
      { state := t
        tape := tapeAtCells
          (some b :: List.append (List.replicate n none) L) R } :=
  Reaches.of_run (by
    have := runConfig_blankRun_exitBit_right hN hF hT n b L R
    rwa [move_right_write_tapeAtCells] at this)

theorem replicate_none_add (m n : Nat) :
    List.replicate (m + n) (none : Option Bool) =
      List.append (List.replicate m none) (List.replicate n none) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 + n = (k + n) + 1 from by lia]
      simp only [List.replicate_succ, List.append_eq, List.cons_append] at *
      rw [ih]

/-- Erase a unary nat field rightward through a four-state cycle, halting on
the cell after the done token. -/
theorem eraseNat_run
    {D : MachineDescription} {s0 s1 s2 s3 t : Nat}
    (h0 : D.lookupTransition s0 (some false) =
      some (transition s0 (some false) none Direction.right s1))
    (h1 : D.lookupTransition s1 (some false) =
      some (transition s1 (some false) none Direction.right s2))
    (h2 : D.lookupTransition s2 (some true) =
      some (transition s2 (some true) none Direction.right s3))
    (h3tick : D.lookupTransition s3 (some false) =
      some (transition s3 (some false) none Direction.right s0))
    (h3done : D.lookupTransition s3 (some true) =
      some (transition s3 (some true) none Direction.right t))
    (n : Nat) (L R : List (Option Bool)) :
    Reaches D
      { state := s0
        tape := tapeAtCells L
          (List.append ((stageNatBits n).map some) R) }
      { state := t
        tape := tapeAtCells
          (List.append (List.replicate (4 * n + 4) none) L) R } := by
  induction n generalizing L with
  | zero =>
      have e1 := stepRight (D := D) h0 L
        (List.append ((List.map some [false, true, true])) R)
      have e2 := stepRight (D := D) h1 (none :: L)
        (List.append ((List.map some [true, true])) R)
      have e3 := stepRight (D := D) h2 (none :: none :: L)
        (List.append ((List.map some [true])) R)
      have e4 := stepRight (D := D) h3done (none :: none :: none :: L) R
      refine Reaches.trans (Reaches.of_eq ?_)
        (e1.trans (Reaches.trans (Reaches.of_eq ?_)
          (e2.trans (Reaches.trans (Reaches.of_eq ?_)
            (e3.trans (Reaches.trans (Reaches.of_eq ?_)
              (e4.trans (Reaches.of_eq ?_)))))))) <;>
        first
          | rfl
          | (congr 1 <;>
              first
                | rfl
                | simp [stageNatBits_zero, List.append_eq, List.replicate])
  | succ n ih =>
      have e1 := stepRight (D := D) h0 L
        (List.append (List.map some [false, true, false])
          (List.append ((stageNatBits n).map some) R))
      have e2 := stepRight (D := D) h1 (none :: L)
        (List.append (List.map some [true, false])
          (List.append ((stageNatBits n).map some) R))
      have e3 := stepRight (D := D) h2 (none :: none :: L)
        (List.append (List.map some [false])
          (List.append ((stageNatBits n).map some) R))
      have e4 := stepRight (D := D) h3tick (none :: none :: none :: L)
        (List.append ((stageNatBits n).map some) R)
      have erest := ih (none :: none :: none :: none :: L)
      have hrep :
          (List.append (List.replicate (4 * n + 4) (none : Option Bool))
            (none :: none :: none :: none :: L)) =
            List.append (List.replicate (4 * (n + 1) + 4) none) L := by
        rw [show 4 * (n + 1) + 4 = (4 * n + 4) + 4 from by lia,
          replicate_none_add]
        simp [List.append_eq, List.append_assoc, List.replicate,
          replicate_none_comm']
      have efin :
          (Configuration.mk t (tapeAtCells
            (List.append (List.replicate (4 * n + 4) none)
              (none :: none :: none :: none :: L)) R)) =
            Configuration.mk t (tapeAtCells
              (List.append (List.replicate (4 * (n + 1) + 4) none) L) R) := by
        rw [hrep]
      refine Reaches.trans (Reaches.of_eq ?_)
        (e1.trans (Reaches.trans (Reaches.of_eq ?_)
          (e2.trans (Reaches.trans (Reaches.of_eq ?_)
            (e3.trans (Reaches.trans (Reaches.of_eq ?_)
              (e4.trans (erest.trans (Reaches.of_eq efin))))))))) <;>
        first
          | rfl
          | (congr 1 <;>
              first
                | rfl
                | simp [stageNatBits_succ, List.append_eq,
                    List.append_assoc])

/--
Entry rewind: from the first trailing blank right of the source bits, rewind
to the leading blank sentinel and skip the transition token; halts on the
first bit of the boolWord input field.
-/
theorem transportEntry_run
    (mid : Word Bool) (last : Bool) :
    Reaches transportEntryDescription
      { state := 0
        tape := tapeSeenLeft
          (none :: none :: none ::
            List.append
              ((List.append (List.append [false, false, false, true] mid)
                [last]).reverse.map some)
              [none])
          (none :: none :: none :: []) }
      { state := 6
        tape := tapeAtCells
          (some true :: some false :: some false :: some false :: [none])
          (List.append (mid.map some)
            (some last :: List.replicate 6 none)) } := by
  have s1 : Reaches transportEntryDescription
      { state := 0
        tape := tapeSeenLeft
          (List.append (List.replicate 3 none)
            (some last ::
              List.append
                ((List.append [false, false, false, true] mid).reverse.map
                  some)
                [none]))
          (none :: none :: none :: []) }
      { state := 1
        tape := tapeSeenLeft
          (List.append
            ((List.append [false, false, false, true] mid).reverse.map some)
            [none])
          (some last ::
            List.append (List.replicate 3 none)
              (none :: none :: none :: [])) } :=
    Reaches.of_run (by
      have := runConfig_blankRun_exitBit_left
        (D := transportEntryDescription) (s := 0) (t := 1)
        (d := Direction.left)
        (by decide) (by decide) (by decide)
        3 last
        (List.append
          ((List.append [false, false, false, true] mid).reverse.map some)
          [none])
        (none :: none :: none :: [])
      rwa [move_left_write_tapeSeenLeft] at this)
  have s2 := crossBitsLeftThenRight
    (D := transportEntryDescription) (s := 1) (t := 2)
    (by decide) (by decide) (by decide)
    ((List.append [false, false, false, true] mid).reverse)
    []
    (some last :: List.append (List.replicate 3 none)
      (none :: none :: none :: []))
  have s3 := stepRight (D := transportEntryDescription)
    (s := 2) (t := 3) (r := some false) (w := some false) (by decide)
    [none]
    (List.append (List.map some (List.append [false, false, true] mid))
      (some last :: List.append (List.replicate 3 none)
        (none :: none :: none :: [])))
  have s4 := stepRight (D := transportEntryDescription)
    (s := 3) (t := 4) (r := some false) (w := some false) (by decide)
    (some false :: [none])
    (List.append (List.map some (List.append [false, true] mid))
      (some last :: List.append (List.replicate 3 none)
        (none :: none :: none :: [])))
  have s5 := stepRight (D := transportEntryDescription)
    (s := 4) (t := 5) (r := some false) (w := some false) (by decide)
    (some false :: some false :: [none])
    (List.append (List.map some (List.append [true] mid))
      (some last :: List.append (List.replicate 3 none)
        (none :: none :: none :: [])))
  have s6 := stepRight (D := transportEntryDescription)
    (s := 5) (t := 6) (r := some true) (w := some true) (by decide)
    (some false :: some false :: some false :: [none])
    (List.append (List.map some mid)
      (some last :: List.append (List.replicate 3 none)
        (none :: none :: none :: [])))
  refine Reaches.trans (Reaches.of_eq ?_)
    (s1.trans (Reaches.trans (Reaches.of_eq ?_)
      (s2.trans (Reaches.trans (Reaches.of_eq ?_)
        (s3.trans (Reaches.trans (Reaches.of_eq ?_)
          (s4.trans (Reaches.trans (Reaches.of_eq ?_)
            (s5.trans (Reaches.trans (Reaches.of_eq ?_)
              (s6.trans (Reaches.of_eq ?_)))))))))))) <;>
    first
      | rfl
      | (congr 1 <;>
          first
            | rfl
            | simp [List.append_eq, List.reverse_reverse, List.cons_append,
                List.append_assoc, List.replicate])

/-- Valid sentinel tokens: the done token and the three cell tokens. -/
def SentinelTokenValid (c2 c3 c4 : Bool) : Prop :=
  (c2 = true ∧ c3 = false ∧ c4 = false) ∨
    (c2 = true ∧ c3 = true ∧ c4 = false) ∨
    (c2 = true ∧ c3 = false ∧ c4 = true) ∨
    (c2 = false ∧ c3 = true ∧ c4 = true)

/--
Sentinel stash: starting on the last cell of the token {lit}`[0,c2,c3,c4]`,
rewrite it to {lit}`[c2,c3,c4,blank]` and halt on the cell after the token.
-/
theorem sentinelStash_run
    (c2 c3 c4 : Bool) (hvalid : SentinelTokenValid c2 c3 c4)
    (L R : List (Option Bool)) :
    Reaches sentinelStashDescription
      { state := 0
        tape := tapeSeenLeft
          (some c4 :: some c3 :: some c2 :: some false :: L) R }
      { state := 18
        tape := tapeAtCells
          (none :: some c4 :: some c3 :: some c2 :: L) R } := by
  rcases hvalid with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact Reaches.of_run (n := 8) (by
      simp [MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        sentinelStashDescription, transition, sFCell, sTCell,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
        tapeSeenLeft, tapeAtCells]
      cases R <;> rfl)

/--
Sentinel restore: starting on the first erased cell right of the stashed
token {lit}`[c2,c3,c4,blank]`, restore {lit}`[0,c2,c3,c4]` and halt back on the
starting cell.
-/
theorem sentinelRestore_run
    (c2 c3 c4 : Bool) (hvalid : SentinelTokenValid c2 c3 c4)
    (L R : List (Option Bool)) :
    Reaches sentinelRestoreDescription
      { state := 0
        tape := tapeSeenLeft
          (none :: none :: some c4 :: some c3 :: some c2 :: L) R }
      { state := 19
        tape := tapeAtCells
          (some c4 :: some c3 :: some c2 :: some false :: L)
          (none :: R) } := by
  rcases hvalid with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact Reaches.of_run (n := 8) (by
      simp [MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        sentinelRestoreDescription, transition, sFCell, sTCell,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
        tapeSeenLeft, tapeAtCells])

/--
Blank walker: from the first blank of a nonempty blank run, walk right and
halt on the first bit.
-/
theorem blankRightWalker_run
    (n : Nat) (b : Bool) (L R : List (Option Bool)) :
    Reaches blankRightWalkerDescription
      { state := 0
        tape := tapeAtCells L
          (List.append (List.replicate (n + 1) none) (some b :: R)) }
      { state := 2
        tape := tapeAtCells
          (List.append (List.replicate (n + 1) none) L) (some b :: R) } := by
  have s1 := crossBlanksRightThenLeft
    (D := blankRightWalkerDescription) (s := 0) (t := 1)
    (by decide) (by decide) (by decide)
    (n + 1) b L R
  have s2 := parkRight
    (D := blankRightWalkerDescription) (s := 1) (t := 2)
    (by decide)
    (List.append (List.replicate n none) L)
    (some b :: R)
  refine s1.trans (Reaches.trans (Reaches.of_eq ?_)
    (s2.trans (Reaches.of_eq ?_))) <;>
    first
      | rfl
      | (congr 1 <;>
          first
            | rfl
            | simp [List.append_eq, List.replicate_succ])

/--
Accept mid eraser: erase four cells, keep four cells, erase a unary nat
field, and halt on the following cell.
-/
theorem acceptMidEraser_run
    (a1 a2 a3 a4 h1 h2 h3 h4 : Bool) (n : Nat)
    (L R : List (Option Bool)) :
    Reaches acceptMidEraserDescription
      { state := 0
        tape := tapeAtCells L
          (some a1 :: some a2 :: some a3 :: some a4 ::
            some h1 :: some h2 :: some h3 :: some h4 ::
              List.append ((stageNatBits n).map some) R) }
      { state := 12
        tape := tapeAtCells
          (List.append (List.replicate (4 * n + 4) none)
            (some h4 :: some h3 :: some h2 :: some h1 ::
              none :: none :: none :: none :: L)) R } := by
  have e1 := stepRight (D := acceptMidEraserDescription)
    (s := 0) (t := 1) (r := some a1) (w := none)
    (by cases a1 <;> decide) L
    (some a2 :: some a3 :: some a4 ::
      some h1 :: some h2 :: some h3 :: some h4 ::
        List.append ((stageNatBits n).map some) R)
  have e2 := stepRight (D := acceptMidEraserDescription)
    (s := 1) (t := 2) (r := some a2) (w := none)
    (by cases a2 <;> decide) (none :: L)
    (some a3 :: some a4 ::
      some h1 :: some h2 :: some h3 :: some h4 ::
        List.append ((stageNatBits n).map some) R)
  have e3 := stepRight (D := acceptMidEraserDescription)
    (s := 2) (t := 3) (r := some a3) (w := none)
    (by cases a3 <;> decide) (none :: none :: L)
    (some a4 ::
      some h1 :: some h2 :: some h3 :: some h4 ::
        List.append ((stageNatBits n).map some) R)
  have e4 := stepRight (D := acceptMidEraserDescription)
    (s := 3) (t := 4) (r := some a4) (w := none)
    (by cases a4 <;> decide) (none :: none :: none :: L)
    (some h1 :: some h2 :: some h3 :: some h4 ::
      List.append ((stageNatBits n).map some) R)
  have e5 := stepRight (D := acceptMidEraserDescription)
    (s := 4) (t := 5) (r := some h1) (w := some h1)
    (by cases h1 <;> decide) (none :: none :: none :: none :: L)
    (some h2 :: some h3 :: some h4 ::
      List.append ((stageNatBits n).map some) R)
  have e6 := stepRight (D := acceptMidEraserDescription)
    (s := 5) (t := 6) (r := some h2) (w := some h2)
    (by cases h2 <;> decide)
    (some h1 :: none :: none :: none :: none :: L)
    (some h3 :: some h4 :: List.append ((stageNatBits n).map some) R)
  have e7 := stepRight (D := acceptMidEraserDescription)
    (s := 6) (t := 7) (r := some h3) (w := some h3)
    (by cases h3 <;> decide)
    (some h2 :: some h1 :: none :: none :: none :: none :: L)
    (some h4 :: List.append ((stageNatBits n).map some) R)
  have e8 := stepRight (D := acceptMidEraserDescription)
    (s := 7) (t := 8) (r := some h4) (w := some h4)
    (by cases h4 <;> decide)
    (some h3 :: some h2 :: some h1 :: none :: none :: none :: none :: L)
    (List.append ((stageNatBits n).map some) R)
  have e9 := eraseNat_run (D := acceptMidEraserDescription)
    (s0 := 8) (s1 := 9) (s2 := 10) (s3 := 11) (t := 12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    n
    (some h4 :: some h3 :: some h2 :: some h1 ::
      none :: none :: none :: none :: L)
    R
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans
    (e7.trans (e8.trans (e9.trans (Reaches.of_eq rfl)))))))))

/--
Reject mid eraser: walk right over a blank run, keep four cells, erase four
cells, erase a unary nat field, and halt on the following cell.
-/
theorem rejectMidEraser_run
    (g : Nat) (h1 h2 h3 h4 r1 r2 r3 r4 : Bool) (n : Nat)
    (L R : List (Option Bool)) :
    Reaches rejectMidEraserDescription
      { state := 0
        tape := tapeAtCells L
          (List.append (List.replicate g none)
            (some h1 :: some h2 :: some h3 :: some h4 ::
              some r1 :: some r2 :: some r3 :: some r4 ::
                List.append ((stageNatBits n).map some) R)) }
      { state := 12
        tape := tapeAtCells
          (List.append (List.replicate (4 * n + 4) none)
            (none :: none :: none :: none ::
              some h4 :: some h3 :: some h2 :: some h1 ::
                List.append (List.replicate g none) L)) R } := by
  have e1 := crossBlanksRightThenRight
    (D := rejectMidEraserDescription) (s := 0) (t := 1)
    (by decide) (by decide) (by decide)
    g h1 L
    (some h2 :: some h3 :: some h4 ::
      some r1 :: some r2 :: some r3 :: some r4 ::
        List.append ((stageNatBits n).map some) R)
  have e2 := stepRight (D := rejectMidEraserDescription)
    (s := 1) (t := 2) (r := some h2) (w := some h2)
    (by cases h2 <;> decide)
    (some h1 :: List.append (List.replicate g none) L)
    (some h3 :: some h4 ::
      some r1 :: some r2 :: some r3 :: some r4 ::
        List.append ((stageNatBits n).map some) R)
  have e3 := stepRight (D := rejectMidEraserDescription)
    (s := 2) (t := 3) (r := some h3) (w := some h3)
    (by cases h3 <;> decide)
    (some h2 :: some h1 :: List.append (List.replicate g none) L)
    (some h4 ::
      some r1 :: some r2 :: some r3 :: some r4 ::
        List.append ((stageNatBits n).map some) R)
  have e4 := stepRight (D := rejectMidEraserDescription)
    (s := 3) (t := 4) (r := some h4) (w := some h4)
    (by cases h4 <;> decide)
    (some h3 :: some h2 :: some h1 ::
      List.append (List.replicate g none) L)
    (some r1 :: some r2 :: some r3 :: some r4 ::
      List.append ((stageNatBits n).map some) R)
  have e5 := stepRight (D := rejectMidEraserDescription)
    (s := 4) (t := 5) (r := some r1) (w := none)
    (by cases r1 <;> decide)
    (some h4 :: some h3 :: some h2 :: some h1 ::
      List.append (List.replicate g none) L)
    (some r2 :: some r3 :: some r4 ::
      List.append ((stageNatBits n).map some) R)
  have e6 := stepRight (D := rejectMidEraserDescription)
    (s := 5) (t := 6) (r := some r2) (w := none)
    (by cases r2 <;> decide)
    (none :: some h4 :: some h3 :: some h2 :: some h1 ::
      List.append (List.replicate g none) L)
    (some r3 :: some r4 :: List.append ((stageNatBits n).map some) R)
  have e7 := stepRight (D := rejectMidEraserDescription)
    (s := 6) (t := 7) (r := some r3) (w := none)
    (by cases r3 <;> decide)
    (none :: none :: some h4 :: some h3 :: some h2 :: some h1 ::
      List.append (List.replicate g none) L)
    (some r4 :: List.append ((stageNatBits n).map some) R)
  have e8 := stepRight (D := rejectMidEraserDescription)
    (s := 7) (t := 8) (r := some r4) (w := none)
    (by cases r4 <;> decide)
    (none :: none :: none :: some h4 :: some h3 :: some h2 :: some h1 ::
      List.append (List.replicate g none) L)
    (List.append ((stageNatBits n).map some) R)
  have e9 := eraseNat_run (D := rejectMidEraserDescription)
    (s0 := 8) (s1 := 9) (s2 := 10) (s3 := 11) (t := 12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    n
    (none :: none :: none :: none ::
      some h4 :: some h3 :: some h2 :: some h1 ::
        List.append (List.replicate g none) L)
    R
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans
    (e7.trans (e8.trans (e9.trans (Reaches.of_eq rfl)))))))))

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
