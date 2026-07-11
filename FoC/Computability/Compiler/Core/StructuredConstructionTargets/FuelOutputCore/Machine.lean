import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable

set_option doc.verso true

/-!
# Fuel-output structured core machine

The typed three-tape machine behind sorry {lit}`#10`: it reads an encoded
halted simulator layout on logical tape 0, checks that the encoded state
field equals the attempt's halt state (a unary chain parametric in that
state), and emits the normalized Boolean result code of the encoded
configuration tape onto logical tape 2, in reverse order through a one-bit
hold buffer so the final tape 2 is exactly the output as a fresh input tape.
Logical tape 1 is never touched.  On either semantic failure (state
mismatch, or a result stream that is not a code-word bit string) the machine
enters a rightward spin state, so the divergence transfer applies.

Phase map over the layout
{lit}`header · inputWord · stage · state · leftList · head · rightList · hit`:
walk right to the end blank (visiting it once — the padded tape-0 contract),
marking the configuration head cell on the way; then walk left emitting the
right-list cells reversed and the head; then walk the left-list rightward
emitting it in stored order up to the marked head; restore the mark, flush
the hold buffer, and rewind to the aligned all-false header group.
-/

namespace FoC
namespace Computability

open Languages

namespace StructuredConstructionTargets
namespace FuelOutputCore

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-- Position inside a four-bit token group. -/
inductive GroupPos where
  | p0 | p1 | p2 | p3
deriving DecidableEq, Repr

/--
Emission bookkeeping carried through the output phases.

{lit}`hold` is the one streamed bit not yet written to tape 2 (the final
stream bit must be written with a stay, which is only known at stream end);
{lit}`pos` counts streamed bits modulo four; {lit}`allF` records whether all
bits of the current reversed group so far are {lit}`false`.
-/
structure Emission where
  hold : Option Bool
  pos : GroupPos
  allF : Bool
deriving DecidableEq, Repr

/-- Bookkeeping before any stream bit. -/
def Emission.start : Emission :=
  { hold := none, pos := GroupPos.p0, allF := true }

/--
Stream one output bit through the alignment tracker.

The stream is the reversed output word, so a group's forward-first bit
arrives last: it may be {lit}`true` only when the three bits streamed before
it in the group were all {lit}`false` (the {lit}`TFFF` move-right pattern);
any other group must be false-led.  {lit}`none` rejects the stream.
-/
def Emission.stream (e : Emission) (bit : Bool) : Option Emission :=
  match e.pos with
  | GroupPos.p0 =>
      some { hold := some bit, pos := GroupPos.p1, allF := !bit }
  | GroupPos.p1 =>
      some { hold := some bit, pos := GroupPos.p2, allF := e.allF && !bit }
  | GroupPos.p2 =>
      some { hold := some bit, pos := GroupPos.p3, allF := e.allF && !bit }
  | GroupPos.p3 =>
      if bit = false ∨ e.allF = true then
        some { hold := some bit, pos := GroupPos.p0, allF := true }
      else
        none

/-- Tape-2 action releasing the current hold buffer into a fresh blank. -/
def Emission.emitAction (e : Emission) : TapeAction :=
  match e.hold with
  | none => keepS
  | some bit => writeL (some bit)

/-- Tape-2 action flushing the final hold buffer in place. -/
def Emission.flushAction (e : Emission) : TapeAction :=
  match e.hold with
  | none => keepS
  | some bit => writeS (some bit)

/--
Typed control states of the fuel-output core.

Groups: header skip, input-word skip, stage skip, the parametric state-field
check chain {lit}`chk`, left-list length skip, the left-blob walk with head
marking (backtrack {lit}`lbB`, mark, return {lit}`lbR`), right-list length
skip, right-blob walk to the end blank, hit-token skip, right-list leftward
emission {lit}`re`, right-length leftward skip {lit}`rt` with marked-head
detection {lit}`hd0`, left-list leftward skip {lit}`ls` and turnaround, the
left-list rightward emission {lit}`le`, the final rewind {lit}`rw`, and the
spin and halt states.
-/
inductive CoreState where
  | hdr0 | hdr1 | hdr2 | hdr3
  | inLen0 | inLen1 | inLen2 | inLen3
  | inBits0 | inBits1 | inBits2 | inBits3
  | stage0 | stage1 | stage2 | stage3
  | chk (j : Nat) (k : GroupPos)
  | lLen0 | lLen1 | lLen2 | lLen3
  | lb0 | lb1 | lb2 | lb3
  | lbB1 | lbB2 | lbB3 | lbB4 | lbMark
  | lbR1 | lbR2 | lbR3 | lbR4 | lbR5
  | rLen0 | rLen1 | rLen2 | rLen3
  | rb0 | rb1 | rb2 | rb3
  | hit3 | hit2 | hit1 | hit0
  | re3 (e : Emission)
  | re2 (v3 : Bool) (e : Emission)
  | re1 (v3 v2 : Bool) (e : Emission)
  | re0 (e : Emission)
  | rt3 (e : Emission)
  | rt2 (v3 : Bool) (e : Emission)
  | rt1 (v3 v2 : Bool) (e : Emission)
  | rt0 (e : Emission)
  | hd0 (v3 v2 : Bool) (e : Emission)
  | ls3 (e : Emission) | ls2 (e : Emission)
  | ls1 (e : Emission) | ls0 (e : Emission)
  | turn1 (e : Emission) | turn2 (e : Emission)
  | le0 (e : Emission) | le1 (e : Emission) | le2 (e : Emission)
  | le3 (v2 : Bool) (e : Emission)
  | rw3 | rw2 (allF : Bool) | rw1 (allF : Bool) | rw0
  | spin
  | halt
deriving DecidableEq, Repr

namespace CoreState

/-- A step that only acts on tape 0. -/
private def step0 (a0 : TapeAction) (target : CoreState) :
    Option (TypedStep CoreState) :=
  some { target := target, action0 := a0, action1 := keepS, action2 := keepS }

/-- A step acting on tape 0 and tape 2. -/
private def step02 (a0 a2 : TapeAction) (target : CoreState) :
    Option (TypedStep CoreState) :=
  some { target := target, action0 := a0, action1 := keepS, action2 := a2 }

/-- Stream a cell bit leftward: emit the hold, advance the tracker. -/
private def streamLeft
    (e : Emission) (bit : Bool) (target : Emission -> CoreState) :
    Option (TypedStep CoreState) :=
  match e.stream bit with
  | some e' => step02 keepL e.emitAction (target e')
  | none => step0 keepL spin

/-- Stream a cell bit rightward: emit the hold, advance the tracker. -/
private def streamRight
    (e : Emission) (bit : Bool) (target : Emission -> CoreState) :
    Option (TypedStep CoreState) :=
  match e.stream bit with
  | some e' => step02 keepR e.emitAction (target e')
  | none => step0 keepR spin

/--
The typed transition function, parametric in the attempt's halt state
{lit}`n`.  Only the tape-0 read is inspected; tape 1 always reads blank and
tape 2 always reads blank until the final flush.  States and reads outside
the run on a valid encoded layout have no transition.
-/
def next (n : Nat) :
    CoreState -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep CoreState)
  -- Header: four false bits.
  | hdr0, some false, _, _ => step0 keepR hdr1
  | hdr1, some false, _, _ => step0 keepR hdr2
  | hdr2, some false, _, _ => step0 keepR hdr3
  | hdr3, some false, _, _ => step0 keepR inLen0
  -- Input-word length field: ticks then done.
  | inLen0, some false, _, _ => step0 keepR inLen1
  | inLen1, some false, _, _ => step0 keepR inLen2
  | inLen2, some true, _, _ => step0 keepR inLen3
  | inLen3, some false, _, _ => step0 keepR inLen0
  | inLen3, some true, _, _ => step0 keepR inBits0
  -- Input-word bit cells; first nat-class token starts the stage field.
  | inBits0, some false, _, _ => step0 keepR inBits1
  | inBits1, some true, _, _ => step0 keepR inBits2
  | inBits1, some false, _, _ => step0 keepR stage2
  | inBits2, some _, _, _ => step0 keepR inBits3
  | inBits3, some _, _, _ => step0 keepR inBits0
  -- Stage field: ticks then done.
  | stage0, some false, _, _ => step0 keepR stage1
  | stage1, some false, _, _ => step0 keepR stage2
  | stage2, some true, _, _ => step0 keepR stage3
  | stage3, some false, _, _ => step0 keepR stage0
  | stage3, some true, _, _ => step0 keepR (chk 0 GroupPos.p0)
  -- State field: match exactly n ticks then done, else spin.
  | chk j GroupPos.p0, some false, _, _ => step0 keepR (chk j GroupPos.p1)
  | chk j GroupPos.p1, some false, _, _ => step0 keepR (chk j GroupPos.p2)
  | chk j GroupPos.p2, some true, _, _ => step0 keepR (chk j GroupPos.p3)
  | chk j GroupPos.p3, some false, _, _ =>
      if j < n then step0 keepR (chk (j + 1) GroupPos.p0)
      else step0 keepR spin
  | chk j GroupPos.p3, some true, _, _ =>
      if j = n then step0 keepR lLen0 else step0 keepR spin
  -- Left-list length field.
  | lLen0, some false, _, _ => step0 keepR lLen1
  | lLen1, some false, _, _ => step0 keepR lLen2
  | lLen2, some true, _, _ => step0 keepR lLen3
  | lLen3, some false, _, _ => step0 keepR lLen0
  | lLen3, some true, _, _ => step0 keepR lb0
  -- Left blob (left cells then head): the last cell token before a
  -- nat-class token is the configuration head; mark it.
  | lb0, some false, _, _ => step0 keepR lb1
  | lb1, some true, _, _ => step0 keepR lb2
  | lb1, some false, _, _ => step0 keepL lbB1
  | lb2, some _, _, _ => step0 keepR lb3
  | lb3, some _, _, _ => step0 keepR lb0
  | lbB1, some _, _, _ => step0 keepL lbB2
  | lbB2, some _, _, _ => step0 keepL lbB3
  | lbB3, some _, _, _ => step0 keepL lbB4
  | lbB4, some _, _, _ => step0 keepL lbMark
  | lbMark, some false, _, _ => step0 (writeR (some true)) lbR1
  | lbR1, some _, _, _ => step0 keepR lbR2
  | lbR2, some _, _, _ => step0 keepR lbR3
  | lbR3, some _, _, _ => step0 keepR lbR4
  | lbR4, some _, _, _ => step0 keepR lbR5
  | lbR5, some false, _, _ => step0 keepR rLen2
  -- Right-list length field.
  | rLen0, some false, _, _ => step0 keepR rLen1
  | rLen1, some false, _, _ => step0 keepR rLen2
  | rLen2, some true, _, _ => step0 keepR rLen3
  | rLen3, some false, _, _ => step0 keepR rLen0
  | rLen3, some true, _, _ => step0 keepR rb0
  -- Right blob (right cells then hit): walk to the end blank.
  | rb0, some false, _, _ => step0 keepR rb1
  | rb0, none, _, _ => step0 keepL hit3
  | rb1, some true, _, _ => step0 keepR rb2
  | rb2, some _, _, _ => step0 keepR rb3
  | rb3, some _, _, _ => step0 keepR rb0
  -- Hit token skip, leftward.
  | hit3, some _, _, _ => step0 keepL hit2
  | hit2, some _, _, _ => step0 keepL hit1
  | hit1, some _, _, _ => step0 keepL hit0
  | hit0, some false, _, _ => step0 keepL (re3 Emission.start)
  -- Right cells leftward: emit zero/one bits, skip blanks, stop at the
  -- right-length done token (the first nat-class token).
  | re3 e, some v3, _, _ => step0 keepL (re2 v3 e)
  | re2 v3 e, some v2, _, _ => step0 keepL (re1 v3 v2 e)
  | re1 true false e, some true, _, _ => streamLeft e false re0
  | re1 false true e, some true, _, _ => streamLeft e true re0
  | re1 false false e, some true, _, _ => step0 keepL (re0 e)
  | re1 true true e, some false, _, _ => step0 keepL (rt0 e)
  | re0 e, some false, _, _ => step0 keepL (re3 e)
  -- Right-length field leftward; the first cell-class token is the marked
  -- configuration head.
  | rt3 e, some v3, _, _ => step0 keepL (rt2 v3 e)
  | rt2 v3 e, some v2, _, _ => step0 keepL (rt1 v3 v2 e)
  | rt1 false true e, some false, _, _ => step0 keepL (rt0 e)
  | rt1 v3 v2 e, some true, _, _ => step0 keepL (hd0 v3 v2 e)
  | rt0 e, some false, _, _ => step0 keepL (rt3 e)
  -- Marked head: emit its bit, continue leftward into the left cells.
  | hd0 true false e, some true, _, _ => streamLeft e false ls3
  | hd0 false true e, some true, _, _ => streamLeft e true ls3
  | hd0 false false e, some true, _, _ => step0 keepL (ls3 e)
  -- Left cells leftward without emission, to the left-length done token.
  | ls3 e, some _, _, _ => step0 keepL (ls2 e)
  | ls2 e, some _, _, _ => step0 keepL (ls1 e)
  | ls1 e, some true, _, _ => step0 keepL (ls0 e)
  | ls1 e, some false, _, _ => step0 keepR (turn1 e)
  | ls0 e, some false, _, _ => step0 keepL (ls3 e)
  | turn1 e, some _, _, _ => step0 keepR (turn2 e)
  | turn2 e, some _, _, _ => step0 keepR (le0 e)
  -- Left cells rightward in stored order, emitting, up to the marked head:
  -- restore the mark, require a whole number of groups, flush the hold.
  | le0 e, some false, _, _ => step0 keepR (le1 e)
  | le0 e, some true, _, _ =>
      match e.pos with
      | GroupPos.p0 => step02 (writeL (some false)) e.flushAction rw3
      | _ => step0 keepR spin
  | le1 e, some true, _, _ => step0 keepR (le2 e)
  | le2 e, some v2, _, _ => step0 keepR (le3 v2 e)
  | le3 false e, some true, _, _ => streamRight e false le0
  | le3 true e, some false, _, _ => streamRight e true le0
  | le3 false e, some false, _, _ => step0 keepR (le0 e)
  -- Rewind to the header: the only aligned group with three false bits
  -- after its first is the header, whose first bit is bit zero.
  | rw3, some v3, _, _ => step0 keepL (rw2 (!v3))
  | rw2 aF, some v2, _, _ => step0 keepL (rw1 (aF && !v2))
  | rw1 true, some false, _, _ => step0 keepL halt
  | rw1 true, some true, _, _ => step0 keepL rw0
  | rw1 false, some _, _, _ => step0 keepL rw0
  | rw0, some false, _, _ => step0 keepL rw3
  -- Spin: move right forever.
  | spin, _, _, _ => step0 keepR spin
  | _, _, _, _ => none

end CoreState

/-- All emission bookkeeping values. -/
def emissionAll : List Emission :=
  ([none, some false, some true] : List (Option Bool)).flatMap fun h =>
    ([GroupPos.p0, GroupPos.p1, GroupPos.p2, GroupPos.p3] :
        List GroupPos).flatMap fun p =>
      ([false, true] : List Bool).map fun a =>
        { hold := h, pos := p, allF := a }

theorem mem_emissionAll (e : Emission) : e ∈ emissionAll := by
  rcases e with ⟨h, p, a⟩
  cases h with
  | none => cases p <;> cases a <;> decide
  | some bit => cases bit <;> cases p <;> cases a <;> decide

/-- Fixed forward-phase states. -/
def fixedStates : List CoreState :=
  [ CoreState.hdr0, CoreState.hdr1, CoreState.hdr2, CoreState.hdr3
  , CoreState.inLen0, CoreState.inLen1, CoreState.inLen2, CoreState.inLen3
  , CoreState.inBits0, CoreState.inBits1, CoreState.inBits2
  , CoreState.inBits3
  , CoreState.stage0, CoreState.stage1, CoreState.stage2, CoreState.stage3
  , CoreState.lLen0, CoreState.lLen1, CoreState.lLen2, CoreState.lLen3
  , CoreState.lb0, CoreState.lb1, CoreState.lb2, CoreState.lb3
  , CoreState.lbB1, CoreState.lbB2, CoreState.lbB3, CoreState.lbB4
  , CoreState.lbMark
  , CoreState.lbR1, CoreState.lbR2, CoreState.lbR3, CoreState.lbR4
  , CoreState.lbR5
  , CoreState.rLen0, CoreState.rLen1, CoreState.rLen2, CoreState.rLen3
  , CoreState.rb0, CoreState.rb1, CoreState.rb2, CoreState.rb3
  , CoreState.hit3, CoreState.hit2, CoreState.hit1, CoreState.hit0
  , CoreState.rw3, CoreState.rw2 false, CoreState.rw2 true
  , CoreState.rw1 false, CoreState.rw1 true, CoreState.rw0
  , CoreState.spin, CoreState.halt ]

/-- States carrying one emission bookkeeping value. -/
def emissionBlock (e : Emission) : List CoreState :=
  [ CoreState.re3 e, CoreState.re0 e
  , CoreState.rt3 e, CoreState.rt0 e
  , CoreState.ls3 e, CoreState.ls2 e, CoreState.ls1 e, CoreState.ls0 e
  , CoreState.turn1 e, CoreState.turn2 e
  , CoreState.le0 e, CoreState.le1 e, CoreState.le2 e
  , CoreState.re2 false e, CoreState.re2 true e
  , CoreState.rt2 false e, CoreState.rt2 true e
  , CoreState.le3 false e, CoreState.le3 true e
  , CoreState.re1 false false e, CoreState.re1 false true e
  , CoreState.re1 true false e, CoreState.re1 true true e
  , CoreState.rt1 false false e, CoreState.rt1 false true e
  , CoreState.rt1 true false e, CoreState.rt1 true true e
  , CoreState.hd0 false false e, CoreState.hd0 false true e
  , CoreState.hd0 true false e, CoreState.hd0 true true e ]

/-- Control states of the fuel-output core for halt parameter {lit}`n`. -/
def coreStates (n : Nat) : List CoreState :=
  List.append fixedStates
    (List.append
      ((List.range (n + 1)).flatMap fun j =>
        [ CoreState.chk j GroupPos.p0, CoreState.chk j GroupPos.p1
        , CoreState.chk j GroupPos.p2, CoreState.chk j GroupPos.p3 ])
      (emissionAll.flatMap emissionBlock))

theorem mem_coreStates_of_fixed {n : Nat} {s : CoreState}
    (h : s ∈ fixedStates) : s ∈ coreStates n :=
  List.mem_append.mpr (Or.inl h)

theorem mem_coreStates_chk {n : Nat} {j : Nat} (hj : j ≤ n)
    (k : GroupPos) : CoreState.chk j k ∈ coreStates n := by
  refine List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl ?_)))
  refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr ?_, ?_⟩
  · exact Nat.lt_succ_of_le hj
  · cases k <;> simp

theorem mem_coreStates_of_emission {n : Nat} {s : CoreState}
    {e : Emission} (h : s ∈ emissionBlock e) : s ∈ coreStates n :=
  List.mem_append.mpr
    (Or.inr
      (List.mem_append.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨e, mem_emissionAll e, h⟩))))

end FuelOutputCore
end StructuredConstructionTargets

end Computability
end FoC
