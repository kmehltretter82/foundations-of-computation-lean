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
def next (n : Nat) (s : CoreState) :
    Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep CoreState) :=
  match s with
  | hdr0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR hdr1
      | _ => none
  | hdr1 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR hdr2
      | _ => none
  | hdr2 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR hdr3
      | _ => none
  | hdr3 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR inLen0
      | _ => none
  | inLen0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR inLen1
      | _ => none
  | inLen1 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR inLen2
      | _ => none
  | inLen2 => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepR inLen3
      | _ => none
  | inLen3 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR inLen0
      | some true => step0 keepR inBits0
      | _ => none
  | inBits0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR inBits1
      | _ => none
  | inBits1 => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepR inBits2
      | some false => step0 keepR stage2
      | _ => none
  | inBits2 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR inBits3
      | _ => none
  | inBits3 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR inBits0
      | _ => none
  | stage0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR stage1
      | _ => none
  | stage1 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR stage2
      | _ => none
  | stage2 => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepR stage3
      | _ => none
  | stage3 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR stage0
      | some true => step0 keepR (chk 0 GroupPos.p0)
      | _ => none
  | chk j k => fun r0 _ _ =>
      match k, r0 with
      | GroupPos.p0, some false => step0 keepR (chk j GroupPos.p1)
      | GroupPos.p1, some false => step0 keepR (chk j GroupPos.p2)
      | GroupPos.p2, some true => step0 keepR (chk j GroupPos.p3)
      | GroupPos.p3, some false =>
          if j < n then step0 keepR (chk (j + 1) GroupPos.p0)
          else step0 keepR spin
      | GroupPos.p3, some true =>
          if j = n then step0 keepR lLen0 else step0 keepR spin
      | _, _ => none
  | lLen0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR lLen1
      | _ => none
  | lLen1 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR lLen2
      | _ => none
  | lLen2 => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepR lLen3
      | _ => none
  | lLen3 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR lLen0
      | some true => step0 keepR lb0
      | _ => none
  | lb0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR lb1
      | _ => none
  | lb1 => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepR lb2
      | some false => step0 keepL lbB1
      | _ => none
  | lb2 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR lb3
      | _ => none
  | lb3 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR lb0
      | _ => none
  | lbB1 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL lbB2
      | _ => none
  | lbB2 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL lbB3
      | _ => none
  | lbB3 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL lbB4
      | _ => none
  | lbB4 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL lbMark
      | _ => none
  | lbMark => fun r0 _ _ =>
      match r0 with
      | some false => step0 (writeR (some true)) lbR1
      | _ => none
  | lbR1 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR lbR2
      | _ => none
  | lbR2 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR lbR3
      | _ => none
  | lbR3 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR lbR4
      | _ => none
  | lbR4 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR lbR5
      | _ => none
  | lbR5 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR rLen2
      | _ => none
  | rLen0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR rLen1
      | _ => none
  | rLen1 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR rLen2
      | _ => none
  | rLen2 => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepR rLen3
      | _ => none
  | rLen3 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR rLen0
      | some true => step0 keepR rb0
      | _ => none
  | rb0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR rb1
      | none => step0 keepL hit3
      | _ => none
  | rb1 => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepR rb2
      | _ => none
  | rb2 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR rb3
      | _ => none
  | rb3 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR rb0
      | _ => none
  | hit3 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL hit2
      | _ => none
  | hit2 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL hit1
      | _ => none
  | hit1 => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL hit0
      | _ => none
  | hit0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepL (re3 Emission.start)
      | _ => none
  | re3 e => fun r0 _ _ =>
      match r0 with
      | some v3 => step0 keepL (re2 v3 e)
      | _ => none
  | re2 v3 e => fun r0 _ _ =>
      match r0 with
      | some v2 => step0 keepL (re1 v3 v2 e)
      | _ => none
  | re1 v3 v2 e => fun r0 _ _ =>
      match v3, v2, r0 with
      | true, false, some true => streamLeft e false re0
      | false, true, some true => streamLeft e true re0
      | false, false, some true => step0 keepL (re0 e)
      | true, true, some false => step0 keepL (rt0 e)
      | _, _, _ => none
  | re0 e => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepL (re3 e)
      | _ => none
  | rt3 e => fun r0 _ _ =>
      match r0 with
      | some v3 => step0 keepL (rt2 v3 e)
      | _ => none
  | rt2 v3 e => fun r0 _ _ =>
      match r0 with
      | some v2 => step0 keepL (rt1 v3 v2 e)
      | _ => none
  | rt1 v3 v2 e => fun r0 _ _ =>
      match v3, v2, r0 with
      | false, true, some false => step0 keepL (rt0 e)
      | v3', v2', some true => step0 keepL (hd0 v3' v2' e)
      | _, _, _ => none
  | rt0 e => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepL (rt3 e)
      | _ => none
  | hd0 v3 v2 e => fun r0 _ _ =>
      match v3, v2, r0 with
      | true, false, some true => streamLeft e false ls3
      | false, true, some true => streamLeft e true ls3
      | false, false, some true => step0 keepL (ls3 e)
      | _, _, _ => none
  | ls3 e => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL (ls2 e)
      | _ => none
  | ls2 e => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepL (ls1 e)
      | _ => none
  | ls1 e => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepL (ls0 e)
      | some false => step0 keepR (turn1 e)
      | _ => none
  | ls0 e => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepL (ls3 e)
      | _ => none
  | turn1 e => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR (turn2 e)
      | _ => none
  | turn2 e => fun r0 _ _ =>
      match r0 with
      | some _ => step0 keepR (le0 e)
      | _ => none
  | le0 e => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepR (le1 e)
      | some true =>
          match e.pos with
          | GroupPos.p0 => step02 (writeL (some false)) e.flushAction rw3
          | _ => step0 keepR spin
      | _ => none
  | le1 e => fun r0 _ _ =>
      match r0 with
      | some true => step0 keepR (le2 e)
      | _ => none
  | le2 e => fun r0 _ _ =>
      match r0 with
      | some v2 => step0 keepR (le3 v2 e)
      | _ => none
  | le3 v2 e => fun r0 _ _ =>
      match v2, r0 with
      | false, some true => streamRight e false le0
      | true, some false => streamRight e true le0
      | false, some false => step0 keepR (le0 e)
      | _, _ => none
  | rw3 => fun r0 _ _ =>
      match r0 with
      | some v3 => step0 keepL (rw2 (!v3))
      | _ => none
  | rw2 aF => fun r0 _ _ =>
      match r0 with
      | some v2 => step0 keepL (rw1 (aF && !v2))
      | _ => none
  | rw1 aF => fun r0 _ _ =>
      match aF, r0 with
      | true, some false => step0 keepL halt
      | true, some true => step0 keepL rw0
      | false, some _ => step0 keepL rw0
      | _, _ => none
  | rw0 => fun r0 _ _ =>
      match r0 with
      | some false => step0 keepL rw3
      | _ => none
  | spin => fun _ _ _ => step0 keepR spin
  | halt => fun _ _ _ => none

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

/-!
## Table instance
-/

theorem chk_mem_bound {n j : Nat} {k : GroupPos}
    (h : CoreState.chk j k ∈ coreStates n) : j ≤ n := by
  rcases List.mem_append.mp h with hfix | hrest
  · exfalso
    simp [fixedStates] at hfix
  · rcases List.mem_append.mp hrest with hchain | hemit
    · rcases List.mem_flatMap.mp hchain with ⟨j', hj', hmem⟩
      have hj'n : j' < n + 1 := List.mem_range.mp hj'
      have hjj : j = j' := by
        simp at hmem
        rcases hmem with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          exact h1
      rw [hjj]
      exact Nat.le_of_lt_succ hj'n
    · exfalso
      rcases List.mem_flatMap.mp hemit with ⟨e, _, hmem⟩
      simp [emissionBlock] at hmem

theorem mem_cs_re3 {n : Nat} (e : Emission) :
    CoreState.re3 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_re2 {n : Nat} (v3 : Bool) (e : Emission) :
    CoreState.re2 v3 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by cases v3 <;> simp [emissionBlock])

theorem mem_cs_re1 {n : Nat} (v3 v2 : Bool) (e : Emission) :
    CoreState.re1 v3 v2 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e)
    (by cases v3 <;> cases v2 <;> simp [emissionBlock])

theorem mem_cs_re0 {n : Nat} (e : Emission) :
    CoreState.re0 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_rt3 {n : Nat} (e : Emission) :
    CoreState.rt3 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_rt2 {n : Nat} (v3 : Bool) (e : Emission) :
    CoreState.rt2 v3 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by cases v3 <;> simp [emissionBlock])

theorem mem_cs_rt1 {n : Nat} (v3 v2 : Bool) (e : Emission) :
    CoreState.rt1 v3 v2 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e)
    (by cases v3 <;> cases v2 <;> simp [emissionBlock])

theorem mem_cs_rt0 {n : Nat} (e : Emission) :
    CoreState.rt0 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_hd0 {n : Nat} (v3 v2 : Bool) (e : Emission) :
    CoreState.hd0 v3 v2 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e)
    (by cases v3 <;> cases v2 <;> simp [emissionBlock])

theorem mem_cs_ls3 {n : Nat} (e : Emission) :
    CoreState.ls3 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_ls2 {n : Nat} (e : Emission) :
    CoreState.ls2 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_ls1 {n : Nat} (e : Emission) :
    CoreState.ls1 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_ls0 {n : Nat} (e : Emission) :
    CoreState.ls0 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_turn1 {n : Nat} (e : Emission) :
    CoreState.turn1 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_turn2 {n : Nat} (e : Emission) :
    CoreState.turn2 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_le0 {n : Nat} (e : Emission) :
    CoreState.le0 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_le1 {n : Nat} (e : Emission) :
    CoreState.le1 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_le2 {n : Nat} (e : Emission) :
    CoreState.le2 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by simp [emissionBlock])

theorem mem_cs_le3 {n : Nat} (v2 : Bool) (e : Emission) :
    CoreState.le3 v2 e ∈ coreStates n :=
  mem_coreStates_of_emission (e := e) (by cases v2 <;> simp [emissionBlock])

set_option maxHeartbeats 1600000 in
theorem next_target_mem (n : Nat) :
    forall s : CoreState, s ∈ coreStates n ->
      forall (r0 r1 r2 : Option Bool) (st : TypedStep CoreState),
        CoreState.next n s r0 r1 r2 = some st ->
          st.target ∈ coreStates n := by
  intro s hs r0 r1 r2 st hnext
  cases s <;> cases r0 <;> try (rename_i b; cases b)
  all_goals simp only [CoreState.next] at hnext
  all_goals repeat' split at hnext
  all_goals
    try
      (delta CoreState.streamLeft CoreState.streamRight Emission.stream at hnext;
        repeat' split at hnext)
  all_goals
    first
      | (cases hnext;
         first
           | (apply mem_coreStates_of_fixed; decide)
           | (apply mem_coreStates_of_fixed; simp [fixedStates]; done)
           | (rename_i a;
              cases a <;>
                (apply mem_coreStates_of_fixed;
                  simp [fixedStates]; done))
           | exact mem_coreStates_chk (chk_mem_bound hs) _
           | exact mem_coreStates_chk (Nat.zero_le n) _
           | (refine mem_coreStates_chk ?_ _;
              refine Nat.succ_le_of_lt ?_;
              assumption)
           | exact mem_cs_re3 _
           | exact mem_cs_re2 _ _
           | exact mem_cs_re1 _ _ _
           | exact mem_cs_re0 _
           | exact mem_cs_rt3 _
           | exact mem_cs_rt2 _ _
           | exact mem_cs_rt1 _ _ _
           | exact mem_cs_rt0 _
           | exact mem_cs_hd0 _ _ _
           | exact mem_cs_ls3 _
           | exact mem_cs_ls2 _
           | exact mem_cs_ls1 _
           | exact mem_cs_ls0 _
           | exact mem_cs_turn1 _
           | exact mem_cs_turn2 _
           | exact mem_cs_le0 _
           | exact mem_cs_le1 _
           | exact mem_cs_le2 _
           | exact mem_cs_le3 _ _)
      | cases hnext

/-- The typed state table of the fuel-output core for halt parameter n. -/
def table (n : Nat) : TypedStateTable CoreState :=
  TypedStateTable.ofList (coreStates n) CoreState.hdr0 CoreState.halt
    (CoreState.next n)
    (mem_coreStates_of_fixed (by decide))
    (mem_coreStates_of_fixed (by decide))
    (by
      intro r0 r1 r2
      cases r0 with
      | none => rfl
      | some b => cases b <;> rfl)
    (next_target_mem n)

end FuelOutputCore
end StructuredConstructionTargets

end Computability
end FoC
