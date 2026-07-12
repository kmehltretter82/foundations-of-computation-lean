import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutputCore.Machine
import FoC.Computability.Compiler.Dovetail.Scanner.TokenAligned

set_option doc.verso true

/-!
# Emission-stream theory for the fuel-output core

The fuel-output core streams the nonblank cells of the encoded configuration
tape in reverse order through the {lit}`Emission` tracker.  This module
develops the pure theory of that stream: folding the tracker over a bit list,
the coupling between the tracker's hold buffer and the tape-2 write shape, the
group-position arithmetic, and the equivalence between tracker acceptance and
membership in the image of {lit}`encodeCodeWordAsInput`.

No machine steps appear here; {lit}`Runs.lean` instantiates these facts along
the structured trajectory.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace FuelOutputCore

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-- Fold the emission tracker over a stream of bits. -/
def streamFold? : Emission -> List Bool -> Option Emission
  | e, [] => some e
  | e, bit :: rest =>
      match e.stream bit with
      | none => none
      | some e' => streamFold? e' rest

@[simp] theorem streamFold?_nil (e : Emission) :
    streamFold? e [] = some e := rfl

theorem streamFold?_cons (e : Emission) (bit : Bool) (rest : List Bool) :
    streamFold? e (bit :: rest) =
      match e.stream bit with
      | none => none
      | some e' => streamFold? e' rest := rfl

theorem streamFold?_cons_of_stream_some
    {e e' : Emission} {bit : Bool} (rest : List Bool)
    (h : e.stream bit = some e') :
    streamFold? e (bit :: rest) = streamFold? e' rest := by
  rw [streamFold?_cons, h]

theorem streamFold?_cons_of_stream_none
    {e : Emission} {bit : Bool} (rest : List Bool)
    (h : e.stream bit = none) :
    streamFold? e (bit :: rest) = none := by
  rw [streamFold?_cons, h]

theorem streamFold?_append (e : Emission) (a b : List Bool) :
    streamFold? e (List.append a b) =
      match streamFold? e a with
      | none => none
      | some e' => streamFold? e' b := by
  induction a generalizing e with
  | nil => rfl
  | cons bit rest ih =>
      show streamFold? e (bit :: List.append rest b) = _
      cases hstep : e.stream bit with
      | none =>
          rw [streamFold?_cons_of_stream_none (List.append rest b) hstep,
            streamFold?_cons_of_stream_none rest hstep]
      | some e1 =>
          rw [streamFold?_cons_of_stream_some (List.append rest b) hstep,
            streamFold?_cons_of_stream_some rest hstep]
          exact ih e1

theorem streamFold?_append_some
    {e e' : Emission} {a b : List Bool}
    (h : streamFold? e (List.append a b) = some e') :
    exists e1 : Emission,
      streamFold? e a = some e1 ∧ streamFold? e1 b = some e' := by
  rw [streamFold?_append] at h
  cases ha : streamFold? e a with
  | none =>
      rw [ha] at h
      cases h
  | some e1 =>
      rw [ha] at h
      exact ⟨e1, rfl, h⟩

/-!
## Hold-buffer tracking
-/

theorem stream_hold {e e' : Emission} {bit : Bool}
    (h : e.stream bit = some e') : e'.hold = some bit := by
  unfold Emission.stream at h
  cases hpos : e.pos <;> rw [hpos] at h
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · by_cases hcond : bit = false ∨ e.allF = true
    · rw [if_pos hcond] at h
      cases h; rfl
    · rw [if_neg hcond] at h
      cases h

theorem streamFold?_snoc_hold
    {e e' : Emission} {s : List Bool} {bit : Bool}
    (h : streamFold? e (List.append s [bit]) = some e') :
    e'.hold = some bit := by
  rcases streamFold?_append_some h with ⟨e1, _hs, hbit⟩
  rw [streamFold?_cons] at hbit
  cases hstep : e1.stream bit with
  | none =>
      rw [hstep] at hbit
      cases hbit
  | some e2 =>
      rw [hstep] at hbit
      have he2 : e2 = e' := by
        simpa using hbit
      rw [← he2]
      exact stream_hold hstep

theorem streamFold?_start_hold
    {e : Emission} {s : List Bool}
    (h : streamFold? Emission.start s = some e) :
    e.hold = s.getLast? := by
  cases hlast : s.getLast? with
  | none =>
      have hs : s = [] := List.getLast?_eq_none_iff.mp hlast
      subst s
      have he : Emission.start = e := by simpa using h
      rw [← he]
      rfl
  | some last =>
      rcases List.getLast?_eq_some_iff.mp hlast with ⟨front, rfl⟩
      simpa using streamFold?_snoc_hold h

/-!
## Position tracking
-/

/-- Advance a group position by one streamed bit. -/
def GroupPos.next : GroupPos -> GroupPos
  | GroupPos.p0 => GroupPos.p1
  | GroupPos.p1 => GroupPos.p2
  | GroupPos.p2 => GroupPos.p3
  | GroupPos.p3 => GroupPos.p0

/-- Advance a group position by a streamed bit count. -/
def GroupPos.advance : GroupPos -> Nat -> GroupPos
  | p, 0 => p
  | p, k + 1 => GroupPos.advance (GroupPos.next p) k

theorem GroupPos.advance_add (p : GroupPos) (a b : Nat) :
    GroupPos.advance p (a + b) =
      GroupPos.advance (GroupPos.advance p a) b := by
  induction a generalizing p with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by lia]
      show
        GroupPos.advance (GroupPos.next p) (a + b) =
          GroupPos.advance (GroupPos.advance (GroupPos.next p) a) b
      exact ih (GroupPos.next p)

theorem GroupPos.advance_four (p : GroupPos) :
    GroupPos.advance p 4 = p := by
  cases p <;> rfl

theorem GroupPos.advance_four_mul (p : GroupPos) (m : Nat) :
    GroupPos.advance p (4 * m) = p := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show 4 * (m + 1) = 4 * m + 4 by lia,
        GroupPos.advance_add, ih, GroupPos.advance_four]

theorem stream_pos {e e' : Emission} {bit : Bool}
    (h : e.stream bit = some e') : e'.pos = GroupPos.next e.pos := by
  unfold Emission.stream at h
  cases hpos : e.pos <;> rw [hpos] at h
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · by_cases hcond : bit = false ∨ e.allF = true
    · rw [if_pos hcond] at h
      cases h; rfl
    · rw [if_neg hcond] at h
      cases h

theorem streamFold?_pos {e e' : Emission} {s : List Bool}
    (h : streamFold? e s = some e') :
    e'.pos = GroupPos.advance e.pos s.length := by
  induction s generalizing e with
  | nil =>
      have he : e = e' := by simpa using h
      rw [← he]
      rfl
  | cons bit rest ih =>
      rw [streamFold?_cons] at h
      cases hstep : e.stream bit with
      | none =>
          rw [hstep] at h
          cases h
      | some e1 =>
          rw [hstep] at h
          have hpos1 := stream_pos hstep
          rw [ih h, hpos1]
          rfl

theorem length_mod_four_eq_zero_of_advance_p0
    {k : Nat} (h : GroupPos.advance GroupPos.p0 k = GroupPos.p0) :
    k % 4 = 0 := by
  have hk : k = 4 * (k / 4) + k % 4 := by
    lia
  rw [hk, GroupPos.advance_add, GroupPos.advance_four_mul] at h
  have hlt : k % 4 < 4 := by lia
  rcases hmod : k % 4 with _ | _ | _ | _ | r
  · rfl
  · rw [hmod] at h
    cases h
  · rw [hmod] at h
    cases h
  · rw [hmod] at h
    cases h
  · rw [hmod] at hlt
    lia

/-!
## Tape-2 write coupling

Streamed bits are written to logical tape 2 one event late through the hold
buffer: each stream event writes the previous hold with a left move, and the
final flush writes the last hold in place.  {lit}`emissionTape` is the tape-2
shape after a given stream prefix.
-/

/-- Tape 2 after streaming {lit}`s`: all but the held last bit, written
leftward. -/
def emissionTape (s : List Bool) : Tape Bool where
  left := (delayedLeftEmissionTape s).left
  head := (delayedLeftEmissionTape s).head
  right := (delayedLeftEmissionTape s).right

@[simp] theorem emissionTape_nil : emissionTape [] = Tape.blank := rfl

theorem emissionTape_read (s : List Bool) :
    Tape.read (emissionTape s) = none := rfl

theorem emitAction_apply_emissionTape
    {acc : List Bool} {e : Emission}
    (hacc : streamFold? Emission.start acc = some e) (bit : Bool) :
    e.emitAction.apply (emissionTape acc) =
      emissionTape (List.append acc [bit]) := by
  simpa [Emission.emitAction, emissionTape] using
    delayedLeftEmitAction_apply (streamFold?_start_hold hacc) bit

theorem flushAction_apply_emissionTape
    {acc : List Bool} {e : Emission}
    (hacc : streamFold? Emission.start acc = some e) :
    e.flushAction.apply (emissionTape acc) = Tape.input acc.reverse := by
  simpa [Emission.flushAction, emissionTape] using
    delayedLeftFlushAction_apply (streamFold?_start_hold hacc)

/-!
## Acceptance versus token alignment
-/

theorem stream_p0_congr {e : Emission} (he : e.pos = GroupPos.p0)
    (bit : Bool) : e.stream bit = Emission.start.stream bit := by
  unfold Emission.stream
  rw [he]
  rfl

theorem streamFold?_p0_congr {e : Emission} (he : e.pos = GroupPos.p0) :
    forall {s : List Bool}, s ≠ [] ->
      streamFold? e s = streamFold? Emission.start s := by
  intro s hs
  cases s with
  | nil => exact absurd rfl hs
  | cons bit rest =>
      rw [streamFold?_cons, streamFold?_cons, stream_p0_congr he]

/-- One reversed valid group folds successfully from any group boundary. -/
theorem streamFold?_symbol_reverse
    (t : MachineCodeSymbol) {e : Emission} (he : e.pos = GroupPos.p0) :
    exists e' : Emission,
      streamFold? e (encodeCodeSymbolAsInput t).reverse = some e' ∧
        e'.pos = GroupPos.p0 := by
  rw [streamFold?_p0_congr he (by cases t <;> simp [encodeCodeSymbolAsInput])]
  cases t <;> exact ⟨_, rfl, rfl⟩

/-- The reversed image of a code word is accepted at a group boundary. -/
theorem streamFold?_encode_reverse (code : Word MachineCodeSymbol) :
    exists e : Emission,
      streamFold? Emission.start
          (encodeCodeWordAsInput code).reverse = some e ∧
        e.pos = GroupPos.p0 := by
  induction code with
  | nil => exact ⟨Emission.start, rfl, rfl⟩
  | cons t rest ih =>
      rcases ih with ⟨e1, hfold1, hpos1⟩
      rcases streamFold?_symbol_reverse t hpos1 with ⟨e2, hfold2, hpos2⟩
      refine ⟨e2, ?_, hpos2⟩
      show
        streamFold? Emission.start
            (List.append (encodeCodeSymbolAsInput t)
              (encodeCodeWordAsInput rest)).reverse = some e2
      rw [show
          (List.append (encodeCodeSymbolAsInput t)
              (encodeCodeWordAsInput rest)).reverse =
            List.append (encodeCodeWordAsInput rest).reverse
              (encodeCodeSymbolAsInput t).reverse by
        simp]
      rw [streamFold?_append, hfold1]
      exact hfold2

/-- A stream group accepted through position {lit}`p3` is a reversed valid
token group. -/
theorem exists_symbol_of_streamFold?_group
    {a b c d : Bool} {e e' : Emission} (he : e.pos = GroupPos.p0)
    (h : streamFold? e [d, c, b, a] = some e') :
    exists t : MachineCodeSymbol,
      encodeCodeSymbolAsInput t = [a, b, c, d] := by
  rw [streamFold?_p0_congr he (by simp)] at h
  have hvalid : a = false ∨ (b = false ∧ c = false ∧ d = false) := by
    cases a <;> cases b <;> cases c <;> cases d <;>
      first
        | exact Or.inl rfl
        | exact Or.inr ⟨rfl, rfl, rfl⟩
        | exact nomatch h
  cases hvalid with
  | inl ha =>
      subst ha
      cases b <;> cases c <;> cases d
      · exact ⟨MachineCodeSymbol.header, rfl⟩
      · exact ⟨MachineCodeSymbol.transition, rfl⟩
      · exact ⟨MachineCodeSymbol.tick, rfl⟩
      · exact ⟨MachineCodeSymbol.done, rfl⟩
      · exact ⟨MachineCodeSymbol.blank, rfl⟩
      · exact ⟨MachineCodeSymbol.zero, rfl⟩
      · exact ⟨MachineCodeSymbol.one, rfl⟩
      · exact ⟨MachineCodeSymbol.moveLeft, rfl⟩
  | inr hbcd =>
      rcases hbcd with ⟨hb, hc, hd⟩
      subst hb; subst hc; subst hd
      cases a
      · exact ⟨MachineCodeSymbol.header, rfl⟩
      · exact ⟨MachineCodeSymbol.moveRight, rfl⟩

private theorem exists_four_of_length_eq_four
    {g : List Bool} (h : g.length = 4) :
    exists a b c d : Bool, g = [a, b, c, d] := by
  cases g with
  | nil => cases h
  | cons a g =>
      cases g with
      | nil => cases h
      | cons b g =>
          cases g with
          | nil => cases h
          | cons c g =>
              cases g with
              | nil => cases h
              | cons d g =>
                  cases g with
                  | nil => exact ⟨a, b, c, d, rfl⟩
                  | cons x g => cases h

private theorem exists_code_of_streamFold?_reverse_fueled :
    forall (fuel : Nat) (w : List Bool), w.length ≤ fuel ->
      forall {e : Emission},
        streamFold? Emission.start w.reverse = some e ->
          e.pos = GroupPos.p0 ->
            exists code : Word MachineCodeSymbol,
              w = encodeCodeWordAsInput code := by
  intro fuel
  induction fuel with
  | zero =>
      intro w hlen e hfold hpos
      have hw : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hw
      exact ⟨[], rfl⟩
  | succ fuel ih =>
      intro w hlen e hfold hpos
      by_cases hwnil : w = []
      · subst hwnil
        exact ⟨[], rfl⟩
      · have hmod : w.length % 4 = 0 := by
          apply length_mod_four_eq_zero_of_advance_p0
          have hposAdv := streamFold?_pos hfold
          rw [List.length_reverse] at hposAdv
          exact hposAdv.symm.trans hpos
        have hlenPos : 0 < w.length :=
          Nat.pos_of_ne_zero
            (fun h0 => hwnil (List.length_eq_zero_iff.mp h0))
        have hfour : 4 ≤ w.length := by
          rcases Nat.lt_or_ge w.length 4 with hlt | hge
          · exfalso
            have := Nat.mod_eq_of_lt hlt
            lia
          · exact hge
        obtain ⟨w', g, hsplit, hglen, hw'len⟩ :
            exists w' g : List Bool,
              w = List.append w' g ∧
                g.length = 4 ∧ w'.length = w.length - 4 := by
          refine
            ⟨w.take (w.length - 4), w.drop (w.length - 4), ?_, ?_, ?_⟩
          · simp
          · rw [List.length_drop]
            lia
          · rw [List.length_take]
            exact Nat.min_eq_left (by lia)
        rcases exists_four_of_length_eq_four hglen with ⟨a, b, c, d, habcd⟩
        have hrev :
            w.reverse =
              List.append [d, c, b, a] w'.reverse := by
          rw [hsplit, habcd]
          simp
        rw [hrev] at hfold
        rcases streamFold?_append_some hfold with ⟨e1, hfold1, hfold2⟩
        have hpos1 : e1.pos = GroupPos.p0 :=
          (streamFold?_pos hfold1).trans rfl
        rcases exists_symbol_of_streamFold?_group rfl hfold1 with ⟨t, ht⟩
        by_cases hw'nil : w' = []
        · refine ⟨[t], ?_⟩
          rw [hsplit, hw'nil, habcd, ← ht]
          show
            List.append [] (encodeCodeSymbolAsInput t) =
              encodeCodeWordAsInput [t]
          rw [encodeCodeWordAsInput_singleton]
          rfl
        · have hw'ne : w'.reverse ≠ [] := by
            intro hcontra
            exact hw'nil (by simpa using congrArg List.reverse hcontra)
          rw [streamFold?_p0_congr hpos1 hw'ne] at hfold2
          have hw'lt : w'.length ≤ fuel := by
            rw [hw'len]
            lia
          rcases ih w' hw'lt hfold2 hpos with ⟨code', hcode'⟩
          refine ⟨List.append code' [t], ?_⟩
          rw [hsplit, hcode', habcd, ← ht,
            encodeCodeWordAsInput_append,
            encodeCodeWordAsInput_singleton]

/-- Acceptance at a group boundary forces the forward word into the image of
{name}`encodeCodeWordAsInput`. -/
theorem exists_code_of_streamFold?_reverse
    {w : List Bool} {e : Emission}
    (hfold : streamFold? Emission.start w.reverse = some e)
    (hpos : e.pos = GroupPos.p0) :
    exists code : Word MachineCodeSymbol,
      w = encodeCodeWordAsInput code :=
  exists_code_of_streamFold?_reverse_fueled
    w.length w (Nat.le_refl _) hfold hpos

end FuelOutputCore
end StructuredConstructionTargets

end Computability
end FoC
