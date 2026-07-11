import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.StateSelector

set_option doc.verso true

/-!
# Exact runs of the raw-state selector phase

This module proves the two independent executions of {lit}`StateSelector`:
the canonical unary state parser reaches the correct finite classification,
and the selector microprogram overwrites exactly the reserved scratch markers
before restoring the right blank.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace StateSelector

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets.FuelOutputCore
open ClassifiedBoundary

/-!
## Step-count-free execution
-/

def cfg
    (D : MachineDescription) (s : State D)
    (T0 T1 T2 : Tape Bool) :
    CommonGround.FiniteTransducers.Structured.Configuration :=
  ThreeTape.config ((table D).stateId s) T0 T1 T2

def Leads
    (D : MachineDescription)
    (c d : CommonGround.FiniteTransducers.Structured.Configuration) : Prop :=
  exists steps : Nat,
    forall tail : Nat,
      (description D).runConfig (tail + steps) c =
        (description D).runConfig tail d

namespace Leads

theorem refl
    (D : MachineDescription)
    (c : CommonGround.FiniteTransducers.Structured.Configuration) :
    Leads D c c :=
  ⟨0, fun _ => rfl⟩

theorem trans
    {D : MachineDescription}
    {c d e : CommonGround.FiniteTransducers.Structured.Configuration}
    (hcd : Leads D c d) (hde : Leads D d e) : Leads D c e := by
  rcases hcd with ⟨first, hfirst⟩
  rcases hde with ⟨second, hsecond⟩
  refine ⟨second + first, fun tail => ?_⟩
  rw [show tail + (second + first) =
      (tail + second) + first by lia]
  rw [hfirst (tail + second), hsecond tail]

theorem to_runConfig
    {D : MachineDescription}
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (h : Leads D c d) :
    exists steps : Nat, (description D).runConfig steps c = d := by
  rcases h with ⟨steps, hsteps⟩
  exact ⟨steps, by simpa [Description.runConfig] using hsteps 0⟩

end Leads

theorem leads_step
    {D : MachineDescription}
    {s target : State D} (hs : s ∈ states D)
    {T0 T1 T2 : Tape Bool} {a0 a1 a2 : TapeAction}
    (hnext :
      next D s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some ⟨target, a0, a1, a2⟩)
    {T0' T1' T2' : Tape Bool}
    (h0 : a0.apply T0 = T0')
    (h1 : a1.apply T1 = T1')
    (h2 : a2.apply T2 = T2') :
    Leads D (cfg D s T0 T1 T2) (cfg D target T0' T1' T2') := by
  refine ⟨1, fun tail => ?_⟩
  have hstep := (table D).runConfig_succ_config hs hnext tail
  change
    (table D).description.runConfig (tail + 1)
        (ThreeTape.config ((table D).stateId s) T0 T1 T2) =
      (table D).description.runConfig tail
        (ThreeTape.config ((table D).stateId target) T0' T1' T2')
  rw [hstep, h0, h1, h2]

theorem stepR_keep
    {D : MachineDescription} {s target : State D}
    (hs : s ∈ states D) {cell : Option Bool}
    (hnext :
      forall r1 r2 : Option Bool,
        next D s cell r1 r2 =
          some ⟨target, keepR, keepS, keepS⟩)
    (leftRev right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads D
      (cfg D s (tapeAtCells leftRev (cell :: right)) T1 T2)
      (cfg D target (tapeAtCells (cell :: leftRev) right) T1 T2) := by
  apply leads_step
    (s := s) (target := target)
    (T0 := tapeAtCells leftRev (cell :: right))
    (T1 := T1) (T2 := T2)
    hs (hnext (Tape.read T1) (Tape.read T2))
  · exact keepR_apply_tapeAtCells leftRev cell right
  · rfl
  · rfl

/-!
## Unary state parsing
-/

@[simp] theorem codeBits_encodeNat_zero :
    codeBits (encodeNat 0) = tokBits MachineCodeSymbol.done := by
  rfl

theorem codeBits_encodeNat_succ (n : Nat) :
    codeBits (encodeNat (n + 1)) =
      List.append (tokBits MachineCodeSymbol.tick)
        (codeBits (encodeNat n)) := by
  rfl

theorem pushBits_encodeNat_succ
    (n : Nat) (leftRev : List (Option Bool)) :
    pushBits (codeBits (encodeNat (n + 1))) leftRev =
      pushBits (codeBits (encodeNat n))
        (pushBits (tokBits MachineCodeSymbol.tick) leftRev) := by
  rw [codeBits_encodeNat_succ, pushBits_append]

theorem nextCount?_eq_some
    {D : MachineDescription} (count : Fin (stateBound D))
    (hnext : count.val + 1 < stateBound D) :
    nextCount? count = some ⟨count.val + 1, hnext⟩ := by
  simp [nextCount?, hnext]

theorem nextCount?_eq_none
    {D : MachineDescription} (count : Fin (stateBound D))
    (hnext : ¬ count.val + 1 < stateBound D) :
    nextCount? count = none := by
  simp [nextCount?, hnext]

/-- Parse a unary suffix while the accumulated value remains in finite
control. -/
theorem leads_parse_within
    (D : MachineDescription) (remaining : Nat)
    (count : Fin (stateBound D))
    (hbound : count.val + remaining < stateBound D)
    (leftRev right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads D
      (cfg D (.parse count .p0)
        (tapeAtCells leftRev
          (List.append (codeBits (encodeNat remaining)) right)) T1 T2)
      (cfg D (.mark (classifyState D (count.val + remaining)))
        (tapeAtCells
          (pushBits (codeBits (encodeNat remaining)) leftRev) right) T1 T2) := by
  induction remaining generalizing count leftRev with
  | zero =>
      simpa [pushBits] using
        (stepR_keep (D := D) (state_mem D _)
          (fun _ _ => rfl) leftRev _ T1 T2).trans
          ((stepR_keep (D := D) (state_mem D _)
            (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_keep (D := D) (state_mem D _)
              (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_keep (D := D) (state_mem D _)
                (fun _ _ => rfl) _ right T1 T2)))
  | succ n ih =>
      have hnext : count.val + 1 < stateBound D := by lia
      let count' : Fin (stateBound D) :=
        ⟨count.val + 1, hnext⟩
      have hrow :
          nextCount? count = some count' := by
        exact nextCount?_eq_some count hnext
      have htick :
          Leads D
            (cfg D (.parse count .p0)
              (tapeAtCells leftRev
                (List.append (codeBits (encodeNat (n + 1))) right)) T1 T2)
            (cfg D (.parse count' .p0)
              (tapeAtCells
                (pushBits (tokBits MachineCodeSymbol.tick) leftRev)
                (List.append (codeBits (encodeNat n)) right)) T1 T2) :=
        (stepR_keep (D := D) (state_mem D _)
          (fun _ _ => rfl) leftRev _ T1 T2).trans
          ((stepR_keep (D := D) (state_mem D _)
            (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_keep (D := D) (state_mem D _)
              (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_keep (D := D) (state_mem D _)
                (fun _ _ => by simp [next, hrow]) _ _ T1 T2)))
      refine htick.trans ?_
      rw [pushBits_encodeNat_succ]
      simpa [count', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih count' (by simp [count']; lia)
          (pushBits (tokBits MachineCodeSymbol.tick) leftRev)

/-- Once the count exceeds the finite bound, skip the rest of the canonical
unary field and select the generic class. -/
theorem leads_overflow
    (D : MachineDescription) (remaining : Nat)
    (leftRev right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads D
      (cfg D (.overflow .p0)
        (tapeAtCells leftRev
          (List.append (codeBits (encodeNat remaining)) right)) T1 T2)
      (cfg D (.mark (.other : StateClass D))
        (tapeAtCells
          (pushBits (codeBits (encodeNat remaining)) leftRev) right) T1 T2) := by
  induction remaining generalizing leftRev with
  | zero =>
      simpa [pushBits] using
        (stepR_keep (D := D) (state_mem D _)
          (fun _ _ => rfl) leftRev _ T1 T2).trans
          ((stepR_keep (D := D) (state_mem D _)
            (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_keep (D := D) (state_mem D _)
              (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_keep (D := D) (state_mem D _)
                (fun _ _ => rfl) _ right T1 T2)))
  | succ n ih =>
      have htick :
          Leads D
            (cfg D (.overflow .p0)
              (tapeAtCells leftRev
                (List.append (codeBits (encodeNat (n + 1))) right)) T1 T2)
            (cfg D (.overflow .p0)
              (tapeAtCells
                (pushBits (tokBits MachineCodeSymbol.tick) leftRev)
                (List.append (codeBits (encodeNat n)) right)) T1 T2) :=
        (stepR_keep (D := D) (state_mem D _)
          (fun _ _ => rfl) leftRev _ T1 T2).trans
          ((stepR_keep (D := D) (state_mem D _)
            (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_keep (D := D) (state_mem D _)
              (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_keep (D := D) (state_mem D _)
                (fun _ _ => rfl) _ _ T1 T2)))
      refine htick.trans ?_
      rw [pushBits_encodeNat_succ]
      exact ih (pushBits (tokBits MachineCodeSymbol.tick) leftRev)

/-- Code of a fixed number of tick tokens. -/
def tickCode (ticks : Nat) : Word MachineCodeSymbol :=
  List.replicate ticks MachineCodeSymbol.tick

theorem encodeNat_eq_tickCode_append_done (n : Nat) :
    encodeNat n = List.append (tickCode n) [MachineCodeSymbol.done] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [encodeNat, tickCode, List.replicate_succ, ih]

theorem encodeNat_split
    (prefixTicks total : Nat) (hle : prefixTicks ≤ total) :
    encodeNat total =
      List.append (tickCode prefixTicks)
        (encodeNat (total - prefixTicks)) := by
  rw [encodeNat_eq_tickCode_append_done,
    encodeNat_eq_tickCode_append_done]
  have hrep :=
    FoC.Computability.list_replicate_add_append
      MachineCodeSymbol.tick prefixTicks (total - prefixTicks)
      [MachineCodeSymbol.done]
  rw [Nat.add_sub_of_le hle] at hrep
  exact hrep

theorem codeBits_tickCode_succ (ticks : Nat) :
    codeBits (tickCode (ticks + 1)) =
      List.append (tokBits MachineCodeSymbol.tick)
        (codeBits (tickCode ticks)) := by
  simp [tickCode, List.replicate_succ, codeBits_cons]

theorem pushBits_tickCode_succ
    (ticks : Nat) (leftRev : List (Option Bool)) :
    pushBits (codeBits (tickCode (ticks + 1))) leftRev =
      pushBits (codeBits (tickCode ticks))
        (pushBits (tokBits MachineCodeSymbol.tick) leftRev) := by
  rw [codeBits_tickCode_succ, pushBits_append]

/-- Consume exactly enough tick tokens to leave bounded finite control. -/
theorem leads_parse_to_overflow
    (D : MachineDescription) (ticksAfter : Nat)
    (count : Fin (stateBound D))
    (ticksBefore : Nat)
    (hboundary : count.val + ticksBefore + 1 = stateBound D)
    (leftRev right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads D
      (cfg D (.parse count .p0)
        (tapeAtCells leftRev
          (List.append (codeBits (tickCode (ticksBefore + 1)))
            (List.append (codeBits (encodeNat ticksAfter)) right))) T1 T2)
      (cfg D (.overflow .p0)
        (tapeAtCells
          (pushBits (codeBits (tickCode (ticksBefore + 1))) leftRev)
          (List.append (codeBits (encodeNat ticksAfter)) right)) T1 T2) := by
  induction ticksBefore generalizing count leftRev with
  | zero =>
      have hnone : ¬ count.val + 1 < stateBound D := by lia
      have hrow : nextCount? count = none :=
        nextCount?_eq_none count hnone
      simpa [tickCode, codeBits_cons, codeBits_nil, pushBits] using
        (stepR_keep (D := D) (state_mem D _)
          (fun _ _ => rfl) leftRev _ T1 T2).trans
          ((stepR_keep (D := D) (state_mem D _)
            (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_keep (D := D) (state_mem D _)
              (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_keep (D := D) (state_mem D _)
                (fun _ _ => by simp [next, hrow]) _ _ T1 T2)))
  | succ ticks ih =>
      have hnext : count.val + 1 < stateBound D := by lia
      let count' : Fin (stateBound D) :=
        ⟨count.val + 1, hnext⟩
      have hrow : nextCount? count = some count' :=
        nextCount?_eq_some count hnext
      have htick :
          Leads D
            (cfg D (.parse count .p0)
              (tapeAtCells leftRev
                (List.append (codeBits (tickCode (ticks + 1 + 1)))
                  (List.append (codeBits (encodeNat ticksAfter)) right)))
              T1 T2)
            (cfg D (.parse count' .p0)
              (tapeAtCells
                (pushBits (tokBits MachineCodeSymbol.tick) leftRev)
                (List.append (codeBits (tickCode (ticks + 1)))
                  (List.append (codeBits (encodeNat ticksAfter)) right)))
              T1 T2) :=
        (stepR_keep (D := D) (state_mem D _)
          (fun _ _ => rfl) leftRev _ T1 T2).trans
          ((stepR_keep (D := D) (state_mem D _)
            (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_keep (D := D) (state_mem D _)
              (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_keep (D := D) (state_mem D _)
                (fun _ _ => by simp [next, hrow]) _ _ T1 T2)))
      refine htick.trans ?_
      rw [pushBits_tickCode_succ]
      simpa [count', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih count' (by simp [count']; lia)
          (pushBits (tokBits MachineCodeSymbol.tick) leftRev)

/-- The canonical state parser always reaches the tag computed by
{name}`classifyState`. -/
theorem leads_parse
    (D : MachineDescription) (rawState : Nat)
    (leftRev right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads D
      (cfg D (.parse (zeroCount D) .p0)
        (tapeAtCells leftRev
          (List.append (codeBits (encodeNat rawState)) right)) T1 T2)
      (cfg D (.mark (classifyState D rawState))
        (tapeAtCells
          (pushBits (codeBits (encodeNat rawState)) leftRev) right) T1 T2) := by
  by_cases hsmall : rawState < stateBound D
  · simpa [zeroCount] using
      leads_parse_within D rawState (zeroCount D)
        (by simp [zeroCount]; exact hsmall) leftRev right T1 T2
  · have hle : stateBound D ≤ rawState := by lia
    let rest := rawState - stateBound D
    have hsplit := encodeNat_split (stateBound D) rawState hle
    have hclass : classifyState D rawState = StateClass.other := by
      apply classifyState_of_not_mem
      intro hmem
      have hlt := mem_fixedStepValues_lt_stateBound hmem
      lia
    rw [hclass]
    rw [hsplit]
    rw [codeBits_append, pushBits_append]
    have hto :
        Leads D
          (cfg D (.parse (zeroCount D) .p0)
            (tapeAtCells leftRev
              (List.append (codeBits (tickCode (stateBound D)))
                (List.append (codeBits (encodeNat rest)) right))) T1 T2)
          (cfg D (.overflow .p0)
            (tapeAtCells
              (pushBits (codeBits (tickCode (stateBound D))) leftRev)
              (List.append (codeBits (encodeNat rest)) right)) T1 T2) := by
      have hbound :
          (zeroCount D).val + (stateBound D - 1) + 1 = stateBound D := by
        simp [zeroCount]
        have := stateBound_pos D
        lia
      simpa [show stateBound D - 1 + 1 = stateBound D by
          have := stateBound_pos D; lia] using
        leads_parse_to_overflow D rest (zeroCount D)
          (stateBound D - 1) hbound leftRev right T1 T2
    have hfull := hto.trans
      (leads_overflow D rest
        (pushBits (codeBits (tickCode (stateBound D))) leftRev)
        right T1 T2)
    simpa [rest, List.append_assoc] using hfull

/-!
## Exact selector emission
-/

/-- Tape-2 cursor while selector bits are written leftward.  The emitted
prefix lies nearest the temporary false marker on the right; the unconsumed
reserved cells are still true. -/
def emissionTape
    (emitted remaining : Word Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  match remaining with
  | [] => tapeAtCells tail
      (List.append (emitted.reverse.map some) [some false])
  | _ :: rest =>
      tapeAtCells
        (List.append
          (List.replicate rest.length (some true : Option Bool)) tail)
        (some true ::
          List.append (emitted.reverse.map some) [some false])

/-- Rightward return cursor after the final selector bit was written. -/
def selectorReturnTape
    (walk : Word Bool) (leftRev : List (Option Bool)) : Tape Bool :=
  tapeAtCells leftRev
    (List.append (walk.map some) [some false])

theorem writeL_mark_selector
    (bits : Word Bool) (hbits : bits ≠ [])
    (tail : List (Option Bool)) :
    (writeL (some false)).apply
        (tapeAtCells
          (List.append
            (List.replicate bits.length (some true : Option Bool)) tail) []) =
      emissionTape [] bits tail := by
  cases bits with
  | nil => contradiction
  | cons bit rest =>
      simp [emissionTape, writeL, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveLeft, tapeAtCells,
        List.replicate_succ]

theorem writeL_emissionTape
    (emitted : Word Bool) (bit nextBit : Bool)
    (rest : Word Bool) (tail : List (Option Bool)) :
    (writeL (some bit)).apply
        (emissionTape emitted (bit :: nextBit :: rest) tail) =
      emissionTape (List.append emitted [bit]) (nextBit :: rest) tail := by
  simp [emissionTape, writeL, TapeAction.apply, HeadMove.apply,
    Tape.write, Tape.move, Tape.moveLeft, tapeAtCells,
    List.replicate_succ, List.reverse_append]

theorem writeR_emissionTape_last
    (emitted : Word Bool) (bit : Bool)
    (tail : List (Option Bool)) :
    (writeR (some bit)).apply (emissionTape emitted [bit] tail) =
      selectorReturnTape emitted.reverse (some bit :: tail) := by
  change
    (writeR (some bit)).apply
        (tapeAtCells tail
          (some true ::
            List.append (emitted.reverse.map some) [some false])) =
      tapeAtCells (some bit :: tail)
        (List.append (emitted.reverse.map some) [some false])
  exact writeR_apply_tapeAtCells
    (some bit) tail (some true)
    (List.append (emitted.reverse.map some) [some false])

theorem keepR_selectorReturnTape
    (bit : Bool) (rest : Word Bool)
    (leftRev : List (Option Bool)) :
    keepR.apply (selectorReturnTape (bit :: rest) leftRev) =
      selectorReturnTape rest (some bit :: leftRev) := by
  cases rest <;>
    rfl

theorem writeS_none_selectorReturnTape_done
    (leftRev : List (Option Bool)) :
    (writeS none).apply (selectorReturnTape [] leftRev) =
      tapeAtCells leftRev [] := by
  rfl

def emitIndexFor
    {D : MachineDescription} (tag : StateClass D)
    (emittedPrefix remaining : Word Bool)
    (hsplit : selectorBits tag = List.append emittedPrefix remaining)
    (hremaining : remaining ≠ []) :
    Fin (selectorBits tag).length :=
  ⟨emittedPrefix.length, by
    have hlen := congrArg List.length hsplit
    simp at hlen
    cases remaining with
    | nil => contradiction
    | cons bit rest =>
        simp at hlen
        lia⟩

def returnStepsFor
    {D : MachineDescription} (tag : StateClass D)
    (walk : Word Bool)
    (hwalk : walk.length < (selectorBits tag).length + 1) :
    Fin ((selectorBits tag).length + 1) :=
  ⟨walk.length, hwalk⟩

theorem leads_tape2
    {D : MachineDescription} {s target : State D}
    (hs : s ∈ states D)
    {T0 T1 T2 : Tape Bool} {a2 : TapeAction}
    (hnext :
      next D s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some ⟨target, keepS, keepS, a2⟩)
    {T2' : Tape Bool} (h2 : a2.apply T2 = T2') :
    Leads D (cfg D s T0 T1 T2) (cfg D target T0 T1 T2') := by
  apply leads_step hs hnext
  · rfl
  · rfl
  · exact h2

/-- Return right across the already-emitted prefix, restore the temporary
blank, and halt. -/
theorem leads_selector_return
    (D : MachineDescription) (tag : StateClass D)
    (walk : Word Bool) (leftRev : List (Option Bool))
    (T0 T1 : Tape Bool)
    (hwalk : walk.length < (selectorBits tag).length + 1) :
    Leads D
      (cfg D (.rewind tag (returnStepsFor tag walk hwalk))
        T0 T1 (selectorReturnTape walk leftRev))
      (cfg D .halt T0 T1
        (tapeAtCells
          (List.append (walk.reverse.map some) leftRev) [])) := by
  induction walk generalizing leftRev with
  | nil =>
      have hzero : (returnStepsFor tag [] hwalk).val = 0 := rfl
      have htoRestore :
          Leads D
            (cfg D (.rewind tag (returnStepsFor tag [] hwalk))
              T0 T1 (selectorReturnTape [] leftRev))
            (cfg D (.restore tag)
              T0 T1 (selectorReturnTape [] leftRev)) := by
        apply leads_tape2 (a2 := keepS)
          (state_mem D _) (by simp [next, hzero])
        rfl
      have htoHalt :
          Leads D
            (cfg D (.restore tag)
              T0 T1 (selectorReturnTape [] leftRev))
            (cfg D .halt T0 T1 (tapeAtCells leftRev [])) := by
        apply leads_tape2 (a2 := writeS none)
          (state_mem D _) (by rfl)
        exact writeS_none_selectorReturnTape_done leftRev
      simpa using htoRestore.trans htoHalt
  | cons bit rest ih =>
      have hpos : 0 < (returnStepsFor tag (bit :: rest) hwalk).val := by
        simp [returnStepsFor]
      have hne :
          (returnStepsFor tag (bit :: rest) hwalk).val ≠ 0 := by
        lia
      have hrest : rest.length < (selectorBits tag).length + 1 := by
        simp at hwalk
        lia
      have hstate :
          predReturnSteps
              (returnStepsFor tag (bit :: rest) hwalk) hpos =
            returnStepsFor tag rest hrest := by
        apply Fin.ext
        simp [predReturnSteps, returnStepsFor]
      have hone :
          Leads D
            (cfg D (.rewind tag
                (returnStepsFor tag (bit :: rest) hwalk))
              T0 T1 (selectorReturnTape (bit :: rest) leftRev))
            (cfg D (.rewind tag (returnStepsFor tag rest hrest))
              T0 T1 (selectorReturnTape rest (some bit :: leftRev))) := by
        apply leads_tape2 (a2 := keepR) (state_mem D _)
          (by simp [next, hne, hstate])
        exact keepR_selectorReturnTape bit rest leftRev
      refine hone.trans ?_
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: leftRev) hrest

/-- Emit the unconsumed suffix of a selector from the matching finite index. -/
theorem leads_selector_emit
    (D : MachineDescription) (tag : StateClass D)
    (emittedPrefix remaining : Word Bool)
    (hsplit : selectorBits tag = List.append emittedPrefix remaining)
    (hremaining : remaining ≠ [])
    (tail : List (Option Bool))
    (T0 T1 : Tape Bool) :
    Leads D
      (cfg D (.emit tag
          (emitIndexFor tag emittedPrefix remaining hsplit hremaining))
        T0 T1 (emissionTape emittedPrefix remaining tail))
      (cfg D .halt T0 T1
        (tapeAtCells
          (List.append ((selectorBits tag).map some) tail) [])) := by
  induction remaining generalizing emittedPrefix with
  | nil => contradiction
  | cons bit rest ih =>
      cases rest with
      | nil =>
          have hlast :
              (emitIndexFor tag emittedPrefix [bit] hsplit (by simp)).val + 1 =
                (selectorBits tag).length := by
            have hlen := congrArg List.length hsplit
            simp [emitIndexFor] at hlen ⊢
            lia
          have hget :
              (selectorBits tag).get
                  (emitIndexFor tag emittedPrefix [bit] hsplit (by simp)) = bit := by
            simp [List.get_eq_getElem, hsplit, emitIndexFor]
          rw [List.get_eq_getElem] at hget
          have hreturn :
              emittedPrefix.reverse.length < (selectorBits tag).length + 1 := by
            have hlen := congrArg List.length hsplit
            simp at hlen
            rw [List.length_reverse]
            lia
          have hstate :
              initialReturnSteps
                  (emitIndexFor tag emittedPrefix [bit] hsplit (by simp)) =
                returnStepsFor tag emittedPrefix.reverse hreturn := by
            apply Fin.ext
            simp [initialReturnSteps, emitIndexFor, returnStepsFor]
          have hone :
              Leads D
                (cfg D (.emit tag
                    (emitIndexFor tag emittedPrefix [bit] hsplit (by simp)))
                  T0 T1 (emissionTape emittedPrefix [bit] tail))
                (cfg D (.rewind tag
                    (returnStepsFor tag emittedPrefix.reverse hreturn))
                  T0 T1
                  (selectorReturnTape emittedPrefix.reverse (some bit :: tail))) := by
            apply leads_tape2 (a2 := writeR (some bit))
              (state_mem D _)
              (by simp [next, hlast, hget, hstate])
            exact writeR_emissionTape_last emittedPrefix bit tail
          refine hone.trans ?_
          have hrewind :=
            leads_selector_return D tag emittedPrefix.reverse (some bit :: tail)
              T0 T1 hreturn
          simpa [hsplit, List.map_append, List.append_assoc] using hrewind
      | cons nextBit rest =>
          have hnotLast :
              (emitIndexFor tag emittedPrefix (bit :: nextBit :: rest)
                  hsplit (by simp)).val + 1 ≠
                (selectorBits tag).length := by
            have hlen := congrArg List.length hsplit
            simp [emitIndexFor] at hlen ⊢
            lia
          have hnext :
              (emitIndexFor tag emittedPrefix (bit :: nextBit :: rest)
                  hsplit (by simp)).val + 1 <
                (selectorBits tag).length := by
            have hlen := congrArg List.length hsplit
            simp [emitIndexFor] at hlen ⊢
            lia
          let emittedPrefix' := List.append emittedPrefix [bit]
          have hsplit' :
              selectorBits tag =
                List.append emittedPrefix' (nextBit :: rest) := by
            simpa [emittedPrefix', List.append_assoc] using hsplit
          have hstate :
              succEmitIndex
                  (emitIndexFor tag emittedPrefix (bit :: nextBit :: rest)
                    hsplit (by simp)) hnext =
                emitIndexFor tag emittedPrefix' (nextBit :: rest)
                  hsplit' (by simp) := by
            apply Fin.ext
            simp [succEmitIndex, emitIndexFor, emittedPrefix']
          have hget :
              (selectorBits tag).get
                  (emitIndexFor tag emittedPrefix (bit :: nextBit :: rest)
                    hsplit (by simp)) = bit := by
            simp [List.get_eq_getElem, hsplit, emitIndexFor]
          rw [List.get_eq_getElem] at hget
          have hone :
              Leads D
                (cfg D (.emit tag
                    (emitIndexFor tag emittedPrefix (bit :: nextBit :: rest)
                      hsplit (by simp)))
                  T0 T1
                  (emissionTape emittedPrefix (bit :: nextBit :: rest) tail))
                (cfg D (.emit tag
                    (emitIndexFor tag emittedPrefix' (nextBit :: rest)
                      hsplit' (by simp)))
                  T0 T1
                  (emissionTape emittedPrefix' (nextBit :: rest) tail)) := by
            apply leads_tape2 (a2 := writeL (some bit))
              (state_mem D _)
              (by simp [next, hnotLast, hget, hstate])
            exact writeL_emissionTape emittedPrefix bit nextBit rest tail
          refine hone.trans ?_
          exact ih emittedPrefix' hsplit' (by simp)

/-- Complete selector microprogram from a true reserved block. -/
theorem leads_selector_mark
    (D : MachineDescription) (tag : StateClass D)
    (tail : List (Option Bool)) (T0 T1 : Tape Bool) :
    Leads D
      (cfg D (.mark tag) T0 T1
        (tapeAtCells
          (List.append
            (List.replicate (selectorBits tag).length
              (some true : Option Bool)) tail) []))
      (cfg D .halt T0 T1
        (tapeAtCells
          (List.append ((selectorBits tag).map some) tail) [])) := by
  have hbits : selectorBits tag ≠ [] :=
    List.ne_nil_of_length_pos (selectorBits_length_pos tag)
  have hmark :
      Leads D
        (cfg D (.mark tag) T0 T1
          (tapeAtCells
            (List.append
              (List.replicate (selectorBits tag).length
                (some true : Option Bool)) tail) []))
        (cfg D (.emit tag (initialEmitIndex tag))
          T0 T1 (emissionTape [] (selectorBits tag) tail)) := by
    apply leads_tape2 (state_mem D _) (by rfl)
    exact writeL_mark_selector (selectorBits tag) hbits tail
  have hindex :
      initialEmitIndex tag =
        emitIndexFor tag [] (selectorBits tag)
          (by simp) hbits := by
    apply Fin.ext
    rfl
  rw [hindex] at hmark
  exact hmark.trans
    (leads_selector_emit D tag [] (selectorBits tag)
      (by simp) hbits tail T0 T1)

/-!
## Simulator-layout specialization
-/

theorem postStageTokens_eq_state_append (L : SimulatorLayout) :
    StageCounter.postStageTokens L =
      List.append (encodeNat L.config.state) (postStateTokens L) := by
  simp [StageCounter.postStageTokens, postStateTokens]

theorem postStageTape_eq_stateField (L : SimulatorLayout) :
    StageCounter.postStageTape L =
      tapeAtCells
        (pushBits (codeBits (encodeNat L.stage))
          (pushBits (codeBits ((L.input.map some).map cellTok))
            (pushBits (codeBits (encodeNat (L.input.map some).length))
              (pushBits (tokBits MachineCodeSymbol.header) [none]))))
        (List.append (codeBits (encodeNat L.config.state))
          (List.append (codeBits (postStateTokens L)) [none])) := by
  unfold StageCounter.postStageTape
  rw [postStageTokens_eq_state_append]
  rw [codeBits_append]
  simp [List.append_assoc]

theorem layoutMarkerTape_eq_reserved
    (D : MachineDescription) (L : SimulatorLayout) :
    SourceCounter.layoutMarkerTape L =
      tapeAtCells
        (List.append
          (List.replicate
            (selectorBits (classifyState D L.config.state)).length
            (some true : Option Bool))
          (remainingScratchMarkers D L)) [] := by
  apply congrArg (fun cells => tapeAtCells cells [])
  exact (restoredScratchMarkers_eq D L).symm

theorem leads_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    Leads D
      (cfg D (.parse (zeroCount D) .p0)
        (StageCounter.postStageTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (SourceCounter.layoutMarkerTape L))
      (cfg D .halt
        (postStateTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (selectorScratchTape D L)) := by
  let leftRev :=
    pushBits (codeBits (encodeNat L.stage))
      (pushBits (codeBits ((L.input.map some).map cellTok))
        (pushBits (codeBits (encodeNat (L.input.map some).length))
          (pushBits (tokBits MachineCodeSymbol.header) [none])))
  let right := List.append (codeBits (postStateTokens L)) [none]
  have hparse :
      Leads D
        (cfg D (.parse (zeroCount D) .p0)
          (StageCounter.postStageTape L)
          (FieldDecomposition.stageCounterTape L.stage)
          (SourceCounter.layoutMarkerTape L))
        (cfg D (.mark (classifyState D L.config.state))
          (postStateTape L)
          (FieldDecomposition.stageCounterTape L.stage)
          (SourceCounter.layoutMarkerTape L)) := by
    rw [postStageTape_eq_stateField]
    simpa [leftRev, right, postStateTape] using
      leads_parse D L.config.state leftRev right
        (FieldDecomposition.stageCounterTape L.stage)
        (SourceCounter.layoutMarkerTape L)
  have hemit :
      Leads D
        (cfg D (.mark (classifyState D L.config.state))
          (postStateTape L)
          (FieldDecomposition.stageCounterTape L.stage)
          (SourceCounter.layoutMarkerTape L))
        (cfg D .halt
          (postStateTape L)
          (FieldDecomposition.stageCounterTape L.stage)
          (selectorScratchTape D L)) := by
    rw [layoutMarkerTape_eq_reserved]
    exact
      leads_selector_mark D (classifyState D L.config.state)
        (remainingScratchMarkers D L)
        (postStateTape L)
        (FieldDecomposition.stageCounterTape L.stage)
  exact hparse.trans hemit

theorem haltsWithTapes_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    (description D).HaltsWithTapes
      (ThreeTape.config (description D).start
        (StageCounter.postStageTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (SourceCounter.layoutMarkerTape L))
      [ postStateTape L
      , FieldDecomposition.stageCounterTape L.stage
      , selectorScratchTape D L ] := by
  rcases (leads_layout D L).to_runConfig with ⟨steps, hrun⟩
  exact ⟨steps, hrun⟩

/-!
## Lowered physical phase
-/

def loweredDescription (D : MachineDescription) : MachineDescription :=
  lowerStructured3Description (description D)

theorem loweredDescription_wellFormed (D : MachineDescription) :
    (loweredDescription D).WellFormed :=
  lowerStructured3Description_wellFormed
    (description_wellFormed D)
    (description_supportsReadWriteRows3 D)

theorem loweredDescription_subroutineReady (D : MachineDescription) :
    (loweredDescription D).SubroutineReady :=
  lowerStructured3Description_subroutineReady
    (description_wellFormed D)
    (description_supportsReadWriteRows3 D)

/-- Exact guarded physical boundary after raw-state classification. -/
def targetTape
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  encodedGuardedStructuredTapes
    [ postStateTape L
    , FieldDecomposition.stageCounterTape L.stage
    , selectorScratchTape D L ]

theorem loweredDescription_haltsFromTapeEquiv
    (D : MachineDescription) (L : SimulatorLayout) :
    (loweredDescription D).HaltsFromTapeEquiv
      (StageCounter.targetTape L) (targetTape D L) := by
  unfold loweredDescription StageCounter.targetTape targetTape
  apply lowerStructured3Description_haltsFromConfigWithTapes
    (description_wellFormed D)
    (description_haltTransitionFree D)
    (description_supportsReadWriteRows3 D)
    (c :=
      ThreeTape.config (description D).start
        (StageCounter.postStageTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (SourceCounter.layoutMarkerTape L))
  · rfl
  · rfl
  · exact haltsWithTapes_layout D L

def Spec
    (D : MachineDescription) (selector : MachineDescription) : Prop :=
  selector.SubroutineReady ∧
    forall L : SimulatorLayout,
      selector.HaltsFromTapeEquiv
        (StageCounter.targetTape L) (targetTape D L)

def Construction (D : MachineDescription) : Prop :=
  exists selector : MachineDescription, Spec D selector

/-- Completed raw-state classification and physical selector phase. -/
theorem construction_core (D : MachineDescription) : Construction D :=
  ⟨loweredDescription D,
    loweredDescription_subroutineReady D,
    loweredDescription_haltsFromTapeEquiv D⟩

end StateSelector
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
