import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.MetadataPrefixRuns

set_option doc.verso true

/-!
# Exact configuration and hit materializer

This target-specific three-tape table consumes the header-start boundary left
by the metadata-prefix phase. It erases the already-preserved layout prefix,
copies the encoded configuration suffix into temporary space to the right of
the tape-2 hit cell, and reconstructs the exact configuration tape on tape 0.
Tape 1 is never changed. The temporary workspace is erased before the saved
hit is restored.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace MetadataPrefix
namespace ConfigTapeAndHit

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

inductive State where
  | hdr0 | hdr1 | hdr2 | hdr3
  | inLen0 | inLen1 | inLen2 | inLen3
  | inBits0 | inBits1 | inBits2 | inBits3
  | stage0 | stage1 | stage2 | stage3
  | rawState0 | rawState1 | rawState2 | rawState3
  | gap1 | gap2 | copy | rewind
  | lLen0 | lLen1 | lLen2 | lLen3
  | lb0 | lb1 | lb2 | lb3
  | lbB1 | lbB2 | lbB3 | lbB4 | lbMark
  | lbR1 | lbR2 | lbR3 | lbR4 | lbR5
  | rLen0 | rLen1 | rLen2 | rLen3
  | rb0 | rb1 | rb2 | rb3
  | hit3 | hit2 (v3 : Bool) | hit1 (v3 v2 : Bool) | hit0 (hit : Bool)
  | re3 (hit : Bool) | re2 (hit v3 : Bool)
  | re1 (hit v3 v2 : Bool) | re0 (hit : Bool) (cell : Option Bool)
  | rt3 (hit : Bool) | rt2 (hit v3 : Bool)
  | rt1 (hit v3 v2 : Bool) | rt0 (hit : Bool)
  | hd0 (hit v3 v2 : Bool)
  | ls3 (hit : Bool) | ls2 (hit : Bool)
  | ls1 (hit : Bool) | ls0 (hit : Bool)
  | turn1 (hit : Bool) | turn2 (hit : Bool)
  | le0 (hit : Bool) | le1 (hit : Bool)
  | le2 (hit : Bool) | le3 (hit v2 : Bool)
  | pos3 (hit : Bool) | pos2 (hit v3 : Bool)
  | pos1 (hit v3 v2 : Bool) | pos0 (hit : Bool)
  | eraseLen (hit : Bool) | restore (hit : Bool)
  | halt
deriving DecidableEq, Repr

def boolValues : List Bool := [false, true]

def cellValues : List (Option Bool) :=
  [none, some false, some true]

@[simp] theorem bool_mem_boolValues (bit : Bool) : bit ∈ boolValues := by
  cases bit <;> simp [boolValues]

@[simp] theorem cell_mem_cellValues (cell : Option Bool) :
    cell ∈ cellValues := by
  cases cell with
  | none => simp [cellValues]
  | some bit => cases bit <;> simp [cellValues]

/-- Decode the two payload bits of a valid cell token. -/
def cellOfTail : Bool → Bool → Option (Option Bool)
  | false, false => some none
  | false, true => some (some false)
  | true, false => some (some true)
  | true, true => none

private def step02
    (a0 a2 : TapeAction) (target : State) : Option (TypedStep State) :=
  some ⟨target, a0, keepS, a2⟩

private def step0 (a0 : TapeAction) (target : State) :
    Option (TypedStep State) :=
  step02 a0 keepS target

private def step2 (a2 : TapeAction) (target : State) :
    Option (TypedStep State) :=
  step02 keepS a2 target

private def eraseR : TapeAction := writeR (none : Option Bool)
private def eraseL : TapeAction := writeL (none : Option Bool)

def next :
    State → Option Bool → Option Bool → Option Bool →
      Option (TypedStep State)
  | .hdr0, some false, _, _ => step0 eraseR .hdr1
  | .hdr1, some false, _, _ => step0 eraseR .hdr2
  | .hdr2, some false, _, _ => step0 eraseR .hdr3
  | .hdr3, some false, _, _ => step0 eraseR .inLen0
  | .inLen0, some false, _, _ => step0 eraseR .inLen1
  | .inLen1, some false, _, _ => step0 eraseR .inLen2
  | .inLen2, some true, _, _ => step0 eraseR .inLen3
  | .inLen3, some false, _, _ => step0 eraseR .inLen0
  | .inLen3, some true, _, _ => step0 eraseR .inBits0
  | .inBits0, some false, _, _ => step0 eraseR .inBits1
  | .inBits1, some true, _, _ => step0 eraseR .inBits2
  | .inBits1, some false, _, _ => step0 eraseR .stage2
  | .inBits2, some _, _, _ => step0 eraseR .inBits3
  | .inBits3, some _, _, _ => step0 eraseR .inBits0
  | .stage0, some false, _, _ => step0 eraseR .stage1
  | .stage1, some false, _, _ => step0 eraseR .stage2
  | .stage2, some true, _, _ => step0 eraseR .stage3
  | .stage3, some false, _, _ => step0 eraseR .stage0
  | .stage3, some true, _, _ => step0 eraseR .rawState0
  | .rawState0, some false, _, _ => step0 eraseR .rawState1
  | .rawState1, some false, _, _ => step0 eraseR .rawState2
  | .rawState2, some true, _, _ => step0 eraseR .rawState3
  | .rawState3, some false, _, _ => step0 eraseR .rawState0
  | .rawState3, some true, _, _ => step0 eraseR .gap1
  | .gap1, _, _, _ => step2 keepR .gap2
  | .gap2, _, _, _ => step2 keepR .copy
  | .copy, some bit, _, _ => step02 eraseR (writeR (some bit)) .copy
  | .copy, none, _, _ => step2 keepL .rewind
  | .rewind, _, _, some _ => step2 keepL .rewind
  | .rewind, _, _, none => step2 keepR .lLen0
  | .lLen0, _, _, some false => step2 keepR .lLen1
  | .lLen1, _, _, some false => step2 keepR .lLen2
  | .lLen2, _, _, some true => step2 keepR .lLen3
  | .lLen3, _, _, some false => step2 keepR .lLen0
  | .lLen3, _, _, some true => step2 keepR .lb0
  | .lb0, _, _, some false => step2 keepR .lb1
  | .lb1, _, _, some true => step2 keepR .lb2
  | .lb1, _, _, some false => step2 keepL .lbB1
  | .lb2, _, _, some _ => step2 keepR .lb3
  | .lb3, _, _, some _ => step2 keepR .lb0
  | .lbB1, _, _, some _ => step2 keepL .lbB2
  | .lbB2, _, _, some _ => step2 keepL .lbB3
  | .lbB3, _, _, some _ => step2 keepL .lbB4
  | .lbB4, _, _, some _ => step2 keepL .lbMark
  | .lbMark, _, _, some false => step2 (writeR (some true)) .lbR1
  | .lbR1, _, _, some _ => step2 keepR .lbR2
  | .lbR2, _, _, some _ => step2 keepR .lbR3
  | .lbR3, _, _, some _ => step2 keepR .lbR4
  | .lbR4, _, _, some _ => step2 keepR .lbR5
  | .lbR5, _, _, some false => step2 keepR .rLen2
  | .rLen0, _, _, some false => step2 keepR .rLen1
  | .rLen1, _, _, some false => step2 keepR .rLen2
  | .rLen2, _, _, some true => step2 keepR .rLen3
  | .rLen3, _, _, some false => step2 keepR .rLen0
  | .rLen3, _, _, some true => step2 keepR .rb0
  | .rb0, _, _, some false => step2 keepR .rb1
  | .rb0, _, _, none => step2 keepL .hit3
  | .rb1, _, _, some true => step2 keepR .rb2
  | .rb2, _, _, some _ => step2 keepR .rb3
  | .rb3, _, _, some _ => step2 keepR .rb0
  | .hit3, _, _, some v3 => step2 eraseL (.hit2 v3)
  | .hit2 v3, _, _, some v2 => step2 eraseL (.hit1 v3 v2)
  | .hit1 true false, _, _, some true => step2 eraseL (.hit0 false)
  | .hit1 false true, _, _, some true => step2 eraseL (.hit0 true)
  | .hit0 hit, _, _, some false => step2 eraseL (.re3 hit)
  | .re3 hit, _, _, some v3 => step2 eraseL (.re2 hit v3)
  | .re2 hit v3, _, _, some v2 => step2 eraseL (.re1 hit v3 v2)
  | .re1 hit true true, _, _, some false => step2 eraseL (.rt0 hit)
  | .re1 hit v3 v2, _, _, some true =>
      match cellOfTail v2 v3 with
      | some cell => step2 eraseL (.re0 hit cell)
      | none => none
  | .re0 hit cell, _, _, some false =>
      step02 (writeL cell) eraseL (.re3 hit)
  | .rt0 hit, _, _, some false => step2 eraseL (.rt3 hit)
  | .rt3 hit, _, _, some v3 => step2 eraseL (.rt2 hit v3)
  | .rt2 hit v3, _, _, some v2 => step2 eraseL (.rt1 hit v3 v2)
  | .rt1 hit _ _, _, _, some false => step2 eraseL (.rt0 hit)
  | .rt1 hit v3 v2, _, _, some true => step2 eraseL (.hd0 hit v3 v2)
  | .hd0 hit v3 v2, _, _, some true =>
      match cellOfTail v2 v3 with
      | some cell => step02 (writeL cell) eraseL (.ls3 hit)
      | none => none
  | .ls3 hit, _, _, some _ => step2 keepL (.ls2 hit)
  | .ls2 hit, _, _, some _ => step2 keepL (.ls1 hit)
  | .ls1 hit, _, _, some true => step2 keepL (.ls0 hit)
  | .ls1 hit, _, _, some false => step2 keepR (.turn1 hit)
  | .ls0 hit, _, _, some false => step2 keepL (.ls3 hit)
  | .turn1 hit, _, _, some _ => step2 keepR (.turn2 hit)
  | .turn2 hit, _, _, some _ => step2 keepR (.le0 hit)
  | .le0 hit, _, _, some false => step2 keepR (.le1 hit)
  | .le0 hit, _, _, none => step02 keepR keepL (.pos3 hit)
  | .le1 hit, _, _, some true => step2 keepR (.le2 hit)
  | .le2 hit, _, _, some v2 => step2 keepR (.le3 hit v2)
  | .le3 hit v2, _, _, some v3 =>
      match cellOfTail v2 v3 with
      | some cell => step02 (writeL cell) keepR (.le0 hit)
      | none => none
  | .pos3 hit, _, _, some v3 => step2 eraseL (.pos2 hit v3)
  | .pos2 hit v3, _, _, some v2 => step2 eraseL (.pos1 hit v3 v2)
  | .pos1 hit _ _, _, _, some true => step2 eraseL (.pos0 hit)
  | .pos1 hit _ _, _, _, some false => step2 eraseL (.eraseLen hit)
  | .pos0 hit, _, _, some false => step02 keepR eraseL (.pos3 hit)
  | .eraseLen hit, _, _, some _ => step2 eraseL (.eraseLen hit)
  | .eraseLen hit, _, _, none => step2 keepL (.restore hit)
  | .restore hit, _, _, _ => step2 (writeS (some hit)) .halt
  | _, _, _, _ => none

def fixedStates : List State :=
  [ .hdr0, .hdr1, .hdr2, .hdr3
  , .inLen0, .inLen1, .inLen2, .inLen3
  , .inBits0, .inBits1, .inBits2, .inBits3
  , .stage0, .stage1, .stage2, .stage3
  , .rawState0, .rawState1, .rawState2, .rawState3
  , .gap1, .gap2, .copy, .rewind
  , .lLen0, .lLen1, .lLen2, .lLen3
  , .lb0, .lb1, .lb2, .lb3
  , .lbB1, .lbB2, .lbB3, .lbB4, .lbMark
  , .lbR1, .lbR2, .lbR3, .lbR4, .lbR5
  , .rLen0, .rLen1, .rLen2, .rLen3
  , .rb0, .rb1, .rb2, .rb3, .hit3, .halt ]

def preHitStates : List State :=
  boolValues.flatMap fun v3 =>
    .hit2 v3 :: boolValues.map fun v2 => .hit1 v3 v2

def pairedHitStates (hit : Bool) : List State :=
  boolValues.flatMap fun v3 =>
    [ .re2 hit v3, .rt2 hit v3, .pos2 hit v3 ] ++
      boolValues.flatMap fun v2 =>
        [ .re1 hit v3 v2, .rt1 hit v3 v2
        , .hd0 hit v3 v2, .pos1 hit v3 v2 ]

def hitStates (hit : Bool) : List State :=
  [ .hit0 hit, .re3 hit, .rt3 hit, .rt0 hit
  , .ls3 hit, .ls2 hit, .ls1 hit, .ls0 hit
  , .turn1 hit, .turn2 hit, .le0 hit, .le1 hit, .le2 hit
  , .pos3 hit, .pos0 hit, .eraseLen hit, .restore hit ] ++
    pairedHitStates hit ++
    cellValues.map (State.re0 hit) ++
    boolValues.map (State.le3 hit)

def states : List State :=
  fixedStates ++ preHitStates ++ boolValues.flatMap hitStates

theorem state_mem (s : State) : s ∈ states := by
  cases s <;>
    simp [states, fixedStates, preHitStates, hitStates, pairedHitStates]

theorem next_target_mem :
    forall s : State, s ∈ states →
      forall (r0 r1 r2 : Option Bool) (st : TypedStep State),
        next s r0 r1 r2 = some st → st.target ∈ states := by
  intro _ _ _ _ _ st _
  exact state_mem st.target

def table : TypedStateTable State :=
  TypedStateTable.ofList states .hdr0 .halt next
    (state_mem .hdr0) (state_mem .halt)
    (by intro r0 r1 r2; rfl) next_target_mem

def description : Description := table.description

theorem description_wellFormed : description.WellFormed :=
  table.description_wellFormed

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  table.description_haltTransitionFree

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description :=
  table.description_supportsReadWriteRows3

theorem description_subroutineReady : description.SubroutineReady :=
  table.description_subroutineReady

end ConfigTapeAndHit
end MetadataPrefix
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
