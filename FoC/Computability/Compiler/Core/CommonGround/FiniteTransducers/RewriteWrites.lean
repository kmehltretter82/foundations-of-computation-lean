import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Transition-table write rewrites

This module factors out the table-level part of scanner-derived rewriters:
reuse a finite control graph and its read/move/target structure, but replace
the write symbol on every transition.  The lemmas here intentionally prove only
table hygiene.  Run invariants still have to be proved for concrete scanner
families, because scanners that revisit cells are not valid under arbitrary
write rewrites.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def rewriteTransitionWriteWith
    (f : TransitionDescription -> Option Bool)
    (t : TransitionDescription) : TransitionDescription :=
  { source := t.source
    read := t.read
    write := f t
    move := t.move
    target := t.target }

def rewriteTransitionWrite
    (f : Option Bool -> Option Bool)
    (t : TransitionDescription) : TransitionDescription :=
  rewriteTransitionWriteWith (fun t => f t.write) t

def mapTransitionWritesWith
    (f : TransitionDescription -> Option Bool)
    (D : MachineDescription) : MachineDescription :=
  { stateCount := D.stateCount
    start := D.start
    halt := D.halt
    transitions := D.transitions.map (rewriteTransitionWriteWith f) }

def mapTransitionWrites
    (f : Option Bool -> Option Bool)
    (D : MachineDescription) : MachineDescription :=
  mapTransitionWritesWith (fun t => f t.write) D

def eraseTransitionWrites (D : MachineDescription) :
    MachineDescription :=
  mapTransitionWrites (fun _ => none) D

theorem rewriteTransitionWrite_wellFormed
    (f : Option Bool -> Option Bool) {stateCount : Nat}
    {t : TransitionDescription}
    (ht : TransitionDescription.WellFormed stateCount t) :
    TransitionDescription.WellFormed stateCount
      (rewriteTransitionWrite f t) := by
  simpa [rewriteTransitionWrite,
    rewriteTransitionWriteWith,
    TransitionDescription.WellFormed] using ht

theorem rewriteTransitionWriteWith_wellFormed
    (f : TransitionDescription -> Option Bool) {stateCount : Nat}
    {t : TransitionDescription}
    (ht : TransitionDescription.WellFormed stateCount t) :
    TransitionDescription.WellFormed stateCount
      (rewriteTransitionWriteWith f t) := by
  simpa [rewriteTransitionWriteWith,
    TransitionDescription.WellFormed] using ht

theorem rewriteTransitionWrite_sameKey
    (f : Option Bool -> Option Bool) (t u : TransitionDescription) :
    TransitionDescription.SameKey (rewriteTransitionWrite f t)
        (rewriteTransitionWrite f u) =
      TransitionDescription.SameKey t u := by
  rfl

theorem rewriteTransitionWriteWith_sameKey
    (f : TransitionDescription -> Option Bool)
    (t u : TransitionDescription) :
    TransitionDescription.SameKey (rewriteTransitionWriteWith f t)
        (rewriteTransitionWriteWith f u) =
      TransitionDescription.SameKey t u := by
  rfl

theorem rewriteTransitionWrite_sameAction
    (f : Option Bool -> Option Bool) {t u : TransitionDescription}
    (h : TransitionDescription.SameAction t u) :
  TransitionDescription.SameAction (rewriteTransitionWrite f t)
      (rewriteTransitionWrite f u) := by
  rcases h with ⟨hwrite, hmove, htarget⟩
  exact ⟨by
    simpa [rewriteTransitionWrite, rewriteTransitionWriteWith] using
      congrArg f hwrite,
    by simpa [rewriteTransitionWrite] using hmove,
    by simpa [rewriteTransitionWrite] using htarget⟩

theorem rewriteTransitionWriteWith_sameAction
    (f : TransitionDescription -> Option Bool)
    {t u : TransitionDescription}
    (hwrite : f t = f u)
    (h : TransitionDescription.SameAction t u) :
    TransitionDescription.SameAction (rewriteTransitionWriteWith f t)
      (rewriteTransitionWriteWith f u) := by
  rcases h with ⟨_, hmove, htarget⟩
  exact ⟨by simp [rewriteTransitionWriteWith, hwrite],
    by simpa [rewriteTransitionWriteWith] using hmove,
    by simpa [rewriteTransitionWriteWith] using htarget⟩

theorem mapTransitionWritesWith_wellFormed
    (f : TransitionDescription -> Option Bool)
    {D : MachineDescription}
    (hD : D.WellFormed)
    (hf :
      forall {t u : TransitionDescription},
        TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u ->
          f t = f u) :
    (mapTransitionWritesWith f D).WellFormed := by
  rcases hD with ⟨hcount, hstart, hhalt, htrans, hdet⟩
  constructor
  · exact hcount
  constructor
  · exact hstart
  constructor
  · exact hhalt
  constructor
  · intro t ht
    rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
    exact rewriteTransitionWriteWith_wellFormed f (htrans base hbase)
  · intro t u ht hu hkey
    rcases List.mem_map.mp ht with ⟨baseT, hbaseT, rfl⟩
    rcases List.mem_map.mp hu with ⟨baseU, hbaseU, rfl⟩
    have hbaseKey :
        TransitionDescription.SameKey baseT baseU := by
      simpa [rewriteTransitionWriteWith,
        TransitionDescription.SameKey] using hkey
    have hbaseAction := hdet baseT baseU hbaseT hbaseU hbaseKey
    exact
      rewriteTransitionWriteWith_sameAction f
        (hf hbaseKey hbaseAction) hbaseAction

theorem mapTransitionWrites_wellFormed
    (f : Option Bool -> Option Bool) {D : MachineDescription}
    (hD : D.WellFormed) :
    (mapTransitionWrites f D).WellFormed := by
  exact
    mapTransitionWritesWith_wellFormed (fun t => f t.write) hD
      (by
        intro t u _hkey haction
        exact congrArg f haction.left)

theorem mapTransitionWritesWith_haltTransitionFree
    (f : TransitionDescription -> Option Bool)
    {D : MachineDescription}
    (hD : D.HaltTransitionFree) :
    (mapTransitionWritesWith f D).HaltTransitionFree := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
  simpa [mapTransitionWritesWith, rewriteTransitionWriteWith] using
    hD base hbase

theorem mapTransitionWrites_haltTransitionFree
    (f : Option Bool -> Option Bool) {D : MachineDescription}
    (hD : D.HaltTransitionFree) :
    (mapTransitionWrites f D).HaltTransitionFree := by
  exact mapTransitionWritesWith_haltTransitionFree
    (fun t => f t.write) hD

theorem mapTransitionWritesWith_subroutineReady
    (f : TransitionDescription -> Option Bool)
    {D : MachineDescription}
    (hD : D.SubroutineReady)
    (hf :
      forall {t u : TransitionDescription},
        TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u ->
          f t = f u) :
    (mapTransitionWritesWith f D).SubroutineReady :=
  ⟨mapTransitionWritesWith_wellFormed f hD.left hf,
    mapTransitionWritesWith_haltTransitionFree f hD.right⟩

theorem mapTransitionWrites_subroutineReady
    (f : Option Bool -> Option Bool) {D : MachineDescription}
    (hD : D.SubroutineReady) :
    (mapTransitionWrites f D).SubroutineReady :=
  ⟨mapTransitionWrites_wellFormed f hD.left,
    mapTransitionWrites_haltTransitionFree f hD.right⟩

theorem eraseTransitionWrites_subroutineReady
    {D : MachineDescription}
    (hD : D.SubroutineReady) :
    (eraseTransitionWrites D).SubroutineReady := by
  exact mapTransitionWrites_subroutineReady (fun _ => none) hD

end FiniteTransducers
end CommonGround

end Computability
end FoC
