import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding

set_option doc.verso true

/-!
# Optional-field replacement

Finite marker seeking and replacement for serialized optional fields in a
protected exact-fuel frame.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Edits
namespace OptionalField

open SerializedFieldComposer

/- A small cursor machine that restores a temporary field-boundary marker and
positions the head on the first token after that boundary. -/
namespace MarkerSeek

inductive Control where
  | header
  | seek
  | gate
deriving DecidableEq

namespace Control

def elems : List Control := [.header, .seek, .gate]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .header, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .seek)
  | .seek, some MachineCodeSymbol.zero =>
      some (some MachineCodeSymbol.done, Direction.right, .gate)
  | .seek, some symbol =>
      some (some symbol, Direction.right, .seek)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .header
  halt := .gate
  transition := transition
  statesFinite := Control.finite

def sourceWord (middle suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    List.append middle (MachineCodeSymbol.zero :: suffix)

def targetLeftRev (middle : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    List.append middle.reverse [MachineCodeSymbol.header]

def sourceConfig (middle suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .header
  tape := Tape.input (sourceWord middle suffix)

def gateConfig (middle suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := SerializedShift.cursorTape (targetLeftRev middle) suffix

def SafePrefix (middle : Word MachineCodeSymbol) : Prop :=
  ∀ symbol, List.Mem symbol middle ->
    symbol ≠ MachineCodeSymbol.zero

def seekConfig
    (leftRev middle suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seek
  tape := SerializedShift.cursorTape leftRev
    (List.append middle (MachineCodeSymbol.zero :: suffix))

def seekGateConfig
    (leftRev middle suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := SerializedShift.cursorTape
    (MachineCodeSymbol.done ::
      List.append middle.reverse leftRev)
    suffix

theorem seek_run_exact
    (leftRev middle suffix : Word MachineCodeSymbol)
    (hsafe : SafePrefix middle) :
    machine.runConfigExact? (middle.length + 1)
        (seekConfig leftRev middle suffix) =
      some (seekGateConfig leftRev middle suffix) := by
  induction middle generalizing leftRev with
  | nil =>
      cases leftRev <;> cases suffix <;> rfl
  | cons current rest ih =>
      have hcurrent : current ≠ MachineCodeSymbol.zero :=
        hsafe current (List.Mem.head rest)
      have hrest : SafePrefix rest := by
        intro symbol hmem
        exact hsafe symbol (List.Mem.tail current hmem)
      change
        machine.runConfigExact? (rest.length + 1 + 1)
            (seekConfig leftRev (current :: rest) suffix) = _
      rw [TuringMachine.runConfigExact?]
      have hstep :
          machine.stepConfig
              (seekConfig leftRev (current :: rest) suffix) =
            some (seekConfig (current :: leftRev) rest suffix) := by
        cases current <;> cases rest <;>
          simp_all [TuringMachine.stepConfig, seekConfig, machine,
            transition, SerializedShift.cursorTape, Tape.read, Tape.write,
            Tape.move, Tape.moveRight, List.map_append]
      rw [hstep]
      simp only
      simpa [seekGateConfig, List.reverse_cons,
        List.append_assoc] using
        ih (current :: leftRev) hrest

theorem header_step
    (middle suffix : Word MachineCodeSymbol) :
    machine.stepConfig (sourceConfig middle suffix) =
      some (seekConfig [MachineCodeSymbol.header] middle suffix) := by
  cases middle <;> cases suffix <;> rfl

theorem run_exact
    (middle suffix : Word MachineCodeSymbol)
    (hsafe : SafePrefix middle) :
    machine.runConfigExact? (middle.length + 2)
        (sourceConfig middle suffix) =
      some (gateConfig middle suffix) := by
  change
    machine.runConfigExact? (middle.length + 1 + 1)
        (sourceConfig middle suffix) = _
  rw [TuringMachine.runConfigExact?]
  rw [header_step]
  simp only
  have hrun := seek_run_exact
    ([MachineCodeSymbol.header] : Word MachineCodeSymbol)
    middle suffix hsafe
  simpa [seekGateConfig, gateConfig, targetLeftRev] using hrun

theorem run_exact_of_tape_equiv
    (middle suffix : Word MachineCodeSymbol)
    (hsafe : SafePrefix middle)
    (T : Tape MachineCodeSymbol)
    (hT : Tape.Equiv (Tape.input (sourceWord middle suffix)) T) :
    exists endpoint,
      machine.runConfigExact? (middle.length + 2)
          { state := Control.header, tape := T } = some endpoint ∧
      endpoint.state = Control.gate ∧
      Tape.Equiv (gateConfig middle suffix).tape endpoint.tape := by
  exact TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
    (run_exact middle suffix hsafe) hT

end MarkerSeek

/- One actual finite machine for replacing a bounded optional field.  A raw
`zero` sentinel remembers the field boundary across delete/rewind; the marker
seek restores that boundary before the bounded insertion phase. -/
namespace Replace

inductive Control where
  | markLeft
  | markPrevious
  | delete (inner : DeleteRestagedMachine.Control)
  | seekEntry
  | seek (inner : MarkerSeek.Control)
  | insertEntry
  | insert (inner : InsertRestagedMachine.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.markLeft, .markPrevious, .seekEntry, .insertEntry] ++
    (DeleteRestagedMachine.Control.finite.elems.map Control.delete) ++
    (MarkerSeek.Control.finite.elems.map Control.seek) ++
    (InsertRestagedMachine.Control.finite.elems.map Control.insert)

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | markLeft => simp [elems]
    | markPrevious => simp [elems]
    | delete inner =>
        simp [elems]
        exact DeleteRestagedMachine.Control.finite.complete inner
    | seekEntry => simp [elems]
    | seek inner =>
        simp [elems]
        exact MarkerSeek.Control.finite.complete inner
    | insertEntry => simp [elems]
    | insert inner =>
        simp [elems]
        exact InsertRestagedMachine.Control.finite.complete inner

end Control

def transition (old new : Option MachineCodeSymbol) :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .markLeft, read =>
      some (read, Direction.left, .markPrevious)
  | .markPrevious, some MachineCodeSymbol.done =>
      some
        (some MachineCodeSymbol.zero, Direction.right,
          .delete (.edit (.erase (DeleteBlock.optionalGap old))))
  | .delete (.rewind .gate), read =>
      some (read, Direction.right, .seekEntry)
  | .delete inner, read =>
      match DeleteRestagedMachine.transition old inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .delete target)
  | .seekEntry, read =>
      some (read, Direction.left, .seek .header)
  | .seek .gate, read =>
      some (read, Direction.right, .insertEntry)
  | .seek inner, read =>
      match MarkerSeek.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .seek target)
  | .insertEntry, read =>
      some
        (read, Direction.left,
          .insert
            (.edit (.carry (InsertBlock.optionalBuffer new))))
  | .insert inner, read =>
      match InsertRestagedMachine.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .insert target)
  | _, _ => none

def machine (old new : Option MachineCodeSymbol) :
    TuringMachine MachineCodeSymbol Control where
  start := .markLeft
  halt := .insert (.rewind .gate)
  transition := transition old new
  statesFinite := Control.finite

def originalLeftRev (middle : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    List.append middle.reverse [MachineCodeSymbol.header]

def markedLeftRev (middle : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.zero ::
    List.append middle.reverse [MachineCodeSymbol.header]

def sourceConfig (old : Option MachineCodeSymbol)
    (middle suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .markLeft
  tape := SerializedShift.cursorTape (originalLeftRev middle)
    (List.append (optionalCellWord old) suffix)

def deleteConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .delete c.state
  tape := c.tape

def seekConfig
    (c : TuringMachine.Configuration MachineCodeSymbol MarkerSeek.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seek c.state
  tape := c.tape

def insertConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .insert c.state
  tape := c.tape

private theorem write_read_eq_self (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T :=
  Machine.moveLeft_moveRight_equiv_self T

theorem mark_handoff_exact
    (old new : Option MachineCodeSymbol)
    (middle suffix : Word MachineCodeSymbol) :
    (machine old new).runConfigExact? 2
        (sourceConfig old middle suffix) =
      some
        (deleteConfig
          (DeleteRestagedMachine.editConfig
            (DeleteBlock.sourceConfig old
              (markedLeftRev middle) suffix))) := by
  cases old with
  | none => cases middle <;> cases suffix <;> rfl
  | some symbol =>
      cases symbol <;> cases middle <;> cases suffix <;> rfl

theorem delete_step_of_some
    (old new : Option MachineCodeSymbol)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine old).stepConfig c = some d) :
    (machine old new).stepConfig (deleteConfig c) =
      some (deleteConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [DeleteRestagedMachine.machine] at hstep
      cases htransition : DeleteRestagedMachine.transition old inner
          (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hnot :
              inner ≠ DeleteRestagedMachine.Control.rewind
                DeleteEndpointRewind.Control.gate := by
            intro hgate
            subst inner
            simp [DeleteRestagedMachine.transition,
              DeleteEndpointRewind.transition] at htransition
          simp [machine, transition, deleteConfig, htransition]

theorem delete_run_of_some
    (old new : Option MachineCodeSymbol) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        DeleteRestagedMachine.Control),
      (DeleteRestagedMachine.machine old).runConfigExact?
          steps source = some target ->
        (machine old new).runConfigExact? steps
            (deleteConfig source) = some (deleteConfig target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using congrArg deleteConfig
        (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          (DeleteRestagedMachine.machine old).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [delete_step_of_some old new source next hstep]
          simp only
          exact ih next target hrun

theorem delete_seek_handoff_exact
    (old new : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine old new).runConfigExact? 2
        (deleteConfig
          { state := DeleteRestagedMachine.Control.rewind .gate
            tape := T }) =
      some
        (seekConfig
          { state := MarkerSeek.Control.header
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, deleteConfig, seekConfig, roundTripTape,
    write_read_eq_self]

theorem seek_step_of_some
    (old new : Option MachineCodeSymbol)
    (c d : TuringMachine.Configuration MachineCodeSymbol MarkerSeek.Control)
    (hstep : MarkerSeek.machine.stepConfig c = some d) :
    (machine old new).stepConfig (seekConfig c) =
      some (seekConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [MarkerSeek.machine] at hstep
      cases htransition : MarkerSeek.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hnot : inner ≠ MarkerSeek.Control.gate := by
            intro hgate
            subst inner
            simp [MarkerSeek.transition] at htransition
          simp [machine, transition, seekConfig, htransition]

theorem seek_run_of_some
    (old new : Option MachineCodeSymbol) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        MarkerSeek.Control),
      MarkerSeek.machine.runConfigExact? steps source = some target ->
        (machine old new).runConfigExact? steps
            (seekConfig source) = some (seekConfig target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using congrArg seekConfig
        (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : MarkerSeek.machine.stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [seek_step_of_some old new source next hstep]
          simp only
          exact ih next target hrun

theorem seek_insert_handoff_exact
    (old new : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol) :
    (machine old new).runConfigExact? 2
        (seekConfig { state := MarkerSeek.Control.gate, tape := T }) =
      some
        (insertConfig
          { state := InsertRestagedMachine.Control.edit
              (.carry (InsertBlock.optionalBuffer new))
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, seekConfig, insertConfig, roundTripTape,
    write_read_eq_self]

theorem insert_run_of_some
    (old new : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control}
    (hrun :
      (InsertRestagedMachine.machine
        (InsertBlock.optionalBuffer new)).runConfigExact?
          steps source = some target) :
    (machine old new).runConfigExact? steps
        (insertConfig source) = some (insertConfig target) := by
  apply TuringMachine.PhaseEmbedding.runConfigExact?_lift_of_eq_some
    (inner := InsertRestagedMachine.machine
      (InsertBlock.optionalBuffer new))
    (outer := machine old new) Control.insert
  · intro c
    cases c with
    | mk inner tape =>
        unfold TuringMachine.stepConfig
        simp only [TuringMachine.PhaseEmbedding.liftConfig,
          machine, transition, InsertRestagedMachine.machine]
        cases htransition : InsertRestagedMachine.transition inner
            (Tape.read tape) with
        | none => rfl
        | some action =>
            rcases action with ⟨write, direction, target⟩
            rfl
  · exact hrun

theorem runConfigExact_trans
    (old new : Option MachineCodeSymbol)
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol Control}
    (hab : (machine old new).runConfigExact? first a = some b)
    (hbc : (machine old new).runConfigExact? second b = some c) :
    (machine old new).runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)

theorem deleteOutput_eq_markerSource
    (middle suffix : Word MachineCodeSymbol) :
    PhysicalBranch.deleteOutput (markedLeftRev middle) suffix =
      MarkerSeek.sourceWord middle suffix := by
  simp [PhysicalBranch.deleteOutput, markedLeftRev,
    MarkerSeek.sourceWord, List.reverse_cons, List.reverse_append,
    List.append_assoc]

def targetWord (middle : Word MachineCodeSymbol)
    (new : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    List.append middle
      (MachineCodeSymbol.done ::
        List.append (optionalCellWord new) suffix)

theorem insertOutput_eq_targetWord
    (middle : Word MachineCodeSymbol)
    (new : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    PhysicalBranch.insertOutput (InsertBlock.optionalBuffer new)
        (originalLeftRev middle) suffix =
      targetWord middle new suffix := by
  simp [PhysicalBranch.insertOutput, originalLeftRev, targetWord,
    InsertBlock.optionalBuffer, List.reverse_cons, List.reverse_append,
    List.append_assoc]

def runSteps
    (old new : Option MachineCodeSymbol)
    (middle suffix : Word MachineCodeSymbol) : Nat :=
  (((((2 +
      DeleteRestagedMachine.runSteps old
        (markedLeftRev middle) suffix) + 2) +
      (middle.length + 2)) + 2) +
    InsertRestagedMachine.runSteps (InsertBlock.optionalBuffer new)
      (originalLeftRev middle) suffix)

theorem run_exact
    (old new : Option MachineCodeSymbol)
    (middle suffix : Word MachineCodeSymbol)
    (hsafe : MarkerSeek.SafePrefix middle) :
    exists endpoint,
      (machine old new).runConfigExact?
          (runSteps old new middle suffix)
          (sourceConfig old middle suffix) = some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv (Tape.input (targetWord middle new suffix))
        endpoint.tape := by
  let buffer := InsertBlock.optionalBuffer new
  let marked : Word MachineCodeSymbol := markedLeftRev middle
  let original : Word MachineCodeSymbol := originalLeftRev middle
  let markerWord : Word MachineCodeSymbol :=
    MarkerSeek.sourceWord middle suffix
  have hmark := mark_handoff_exact old new middle suffix
  have hdeleteInner :=
    DeleteRestagedMachine.run_exact old marked suffix
  have hdeleteOuter := delete_run_of_some old new _ _ _ hdeleteInner
  have hthroughDelete :=
    runConfigExact_trans old new hmark hdeleteOuter
  let deleteEndpoint :=
    DeleteRestagedMachine.rewindConfig
      (DeleteEndpointRewind.gateConfig
        (PhysicalBranch.deleteOutput marked suffix) old)
  have hdeleteHandoff :=
    delete_seek_handoff_exact old new deleteEndpoint.tape
  have hthroughHandoff :=
    runConfigExact_trans old new hthroughDelete hdeleteHandoff
  have hdeleteWord :
      PhysicalBranch.deleteOutput marked suffix = markerWord := by
    simpa [marked, markerWord] using
      deleteOutput_eq_markerSource middle suffix
  have hdeleteTape :
      Tape.Equiv deleteEndpoint.tape (Tape.input markerWord) := by
    dsimp [deleteEndpoint]
    rw [hdeleteWord]
    exact DeleteEndpointRewind.gateTape_equiv_input markerWord old
  have hbouncedTape :
      Tape.Equiv (Tape.input markerWord)
        (roundTripTape deleteEndpoint.tape) := by
    exact Tape.Equiv.symm
      (Tape.Equiv.trans (roundTripTape_equiv deleteEndpoint.tape)
        hdeleteTape)
  rcases MarkerSeek.run_exact_of_tape_equiv middle suffix hsafe
      (roundTripTape deleteEndpoint.tape) hbouncedTape with
    ⟨seekEndpoint, hseekInner, hseekState, hseekTape⟩
  have hseekOuter := seek_run_of_some old new _ _ _ hseekInner
  have hthroughSeek :=
    runConfigExact_trans old new hthroughHandoff hseekOuter
  have hinsertHandoff :=
    seek_insert_handoff_exact old new seekEndpoint.tape
  have hinsertHandoff' :
      (machine old new).runConfigExact? 2 (seekConfig seekEndpoint) =
        some
          (insertConfig
            { state := InsertRestagedMachine.Control.edit
                (.carry (InsertBlock.optionalBuffer new))
              tape := roundTripTape seekEndpoint.tape }) := by
    simpa [seekConfig, hseekState] using hinsertHandoff
  have hthroughInsertHandoff :=
    runConfigExact_trans old new hthroughSeek hinsertHandoff'
  have hinsertTape :
      Tape.Equiv
        (InsertRestagedMachine.editConfig
          (InsertBlock.config buffer original suffix)).tape
        (roundTripTape seekEndpoint.tape) := by
    have hround := roundTripTape_equiv seekEndpoint.tape
    have hclean :
        (InsertRestagedMachine.editConfig
          (InsertBlock.config buffer original suffix)).tape =
          (MarkerSeek.gateConfig middle suffix).tape := by
      rfl
    rw [hclean]
    exact Tape.Equiv.trans hseekTape (Tape.Equiv.symm hround)
  have hbufferNonempty : buffer.word ≠ [] := by
    simpa [buffer] using InsertBlock.optionalBuffer_nonempty new
  have hinsertClean :=
    InsertRestagedMachine.run_exact buffer original suffix hbufferNonempty
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hinsertClean hinsertTape with
    ⟨insertEndpoint, hinsertInner, hinsertState, hinsertEndpointTape⟩
  have hinsertOuter := insert_run_of_some old new hinsertInner
  have hfull :=
    runConfigExact_trans old new hthroughInsertHandoff hinsertOuter
  refine ⟨insertConfig insertEndpoint, ?_, ?_, ?_⟩
  · simpa [runSteps, marked, original, buffer] using hfull
  · simpa [insertConfig, InsertRestagedMachine.rewindConfig,
      RewindWord.gateConfig] using hinsertState
  · have houtput :
        PhysicalBranch.insertOutput buffer original suffix =
          targetWord middle new suffix := by
      simpa [buffer, original] using
        insertOutput_eq_targetWord middle new suffix
    have hcleanEquiv :
        Tape.Equiv (Tape.input (targetWord middle new suffix))
          (InsertRestagedMachine.rewindConfig
            (RewindWord.gateConfig
              (PhysicalBranch.insertOutput buffer original suffix) 0)).tape := by
      rw [houtput]
      exact Tape.Equiv.symm
        (RewindWord.gateTape_equiv_input
          (targetWord middle new suffix) 0)
    exact Tape.Equiv.trans hcleanEquiv hinsertEndpointTape

end Replace

namespace LayoutSpecialization

def cellsPayloadMiddle : List (Option MachineCodeSymbol) ->
    Word MachineCodeSymbol
  | [] => []
  | [cell] => HeadLocator.ticks (optionalCodeSymbolTag cell)
  | cell :: next :: rest =>
      List.append (optionalCellWord cell)
        (cellsPayloadMiddle (next :: rest))

theorem cellsPayloadWord_decomp
    (cell : Option MachineCodeSymbol)
    (rest : List (Option MachineCodeSymbol)) :
    HeadLocator.cellsPayloadWord (cell :: rest) =
      List.append (cellsPayloadMiddle (cell :: rest))
        [MachineCodeSymbol.done] := by
  induction rest generalizing cell with
  | nil =>
      simp [HeadLocator.cellsPayloadWord, cellsPayloadMiddle,
        HeadLocator.optionalCellWord_eq_ticks_done]
  | cons next rest ih =>
      rw [HeadLocator.cellsPayloadWord]
      rw [ih next]
      simp [cellsPayloadMiddle, List.append_assoc]

def optionalCellsMiddle (cells : List (Option MachineCodeSymbol)) :
    Word MachineCodeSymbol :=
  match cells with
  | [] => []
  | cell :: rest =>
      List.append (MachineDescription.encodeNat (cell :: rest).length)
        (cellsPayloadMiddle (cell :: rest))

theorem optionalCellsWord_eq_count_payload
    (cells : List (Option MachineCodeSymbol)) :
    optionalCellsWord cells =
      List.append (MachineDescription.encodeNat cells.length)
        (HeadLocator.cellsPayloadWord cells) := by
  unfold optionalCellsWord encodeOptionalCodeSymbolsAppend
    MachineDescription.encodeNatAppend
  rw [← HeadLocator.cellsPayloadWord_eq_encode]

theorem optionalCellsWord_decomp
    (cells : List (Option MachineCodeSymbol)) :
    optionalCellsWord cells =
      List.append (optionalCellsMiddle cells)
        [MachineCodeSymbol.done] := by
  cases cells with
  | nil => rfl
  | cons cell rest =>
      rw [optionalCellsWord_eq_count_payload]
      rw [cellsPayloadWord_decomp]
      simp [optionalCellsMiddle, List.append_assoc]

def middle {stateCount : Nat} (L : Layout stateCount) :
    Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat L.fuel)
    (List.append (MachineDescription.encodeNat L.state.val)
      (optionalCellsMiddle L.left))

theorem headPrefix_decomp {stateCount : Nat}
    (L : Layout stateCount) :
    headPrefix L =
      MachineCodeSymbol.header ::
        List.append (middle L) [MachineCodeSymbol.done] := by
  unfold headPrefix statePrefix middle
  rw [optionalCellsWord_decomp]
  simp [List.append_assoc]

theorem safe_append
    (first second : Word MachineCodeSymbol)
    (hfirst : MarkerSeek.SafePrefix first)
    (hsecond : MarkerSeek.SafePrefix second) :
    MarkerSeek.SafePrefix (List.append first second) := by
  intro symbol hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hfirst symbol hmem
  · exact hsecond symbol hmem

theorem encodeNat_safe (n : Nat) :
    MarkerSeek.SafePrefix (MachineDescription.encodeNat n) := by
  induction n with
  | zero =>
      intro symbol hmem
      cases hmem with
      | head => decide
      | tail _ htail => cases htail
  | succ n ih =>
      intro symbol hmem
      cases hmem with
      | head => decide
      | tail _ htail => exact ih symbol htail

theorem ticks_safe (n : Nat) :
    MarkerSeek.SafePrefix (HeadLocator.ticks n) := by
  induction n with
  | zero =>
      intro symbol hmem
      cases hmem
  | succ n ih =>
      intro symbol hmem
      cases hmem with
      | head => decide
      | tail _ htail => exact ih symbol htail

theorem optionalCellWord_safe (cell : Option MachineCodeSymbol) :
    MarkerSeek.SafePrefix (optionalCellWord cell) := by
  rw [HeadLocator.optionalCellWord_eq_ticks_done]
  apply safe_append
  · exact ticks_safe (optionalCodeSymbolTag cell)
  · intro symbol hmem
    cases hmem with
    | head => decide
    | tail _ htail => cases htail

theorem cellsPayloadMiddle_safe
    (cells : List (Option MachineCodeSymbol)) :
    MarkerSeek.SafePrefix (cellsPayloadMiddle cells) := by
  induction cells with
  | nil =>
      intro symbol hmem
      cases hmem
  | cons cell rest ih =>
      cases rest with
      | nil =>
          simpa [cellsPayloadMiddle] using
            ticks_safe (optionalCodeSymbolTag cell)
      | cons next rest =>
          simp only [cellsPayloadMiddle]
          exact safe_append _ _ (optionalCellWord_safe cell) ih

theorem optionalCellsMiddle_safe
    (cells : List (Option MachineCodeSymbol)) :
    MarkerSeek.SafePrefix (optionalCellsMiddle cells) := by
  cases cells with
  | nil =>
      intro symbol hmem
      cases hmem
  | cons cell rest =>
      simp only [optionalCellsMiddle]
      exact safe_append _ _
        (encodeNat_safe (cell :: rest).length)
        (cellsPayloadMiddle_safe (cell :: rest))

theorem middle_safe {stateCount : Nat}
    (L : Layout stateCount) :
    MarkerSeek.SafePrefix (middle L) := by
  unfold middle
  exact safe_append _ _ (encodeNat_safe L.fuel)
    (safe_append _ _ (encodeNat_safe L.state.val)
      (optionalCellsMiddle_safe L.left))

def sourceConfig {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Replace.Control where
  state := .markLeft
  tape := SerializedShift.cursorTape (headPrefix L).reverse
    (headSuffix L callerData)

theorem sourceConfig_eq_replaceSource {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    sourceConfig L callerData =
      Replace.sourceConfig L.head (middle L)
        (HeadLocator.afterHeadWord L callerData) := by
  unfold sourceConfig Replace.sourceConfig Replace.originalLeftRev
  rw [headPrefix_decomp]
  simp [headSuffix, HeadLocator.afterHeadWord, List.reverse_append]

theorem targetWord_eq_protectedWord {stateCount : Nat}
    (L : Layout stateCount) (newHead : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    Replace.targetWord (middle L) newHead
        (HeadLocator.afterHeadWord L callerData) =
      Frame.protectedWord
        (HeadReplacement.replaceHead L newHead) callerData := by
  rw [← HeadReplacement.replacementWord_eq_protectedWord]
  unfold Replace.targetWord HeadReplacement.replacementWord
  rw [headPrefix_decomp]
  simp [List.append_assoc]

def runSteps {stateCount : Nat}
    (L : Layout stateCount) (newHead : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) : Nat :=
  Replace.runSteps L.head newHead (middle L)
    (HeadLocator.afterHeadWord L callerData)

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount) (newHead : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      (Replace.machine L.head newHead).runConfigExact?
          (runSteps L newHead callerData)
          (sourceConfig L callerData) = some endpoint ∧
      endpoint.state = Replace.Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (HeadReplacement.replaceHead L newHead) callerData))
        endpoint.tape := by
  rcases Replace.run_exact L.head newHead (middle L)
      (HeadLocator.afterHeadWord L callerData) (middle_safe L) with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, hstate, ?_⟩
  · simpa [runSteps, sourceConfig_eq_replaceSource] using hrun
  · rw [targetWord_eq_protectedWord] at htape
    exact htape

end LayoutSpecialization

end OptionalField
end Edits
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
