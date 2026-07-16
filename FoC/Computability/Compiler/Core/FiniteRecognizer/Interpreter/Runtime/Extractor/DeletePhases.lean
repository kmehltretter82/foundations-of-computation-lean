import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

namespace FoC
namespace Computability

open Languages

namespace RuntimeKeySelectedExtractorArbitrary

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

/-!
**Arbitrary-rest selected-row extractor.** The selected target terminator is
temporarily erased to a physical blank, a collision-free sentinel because
words contain only nonblank tape cells. The machine deletes each later
repeated-key row one token at a time. After each deletion the one-token shifter
returns to the sentinel; closeout restores the selected target terminator and
rewinds to the selected transition marker.
-/

inductive Phase where
  | boundary
  | queryNat
  | queryCell
  | needTransition
  | rowSource
  | rowRead
  | rowWrite
  | rowMove
  | rowTarget
deriving DecidableEq

namespace Phase

def finite : Foundation.FiniteType Phase where
  elems := [.boundary, .queryNat, .queryCell, .needTransition,
    .rowSource, .rowRead, .rowWrite, .rowMove, .rowTarget]
  complete := by
    intro phase
    cases phase <;> simp

end Phase

inductive Control where
  | skipWrite
  | skipMove
  | scanTarget
  | parse (phase : Phase)
  | delete (next : Phase) (inner : DeleteRestagedMachine.Control)
  | bounce (next : Phase)
  | restoreTarget
  | rewindSelected
  | bounceSelected
  | halt
deriving DecidableEq

namespace Control

def phaseDeleteFinite : Foundation.FiniteType
    (Phase × DeleteRestagedMachine.Control) :=
  Foundation.FiniteType.prod Phase.finite
    DeleteRestagedMachine.Control.finite

def elems : List Control :=
  [skipWrite, skipMove, scanTarget] ++
    Phase.finite.elems.map Control.parse ++
    phaseDeleteFinite.elems.map
      (fun payload => Control.delete payload.1 payload.2) ++
    Phase.finite.elems.map Control.bounce ++
    [restoreTarget, rewindSelected, bounceSelected, halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | skipWrite => simp [elems]
    | skipMove => simp [elems]
    | scanTarget => simp [elems]
    | parse phase => simp [elems, Phase.finite.complete phase]
    | delete next inner =>
        have h := phaseDeleteFinite.complete (next, inner)
        simp [elems, h]
    | bounce next => simp [elems, Phase.finite.complete next]
    | restoreTarget => simp [elems]
    | rewindSelected => simp [elems]
    | bounceSelected => simp [elems]
    | halt => simp [elems]

end Control

def mapAction (wrap : inner -> Control)
    (action : Option MachineCodeSymbol × Direction × inner) :
    Option MachineCodeSymbol × Direction × Control :=
  (action.1, action.2.1, wrap action.2.2)

def deleteStart : DeleteRestagedMachine.Control :=
  .edit (.erase (DeleteBlock.optionalGap none))

def beginDelete (next : Phase) (read : Option MachineCodeSymbol) :
    Option (Option MachineCodeSymbol × Direction × Control) :=
  match DeleteRestagedMachine.transition none deleteStart read with
  | none => none
  | some action => some (mapAction (Control.delete next) action)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .skipWrite, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .skipMove)
  | .skipWrite, some MachineCodeSymbol.zero =>
      some (some MachineCodeSymbol.zero, Direction.right, .skipMove)
  | .skipWrite, some MachineCodeSymbol.one =>
      some (some MachineCodeSymbol.one, Direction.right, .skipMove)
  | .skipMove, some MachineCodeSymbol.moveLeft =>
      some (some MachineCodeSymbol.moveLeft, Direction.right, .scanTarget)
  | .skipMove, some MachineCodeSymbol.moveRight =>
      some (some MachineCodeSymbol.moveRight, Direction.right, .scanTarget)
  | .scanTarget, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .scanTarget)
  | .scanTarget, some MachineCodeSymbol.done =>
      some (none, Direction.right, .parse .boundary)
  | .parse .boundary, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.left, .restoreTarget)
  | .parse .boundary, some MachineCodeSymbol.transition =>
      beginDelete .rowSource (some MachineCodeSymbol.transition)
  | .parse .queryNat, some MachineCodeSymbol.tick =>
      beginDelete .queryNat (some MachineCodeSymbol.tick)
  | .parse .queryNat, some MachineCodeSymbol.done =>
      beginDelete .queryCell (some MachineCodeSymbol.done)
  | .parse .queryCell, some MachineCodeSymbol.blank =>
      beginDelete .needTransition (some MachineCodeSymbol.blank)
  | .parse .queryCell, some MachineCodeSymbol.zero =>
      beginDelete .needTransition (some MachineCodeSymbol.zero)
  | .parse .queryCell, some MachineCodeSymbol.one =>
      beginDelete .needTransition (some MachineCodeSymbol.one)
  | .parse .needTransition, some MachineCodeSymbol.transition =>
      beginDelete .rowSource (some MachineCodeSymbol.transition)
  | .parse .rowSource, some MachineCodeSymbol.tick =>
      beginDelete .rowSource (some MachineCodeSymbol.tick)
  | .parse .rowSource, some MachineCodeSymbol.done =>
      beginDelete .rowRead (some MachineCodeSymbol.done)
  | .parse .rowRead, some MachineCodeSymbol.blank =>
      beginDelete .rowWrite (some MachineCodeSymbol.blank)
  | .parse .rowRead, some MachineCodeSymbol.zero =>
      beginDelete .rowWrite (some MachineCodeSymbol.zero)
  | .parse .rowRead, some MachineCodeSymbol.one =>
      beginDelete .rowWrite (some MachineCodeSymbol.one)
  | .parse .rowWrite, some MachineCodeSymbol.blank =>
      beginDelete .rowMove (some MachineCodeSymbol.blank)
  | .parse .rowWrite, some MachineCodeSymbol.zero =>
      beginDelete .rowMove (some MachineCodeSymbol.zero)
  | .parse .rowWrite, some MachineCodeSymbol.one =>
      beginDelete .rowMove (some MachineCodeSymbol.one)
  | .parse .rowMove, some MachineCodeSymbol.moveLeft =>
      beginDelete .rowTarget (some MachineCodeSymbol.moveLeft)
  | .parse .rowMove, some MachineCodeSymbol.moveRight =>
      beginDelete .rowTarget (some MachineCodeSymbol.moveRight)
  | .parse .rowTarget, some MachineCodeSymbol.tick =>
      beginDelete .rowTarget (some MachineCodeSymbol.tick)
  | .parse .rowTarget, some MachineCodeSymbol.done =>
      beginDelete .boundary (some MachineCodeSymbol.done)
  | .delete next (.rewind .gate), read =>
      some (read, Direction.right, .bounce next)
  | .delete next inner, read =>
      match DeleteRestagedMachine.transition none inner read with
      | none => none
      | some action => some (mapAction (Control.delete next) action)
  | .bounce next, read =>
      some (read, Direction.left, .parse next)
  | .restoreTarget, none =>
      some (some MachineCodeSymbol.done, Direction.left, .rewindSelected)
  | .rewindSelected, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.transition, Direction.right,
        .bounceSelected)
  | .rewindSelected, some current =>
      some (some current, Direction.left, .rewindSelected)
  | .bounceSelected, read =>
      some (read, Direction.left, .halt)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .skipWrite
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceTape
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  runtimeKeyRepeatedRowTargetTape baseLeftRev queryState queryRead
    selected rest protectedSuffix

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .skipWrite
  tape := sourceTape baseLeftRev queryState queryRead selected rest
    protectedSuffix

def targetTape
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  runtimeKeyComparatorTape
    (FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySelectedExtractor.actionBase
      baseLeftRev queryState queryRead)
    (MachineDescription.encodeTransitionAppend selected
      (MachineCodeSymbol.header :: protectedSuffix))

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := targetTape baseLeftRev queryState queryRead selected
    protectedSuffix

def selectedPrefixLeft
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription) : Word MachineCodeSymbol :=
  RuntimeKeySelectedExtractor.selectedPrefixLeft baseLeftRev queryState
    queryRead selected

def disposalLeftRev
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription) : Word MachineCodeSymbol :=
  List.append
    (List.replicate selected.target MachineCodeSymbol.tick).reverse
    (runtimeKeyDirectionSymbol selected.move ::
      runtimeKeyCellSymbol selected.write ::
      selectedPrefixLeft baseLeftRev queryState queryRead selected)

def sentinelTape
    (leftRev rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := none :: leftRev.map some
        head := none
        right := [] }
  | first :: suffix =>
      { left := none :: leftRev.map some
        head := some first
        right := suffix.map some }

def parseConfig (phase : Phase)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .parse phase
  tape := sentinelTape leftRev rest

theorem sourceTape_shape
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    sourceTape baseLeftRev queryState queryRead selected rest
        protectedSuffix =
      runtimeKeyComparatorTape
        (selectedPrefixLeft baseLeftRev queryState queryRead selected)
        (runtimeKeyCellSymbol selected.write ::
          runtimeKeyDirectionSymbol selected.move ::
          MachineDescription.encodeNatAppend selected.target
            (runtimeKeyRepeatedTableFrame queryState queryRead rest
              protectedSuffix)) := by
  simp [sourceTape, runtimeKeyRepeatedRowTargetTape,
    selectedPrefixLeft,
    RuntimeKeySelectedExtractor.selectedPrefixLeft,
    runtimeKeyRepeatedActionSuffix,
    runtimeKey_encodeCell_eq_singleton,
    runtimeKey_encodeDirection_eq_singleton,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeDirectionAppend]
  done

def cursorConfig (state : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := state
  tape := runtimeKeyComparatorTape leftRev rest

theorem step_write
    (write : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      { state := .skipWrite
        tape := runtimeKeyComparatorTape leftRev
          (runtimeKeyCellSymbol write :: suffix) }
      { state := .skipMove
        tape := runtimeKeyComparatorTape
          (runtimeKeyCellSymbol write :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    (runtimeKeyCellSymbol write) (runtimeKeyCellSymbol write) suffix]
  cases write with
  | none =>
      exact TuringMachine.Step.mk (by
        simp [machine, transition, runtimeKeyCellSymbol,
          runtimeKeyComparatorTape, Tape.read])
  | some bit =>
      cases bit <;>
        exact TuringMachine.Step.mk (by
          simp [machine, transition, runtimeKeyCellSymbol,
            runtimeKeyComparatorTape, Tape.read])
  done

theorem step_move
    (move : Direction)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      { state := .skipMove
        tape := runtimeKeyComparatorTape leftRev
          (runtimeKeyDirectionSymbol move :: suffix) }
      { state := .scanTarget
        tape := runtimeKeyComparatorTape
          (runtimeKeyDirectionSymbol move :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    (runtimeKeyDirectionSymbol move)
    (runtimeKeyDirectionSymbol move) suffix]
  cases move <;>
    exact TuringMachine.Step.mk (by
      simp [machine, transition, runtimeKeyDirectionSymbol,
        runtimeKeyComparatorTape, Tape.read])
  done

theorem step_target_tick
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      { state := .scanTarget
        tape := runtimeKeyComparatorTape leftRev
          (MachineCodeSymbol.tick :: suffix) }
      { state := .scanTarget
        tape := runtimeKeyComparatorTape
          (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← runtimeKeyComparatorTape_move_right leftRev
    MachineCodeSymbol.tick MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [machine, transition, runtimeKeyComparatorTape, Tape.read])
  done

theorem computes_target_ticks
    (target : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .scanTarget
        tape := runtimeKeyComparatorTape leftRev
          (List.append
            (List.replicate target MachineCodeSymbol.tick) suffix) }
      { state := .scanTarget
        tape := runtimeKeyComparatorTape
          (List.append
            (List.replicate target MachineCodeSymbol.tick).reverse
            leftRev) suffix } := by
  induction target generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ target ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [List.replicate_succ] using
            step_target_tick leftRev
              (List.append
                (List.replicate target MachineCodeSymbol.tick) suffix))
        (by
          simpa [List.replicate_succ, List.reverse_cons,
            List.append_assoc] using
            ih (MachineCodeSymbol.tick :: leftRev))
  done

theorem erase_done_move_right
    (leftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write none
          (runtimeKeyComparatorTape leftRev
            (MachineCodeSymbol.done :: first :: rest))) =
      sentinelTape leftRev (first :: rest) := by
  rfl
  done

theorem step_target_done_erase
    (leftRev frame : Word MachineCodeSymbol)
    (hframe : frame ≠ []) :
    TuringMachine.Step machine
      { state := .scanTarget
        tape := runtimeKeyComparatorTape leftRev
          (MachineCodeSymbol.done :: frame) }
      { state := .parse .boundary
        tape := sentinelTape leftRev frame } := by
  cases frame with
  | nil => contradiction
  | cons first rest =>
      rw [← erase_done_move_right leftRev first rest]
      exact TuringMachine.Step.mk (by
        simp [machine, transition, runtimeKeyComparatorTape, Tape.read])
  done

theorem frame_ne_nil
    (queryState : Nat) (queryRead : Option Bool)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    runtimeKeyRepeatedTableFrame queryState queryRead rest
      protectedSuffix ≠ [] := by
  cases rest <;> simp [runtimeKeyRepeatedTableFrame]
  done

theorem computes_to_disposal
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (sourceConfig baseLeftRev queryState queryRead selected rest
        protectedSuffix)
      (parseConfig .boundary
        (disposalLeftRev baseLeftRev queryState queryRead selected)
        (runtimeKeyRepeatedTableFrame queryState queryRead rest
          protectedSuffix)) := by
  let prefixLeft :=
    selectedPrefixLeft baseLeftRev queryState queryRead selected
  let frame :=
    runtimeKeyRepeatedTableFrame queryState queryRead rest protectedSuffix
  have hwrite :
      TuringMachine.Step machine
        (sourceConfig baseLeftRev queryState queryRead selected rest
          protectedSuffix)
        (cursorConfig .skipMove
          (runtimeKeyCellSymbol selected.write :: prefixLeft)
          (runtimeKeyDirectionSymbol selected.move ::
            MachineDescription.encodeNatAppend selected.target frame)) := by
    rw [sourceConfig, sourceTape_shape]
    exact step_write selected.write prefixLeft
      (runtimeKeyDirectionSymbol selected.move ::
        MachineDescription.encodeNatAppend selected.target frame)
  have hmove :
      TuringMachine.Step machine
        (cursorConfig .skipMove
          (runtimeKeyCellSymbol selected.write :: prefixLeft)
          (runtimeKeyDirectionSymbol selected.move ::
            MachineDescription.encodeNatAppend selected.target frame))
        (cursorConfig .scanTarget
          (runtimeKeyDirectionSymbol selected.move ::
            runtimeKeyCellSymbol selected.write :: prefixLeft)
          (MachineDescription.encodeNatAppend selected.target frame)) :=
    step_move selected.move
      (runtimeKeyCellSymbol selected.write :: prefixLeft)
      (MachineDescription.encodeNatAppend selected.target frame)
  have hticks :
      TuringMachine.Computes machine
        (cursorConfig .scanTarget
          (runtimeKeyDirectionSymbol selected.move ::
            runtimeKeyCellSymbol selected.write :: prefixLeft)
          (MachineDescription.encodeNatAppend selected.target frame))
        (cursorConfig .scanTarget
          (disposalLeftRev baseLeftRev queryState queryRead selected)
          (MachineCodeSymbol.done :: frame)) := by
    simpa [cursorConfig, MachineDescription.encodeNatAppend,
      runtimeKey_encodeNat_eq_replicate_tick_done,
      disposalLeftRev, prefixLeft, List.append_assoc] using
        computes_target_ticks selected.target
          (runtimeKeyDirectionSymbol selected.move ::
            runtimeKeyCellSymbol selected.write :: prefixLeft)
          (MachineCodeSymbol.done :: frame)
  have hdone :
      TuringMachine.Step machine
        (cursorConfig .scanTarget
          (disposalLeftRev baseLeftRev queryState queryRead selected)
          (MachineCodeSymbol.done :: frame))
        (parseConfig .boundary
          (disposalLeftRev baseLeftRev queryState queryRead selected)
          frame) :=
    step_target_done_erase
      (disposalLeftRev baseLeftRev queryState queryRead selected) frame
      (frame_ne_nil queryState queryRead rest protectedSuffix)
  exact TuringMachine.Computes.step hwrite
    (TuringMachine.Computes.step hmove
      (TuringMachine.computes_trans hticks
        (TuringMachine.Computes.step hdone
          (TuringMachine.Computes.refl _))))
  done

namespace SentinelDelete

def pullTape
    (baseLeftRev processedRev rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := none :: List.append (processedRev.map some)
          (none :: baseLeftRev.map some)
        head := none
        right := [] }
  | current :: suffix =>
      { left := none :: List.append (processedRev.map some)
          (none :: baseLeftRev.map some)
        head := some current
        right := suffix.map some }

def pullConfig
    (baseLeftRev processedRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control where
  state := .edit .pull
  tape := pullTape baseLeftRev processedRev rest

def exitTape
    (baseLeftRev wordRev : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol where
  left := List.append (wordRev.map some)
    (none :: baseLeftRev.map some)
  head := none
  right := [none]

def exitConfig
    (baseLeftRev wordRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control where
  state := .edit .halt
  tape := exitTape baseLeftRev wordRev

theorem pull_symbol_exact
    (baseLeftRev processedRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact? 3
        (pullConfig baseLeftRev processedRev (current :: suffix)) =
      some (pullConfig baseLeftRev
        (current :: processedRev) suffix) := by
  cases current <;> cases suffix <;> rfl
  done

theorem pull_finish_exact
    (baseLeftRev processedRev : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact? 1
        (pullConfig baseLeftRev processedRev []) =
      some (exitConfig baseLeftRev processedRev) := by
  rfl
  done

def editSteps (suffix : Word MachineCodeSymbol) : Nat :=
  3 * suffix.length + 1

theorem editSteps_cons
    (current : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    editSteps (current :: suffix) = 3 + editSteps suffix := by
  simp [editSteps]
  lia
  done

theorem edit_run_exact
    (baseLeftRev processedRev suffix : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact?
        (editSteps suffix)
        (pullConfig baseLeftRev processedRev suffix) =
      some (exitConfig baseLeftRev
        (List.append suffix.reverse processedRev)) := by
  induction suffix generalizing processedRev with
  | nil =>
      simpa [editSteps] using
        pull_finish_exact baseLeftRev processedRev
  | cons current suffix ih =>
      rw [editSteps_cons]
      rw [DeleteRestagedMachine.runConfigExact?_add]
      rw [pull_symbol_exact]
      simp only
      simpa [editSteps, List.reverse_cons, List.append_assoc] using
        ih (current :: processedRev)
  done

def scanTape
    (baseLeftRev remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := baseLeftRev.map some
        head := none
        right := List.append (crossed.map some)
          (DeleteEndpointRewind.trailingCells none) }
  | current :: rest =>
      { left := List.append (rest.map some)
          (none :: baseLeftRev.map some)
        head := some current
        right := List.append (crossed.map some)
          (DeleteEndpointRewind.trailingCells none) }

def scanConfig
    (baseLeftRev remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control where
  state := .rewind .scan
  tape := scanTape baseLeftRev remainingRev crossed

def gateTape
    (baseLeftRev word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.right (scanTape baseLeftRev [] word)

def gateConfig
    (baseLeftRev word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control where
  state := .rewind .gate
  tape := gateTape baseLeftRev word

theorem exit_step
    (baseLeftRev wordRev : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).stepConfig
        (exitConfig baseLeftRev wordRev) =
      some (scanConfig baseLeftRev wordRev []) := by
  cases wordRev <;> rfl
  done

theorem scan_step
    (baseLeftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).stepConfig
        (scanConfig baseLeftRev (current :: remainingRev) crossed) =
      some (scanConfig baseLeftRev remainingRev
        (current :: crossed)) := by
  cases remainingRev <;> rfl
  done

theorem scan_finish
    (baseLeftRev crossed : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).stepConfig
        (scanConfig baseLeftRev [] crossed) =
      some (gateConfig baseLeftRev crossed) := by
  cases crossed <;> rfl
  done

theorem scan_run_exact
    (baseLeftRev remainingRev crossed : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact?
        (remainingRev.length + 1)
        (scanConfig baseLeftRev remainingRev crossed) =
      some (gateConfig baseLeftRev
        (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact scan_finish baseLeftRev crossed
  | cons current remainingRev ih =>
      change (DeleteRestagedMachine.machine none).runConfigExact?
        ((remainingRev.length + 1) + 1)
        (scanConfig baseLeftRev (current :: remainingRev) crossed) = _
      rw [TuringMachine.runConfigExact?, scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]
  done

def rewindSteps (wordRev : Word MachineCodeSymbol) : Nat :=
  wordRev.length + 2

theorem rewind_run_exact
    (baseLeftRev wordRev : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact?
        (rewindSteps wordRev) (exitConfig baseLeftRev wordRev) =
      some (gateConfig baseLeftRev wordRev.reverse) := by
  unfold rewindSteps
  rw [show wordRev.length + 2 = 1 + (wordRev.length + 1) by lia]
  rw [DeleteRestagedMachine.runConfigExact?_add]
  have hfirst :
      (DeleteRestagedMachine.machine none).runConfigExact? 1
          (exitConfig baseLeftRev wordRev) =
        some (scanConfig baseLeftRev wordRev []) := by
    rw [TuringMachine.runConfigExact?, exit_step]
    rfl
  rw [hfirst]
  simp only
  simpa using scan_run_exact baseLeftRev wordRev
    ([] : Word MachineCodeSymbol)
  done

def runSteps (suffix : Word MachineCodeSymbol) : Nat :=
  editSteps suffix + rewindSteps suffix.reverse

theorem run_exact
    (baseLeftRev suffix : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact?
        (runSteps suffix) (pullConfig baseLeftRev [] suffix) =
      some (gateConfig baseLeftRev suffix) := by
  unfold runSteps
  rw [DeleteRestagedMachine.runConfigExact?_add]
  rw [edit_run_exact]
  simp only
  have happend :
      List.append suffix.reverse ([] : Word MachineCodeSymbol) =
        suffix.reverse := by
    change List.append suffix.reverse [] = _
    exact List.append_nil _
  rw [happend]
  rw [rewind_run_exact]
  simp
  done

theorem gate_tape_equiv_sentinel
    (baseLeftRev word : Word MachineCodeSymbol) :
    Tape.Equiv (gateTape baseLeftRev word)
      (sentinelTape baseLeftRev word) := by
  cases word with
  | nil =>
      refine ⟨rfl, rfl, ?_⟩
      rfl
  | cons first rest =>
      refine ⟨rfl, rfl, ?_⟩
      change Tape.dropTrailingNone
          (List.append (rest.map some)
            (List.replicate 2 (none : Option MachineCodeSymbol))) =
        Tape.dropTrailingNone (rest.map some)
      exact dropTrailingNone_append_replicate_none (rest.map some) 2
  done

end SentinelDelete

def deleteConfig (next : Phase)
    (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.delete next) c

theorem delete_step_of_some
    (next : Phase)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine none).stepConfig c =
      some d) :
    machine.stepConfig (deleteConfig next c) =
      some (deleteConfig next d) := by
  cases c with
  | mk state tape =>
      cases d with
      | mk nextState nextTape =>
          unfold TuringMachine.stepConfig at hstep ⊢
          dsimp [DeleteRestagedMachine.machine] at hstep
          cases haction : DeleteRestagedMachine.transition none state
              (Tape.read tape) with
          | none =>
              rw [haction] at hstep
              contradiction
          | some innerAction =>
              rcases innerAction with ⟨write, direction, targetState⟩
              rw [haction] at hstep
              simp only at hstep
              cases hstep
              cases state with
              | edit inner =>
                  cases inner <;>
                    simp_all [machine, transition, deleteConfig,
                      mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig]
              | rewind inner =>
                  cases inner <;>
                    simp_all [machine, transition, deleteConfig,
                      mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig,
                      DeleteRestagedMachine.transition,
                      DeleteEndpointRewind.transition]
  done

theorem delete_run_of_eq_some
    (next : Phase) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control}
    (hrun : (DeleteRestagedMachine.machine none).runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (deleteConfig next source) =
      some (deleteConfig next target) := by
  exact
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (Control.delete next) (delete_step_of_some next) hrun
  done

theorem beginDelete_eq
    (next : Phase) (deleted : MachineCodeSymbol) :
    beginDelete next (some deleted) =
      some (none, Direction.right,
        .delete next (.edit .pull)) := by
  cases deleted <;> rfl
  done

theorem parse_delete_step
    (phase next : Phase)
    (baseLeftRev suffix : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol)
    (hdelete : transition (.parse phase) (some deleted) =
      beginDelete next (some deleted)) :
    machine.stepConfig
        (parseConfig phase baseLeftRev (deleted :: suffix)) =
      some (deleteConfig next
        (SentinelDelete.pullConfig baseLeftRev [] suffix)) := by
  have hread : Tape.read
      (sentinelTape baseLeftRev (deleted :: suffix)) = some deleted := by
    cases suffix <;> rfl
  unfold TuringMachine.stepConfig
  simp only [machine, parseConfig, deleteConfig,
    TuringMachine.PhaseEmbedding.liftConfig]
  rw [hread, hdelete, beginDelete_eq]
  cases suffix <;> rfl
  done

def gateParseConfig (phase : Phase)
    (baseLeftRev word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .parse phase
  tape := SentinelDelete.gateTape baseLeftRev word

theorem delete_bounce_exact
    (next : Phase)
    (baseLeftRev word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (deleteConfig next
          (SentinelDelete.gateConfig baseLeftRev word)) =
      some (gateParseConfig next baseLeftRev word) := by
  cases word with
  | nil => rfl
  | cons first rest =>
      cases rest <;> rfl
  done

def deletePhaseSteps (suffix : Word MachineCodeSymbol) : Nat :=
  1 + SentinelDelete.runSteps suffix + 2

theorem runConfigExact_trans
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol Control}
    (hab : machine.runConfigExact? first a = some b)
    (hbc : machine.runConfigExact? second b = some c) :
    machine.runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)
  done

theorem delete_symbol_exact
    (phase next : Phase)
    (baseLeftRev suffix : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol)
    (hdelete : transition (.parse phase) (some deleted) =
      beginDelete next (some deleted)) :
    machine.runConfigExact? (deletePhaseSteps suffix)
        (parseConfig phase baseLeftRev (deleted :: suffix)) =
      some (gateParseConfig next baseLeftRev suffix) := by
  unfold deletePhaseSteps
  have hfirst : machine.runConfigExact? 1
      (parseConfig phase baseLeftRev (deleted :: suffix)) =
    some (deleteConfig next
      (SentinelDelete.pullConfig baseLeftRev [] suffix)) := by
    rw [TuringMachine.runConfigExact?,
      parse_delete_step phase next baseLeftRev suffix deleted hdelete]
    rfl
  exact runConfigExact_trans
    (runConfigExact_trans hfirst
      (delete_run_of_eq_some next
        (SentinelDelete.run_exact baseLeftRev suffix)))
    (delete_bounce_exact next baseLeftRev suffix)
  done

theorem delete_symbol_of_tape_equiv
    (phase next : Phase)
    (baseLeftRev suffix : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (hdelete : transition (.parse phase) (some deleted) =
      beginDelete next (some deleted))
    (htape : Tape.Equiv
      (sentinelTape baseLeftRev (deleted :: suffix)) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      machine.runConfigExact? (deletePhaseSteps suffix)
          { state := .parse phase, tape := tape } =
        some { state := .parse next, tape := targetTape } ∧
      Tape.Equiv (sentinelTape baseLeftRev suffix) targetTape := by
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (delete_symbol_exact phase next baseLeftRev suffix deleted
          hdelete) htape with
    ⟨targetConfig', hrun, hstate, htarget⟩
  rcases targetConfig' with ⟨targetState, targetTape⟩
  simp only [gateParseConfig] at hstate
  subst targetState
  refine ⟨targetTape, hrun, ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (SentinelDelete.gate_tape_equiv_sentinel baseLeftRev suffix))
    htarget
  done

theorem delete_symbol_computes_of_tape_equiv
    (phase next : Phase)
    (baseLeftRev suffix : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (hdelete : transition (.parse phase) (some deleted) =
      beginDelete next (some deleted))
    (htape : Tape.Equiv
      (sentinelTape baseLeftRev (deleted :: suffix)) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
          { state := .parse phase, tape := tape }
          { state := .parse next, tape := targetTape } ∧
      Tape.Equiv (sentinelTape baseLeftRev suffix) targetTape := by
  rcases delete_symbol_of_tape_equiv phase next baseLeftRev suffix
      deleted tape hdelete htape with
    ⟨targetTape, hrun, htape'⟩
  exact ⟨targetTape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun),
    htape'⟩
  done

theorem disposeNat
    (phase next : Phase)
    (htick : transition (.parse phase)
      (some MachineCodeSymbol.tick) =
        beginDelete phase (some MachineCodeSymbol.tick))
    (hdone : transition (.parse phase)
      (some MachineCodeSymbol.done) =
        beginDelete next (some MachineCodeSymbol.done))
    (baseLeftRev : Word MachineCodeSymbol)
    (value : Nat) (suffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (sentinelTape baseLeftRev
        (MachineDescription.encodeNatAppend value suffix)) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
          { state := .parse phase, tape := tape }
          { state := .parse next, tape := targetTape } ∧
      Tape.Equiv (sentinelTape baseLeftRev suffix) targetTape := by
  induction value generalizing tape with
  | zero =>
      have hsource : Tape.Equiv
          (sentinelTape baseLeftRev
            (MachineCodeSymbol.done :: suffix)) tape := by
        simpa [MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat] using htape
      exact delete_symbol_computes_of_tape_equiv phase next
        baseLeftRev suffix MachineCodeSymbol.done tape hdone hsource
  | succ value ih =>
      let tail := MachineDescription.encodeNatAppend value suffix
      have hsource : Tape.Equiv
          (sentinelTape baseLeftRev
            (MachineCodeSymbol.tick :: tail)) tape := by
        simpa [tail, MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat] using htape
      rcases delete_symbol_computes_of_tape_equiv phase phase
          baseLeftRev tail MachineCodeSymbol.tick tape htick hsource with
        ⟨middleTape, hfirst, hmiddle⟩
      rcases ih middleTape hmiddle with
        ⟨targetTape, hrest, htarget⟩
      exact ⟨targetTape,
        TuringMachine.computes_trans hfirst hrest, htarget⟩
  done

theorem disposeCell
    (phase next : Phase)
    (baseLeftRev : Word MachineCodeSymbol)
    (cell : Option Bool) (suffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (hblank : transition (.parse phase)
      (some MachineCodeSymbol.blank) =
        beginDelete next (some MachineCodeSymbol.blank))
    (hzero : transition (.parse phase)
      (some MachineCodeSymbol.zero) =
        beginDelete next (some MachineCodeSymbol.zero))
    (hone : transition (.parse phase)
      (some MachineCodeSymbol.one) =
        beginDelete next (some MachineCodeSymbol.one))
    (htape : Tape.Equiv
      (sentinelTape baseLeftRev
        (MachineDescription.encodeCellAppend cell suffix)) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
          { state := .parse phase, tape := tape }
          { state := .parse next, tape := targetTape } ∧
      Tape.Equiv (sentinelTape baseLeftRev suffix) targetTape := by
  cases cell with
  | none =>
      exact delete_symbol_computes_of_tape_equiv phase next
        baseLeftRev suffix MachineCodeSymbol.blank tape hblank (by
          simpa [MachineDescription.encodeCellAppend,
            MachineDescription.encodeCell] using htape)
  | some bit =>
      cases bit with
      | false =>
          exact delete_symbol_computes_of_tape_equiv phase next
            baseLeftRev suffix MachineCodeSymbol.zero tape hzero (by
              simpa [MachineDescription.encodeCellAppend,
                MachineDescription.encodeCell] using htape)
      | true =>
          exact delete_symbol_computes_of_tape_equiv phase next
            baseLeftRev suffix MachineCodeSymbol.one tape hone (by
              simpa [MachineDescription.encodeCellAppend,
                MachineDescription.encodeCell] using htape)
  done

theorem disposeDirection
    (phase next : Phase)
    (baseLeftRev : Word MachineCodeSymbol)
    (move : Direction) (suffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (hleft : transition (.parse phase)
      (some MachineCodeSymbol.moveLeft) =
        beginDelete next (some MachineCodeSymbol.moveLeft))
    (hright : transition (.parse phase)
      (some MachineCodeSymbol.moveRight) =
        beginDelete next (some MachineCodeSymbol.moveRight))
    (htape : Tape.Equiv
      (sentinelTape baseLeftRev
        (MachineDescription.encodeDirectionAppend move suffix)) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
          { state := .parse phase, tape := tape }
          { state := .parse next, tape := targetTape } ∧
      Tape.Equiv (sentinelTape baseLeftRev suffix) targetTape := by
  cases move with
  | left =>
      exact delete_symbol_computes_of_tape_equiv phase next
        baseLeftRev suffix MachineCodeSymbol.moveLeft tape hleft (by
          simpa [MachineDescription.encodeDirectionAppend,
            MachineDescription.encodeDirection] using htape)
  | right =>
      exact delete_symbol_computes_of_tape_equiv phase next
        baseLeftRev suffix MachineCodeSymbol.moveRight tape hright (by
          simpa [MachineDescription.encodeDirectionAppend,
            MachineDescription.encodeDirection] using htape)
  done

theorem disposeRow
    (baseLeftRev : Word MachineCodeSymbol)
    (row : TransitionDescription)
    (rest : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (sentinelTape baseLeftRev
        (MachineDescription.encodeTransitionAppend row
          (MachineDescription.encodeTransitionsAppend rest
            (MachineCodeSymbol.header :: protectedSuffix)))) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
          { state := .parse .boundary, tape := tape }
          { state := .parse .boundary, tape := targetTape } ∧
      Tape.Equiv
        (sentinelTape baseLeftRev
          (MachineDescription.encodeTransitionsAppend rest
            (MachineCodeSymbol.header :: protectedSuffix))) targetTape := by
  let rowsTail := MachineDescription.encodeTransitionsAppend rest
    (MachineCodeSymbol.header :: protectedSuffix)
  let targetTail := MachineDescription.encodeNatAppend row.target rowsTail
  let moveTail := MachineDescription.encodeDirectionAppend row.move targetTail
  let writeTail := MachineDescription.encodeCellAppend row.write moveTail
  let readTail := MachineDescription.encodeCellAppend row.read writeTail
  let sourceTail := MachineDescription.encodeNatAppend row.source readTail
  have hsource : Tape.Equiv
      (sentinelTape baseLeftRev
        (MachineCodeSymbol.transition :: sourceTail)) tape := by
    simpa [sourceTail, readTail, writeTail, moveTail, targetTail, rowsTail,
      MachineDescription.encodeTransitionAppend,
      runtimeKeyRawTransitionTail] using htape
  rcases delete_symbol_computes_of_tape_equiv .boundary .rowSource
      baseLeftRev sourceTail MachineCodeSymbol.transition tape (by rfl)
      hsource with
    ⟨sourceTape, hsourceStep, hsourceTape⟩
  rcases disposeNat .rowSource .rowRead (by rfl) (by rfl)
      baseLeftRev row.source readTail sourceTape (by
        simpa [sourceTail] using hsourceTape) with
    ⟨readTape, hreadStep, hreadTape⟩
  rcases disposeCell .rowRead .rowWrite baseLeftRev row.read writeTail
      readTape (by rfl) (by rfl) (by rfl) (by
        simpa [readTail] using hreadTape) with
    ⟨writeTape, hwriteStep, hwriteTape⟩
  rcases disposeCell .rowWrite .rowMove baseLeftRev row.write moveTail
      writeTape (by rfl) (by rfl) (by rfl) (by
        simpa [writeTail] using hwriteTape) with
    ⟨moveTape, hmoveStep, hmoveTape⟩
  rcases disposeDirection .rowMove .rowTarget baseLeftRev row.move
      targetTail moveTape (by rfl) (by rfl) (by
        simpa [moveTail] using hmoveTape) with
    ⟨targetTape, htargetStep, htargetTape⟩
  rcases disposeNat .rowTarget .boundary (by rfl) (by rfl)
      baseLeftRev row.target rowsTail targetTape (by
        simpa [targetTail] using htargetTape) with
    ⟨finishTape, hfinishStep, hfinishTape⟩
  refine ⟨finishTape, ?_, ?_⟩
  · exact TuringMachine.computes_trans hsourceStep
      (TuringMachine.computes_trans hreadStep
        (TuringMachine.computes_trans hwriteStep
          (TuringMachine.computes_trans hmoveStep
            (TuringMachine.computes_trans htargetStep hfinishStep))))
  · simpa [rowsTail] using hfinishTape
  done

theorem disposeRows
    (baseLeftRev : Word MachineCodeSymbol)
    (rows : List TransitionDescription)
    (protectedSuffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (sentinelTape baseLeftRev
        (MachineDescription.encodeTransitionsAppend rows
          (MachineCodeSymbol.header :: protectedSuffix))) tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
          { state := .parse .boundary, tape := tape }
          { state := .parse .boundary, tape := targetTape } ∧
      Tape.Equiv
        (sentinelTape baseLeftRev
          (MachineCodeSymbol.header :: protectedSuffix)) targetTape := by
  induction rows generalizing tape with
  | nil =>
      refine ⟨tape, TuringMachine.Computes.refl _, ?_⟩
      simpa [MachineDescription.encodeTransitionsAppend] using htape
  | cons row rest ih =>
      rcases disposeRow baseLeftRev row rest protectedSuffix tape (by
        simpa [MachineDescription.encodeTransitionsAppend] using htape) with
        ⟨middleTape, hfirst, hmiddle⟩
      rcases ih middleTape hmiddle with
        ⟨targetTape, hrest, htarget⟩
      exact ⟨targetTape, TuringMachine.computes_trans hfirst hrest,
        htarget⟩
  done

end RuntimeKeySelectedExtractorArbitrary

end Computability
end FoC
