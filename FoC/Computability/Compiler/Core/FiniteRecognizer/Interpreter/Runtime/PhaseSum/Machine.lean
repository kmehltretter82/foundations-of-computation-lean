import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.BoundedLoop
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.RuntimePhaseSum

open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.StackIteration
open FiniteRecognizer.Interpreter.SelectedUpdateIntegration
open FiniteRecognizer.Interpreter.FinalGateMaterializer
open FiniteRecognizer.Interpreter.NoMatchFinalGate
open FiniteRecognizer.Interpreter.NoMatchFinalGate.LastMiss
open FiniteRecognizer.Interpreter.SemanticIteration
open FiniteRecognizer.Interpreter.BoundedLoopInduction
open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

abbrev Action := FiniteRecognizer.Interpreter.RuntimeAction.Action

inductive PrefixPurpose where
  | initial
  | leftPop
  | rightCheck
deriving DecidableEq

namespace PrefixPurpose

def finite : Foundation.FiniteType PrefixPurpose where
  elems := [.initial, .leftPop, .rightCheck]
  complete := by intro purpose; cases purpose <;> simp

end PrefixPurpose

inductive StackPurpose where
  | miss
  | initial (action : Action) (zeroCopies : Bool)
  | leftPop (action : Action)
  | rightCheck (action : Action)
deriving DecidableEq

namespace StackPurpose

def finite : Foundation.FiniteType StackPurpose where
  elems := .miss ::
    (FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.flatMap fun action =>
      [StackPurpose.initial action false,
        StackPurpose.initial action true]) ++
    FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map StackPurpose.leftPop ++
    FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map StackPurpose.rightCheck
  complete := by
    intro purpose
    cases purpose with
    | miss => simp
    | initial action zeroCopies =>
        cases zeroCopies <;>
          simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | leftPop action =>
        simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | rightCheck action =>
        simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]

end StackPurpose

inductive PrependMode where
  | left (action : Action) (wasEmpty : Bool)
  | right (action : Action)
deriving DecidableEq

namespace PrependMode

def finite : Foundation.FiniteType PrependMode where
  elems :=
    (FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.flatMap fun action =>
      [PrependMode.left action false, PrependMode.left action true]) ++
    FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map PrependMode.right
  complete := by
    intro mode
    cases mode with
    | left action wasEmpty =>
        cases wasEmpty <;>
          simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | right action =>
        simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]

end PrependMode

inductive BoundaryMode where
  | missLeft
  | missRight
  | finalLeft
  | finalRight
  | leftWrite (action : Action) (wasEmpty : Bool)
  | rightCheck (action : Action)
deriving DecidableEq

namespace BoundaryMode

def finite : Foundation.FiniteType BoundaryMode where
  elems := [.missLeft, .missRight, .finalLeft, .finalRight] ++
    (FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.flatMap fun action =>
      [BoundaryMode.leftWrite action false,
        BoundaryMode.leftWrite action true]) ++
    FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map BoundaryMode.rightCheck
  complete := by
    intro mode
    cases mode with
    | missLeft => simp
    | missRight => simp
    | finalLeft => simp
    | finalRight => simp
    | leftWrite action wasEmpty =>
        cases wasEmpty <;>
          simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | rightCheck action =>
        simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]

end BoundaryMode

inductive PopMode where
  | left (action : Action)
  | right (action : Action)
deriving DecidableEq

namespace PopMode

def finite : Foundation.FiniteType PopMode where
  elems := FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map PopMode.left ++
    FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map PopMode.right
  complete := by
    intro mode
    cases mode with
    | left action =>
        simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | right action =>
        simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]

end PopMode

inductive RewindMode where
  | finalSuccess (haltToken : Bool)
  | finalMiss
  | rightEmpty (action : Action)
deriving DecidableEq

namespace RewindMode

def finite : Foundation.FiniteType RewindMode where
  elems := [.finalSuccess false, .finalSuccess true, .finalMiss] ++
    FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map RewindMode.rightEmpty
  complete := by
    intro mode
    cases mode with
    | finalSuccess haltToken => cases haltToken <;> simp
    | finalMiss => simp
    | rightEmpty action =>
        simp [FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]

end RewindMode

inductive Control where
  | scan (inner : RuntimeKeySingleKeyRepair.ComparatorState)
  | extract (inner : RuntimeKeySelectedExtractorArbitrary.Control)
  | action (inner : FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control)
  | cleanup (inner : FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control)
  | prefixPhase (purpose : PrefixPurpose)
      (inner : FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control)
  | stackProbe (action : Action)
  | stackProbeBounce (action : Action) (zeroCopies : Bool)
  | stack (purpose : StackPurpose) (inner : FiniteRecognizer.Interpreter.StackSkip.Control)
  | leftProbe (action : Action)
  | leftProbeBounce (action : Action) (wasEmpty : Bool)
  | boundary (mode : BoundaryMode)
      (inner : FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control)
  | prepend (mode : PrependMode)
      (inner : FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control)
  | rightProbe (action : Action)
  | rightProbeBounce (action : Action) (wasEmpty : Bool)
  | pop (mode : PopMode) (inner : FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control)
  | restage (inner : NextCopyRestager.Control)
  | haltMarker (inner : FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.Control)
  | doubleMarker (inner : FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.Control)
  | rewind (mode : RewindMode)
      (inner : RewindWord.Control)
  | prefixBuilder (inner : FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.Control)
  | currentBuilder (inner : FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.Control)
  | haltCopier (inner : FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.Control)
  | finalCompare (inner : RuntimeKeyComparatorState)
  | accept
  | reject
deriving DecidableEq

namespace Control

def prefixFinite := Foundation.FiniteType.prod PrefixPurpose.finite
  FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control.finite

def actionBoolFinite := Foundation.FiniteType.prod
  FiniteRecognizer.Interpreter.RuntimeAction.Action.finite
  { elems := [false, true], complete := by intro bit; cases bit <;> simp }

def stackFinite := Foundation.FiniteType.prod StackPurpose.finite
  FiniteRecognizer.Interpreter.StackSkip.Control.finite

def boundaryFinite := Foundation.FiniteType.prod BoundaryMode.finite
  FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control.finite

def prependFinite := Foundation.FiniteType.prod PrependMode.finite
  FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.finite

def popFinite := Foundation.FiniteType.prod PopMode.finite
  FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control.finite

def rewindFinite := Foundation.FiniteType.prod RewindMode.finite
  RewindWord.Control.finite

def elems : List Control :=
  RuntimeKeySingleKeyRepair.ComparatorState.finite.elems.map scan ++
  RuntimeKeySelectedExtractorArbitrary.Control.finite.elems.map extract ++
  FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.finite.elems.map action ++
  FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.finite.elems.map cleanup ++
  prefixFinite.elems.map (fun payload => prefixPhase payload.1 payload.2) ++
  FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map stackProbe ++
  actionBoolFinite.elems.map
    (fun payload => stackProbeBounce payload.1 payload.2) ++
  stackFinite.elems.map (fun payload => stack payload.1 payload.2) ++
  FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map leftProbe ++
  actionBoolFinite.elems.map
    (fun payload => leftProbeBounce payload.1 payload.2) ++
  boundaryFinite.elems.map (fun payload => boundary payload.1 payload.2) ++
  prependFinite.elems.map (fun payload => prepend payload.1 payload.2) ++
  FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map rightProbe ++
  actionBoolFinite.elems.map
    (fun payload => rightProbeBounce payload.1 payload.2) ++
  popFinite.elems.map (fun payload => pop payload.1 payload.2) ++
  NextCopyRestager.Control.finite.elems.map restage ++
  FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.Control.finite.elems.map
    haltMarker ++
  FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.Control.finite.elems.map
    doubleMarker ++
  rewindFinite.elems.map (fun payload => rewind payload.1 payload.2) ++
  FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.Control.finite.elems.map
    prefixBuilder ++
  FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.Control.finite.elems.map
    currentBuilder ++
  FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.Control.finite.elems.map
    haltCopier ++
  RuntimeKeyComparatorState.finite.elems.map finalCompare ++
  [.accept, .reject]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | scan inner => simp [elems, RuntimeKeySingleKeyRepair.ComparatorState.finite.complete inner]
    | extract inner => simp [elems, RuntimeKeySelectedExtractorArbitrary.Control.finite.complete inner]
    | action inner => simp [elems, FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control.finite.complete inner]
    | cleanup inner => simp [elems, FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control.finite.complete inner]
    | prefixPhase purpose inner => simp [elems, prefixFinite.complete (purpose, inner)]
    | stackProbe action => simp [elems, FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | stackProbeBounce action zeroCopies => simp [elems, actionBoolFinite.complete (action, zeroCopies)]
    | stack purpose inner => simp [elems, stackFinite.complete (purpose, inner)]
    | leftProbe action => simp [elems, FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | leftProbeBounce action wasEmpty => simp [elems, actionBoolFinite.complete (action, wasEmpty)]
    | boundary mode inner => simp [elems, boundaryFinite.complete (mode, inner)]
    | prepend mode inner => simp [elems, prependFinite.complete (mode, inner)]
    | rightProbe action => simp [elems, FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | rightProbeBounce action wasEmpty => simp [elems, actionBoolFinite.complete (action, wasEmpty)]
    | pop mode inner => simp [elems, popFinite.complete (mode, inner)]
    | restage inner => simp [elems, NextCopyRestager.Control.finite.complete inner]
    | haltMarker inner => simp [elems, FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.Control.finite.complete inner]
    | doubleMarker inner => simp [elems, FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.Control.finite.complete inner]
    | rewind mode inner => simp [elems, rewindFinite.complete (mode, inner)]
    | prefixBuilder inner => simp [elems, FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.Control.finite.complete inner]
    | currentBuilder inner => simp [elems, FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.Control.finite.complete inner]
    | haltCopier inner => simp [elems, FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.Control.finite.complete inner]
    | finalCompare inner => simp [elems, RuntimeKeyComparatorState.finite.complete inner]
    | accept => simp [elems]
    | reject => simp [elems]

end Control

def mapTransition
    {innerState : Type}
    (embed : innerState -> Control) :
    Option (Option MachineCodeSymbol × Direction × innerState) ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def scanEmbed : RuntimeKeySingleKeyRepair.ComparatorState -> Control
  | .selected => .extract .skipWrite
  | .exhausted => .stack .miss .afterHeader
  | inner => .scan inner

def extractEmbed : RuntimeKeySelectedExtractorArbitrary.Control -> Control
  | .halt => .action .needTransition
  | inner => .extract inner

def actionEmbed : FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control -> Control
  | .ready write move =>
      .cleanup (.enter { write := write, move := move })
  | inner => .action inner

def cleanupEmbed : FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control -> Control
  | .ready action => .prefixPhase .initial (.target action)
  | inner => .cleanup inner

def prefixEmbed
    (purpose : PrefixPurpose) :
    FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control -> Control
  | .ready action =>
      match purpose with
      | .initial => .stackProbe action
      | .leftPop => .stack (.leftPop action) .afterHeader
      | .rightCheck => .stack (.rightCheck action) .afterHeader
  | inner => .prefixPhase purpose inner

def stackEmbed
    (purpose : StackPurpose) : FiniteRecognizer.Interpreter.StackSkip.Control -> Control
  | .ready =>
      match purpose with
      | .miss => .boundary .missLeft (.locate .count)
      | .initial _action true =>
          .boundary .finalLeft (.locate .count)
      | .initial action false =>
          match action.move with
          | .left => .leftProbe action
          | .right => .prepend (.right action) (.locate .count)
      | .leftPop action => .pop (.left action) (.locate .count)
      | .rightCheck action =>
          .boundary (.rightCheck action) (.locate .count)
  | inner => .stack purpose inner

def boundaryEmbed
    (mode : BoundaryMode) :
    FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control -> Control
  | .ready =>
      match mode with
      | .missLeft => .boundary .missRight (.locate .count)
      | .missRight => .doubleMarker .enter
      | .finalLeft => .boundary .finalRight (.locate .count)
      | .finalRight => .haltMarker .enter
      | .leftWrite action wasEmpty =>
          .prepend (.left action wasEmpty) (.locate .count)
      | .rightCheck action => .rightProbe action
  | inner => .boundary mode inner

def prependEmbed
    (mode : PrependMode) :
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control -> Control
  | .insert (.rewind .gate) =>
      match mode with
      | .left _action true => .restage (.target none)
      | .left action false => .prefixPhase .leftPop (.target action)
      | .right action => .prefixPhase .rightCheck (.target action)
  | inner => .prepend mode inner

def popEmbed
    (mode : PopMode) : FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control -> Control
  | .ready nextHead => .restage (.target nextHead)
  | inner => .pop mode inner

def restageEmbed : NextCopyRestager.Control -> Control
  | .ready _ => .scan (.inner RuntimeKeyComparatorState.scanQuery)
  | inner => .restage inner

def haltMarkerEmbed :
    FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.Control -> Control
  | .ready token => .rewind (.finalSuccess token) .scan
  | inner => .haltMarker inner

def doubleMarkerEmbed :
    FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.Control -> Control
  | .ready => .rewind .finalMiss .scan
  | inner => .doubleMarker inner

def rewindEmbed (mode : RewindMode) : RewindWord.Control -> Control
  | .gate =>
      match mode with
      | .finalSuccess token => .prefixBuilder (.start token)
      | .finalMiss => .currentBuilder .start
      | .rightEmpty _ => .restage (.target none)
  | inner => .rewind mode inner

def prefixBuilderEmbed :
    FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.Control -> Control
  | .ready token => .haltCopier (.seekSource token)
  | inner => .prefixBuilder inner

def currentBuilderEmbed :
    FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.Control -> Control
  | .ready token => .haltCopier (.seekSource token)
  | inner => .currentBuilder inner

def haltCopierEmbed :
    FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.Control -> Control
  | .ready => .finalCompare .needHeader
  | inner => .haltCopier inner

def finalCompareEmbed : RuntimeKeyComparatorState -> Control
  | .matched => .accept
  | .missed => .reject
  | inner => .finalCompare inner

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .scan inner, read =>
      mapTransition scanEmbed (comparatorMachine.transition inner read)
  | .extract inner, read =>
      mapTransition extractEmbed
        (RuntimeKeySelectedExtractorArbitrary.machine.transition inner read)
  | .action inner, read =>
      mapTransition actionEmbed
        (FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine.transition inner read)
  | .cleanup inner, read =>
      mapTransition cleanupEmbed
        (FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine.transition inner read)
  | .prefixPhase purpose inner, read =>
      mapTransition (prefixEmbed purpose)
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine.transition inner read)
  | .stackProbe action, some symbol =>
      some (some symbol, Direction.left,
        .stackProbeBounce action (symbol = MachineCodeSymbol.header))
  | .stackProbeBounce action zeroCopies, read =>
      some (read, Direction.right,
        .stack (.initial action zeroCopies) .afterHeader)
  | .stack purpose inner, read =>
      mapTransition (stackEmbed purpose)
        (FiniteRecognizer.Interpreter.StackSkip.machine.transition inner read)
  | .leftProbe action, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left,
        .leftProbeBounce action true)
  | .leftProbe action, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left,
        .leftProbeBounce action false)
  | .leftProbeBounce action wasEmpty, read =>
      some (read, Direction.right,
        .boundary (.leftWrite action wasEmpty) (.locate .count))
  | .boundary mode inner, read =>
      mapTransition (boundaryEmbed mode)
        (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine.transition inner read)
  | .prepend mode inner, read =>
      mapTransition (prependEmbed mode)
        ((FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine
          (match mode with
           | .left action _ => action.write
           | .right action => action.write)).transition inner read)
  | .rightProbe action, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left,
        .rightProbeBounce action true)
  | .rightProbe action, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left,
        .rightProbeBounce action false)
  | .rightProbeBounce action true, read =>
      some (read, Direction.right,
        .rewind (.rightEmpty action) .scan)
  | .rightProbeBounce action false, read =>
      some (read, Direction.right,
        .pop (.right action) (.locate .count))
  | .pop mode inner, read =>
      mapTransition (popEmbed mode)
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine.transition inner read)
  | .restage inner, read =>
      mapTransition restageEmbed
        (NextCopyRestager.machine.transition inner read)
  | .haltMarker inner, read =>
      mapTransition haltMarkerEmbed
        (FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.machine.transition
          inner read)
  | .doubleMarker inner, read =>
      mapTransition doubleMarkerEmbed
        (FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.machine.transition
          inner read)
  | .rewind mode inner, read =>
      mapTransition (rewindEmbed mode)
        (RewindWord.machine.transition inner read)
  | .prefixBuilder inner, read =>
      mapTransition prefixBuilderEmbed
        (FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.machine.transition
          inner read)
  | .currentBuilder inner, read =>
      mapTransition currentBuilderEmbed
        (FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.machine.transition
          inner read)
  | .haltCopier inner, read =>
      mapTransition haltCopierEmbed
        (FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.machine.transition
          inner read)
  | .finalCompare inner, read =>
      mapTransition finalCompareEmbed
        (runtimeKeyComparatorMachine.transition inner read)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := scanEmbed comparatorMachine.start
  halt := .accept
  transition := transition
  statesFinite := Control.finite

theorem accept_transition_none
    (read : Option MachineCodeSymbol) :
    machine.transition .accept read = none := by
  rfl

theorem reject_transition_none
    (read : Option MachineCodeSymbol) :
    machine.transition .reject read = none := by
  rfl

theorem haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled machine := by
  intro read
  exact accept_transition_none read

theorem step_of_transition_embedding
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hsimulate : forall
      (source target : innerState)
      (read write : Option MachineCodeSymbol)
      (direction : Direction),
        inner.transition source read = some (write, direction, target) ->
        transition (embed source) read =
          some (write, direction, embed target))
    (source target :
      TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig source = some target) :
    machine.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  cases source with
  | mk sourceState tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [machine]
      cases htransition :
          inner.transition sourceState (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, targetState⟩
          rw [htransition] at hstep
          simp only at hstep
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          rw [hsimulate sourceState targetState (Tape.read tape) write
            direction htransition]
          cases hstep
          rfl

theorem computes_of_transition_embedding
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hsimulate : forall
      (source target : innerState)
      (read write : Option MachineCodeSymbol)
      (direction : Direction),
        inner.transition source read = some (write, direction, target) ->
        transition (embed source) read =
          some (write, direction, embed target))
    {source target :
      TuringMachine.Configuration MachineCodeSymbol innerState}
    (hrun : TuringMachine.Computes inner source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    embed
  · intro source target hstep
    exact step_of_transition_embedding inner embed hsimulate source target
      hstep
  · exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem scan_transition_of_eq_some
    (source target : RuntimeKeySingleKeyRepair.ComparatorState)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : comparatorMachine.transition source read =
      some (write, direction, target)) :
    transition (scanEmbed source) read =
      some (write, direction, scanEmbed target) := by
  cases source <;>
    simp [scanEmbed, comparatorMachine, transition, mapTransition]
      at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem extract_transition_of_eq_some
    (source target : RuntimeKeySelectedExtractorArbitrary.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition :
      RuntimeKeySelectedExtractorArbitrary.machine.transition source read =
        some (write, direction, target)) :
    transition (extractEmbed source) read =
      some (write, direction, extractEmbed target) := by
  cases source <;>
    simp [extractEmbed, RuntimeKeySelectedExtractorArbitrary.machine,
      RuntimeKeySelectedExtractorArbitrary.transition, transition,
      mapTransition] at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem action_transition_of_eq_some
    (source target : FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine.transition
      source read = some (write, direction, target)) :
    transition (actionEmbed source) read =
      some (write, direction, actionEmbed target) := by
  cases source <;>
    simp [actionEmbed, FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine,
      FiniteRecognizer.Interpreter.RuntimeActionPrefix.transition, transition, mapTransition]
      at htransition ⊢
  all_goals simp [htransition]

theorem cleanup_transition_of_eq_some
    (source target : FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine.transition
      source read = some (write, direction, target)) :
    transition (cleanupEmbed source) read =
      some (write, direction, cleanupEmbed target) := by
  cases source <;>
    simp [cleanupEmbed, FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine,
      FiniteRecognizer.Interpreter.RuntimeLeftCleanup.transition, transition, mapTransition]
      at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem scan_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeySingleKeyRepair.ComparatorState}
    (hrun : TuringMachine.Computes comparatorMachine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig scanEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig scanEmbed target) :=
  computes_of_transition_embedding comparatorMachine scanEmbed
    scan_transition_of_eq_some hrun

theorem extract_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeySelectedExtractorArbitrary.Control}
    (hrun : TuringMachine.Computes
      RuntimeKeySelectedExtractorArbitrary.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig extractEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig extractEmbed target) :=
  computes_of_transition_embedding
    RuntimeKeySelectedExtractorArbitrary.machine extractEmbed
      extract_transition_of_eq_some hrun

theorem action_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.RuntimeActionPrefix.Control}
    (hrun : TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine
      source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig actionEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig actionEmbed target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.RuntimeActionPrefix.machine
    actionEmbed action_transition_of_eq_some hrun

theorem cleanup_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.RuntimeLeftCleanup.Control}
    (hrun : TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine
      source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig cleanupEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig cleanupEmbed target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.RuntimeLeftCleanup.machine
    cleanupEmbed cleanup_transition_of_eq_some hrun

theorem prefix_transition_of_eq_some
    (purpose : PrefixPurpose)
    (source target : FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine.transition
      source read = some (write, direction, target)) :
    transition (prefixEmbed purpose source) read =
      some (write, direction, prefixEmbed purpose target) := by
  have hnormal : prefixEmbed purpose source =
      .prefixPhase purpose source := by
    cases source with
    | target _ => rfl
    | guard _ => rfl
    | ready _ =>
        simp [FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine,
          FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.transition] at htransition
    | halt => rfl
  rw [hnormal]
  change mapTransition (prefixEmbed purpose)
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine.transition source read) = _
  rw [htransition]
  rfl

theorem stack_transition_of_eq_some
    (purpose : StackPurpose)
    (source target : FiniteRecognizer.Interpreter.StackSkip.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.StackSkip.machine.transition source read =
      some (write, direction, target)) :
    transition (stackEmbed purpose source) read =
      some (write, direction, stackEmbed purpose target) := by
  have hnormal : stackEmbed purpose source = .stack purpose source := by
    cases source with
    | afterHeader => rfl
    | scan => rfl
    | ready =>
        simp [FiniteRecognizer.Interpreter.StackSkip.machine, FiniteRecognizer.Interpreter.StackSkip.transition]
          at htransition
    | halt => rfl
  rw [hnormal]
  change mapTransition (stackEmbed purpose)
      (FiniteRecognizer.Interpreter.StackSkip.machine.transition source read) = _
  rw [htransition]
  rfl

theorem boundary_transition_of_eq_some
    (mode : BoundaryMode)
    (source target : FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine.transition
      source read = some (write, direction, target)) :
    transition (boundaryEmbed mode source) read =
      some (write, direction, boundaryEmbed mode target) := by
  have hnormal : boundaryEmbed mode source = .boundary mode source := by
    cases source with
    | locate _ => rfl
    | enter => rfl
    | payload => rfl
    | bounce => rfl
    | ready =>
        simp [FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine,
          FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.transition] at htransition
    | halt => rfl
  rw [hnormal]
  change mapTransition (boundaryEmbed mode)
      (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine.transition source read) = _
  rw [htransition]
  rfl

def prependModeWrite : PrependMode -> Option Bool
  | .left action _ => action.write
  | .right action => action.write

theorem prepend_transition_of_eq_some
    (mode : PrependMode)
    (source target : FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition :
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine
        (prependModeWrite mode)).transition source read =
          some (write, direction, target)) :
    transition (prependEmbed mode source) read =
      some (write, direction, prependEmbed mode target) := by
  have hterminal : source ≠
      FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control.insert (.rewind .gate) := by
    intro heq
    subst source
    simp [FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine,
      FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.transition,
      InsertRestagedMachine.transition, RewindWord.transition]
      at htransition
  have hnormal : prependEmbed mode source = .prepend mode source := by
    cases source with
    | locate _ => rfl
    | replaceCountDone => rfl
    | insert inner =>
        cases inner with
        | edit _ => rfl
        | rewind rewind =>
            cases rewind with
            | start => rfl
            | scan => rfl
            | gate => exact False.elim (hterminal rfl)
  rw [hnormal]
  change mapTransition (prependEmbed mode)
      ((FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine
        (prependModeWrite mode)).transition source read) = _
  rw [htransition]
  rfl

theorem pop_transition_of_eq_some
    (mode : PopMode)
    (source target : FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine.transition
      source read = some (write, direction, target)) :
    transition (popEmbed mode source) read =
      some (write, direction, popEmbed mode target) := by
  cases mode <;> cases source <;>
    simp [popEmbed, FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine,
      FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.transition, transition,
      mapTransition] at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem restage_transition_of_eq_some
    (source target : NextCopyRestager.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : NextCopyRestager.machine.transition source read =
      some (write, direction, target)) :
    transition (restageEmbed source) read =
      some (write, direction, restageEmbed target) := by
  cases source <;>
    simp [restageEmbed, NextCopyRestager.machine,
      NextCopyRestager.transition, transition, mapTransition]
      at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem haltMarker_transition_of_eq_some
    (source target : FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.machine.transition
      source read = some (write, direction, target)) :
    transition (haltMarkerEmbed source) read =
      some (write, direction, haltMarkerEmbed target) := by
  cases source <;>
    simp [haltMarkerEmbed, FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.machine,
      FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.transition, transition,
      mapTransition] at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem doubleMarker_transition_of_eq_some
    (source target :
      FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition :
      FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.machine.transition
        source read = some (write, direction, target)) :
    transition (doubleMarkerEmbed source) read =
      some (write, direction, doubleMarkerEmbed target) := by
  cases source <;>
    simp [doubleMarkerEmbed,
      FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.machine,
      FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.transition,
      transition, mapTransition] at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem rewind_transition_of_eq_some
    (mode : RewindMode)
    (source target : RewindWord.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : RewindWord.machine.transition source read =
      some (write, direction, target)) :
    transition (rewindEmbed mode source) read =
      some (write, direction, rewindEmbed mode target) := by
  cases mode <;> cases source <;>
    simp [rewindEmbed, RewindWord.machine, RewindWord.transition,
      transition, mapTransition] at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem prefixBuilder_transition_of_eq_some
    (source target : FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition :
      FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.machine.transition
        source read = some (write, direction, target)) :
    transition (prefixBuilderEmbed source) read =
      some (write, direction, prefixBuilderEmbed target) := by
  cases source <;>
    simp [prefixBuilderEmbed,
      FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.machine,
      FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.transition,
      transition, mapTransition] at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem currentBuilder_transition_of_eq_some
    (source target : FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition :
      FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.machine.transition
        source read = some (write, direction, target)) :
    transition (currentBuilderEmbed source) read =
      some (write, direction, currentBuilderEmbed target) := by
  cases source <;>
    simp [currentBuilderEmbed,
      FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.machine,
      FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.transition,
      transition, mapTransition] at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem haltCopier_transition_of_eq_some
    (source target : FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.machine.transition
      source read = some (write, direction, target)) :
    transition (haltCopierEmbed source) read =
      some (write, direction, haltCopierEmbed target) := by
  cases source <;>
    simp [haltCopierEmbed, FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.machine,
      FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.transition,
      transition, mapTransition] at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem finalCompare_transition_of_eq_some
    (source target : RuntimeKeyComparatorState)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : runtimeKeyComparatorMachine.transition source read =
      some (write, direction, target)) :
    transition (finalCompareEmbed source) read =
      some (write, direction, finalCompareEmbed target) := by
  cases source <;>
    simp [finalCompareEmbed, runtimeKeyComparatorMachine,
      transition, mapTransition]
      at htransition ⊢
  all_goals simp [htransition]
  all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem prefix_computes
    (purpose : PrefixPurpose)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig (prefixEmbed purpose) source)
      (TuringMachine.PhaseEmbedding.liftConfig (prefixEmbed purpose) target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.DirectContextUpdate.Prefix.machine
    (prefixEmbed purpose) (prefix_transition_of_eq_some purpose) hrun

theorem stack_computes
    (purpose : StackPurpose)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.StackSkip.Control}
    (hrun : TuringMachine.Computes FiniteRecognizer.Interpreter.StackSkip.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig (stackEmbed purpose) source)
      (TuringMachine.PhaseEmbedding.liftConfig (stackEmbed purpose) target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.StackSkip.machine
    (stackEmbed purpose) (stack_transition_of_eq_some purpose) hrun

theorem boundary_computes
    (mode : BoundaryMode)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig (boundaryEmbed mode) source)
      (TuringMachine.PhaseEmbedding.liftConfig (boundaryEmbed mode) target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.machine
    (boundaryEmbed mode) (boundary_transition_of_eq_some mode) hrun

theorem prepend_computes
    (mode : PrependMode)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.Control}
    (hrun : TuringMachine.Computes
      (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine (prependModeWrite mode))
      source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig (prependEmbed mode) source)
      (TuringMachine.PhaseEmbedding.liftConfig (prependEmbed mode) target) :=
  computes_of_transition_embedding
    (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.machine (prependModeWrite mode))
    (prependEmbed mode) (prepend_transition_of_eq_some mode) hrun

theorem pop_computes
    (mode : PopMode)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.Control}
    (hrun : TuringMachine.Computes FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
      source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig (popEmbed mode) source)
      (TuringMachine.PhaseEmbedding.liftConfig (popEmbed mode) target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.machine
    (popEmbed mode) (pop_transition_of_eq_some mode) hrun

theorem restage_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      NextCopyRestager.Control}
    (hrun : TuringMachine.Computes NextCopyRestager.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig restageEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig restageEmbed target) :=
  computes_of_transition_embedding NextCopyRestager.machine restageEmbed
    restage_transition_of_eq_some hrun

theorem haltMarker_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig haltMarkerEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig haltMarkerEmbed target) :=
  computes_of_transition_embedding
    FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltMarker.machine haltMarkerEmbed
      haltMarker_transition_of_eq_some hrun

theorem doubleMarker_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig doubleMarkerEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig doubleMarkerEmbed target) :=
  computes_of_transition_embedding
    FiniteRecognizer.Interpreter.NoMatchFinalGate.DoubleTransitionMarker.machine
      doubleMarkerEmbed doubleMarker_transition_of_eq_some hrun

theorem rewind_computes
    (mode : RewindMode)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RewindWord.Control}
    (hrun : TuringMachine.Computes RewindWord.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig (rewindEmbed mode) source)
      (TuringMachine.PhaseEmbedding.liftConfig (rewindEmbed mode) target) :=
  computes_of_transition_embedding RewindWord.machine (rewindEmbed mode)
    (rewind_transition_of_eq_some mode) hrun

theorem prefixBuilder_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig prefixBuilderEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig prefixBuilderEmbed target) :=
  computes_of_transition_embedding
    FiniteRecognizer.Interpreter.FinalGateMaterializer.PrefixBuilder.machine prefixBuilderEmbed
      prefixBuilder_transition_of_eq_some hrun

theorem currentBuilder_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig currentBuilderEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig currentBuilderEmbed target) :=
  computes_of_transition_embedding
    FiniteRecognizer.Interpreter.NoMatchFinalGate.CurrentBuilder.machine currentBuilderEmbed
      currentBuilder_transition_of_eq_some hrun

theorem haltCopier_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.machine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig haltCopierEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig haltCopierEmbed target) :=
  computes_of_transition_embedding
    FiniteRecognizer.Interpreter.FinalGateMaterializer.HaltCopier.machine haltCopierEmbed
      haltCopier_transition_of_eq_some hrun

theorem finalCompare_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeyComparatorState}
    (hrun : TuringMachine.Computes runtimeKeyComparatorMachine source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig finalCompareEmbed source)
      (TuringMachine.PhaseEmbedding.liftConfig finalCompareEmbed target) :=
  computes_of_transition_embedding runtimeKeyComparatorMachine
    finalCompareEmbed finalCompare_transition_of_eq_some hrun

end FiniteRecognizer.Interpreter.RuntimePhaseSum

end Computability
end FoC
