import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.HeadCursorMachine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.RightFieldLocator
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.OptionalField
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Serialized head-cursor runs

Exact executions for locating the serialized head field and positioning the
cursor at its first token.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Dispatch
namespace HeadCursor

open SerializedFieldComposer

namespace GenericPrefix

open Dispatch.RightFieldLocator

def afterState {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append (optionalCellsWord L.left)
    (List.append (optionalCellWord L.head) suffix)

def sourceWord {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append (headPrefix L)
    (List.append (optionalCellWord L.head) suffix)

theorem sourceWord_decomp {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    sourceWord L suffix =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend L.fuel
          (MachineDescription.encodeNatAppend L.state.val
            (afterState L suffix)) := by
  unfold sourceWord afterState headPrefix statePrefix
    MachineDescription.encodeNatAppend
  simp [List.append_assoc]

theorem afterState_eq_count_payload {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    afterState L suffix =
      MachineDescription.encodeNatAppend L.left.length
        (HeadLocator.cellsPayloadAppend L.left
          (List.append (optionalCellWord L.head) suffix)) := by
  unfold afterState MachineDescription.encodeNatAppend
  rw [Edits.OptionalField.LayoutSpecialization.optionalCellsWord_eq_count_payload]
  rw [HeadLocator.cellsPayloadAppend_eq_append]
  simp [List.append_assoc]

def fieldSource {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol FieldLocator.Control :=
  FieldLocator.config .header [] (sourceWord L suffix)

theorem field_run_exact {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    (FieldLocator.machine .leftCount).runConfigExact?
        (FieldLocator.leftCountSteps L) (fieldSource L suffix) =
      some
        (FieldLocator.config .gate
          (LeftPrepend.leftCountPrefix L).reverse
          (afterState L suffix)) := by
  unfold FieldLocator.leftCountSteps fieldSource
  rw [sourceWord_decomp]
  rw [FieldLocator.runConfigExact?_add]
  have hheader :
      (FieldLocator.machine .leftCount).runConfigExact? 1
          (FieldLocator.config .header []
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend L.fuel
                (MachineDescription.encodeNatAppend L.state.val
                  (afterState L suffix)))) =
        some
          (FieldLocator.config .fuel [MachineCodeSymbol.header]
            (MachineDescription.encodeNatAppend L.fuel
              (MachineDescription.encodeNatAppend L.state.val
                (afterState L suffix)))) := by
    rw [TuringMachine.runConfigExact?]
    rw [FieldLocator.header_step]
    rfl
  rw [hheader]
  simp only
  rw [FieldLocator.runConfigExact?_add]
  rw [FieldLocator.fuel_run_later .leftCount (by decide)]
  simp only
  rw [FieldLocator.state_run_leftCount]
  simp [LeftPrepend.leftCountPrefix,
    MachineDescription.encodeNatAppend, List.reverse_cons,
    List.reverse_append, List.append_assoc]

def counterSource {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Counter.Control :=
  Counter.config .markCountBoundary
    (LeftPrepend.leftCountPrefix L).reverse (afterState L suffix)

def counterGate {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Counter.Control :=
  Counter.config .gate
    (MachineCodeSymbol.blank ::
      List.append (HeadLocator.transitionMarkers L.left.length)
        (HeadLocator.countBaseLeftRev L))
    (List.append (HeadLocator.markedCellsWord L.left)
      (List.append (optionalCellWord L.head) suffix))

theorem counter_run_exact {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    Counter.machine.runConfigExact? (Counter.runSteps L)
        (counterSource L suffix) =
      some (counterGate L suffix) := by
  unfold Counter.runSteps counterSource counterGate
  rw [Counter.leftCountPrefix_reverse_eq_countBase]
  rw [afterState_eq_count_payload]
  rw [show HeadLocator.countBaseLeftRev L =
      MachineCodeSymbol.done :: HeadLocator.topFieldsRev L by rfl]
  rw [Counter.runConfigExact?_add]
  rw [Counter.markCountBoundary_roundTrip_exact]
  simp only
  rw [Counter.runConfigExact?_add]
  rw [Counter.processAllCells_run_exact]
  simp only
  change
    Counter.machine.runConfigExact? 1
        (Counter.config .countCheck
          (List.append (HeadLocator.transitionMarkers L.left.length)
            (HeadLocator.countBaseLeftRev L))
          (MachineCodeSymbol.blank ::
            List.append (HeadLocator.markedCellsWord L.left)
              (List.append (optionalCellWord L.head) suffix))) = _
  rw [TuringMachine.runConfigExact?]
  rw [Counter.countCheck_blank_step]
  rfl

def decoderSource {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol HeadDecoder.Control :=
  HeadDecoder.config (.decode ⟨0, by decide⟩)
    (HeadDecoder.markedCountBaseLeftRev L)
    (List.append (HeadLocator.markedCellsWord L.left)
      (List.append (optionalCellWord L.head) suffix))

def decoderGate {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol HeadDecoder.Control :=
  HeadDecoder.config (.gate L.head)
    (List.append (optionalCellWord L.head).reverse
      (List.append (HeadLocator.markedCellsWord L.left).reverse
        (HeadDecoder.markedCountBaseLeftRev L))) suffix

theorem decoder_run_exact {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    HeadDecoder.machine.runConfigExact? (HeadDecoder.runSteps L.left L.head)
        (decoderSource L suffix) =
      some (decoderGate L suffix) := by
  simpa [decoderSource, decoderGate] using
    HeadDecoder.run_exact L.left L.head
      (HeadDecoder.markedCountBaseLeftRev L) suffix

def sourceConfig {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol OuterLocator.Control :=
  OuterLocator.locateConfig (fieldSource L suffix)

def gateConfig {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol OuterLocator.Control :=
  OuterLocator.decodeConfig (decoderGate L suffix)

def runSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  (((FieldLocator.leftCountSteps L + 2) + Counter.runSteps L) + 2) +
    HeadDecoder.runSteps L.left L.head

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    OuterLocator.machine.runConfigExact? (runSteps L) (sourceConfig L suffix) =
      some (gateConfig L suffix) := by
  have hlocate := OuterLocator.locate_run_of_some (field_run_exact L suffix)
  have hhandoffOne := OuterLocator.locate_counter_handoff
    MachineCodeSymbol.done (HeadLocator.topFieldsRev L)
      (afterState L suffix)
  have hhandoffOne' :
      OuterLocator.machine.runConfigExact? 2
          (OuterLocator.locateConfig
            (FieldLocator.config .gate
              (LeftPrepend.leftCountPrefix L).reverse
              (afterState L suffix))) =
        some
          (OuterLocator.counterConfig (counterSource L suffix)) := by
    unfold counterSource
    rw [Counter.leftCountPrefix_reverse_eq_countBase]
    simpa [HeadLocator.countBaseLeftRev] using hhandoffOne
  have hcounter := OuterLocator.counter_run_of_some (counter_run_exact L suffix)
  have hhandoffTwo := OuterLocator.counter_decode_handoff
    MachineCodeSymbol.blank
      (List.append (HeadLocator.transitionMarkers L.left.length)
        (HeadLocator.countBaseLeftRev L))
      (List.append (HeadLocator.markedCellsWord L.left)
        (List.append (optionalCellWord L.head) suffix))
  have hdecode := OuterLocator.decode_run_of_some (decoder_run_exact L suffix)
  have hfirst := OuterLocator.runConfigExact_trans hlocate hhandoffOne'
  have hsecond := OuterLocator.runConfigExact_trans hfirst hcounter
  have hthird := OuterLocator.runConfigExact_trans hsecond hhandoffTwo
  have hfourth := OuterLocator.runConfigExact_trans hthird hdecode
  simpa [runSteps, sourceConfig, gateConfig, counterSource, counterGate,
    decoderSource, HeadDecoder.markedCountBaseLeftRev,
    HeadLocator.countBaseLeftRev, Nat.add_assoc] using hfourth

end GenericPrefix

namespace Full

open Dispatch.RightFieldLocator

inductive Control where
  | locate (inner : OuterLocator.Control)
  | post (inner : Post.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  List.append
    (OuterLocator.Control.elems.map Control.locate)
    (Post.Control.elems.map Control.post)

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        have h := OuterLocator.Control.finite.complete inner
        change inner ∈ OuterLocator.Control.elems at h
        simp [elems, h]
    | post inner =>
        have h := Post.Control.finite.complete inner
        change inner ∈ Post.Control.elems at h
        simp [elems, h]

end Control

def mapLocateAction :
    Option MachineCodeSymbol × Direction × OuterLocator.Control ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) => (write, direction, .locate target)

def mapPostAction :
    Option MachineCodeSymbol × Direction × Post.Control ->
      Option MachineCodeSymbol × Direction × Control
  | (write, direction, target) => (write, direction, .post target)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate inner, read =>
      match OuterLocator.transition inner read with
      | some action => some (mapLocateAction action)
      | none =>
          match inner with
          | .decode (.gate head) =>
              Option.map mapPostAction (Post.transition (.entry head) read)
          | _ => none
  | .post inner, read =>
      Option.map mapPostAction (Post.transition inner read)

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locate OuterLocator.machine.start
  halt := .post Post.machine.halt
  transition := transition
  statesFinite := Control.finite

def locateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      OuterLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.locate c

def postConfig
    (c : TuringMachine.Configuration MachineCodeSymbol Post.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.post c

def postEmbed : Post.Control -> Control
  | .entry head => .locate (.decode (.gate head))
  | inner => .post inner

def postEmbedConfig
    (c : TuringMachine.Configuration MachineCodeSymbol Post.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig postEmbed c

theorem locate_step_of_some
    (c d : TuringMachine.Configuration MachineCodeSymbol
      OuterLocator.Control)
    (hstep : OuterLocator.machine.stepConfig c = some d) :
    machine.stepConfig (locateConfig c) = some (locateConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [OuterLocator.machine] at hstep
      cases htransition : OuterLocator.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          simp [machine, transition, locateConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            htransition, mapLocateAction]

theorem locate_run_of_some
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      OuterLocator.Control}
    (hrun : OuterLocator.machine.runConfigExact? steps source = some target) :
    machine.runConfigExact? steps (locateConfig source) =
      some (locateConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.locate
  · exact locate_step_of_some
  · exact hrun

theorem post_step_of_some
    (c d : TuringMachine.Configuration MachineCodeSymbol Post.Control)
    (hstep : Post.machine.stepConfig c = some d) :
    machine.stepConfig (postEmbedConfig c) =
      some (postEmbedConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Post.machine] at hstep
      cases htransition : Post.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have htarget : postEmbed target = Control.post target := by
            cases target with
            | entry targetHead =>
                exfalso
                cases inner <;>
                  cases hread : Tape.read tape with
                  | none =>
                      simp [Post.transition, hread] at htransition
                  | some symbol =>
                      cases symbol <;>
                        simp [Post.transition, hread] at htransition
            | markHeadDelimiter _ => rfl
            | restoreCells _ => rfl
            | restoreCount _ => rfl
            | seekTopHeader _ => rfl
            | scanMarker _ => rfl
            | returnToHead _ => rfl
            | positioned _ => rfl
          simp only [postEmbedConfig,
            TuringMachine.PhaseEmbedding.liftConfig]
          rw [htarget]
          cases inner with
          | entry head =>
              simp [machine, transition, postEmbed,
                OuterLocator.transition, HeadDecoder.transition,
                htransition, mapPostAction]
          | markHeadDelimiter head =>
              simp [machine, transition, postEmbed, htransition,
                mapPostAction]
          | restoreCells head =>
              simp [machine, transition, postEmbed, htransition,
                mapPostAction]
          | restoreCount head =>
              simp [machine, transition, postEmbed, htransition,
                mapPostAction]
          | seekTopHeader head =>
              simp [machine, transition, postEmbed, htransition,
                mapPostAction]
          | scanMarker head =>
              simp [machine, transition, postEmbed, htransition,
                mapPostAction]
          | returnToHead head =>
              simp [machine, transition, postEmbed, htransition,
                mapPostAction]
          | positioned head =>
              simp [machine, transition, postEmbed, htransition,
                mapPostAction]

theorem post_run_of_some
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol Post.Control}
    (hrun : Post.machine.runConfigExact? steps source = some target) :
    machine.runConfigExact? steps (postEmbedConfig source) =
      some (postEmbedConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      postEmbed
  · exact post_step_of_some
  · exact hrun

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

def sourceConfig {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  locateConfig (GenericPrefix.sourceConfig L (first :: rest))

def positionedConfig {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  postConfig (Post.positionedConfig L first rest)

def runSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  GenericPrefix.runSteps L + Post.runSteps L

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps L) (sourceConfig L first rest) =
      some (positionedConfig L first rest) := by
  have hprefix := locate_run_of_some
    (GenericPrefix.run_exact L (first :: rest))
  have hpost := post_run_of_some (Post.run_exact L first rest)
  have hseam :
      locateConfig (GenericPrefix.gateConfig L (first :: rest)) =
        postEmbedConfig (Post.sourceConfig L first rest) := by
    rfl
  rw [hseam] at hprefix
  have hpost' :
      machine.runConfigExact? (Post.runSteps L)
          (postEmbedConfig (Post.sourceConfig L first rest)) =
        some (positionedConfig L first rest) := by
    simpa [positionedConfig, postConfig, postEmbedConfig, postEmbed,
      Post.positionedConfig, Post.cursorConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hpost
  have htotal := runConfigExact_trans hprefix hpost'
  simpa [runSteps, sourceConfig] using htotal

theorem sourceConfig_eq_initial {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    sourceConfig L first rest =
      TuringMachine.initial machine
        (GenericPrefix.sourceWord L (first :: rest)) := by
  rfl

theorem run_from_equiv {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol)
    (hT : Tape.Equiv
      (Tape.input (GenericPrefix.sourceWord L (first :: rest))) T) :
    exists endpoint,
      machine.runConfigExact? (runSteps L)
          { state := machine.start, tape := T } = some endpoint ∧
      endpoint.state = Control.post (.positioned L.head) ∧
      Tape.Equiv (positionedConfig L first rest).tape endpoint.tape := by
  have hclean := run_exact L first rest
  rw [sourceConfig_eq_initial] at hclean
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hT with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, ?_, htape⟩
  · simpa [TuringMachine.initial] using hrun
  · simpa [positionedConfig, postConfig,
      Post.positionedConfig, Post.cursorConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hstate

end Full

end HeadCursor
end Dispatch
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
