import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Materializer
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Exact-fuel two-blank compactor

Compaction of the padded nonempty stage-input materializer endpoint into the
protected-layout representation consumed by the strict probe.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace StageInput

namespace TwoBlankCompactor

def gapCell : Option MachineCodeSymbol := some MachineCodeSymbol.header

inductive Control where
  | seek
  | handoff
  | compact (inner :
      SerializedFieldComposer.DeleteRestagedMachine.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.seek, .handoff] ++
    SerializedFieldComposer.DeleteRestagedMachine.Control.finite.elems.map
      Control.compact

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | seek => simp [elems]
    | handoff => simp [elems]
    | compact inner =>
        simp [elems]
        exact
          SerializedFieldComposer.DeleteRestagedMachine.Control.finite.complete
            inner

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .seek, some symbol =>
      some (some symbol, Direction.right, .seek)
  | .seek, none =>
      some (none, Direction.left, .handoff)
  | .handoff, cell =>
      some
        (cell, Direction.right,
          .compact
            (.edit (.erase
              (SerializedFieldComposer.DeleteBlock.optionalGap
                gapCell))))
  | .compact inner, cell =>
      match SerializedFieldComposer.DeleteRestagedMachine.transition
          gapCell inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .compact target)

def machine : TuringMachine MachineCodeSymbol Control where
  start := .seek
  halt := .compact (.rewind .gate)
  transition := transition
  statesFinite := Control.finite

def config (control : Control) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := tape

def compactConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      SerializedFieldComposer.DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.compact c

def seekTape
    (remaining crossed body : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := crossed.map some
        head := none
        right := none :: body.map some }
  | current :: rest =>
      { left := crossed.map some
        head := some current
        right := List.append (rest.map some)
          (none :: none :: body.map some) }

def seekConfig
    (remaining crossed body : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .seek (seekTape remaining crossed body)

theorem seek_step
    (current : MachineCodeSymbol)
    (remaining crossed body : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekConfig (current :: remaining) crossed body) =
      some (seekConfig remaining (current :: crossed) body) := by
  cases remaining <;> cases body <;> rfl

theorem seek_run_exact
    (remaining crossed body : Word MachineCodeSymbol) :
    machine.runConfigExact? remaining.length
        (seekConfig remaining crossed body) =
      some
        (seekConfig []
          (List.append remaining.reverse crossed) body) := by
  induction remaining generalizing crossed with
  | nil => rfl
  | cons current remaining ih =>
      change machine.runConfigExact? (remaining.length + 1)
        (seekConfig (current :: remaining) crossed body) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

def gapSource
    (leftRev body : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      SerializedFieldComposer.DeleteRestagedMachine.Control where
  state := .edit
    (.erase (SerializedFieldComposer.DeleteBlock.optionalGap gapCell))
  tape :=
    { left := leftRev.map some
      head := none
      right := none :: body.map some }

theorem handoff_run_exact
    (first : MachineCodeSymbol)
    (leftRest body : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (seekConfig [] (first :: leftRest) body) =
      some (compactConfig (gapSource (first :: leftRest) body)) := by
  cases leftRest <;> cases body <;> rfl

theorem compact_step
    (c : TuringMachine.Configuration MachineCodeSymbol
      SerializedFieldComposer.DeleteRestagedMachine.Control) :
    machine.stepConfig (compactConfig c) =
      Option.map compactConfig
        ((SerializedFieldComposer.DeleteRestagedMachine.machine
          gapCell).stepConfig c) := by
  cases c with
  | mk state tape =>
      unfold TuringMachine.stepConfig
      simp only [compactConfig,
        TuringMachine.PhaseEmbedding.liftConfig,
        machine, transition,
        SerializedFieldComposer.DeleteRestagedMachine.machine]
      cases htransition :
          SerializedFieldComposer.DeleteRestagedMachine.transition
            gapCell state
            (Tape.read tape) with
      | none => rfl
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rfl

def rawGapSource
    (leftRev body : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      SerializedFieldComposer.DeleteBlock.Control where
  state := .erase
    (SerializedFieldComposer.DeleteBlock.optionalGap gapCell)
  tape :=
    { left := leftRev.map some
      head := none
      right := none :: body.map some }

theorem gapSource_eq_editConfig
    (leftRev body : Word MachineCodeSymbol) :
    gapSource leftRev body =
      SerializedFieldComposer.DeleteRestagedMachine.editConfig
        (rawGapSource leftRev body) := by
  rfl

theorem erase_two_run_exact
    (leftRev body : Word MachineCodeSymbol) :
    (SerializedFieldComposer.DeleteBlock.machine
        (SerializedFieldComposer.DeleteBlock.optionalGap
          gapCell)).runConfigExact? 2
        (rawGapSource leftRev body) =
      some
        (SerializedFieldComposer.DeleteBlock.pullConfig
          (SerializedFieldComposer.DeleteBlock.optionalGap gapCell)
          leftRev body) := by
  cases body <;> rfl

def rawGapSteps (body : Word MachineCodeSymbol) : Nat :=
  2 +
    ((2 *
      (SerializedFieldComposer.DeleteBlock.optionalGap gapCell).val + 1) *
      body.length + 1)

theorem rawGap_run_exact
    (leftRev body : Word MachineCodeSymbol) :
    (SerializedFieldComposer.DeleteBlock.machine
        (SerializedFieldComposer.DeleteBlock.optionalGap
          gapCell)).runConfigExact?
        (rawGapSteps body)
        (rawGapSource leftRev body) =
      some
        (SerializedFieldComposer.DeleteBlock.exitConfig gapCell
          (List.append body.reverse leftRev)) := by
  unfold rawGapSteps
  rw [SerializedFieldComposer.DeleteBlock.runConfigExact?_add]
  rw [erase_two_run_exact]
  simp only
  exact SerializedFieldComposer.DeleteBlock.pull_run_exact
    gapCell leftRev body

theorem editGap_run_exact
    (leftRev body : Word MachineCodeSymbol) :
    (SerializedFieldComposer.DeleteRestagedMachine.machine
        gapCell).runConfigExact?
        (rawGapSteps body)
        (gapSource leftRev body) =
      some
        (SerializedFieldComposer.DeleteRestagedMachine.editConfig
          (SerializedFieldComposer.DeleteBlock.exitConfig gapCell
            (List.append body.reverse leftRev))) := by
  rw [gapSource_eq_editConfig]
  exact
    SerializedFieldComposer.DeleteRestagedMachine.edit_run_of_eq_some
      gapCell _ _ _ (rawGap_run_exact leftRev body)

def innerRunSteps
    (leftRev body : Word MachineCodeSymbol) : Nat :=
  rawGapSteps body +
    SerializedFieldComposer.DeleteEndpointRewind.runSteps
      gapCell (List.append body.reverse leftRev)

theorem inner_run_exact
    (leftRev body : Word MachineCodeSymbol) :
    (SerializedFieldComposer.DeleteRestagedMachine.machine
        gapCell).runConfigExact?
        (innerRunSteps leftRev body)
        (gapSource leftRev body) =
      some
        (SerializedFieldComposer.DeleteRestagedMachine.rewindConfig
          (SerializedFieldComposer.DeleteEndpointRewind.gateConfig
            (List.append leftRev.reverse body) gapCell)) := by
  unfold innerRunSteps
  rw [SerializedFieldComposer.DeleteRestagedMachine.runConfigExact?_add]
  rw [editGap_run_exact]
  simp only
  rw [SerializedFieldComposer.DeleteRestagedMachine.rewind_run_exact]
  simp [List.reverse_append]

theorem compact_run_exact
    (leftRev body : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (innerRunSteps leftRev body)
        (compactConfig (gapSource leftRev body)) =
      some
        (compactConfig
          (SerializedFieldComposer.DeleteRestagedMachine.rewindConfig
            (SerializedFieldComposer.DeleteEndpointRewind.gateConfig
              (List.append leftRev.reverse body) gapCell))) := by
  apply
    TuringMachine.PhaseEmbedding.runConfigExact?_lift_of_eq_some
      Control.compact compact_step
  exact inner_run_exact leftRev body

theorem handoff_run_exact_of_ne_nil
    (leftRev body : Word MachineCodeSymbol)
    (hnonempty : leftRev ≠ []) :
    machine.runConfigExact? 2 (seekConfig [] leftRev body) =
      some (compactConfig (gapSource leftRev body)) := by
  cases leftRev with
  | nil => contradiction
  | cons first rest => exact handoff_run_exact first rest body

theorem runConfigExact?_add
    (first second : Nat)
    (c : TuringMachine.Configuration MachineCodeSymbol Control) :
    machine.runConfigExact? (first + second) c =
      match machine.runConfigExact? first c with
      | none => none
      | some middle => machine.runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add]
      rw [TuringMachine.runConfigExact?]
      rw [TuringMachine.runConfigExact?]
      cases hstep : machine.stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next

def runSteps
    (fuelWord body : Word MachineCodeSymbol) : Nat :=
  fuelWord.length + 2 +
    innerRunSteps
      (List.append fuelWord.reverse [MachineCodeSymbol.header]) body

theorem run_exact
    (fuelWord body : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps fuelWord body)
        (seekConfig fuelWord [MachineCodeSymbol.header] body) =
      some
        (compactConfig
          (SerializedFieldComposer.DeleteRestagedMachine.rewindConfig
            (SerializedFieldComposer.DeleteEndpointRewind.gateConfig
              (MachineCodeSymbol.header ::
                List.append fuelWord body)
              gapCell))) := by
  unfold runSteps
  rw [show fuelWord.length + 2 +
        innerRunSteps
          (List.append fuelWord.reverse [MachineCodeSymbol.header]) body =
      fuelWord.length +
        (2 + innerRunSteps
          (List.append fuelWord.reverse [MachineCodeSymbol.header]) body) by
    lia]
  rw [runConfigExact?_add]
  rw [seek_run_exact]
  simp only
  rw [runConfigExact?_add]
  rw [handoff_run_exact_of_ne_nil]
  · simp only
    rw [compact_run_exact]
    simp [List.reverse_append]
  · intro hnil
    have hparts := List.append_eq_nil_iff.mp hnil
    simp at hparts

theorem endpoint_tape_equiv_input
    (fuelWord body : Word MachineCodeSymbol) :
    Tape.Equiv
      (compactConfig
        (SerializedFieldComposer.DeleteRestagedMachine.rewindConfig
          (SerializedFieldComposer.DeleteEndpointRewind.gateConfig
            (MachineCodeSymbol.header :: List.append fuelWord body)
            gapCell))).tape
      (Tape.input
        (MachineCodeSymbol.header :: List.append fuelWord body)) := by
  exact
    SerializedFieldComposer.DeleteEndpointRewind.gateTape_equiv_input
      (MachineCodeSymbol.header :: List.append fuelWord body) gapCell

def materializerBody {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (InitialMaterializer.NonemptyFixedPrefix.fixedPrefix M headSymbol)
    (InitialMaterializer.NonemptyRightRegion.region rest)

def idealMaterializerSource {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  seekConfig (MachineDescription.encodeNat fuel)
    [MachineCodeSymbol.header]
    (materializerBody M headSymbol rest)

theorem seekTape_equiv_haltTape
    (fuelWord body : Word MachineCodeSymbol)
    (hfuel : fuelWord ≠ []) :
    Tape.Equiv
      (seekTape fuelWord [MachineCodeSymbol.header] body)
      (InitialMaterializer.HeaderLeftInstaller.haltTape
        fuelWord body) := by
  cases fuelWord with
  | nil => contradiction
  | cons first rest =>
      refine ⟨rfl, rfl, ?_⟩
      simpa [seekTape,
        InitialMaterializer.HeaderLeftInstaller.haltTape,
        List.append_assoc] using
        (FoC.Computability.dropTrailingNone_append_none
          (List.append (rest.map some)
            (none :: none :: body.map some))).symm

theorem idealSource_equiv_materializerTape {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    Tape.Equiv
      (idealMaterializerSource M fuel headSymbol rest).tape
      (InitialMaterializer.FullMaterializerMachine.nonemptyHaltTape
        M fuel headSymbol rest) := by
  unfold idealMaterializerSource materializerBody seekConfig config
    InitialMaterializer.FullMaterializerMachine.nonemptyHaltTape
  apply seekTape_equiv_haltTape
  rw [InitialMaterializer.OneCellMachine.encodeNat_eq_ticks_done]
  intro hnil
  have hparts := List.append_eq_nil_iff.mp hnil
  simp at hparts

theorem outputWord_eq_protectedWord {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    MachineCodeSymbol.header ::
        List.append (MachineDescription.encodeNat fuel)
          (materializerBody M headSymbol rest) =
      Frame.protectedWord
        (Layout.initial M (headSymbol :: rest) fuel) [] := by
  exact
    InitialMaterializer.NonemptyFixedPrefix.body_eq_initial_protectedWord
      M fuel headSymbol rest

theorem materializer_contextLength_eq_canonical_add_three
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    Tape.contextLength
        (InitialMaterializer.FullMaterializerMachine.nonemptyHaltTape
          M fuel headSymbol rest) =
      Tape.contextLength
          (Tape.input
            (Frame.protectedWord
              (Layout.initial M (headSymbol :: rest) fuel) [])) + 3 := by
  rw [← outputWord_eq_protectedWord M fuel headSymbol rest]
  unfold
    InitialMaterializer.FullMaterializerMachine.nonemptyHaltTape
    materializerBody
  rw [InitialMaterializer.OneCellMachine.encodeNat_eq_ticks_done]
  cases fuel <;>
    simp [InitialMaterializer.HeaderLeftInstaller.haltTape,
      Tape.contextLength, Tape.input, List.length_append,
      List.replicate_succ] <;>
    lia

theorem no_exact_run_to_literal_canonical
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (N : TuringMachine MachineCodeSymbol state)
    (sourceState targetState : state)
    (steps : Nat) :
    N.runConfigExact? steps
        { state := sourceState
          tape :=
            InitialMaterializer.FullMaterializerMachine.nonemptyHaltTape
              M fuel headSymbol rest } ≠
      some
        { state := targetState
          tape :=
            Tape.input
              (Frame.protectedWord
                (Layout.initial M (headSymbol :: rest) fuel) []) } := by
  intro hrun
  have hcomp :=
    TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun
  have hmono := TuringMachine.computesIn_contextLength_mono hcomp
  rw [materializer_contextLength_eq_canonical_add_three] at hmono
  lia

def materializerRunSteps {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) : Nat :=
  runSteps (MachineDescription.encodeNat fuel)
    (materializerBody M headSymbol rest)

theorem run_from_materializerTape {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    exists endpoint,
      machine.runConfigExact?
          (materializerRunSteps M fuel headSymbol rest)
          (config .seek
            (InitialMaterializer.FullMaterializerMachine.nonemptyHaltTape
              M fuel headSymbol rest)) =
        some endpoint ∧
      endpoint.state = machine.halt ∧
      Tape.Equiv endpoint.tape
        (Tape.input
          (Frame.protectedWord
            (Layout.initial M (headSymbol :: rest) fuel) [])) := by
  let fuelWord := MachineDescription.encodeNat fuel
  let body := materializerBody M headSymbol rest
  let cleanTarget :=
    compactConfig
      (SerializedFieldComposer.DeleteRestagedMachine.rewindConfig
        (SerializedFieldComposer.DeleteEndpointRewind.gateConfig
          (MachineCodeSymbol.header :: List.append fuelWord body)
          gapCell))
  have hclean :
      machine.runConfigExact? (runSteps fuelWord body)
          (seekConfig fuelWord [MachineCodeSymbol.header] body) =
        some cleanTarget := by
    exact run_exact fuelWord body
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean (idealSource_equiv_materializerTape M fuel headSymbol rest) with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, hstate, ?_⟩
  · simpa [materializerRunSteps, fuelWord, body,
      idealMaterializerSource, seekConfig, config] using hrun
  · exact Tape.Equiv.trans (Tape.Equiv.symm htape) (by
      rw [← outputWord_eq_protectedWord M fuel headSymbol rest]
      exact endpoint_tape_equiv_input fuelWord body)

theorem run_from_equiv_materializerTape {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (paddedTape : Tape MachineCodeSymbol)
    (hpadded : Tape.Equiv
      (InitialMaterializer.FullMaterializerMachine.nonemptyHaltTape
        M fuel headSymbol rest)
      paddedTape) :
    exists endpoint,
      machine.runConfigExact?
          (materializerRunSteps M fuel headSymbol rest)
          (config .seek paddedTape) =
        some endpoint ∧
      endpoint.state = machine.halt ∧
      Tape.Equiv endpoint.tape
        (Tape.input
          (Frame.protectedWord
            (Layout.initial M (headSymbol :: rest) fuel) [])) := by
  rcases run_from_materializerTape M fuel headSymbol rest with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hpadded with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨endpoint, hrun, hstate.trans hcleanState,
    Tape.Equiv.trans (Tape.Equiv.symm htape) hcleanTape⟩

end TwoBlankCompactor

end StageInput
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
