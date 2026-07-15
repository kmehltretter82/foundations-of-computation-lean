import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Contextual.Finish

set_option doc.verso true

/-!
# Contextual product materializer assembly

Run the unchanged stage-input materializer on a copied right call while
preserving the original outer call beyond its left boundary.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductContextual

namespace Full

abbrev Control {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :=
  InitialMaterializer.FullMaterializerMachine.Control M

def parserConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol
      (InitialMaterializer.StageFuelParser.Control stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  InitialMaterializer.FullMaterializerMachine.parseConfig M c

def tailConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  InitialMaterializer.FullMaterializerMachine.tailConfig M c

def emptyWriteConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol
      (Fin ((InitialMaterializer.EmptyInputSuffix.suffix M).length + 1))) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  InitialMaterializer.FullMaterializerMachine.emptyWriteConfig M c

def emptyPrependConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.PrependHeader.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  InitialMaterializer.FullMaterializerMachine.emptyPrependConfig M c

def baseRewindConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.SeparatorRewind.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  InitialMaterializer.FullMaterializerMachine.baseRewindConfig
    M headSymbol c

def rawConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.RawTailLoopMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  InitialMaterializer.FullMaterializerMachine.rawConfig M headSymbol c

def blockConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol
      (InitialMaterializer.VariableBlockInsert.Control
        (InitialMaterializer.NonemptyFixedPrefix.capacity M))) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  InitialMaterializer.FullMaterializerMachine.blockConfig M headSymbol c

def headerConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.HeaderLeftInstaller.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  InitialMaterializer.FullMaterializerMachine.headerConfig M c

def sourceConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol)
    (fuel : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  parserConfig M
    (Parser.config (.fuel M.start) outerRev []
      (MachineDescription.encodeNatAppend fuel input))

theorem parser_run {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol)
    (fuel : Nat) (input : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
        (fuel + 1) (sourceConfig M outerRev fuel input) =
      some (parserConfig M
        (Parser.config (.gate M.start) outerRev
          (MachineDescription.encodeNat fuel).reverse input)) := by
  exact InitialMaterializer.FullMaterializerMachine.parse_run_of_eq_some
    M (fuel + 1) _ _ (Parser.run_exact M.start fuel outerRev input)

theorem parse_empty_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol) (fuel : Nat) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 2
        (parserConfig M
          (Parser.config (.gate M.start) outerRev
            (MachineDescription.encodeNat fuel).reverse [])) =
      some (emptyWriteConfig M
        (EmptyWriter.config
          (InitialMaterializer.EmptyInputSuffix.suffix M) 0 (by simp)
          outerRev (MachineDescription.encodeNat fuel).reverse)) := by
  have hnonempty : (MachineDescription.encodeNat fuel).reverse ≠ [] := by
    rw [InitialMaterializer.OneCellMachine.encodeNat_eq_ticks_done]
    simp
  cases hleft : (MachineDescription.encodeNat fuel).reverse with
  | nil => contradiction
  | cons leftHead leftRest =>
      cases outerRev <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          InitialMaterializer.FullMaterializerMachine.machine,
          InitialMaterializer.FullMaterializerMachine.transition,
          parserConfig, emptyWriteConfig,
          InitialMaterializer.FullMaterializerMachine.parseConfig,
          InitialMaterializer.FullMaterializerMachine.emptyWriteConfig,
          Parser.config, Parser.tape, EmptyWriter.config,
          InitialMaterializer.FixedWordWriter.stateAt,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem empty_writer_run {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev leftRev : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
        (InitialMaterializer.EmptyInputSuffix.suffix M).length
        (emptyWriteConfig M
          (EmptyWriter.config
            (InitialMaterializer.EmptyInputSuffix.suffix M) 0 (by simp)
            outerRev leftRev)) =
      some (emptyWriteConfig M
        (EmptyWriter.config
          (InitialMaterializer.EmptyInputSuffix.suffix M)
          (InitialMaterializer.EmptyInputSuffix.suffix M).length
          (by simp) outerRev
          (List.append
            (InitialMaterializer.EmptyInputSuffix.suffix M).reverse
            leftRev))) := by
  exact
    InitialMaterializer.FullMaterializerMachine.empty_write_run_of_eq_some
      M (InitialMaterializer.EmptyInputSuffix.suffix M).length _ _
        (EmptyWriter.run_exact
          (InitialMaterializer.EmptyInputSuffix.suffix M)
          outerRev leftRev)

theorem empty_header_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev wordRev : Word MachineCodeSymbol)
    (hnonempty : wordRev ≠ []) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 2
        (emptyWriteConfig M
          (EmptyWriter.config
            (InitialMaterializer.EmptyInputSuffix.suffix M)
            (InitialMaterializer.EmptyInputSuffix.suffix M).length
            (by simp) outerRev wordRev)) =
      some (emptyPrependConfig M
        (Prepend.startConfig outerRev wordRev)) := by
  cases wordRev with
  | nil => contradiction
  | cons first rest =>
      cases outerRev <;> cases rest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          InitialMaterializer.FullMaterializerMachine.machine,
          InitialMaterializer.FullMaterializerMachine.transition,
          emptyWriteConfig, emptyPrependConfig,
          InitialMaterializer.FullMaterializerMachine.emptyWriteConfig,
          InitialMaterializer.FullMaterializerMachine.emptyPrependConfig,
          EmptyWriter.config,
          InitialMaterializer.FixedWordWriter.stateAt,
          Prepend.startConfig, Prepend.farRightTape,
          Parser.tape,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem empty_prepend_run {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev wordRev : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
        (wordRev.length + 2)
        (emptyPrependConfig M (Prepend.startConfig outerRev wordRev)) =
      some (emptyPrependConfig M
        (Prepend.gateConfig outerRev wordRev.reverse)) := by
  exact
    InitialMaterializer.FullMaterializerMachine.empty_prepend_run_of_eq_some
      M (wordRev.length + 2) _ _ (Prepend.run_exact outerRev wordRev)

theorem parse_nonempty_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol) (fuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 2
        (parserConfig M
          (Parser.config (.gate M.start) outerRev
            (MachineDescription.encodeNat fuel).reverse
            (headSymbol :: rest))) =
      some (tailConfig M
        (Tail.sourceConfig outerRev
          (MachineDescription.encodeNat fuel).reverse headSymbol rest)) := by
  have hnonempty : (MachineDescription.encodeNat fuel).reverse ≠ [] := by
    rw [InitialMaterializer.OneCellMachine.encodeNat_eq_ticks_done]
    simp
  cases hleft : (MachineDescription.encodeNat fuel).reverse with
  | nil => contradiction
  | cons leftHead leftRest =>
      cases rest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          InitialMaterializer.FullMaterializerMachine.machine,
          InitialMaterializer.FullMaterializerMachine.transition,
          parserConfig, tailConfig,
          InitialMaterializer.FullMaterializerMachine.parseConfig,
          InitialMaterializer.FullMaterializerMachine.tailConfig,
          Parser.config, Parser.tape, Tail.sourceConfig, Tail.sourceTape,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tail_run {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev fuelRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
        (rest.length + 4)
        (tailConfig M (Tail.sourceConfig outerRev fuelRev headSymbol rest)) =
      some (tailConfig M
        (Tail.haltConfig headSymbol outerRev fuelRev rest.reverse)) := by
  exact InitialMaterializer.FullMaterializerMachine.tail_run_of_eq_some
    M (rest.length + 4) _ _
      (Tail.run_exact outerRev fuelRev headSymbol rest)

theorem tail_base_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 2
        (tailConfig M
          (Tail.haltConfig headSymbol outerRev fuelRev restRev)) =
      some (baseRewindConfig M headSymbol
        (InitialMaterializer.SeparatorRewind.startConfigCells
          (rewindLeftContext outerRev fuelRev restRev)
          [Frame.callerTag, MachineCodeSymbol.done])) := by
  cases outerRev <;> cases fuelRev <;> cases restRev <;> rfl

theorem base_rewind_run {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 4
        (baseRewindConfig M headSymbol
          (InitialMaterializer.SeparatorRewind.startConfigCells
            (rewindLeftContext outerRev fuelRev restRev)
            [Frame.callerTag, MachineCodeSymbol.done])) =
      some (baseRewindConfig M headSymbol
        (InitialMaterializer.SeparatorRewind.gateConfigCells
          (rewindLeftContext outerRev fuelRev restRev)
          [MachineCodeSymbol.done, Frame.callerTag])) := by
  exact
    InitialMaterializer.FullMaterializerMachine.base_rewind_run_of_eq_some
      M headSymbol 4 _ _
        (InitialMaterializer.SeparatorRewind.run_exact_cells
          (rewindLeftContext outerRev fuelRev restRev)
          ([Frame.callerTag, MachineCodeSymbol.done] :
            Word MachineCodeSymbol))

theorem base_raw_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 2
        (baseRewindConfig M headSymbol
          (InitialMaterializer.SeparatorRewind.gateConfigCells
            (rewindLeftContext outerRev fuelRev restRev)
            [MachineCodeSymbol.done, Frame.callerTag])) =
      some (rawConfig M headSymbol
        (Raw.gateConfig outerRev restRev [] fuelRev)) := by
  rfl

theorem raw_run_to_done_equiv {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (outerRev remainingRev processed fuelRev : Word MachineCodeSymbol) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol (Control M)),
      (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
          steps
          (rawConfig M headSymbol
            (Raw.gateConfig outerRev remainingRev processed fuelRev)) =
        some endpoint ∧
      (rawConfig M headSymbol
        (Raw.doneConfig outerRev
          (List.append remainingRev.reverse processed) fuelRev)).state =
        endpoint.state ∧
      Tape.Equiv
        (rawConfig M headSymbol
          (Raw.doneConfig outerRev
            (List.append remainingRev.reverse processed) fuelRev)).tape
        endpoint.tape := by
  rcases Raw.run_to_done_equiv outerRev remainingRev processed fuelRev with
    ⟨steps, innerEndpoint, hrun, hstate, htape⟩
  refine ⟨steps, rawConfig M headSymbol innerEndpoint, ?_, ?_, ?_⟩
  · exact InitialMaterializer.FullMaterializerMachine.raw_run_of_eq_some
      M headSymbol steps _ _ hrun
  · exact congrArg
      (InitialMaterializer.FullMaterializerMachine.Control.raw
        (M := M) headSymbol) hstate
  · exact htape

def blockPaddedSourceConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .block headSymbol
    (.carry (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol))
  tape := (Raw.doneConfigCells rest deepLeft).tape

theorem raw_block_bridge_exact_cells {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 2
        (rawConfig M headSymbol (Raw.doneConfigCells rest deepLeft)) =
      some (blockPaddedSourceConfig M headSymbol rest deepLeft) := by
  have hnonempty :=
    InitialMaterializer.NonemptyRightRegion.region_ne_nil rest
  cases hregion : InitialMaterializer.NonemptyRightRegion.region rest with
  | nil => contradiction
  | cons first regionRest =>
      cases regionRest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          InitialMaterializer.FullMaterializerMachine.machine,
          InitialMaterializer.FullMaterializerMachine.transition,
          rawConfig, blockPaddedSourceConfig,
          InitialMaterializer.FullMaterializerMachine.rawConfig,
          Raw.doneConfigCells,
          InitialMaterializer.SeparatorRewind.gateTapeCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          hregion]

theorem block_run {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
        (InitialMaterializer.NonemptyFixedPrefix.runSteps M headSymbol rest)
        (blockConfig M headSymbol
          (FixedPrefix.sourceConfig M headSymbol rest deepLeft)) =
      some (blockConfig M headSymbol
        (FixedPrefix.endpointConfig M headSymbol rest deepLeft)) := by
  exact InitialMaterializer.FullMaterializerMachine.block_run_of_eq_some
    M headSymbol
    (InitialMaterializer.NonemptyFixedPrefix.runSteps M headSymbol rest)
    _ _ (FixedPrefix.run_exact M headSymbol rest deepLeft)

theorem block_header_bridge_from_endpoint {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (outerRev rest fuelRev : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 2
        (blockConfig M headSymbol
          (FixedPrefix.endpointConfig M headSymbol rest
            (List.append (fuelRev.map some)
              (none :: outerRev.map some)))) =
      some (headerConfig M
        (Header.sourceConfig outerRev
          (InitialMaterializer.VariableBlockInsert.finalLeftRev
            (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol) []
            (InitialMaterializer.NonemptyRightRegion.region rest))
          fuelRev)) := by
  let wordRev :=
    InitialMaterializer.VariableBlockInsert.finalLeftRev
      (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol) []
      (InitialMaterializer.NonemptyRightRegion.region rest)
  have hnonempty : wordRev ≠ [] := by
    intro hnil
    have hword :=
      InitialMaterializer.NonemptyFixedPrefix.endpoint_word_reverse
        M headSymbol rest
    change wordRev.reverse = _ at hword
    rw [hnil] at hword
    have hright :
        List.append
            (InitialMaterializer.NonemptyFixedPrefix.fixedPrefix M headSymbol)
            (InitialMaterializer.NonemptyRightRegion.region rest) ≠ [] := by
      intro hempty
      exact InitialMaterializer.NonemptyFixedPrefix.fixedPrefix_ne_nil
        M headSymbol (List.append_eq_nil_iff.mp hempty).1
    exact hright hword.symm
  cases hrev : wordRev with
  | nil => contradiction
  | cons first tail =>
      cases tail <;> cases fuelRev <;> cases outerRev <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          InitialMaterializer.FullMaterializerMachine.machine,
          InitialMaterializer.FullMaterializerMachine.transition,
          blockConfig, headerConfig,
          InitialMaterializer.FullMaterializerMachine.blockConfig,
          InitialMaterializer.FullMaterializerMachine.headerConfig,
          FixedPrefix.endpointConfig, FixedPrefix.baseCells,
          InitialMaterializer.VariableBlockInsert.haltConfig,
          Header.sourceConfig, wordRev, hrev,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem header_run {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol) (fuel : Nat)
    (wordRev : Word MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
        (InitialMaterializer.HeaderLeftInstaller.runSteps fuel wordRev)
        (headerConfig M
          (Header.sourceConfig outerRev wordRev
            (MachineDescription.encodeNat fuel).reverse)) =
      some (headerConfig M
        (Header.haltConfig outerRev
          (MachineDescription.encodeNat fuel) wordRev.reverse)) := by
  exact InitialMaterializer.FullMaterializerMachine.header_run_of_eq_some
    M (InitialMaterializer.HeaderLeftInstaller.runSteps fuel wordRev)
    _ _ (Header.run_exact outerRev fuel wordRev)

def nonemptyHaltTape {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol) (fuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Header.haltTape outerRev (MachineDescription.encodeNat fuel)
    (List.append
      (InitialMaterializer.NonemptyFixedPrefix.fixedPrefix M headSymbol)
      (InitialMaterializer.NonemptyRightRegion.region rest))

def emptyHaltTape {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol) (fuel : Nat) :
    Tape MachineCodeSymbol :=
  Prepend.gateTape outerRev
    (InitialMaterializer.EmptyInputSuffix.body M fuel)

theorem empty_run_to_contextual_endpoint {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol) (fuel : Nat) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol (Control M)),
      (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
          steps (sourceConfig M outerRev fuel []) = some endpoint ∧
      endpoint.state = .emptyPrepend .gate ∧
      endpoint.tape = emptyHaltTape M outerRev fuel := by
  let fuelRev := (MachineDescription.encodeNat fuel).reverse
  let writerRev := List.append
    (InitialMaterializer.EmptyInputSuffix.suffix M).reverse fuelRev
  have hparse := parser_run M outerRev fuel []
  have hparseBridge := parse_empty_bridge_exact M outerRev fuel
  have hwriter :
      (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
          (InitialMaterializer.EmptyInputSuffix.suffix M).length
          (emptyWriteConfig M
            (EmptyWriter.config
              (InitialMaterializer.EmptyInputSuffix.suffix M) 0 (by simp)
              outerRev fuelRev)) =
        some (emptyWriteConfig M
          (EmptyWriter.config
            (InitialMaterializer.EmptyInputSuffix.suffix M)
            (InitialMaterializer.EmptyInputSuffix.suffix M).length
            (by simp) outerRev writerRev)) := by
    simpa [writerRev] using empty_writer_run M outerRev fuelRev
  have hwriterNonempty : writerRev ≠ [] := by
    intro hnil
    have hparts := List.append_eq_nil_iff.mp hnil
    have hfuel : fuelRev ≠ [] := by
      unfold fuelRev
      rw [InitialMaterializer.OneCellMachine.encodeNat_eq_ticks_done]
      simp
    exact hfuel hparts.2
  have hwriterBridge :=
    empty_header_bridge_exact M outerRev writerRev hwriterNonempty
  have hprepend := empty_prepend_run M outerRev writerRev
  have hprefix0 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hparse hparseBridge
  have hprefix1 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix0 hwriter
  have hprefix2 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix1 hwriterBridge
  have hfull :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix2 hprepend
  have hwriterShape :
      writerRev =
        (InitialMaterializer.EmptyInputSuffix.body M fuel).reverse := by
    exact
      InitialMaterializer.EmptyInputSuffix.writer_leftRev_eq_body_reverse
        M fuel
  refine ⟨_,
    emptyPrependConfig M
      (Prepend.gateConfig outerRev writerRev.reverse),
    hfull, rfl, ?_⟩
  change Prepend.gateTape outerRev writerRev.reverse = _
  rw [hwriterShape]
  simp [emptyHaltTape]

theorem nonempty_run_to_contextual_endpoint {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outerRev : Word MachineCodeSymbol) (fuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol (Control M)),
      (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
          steps (sourceConfig M outerRev fuel (headSymbol :: rest)) =
        some endpoint ∧
      endpoint.state = .header .halt ∧
      Tape.Equiv
        (nonemptyHaltTape M outerRev fuel headSymbol rest)
        endpoint.tape := by
  let fuelRev := (MachineDescription.encodeNat fuel).reverse
  let deepLeft := List.append (fuelRev.map some)
    (none :: outerRev.map some)
  have hparse := parser_run M outerRev fuel (headSymbol :: rest)
  have hparseBridge :=
    parse_nonempty_bridge_exact M outerRev fuel headSymbol rest
  have htail := tail_run M outerRev fuelRev headSymbol rest
  have htailBridge :=
    tail_base_bridge_exact M headSymbol outerRev fuelRev rest.reverse
  have hbase :=
    base_rewind_run M headSymbol outerRev fuelRev rest.reverse
  have hbaseBridge :=
    base_raw_bridge_exact M headSymbol outerRev fuelRev rest.reverse
  rcases raw_run_to_done_equiv M headSymbol outerRev rest.reverse [] fuelRev with
    ⟨rawSteps, rawEndpoint, hraw, hrawState, hrawTape⟩
  have hrestProcessed : List.append rest.reverse.reverse [] = rest := by
    simp
  rw [hrestProcessed] at hrawState hrawTape
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := rawConfig M headSymbol
        (Raw.doneConfigCells rest deepLeft))
      (padded := rawEndpoint)
      (cleanFinal := blockPaddedSourceConfig M headSymbol rest deepLeft)
      (InitialMaterializer.FullMaterializerMachine.machine M) 2
      (by
        change
          InitialMaterializer.FullMaterializerMachine.Control.raw
              (M := M) headSymbol (Raw.doneConfigCells rest deepLeft).state =
            rawEndpoint.state
        exact hrawState)
      hrawTape
      (raw_block_bridge_exact_cells M headSymbol rest deepLeft) with
    ⟨actualBlockReady, hactualBlockBridge, hblockReadyState,
      hblockReadyTape⟩
  have hblockInputState :
      (blockConfig M headSymbol
        (FixedPrefix.sourceConfig M headSymbol rest deepLeft)).state =
        actualBlockReady.state := by
    exact hblockReadyState
  have hblockInputTape :
      Tape.Equiv
        (blockConfig M headSymbol
          (FixedPrefix.sourceConfig M headSymbol rest deepLeft)).tape
        actualBlockReady.tape := by
    exact Tape.Equiv.trans
      (Tape.Equiv.symm
        (FixedPrefix.raw_done_equiv_source M headSymbol rest deepLeft))
      hblockReadyTape
  have hblockClean := block_run M headSymbol rest deepLeft
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := blockConfig M headSymbol
        (FixedPrefix.sourceConfig M headSymbol rest deepLeft))
      (padded := actualBlockReady)
      (cleanFinal := blockConfig M headSymbol
        (FixedPrefix.endpointConfig M headSymbol rest deepLeft))
      (InitialMaterializer.FullMaterializerMachine.machine M)
      (InitialMaterializer.NonemptyFixedPrefix.runSteps M headSymbol rest)
      hblockInputState hblockInputTape hblockClean with
    ⟨actualBlockEndpoint, hactualBlock, hblockEndpointState,
      hblockEndpointTape⟩
  let insertedRev :=
    InitialMaterializer.VariableBlockInsert.finalLeftRev
      (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol) []
      (InitialMaterializer.NonemptyRightRegion.region rest)
  have hblockBridgeClean :
      (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact? 2
          (blockConfig M headSymbol
            (FixedPrefix.endpointConfig M headSymbol rest deepLeft)) =
        some (headerConfig M
          (Header.sourceConfig outerRev insertedRev fuelRev)) := by
    simpa [deepLeft, fuelRev, insertedRev] using
      block_header_bridge_from_endpoint M headSymbol outerRev rest fuelRev
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := blockConfig M headSymbol
        (FixedPrefix.endpointConfig M headSymbol rest deepLeft))
      (padded := actualBlockEndpoint)
      (cleanFinal := headerConfig M
        (Header.sourceConfig outerRev insertedRev fuelRev))
      (InitialMaterializer.FullMaterializerMachine.machine M) 2
      hblockEndpointState hblockEndpointTape hblockBridgeClean with
    ⟨actualHeaderReady, hactualHeaderBridge, hheaderReadyState,
      hheaderReadyTape⟩
  have hheaderClean :
      (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
          (InitialMaterializer.HeaderLeftInstaller.runSteps fuel insertedRev)
          (headerConfig M
            (Header.sourceConfig outerRev insertedRev fuelRev)) =
        some (headerConfig M
          (Header.haltConfig outerRev
            (MachineDescription.encodeNat fuel) insertedRev.reverse)) := by
    simpa [fuelRev] using header_run M outerRev fuel insertedRev
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := headerConfig M
        (Header.sourceConfig outerRev insertedRev fuelRev))
      (padded := actualHeaderReady)
      (cleanFinal := headerConfig M
        (Header.haltConfig outerRev
          (MachineDescription.encodeNat fuel) insertedRev.reverse))
      (InitialMaterializer.FullMaterializerMachine.machine M)
      (InitialMaterializer.HeaderLeftInstaller.runSteps fuel insertedRev)
      hheaderReadyState hheaderReadyTape hheaderClean with
    ⟨actualEndpoint, hactualHeader, hfinalState, hfinalTape⟩
  have hprefix0 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hparse hparseBridge
  have hprefix1 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix0 htail
  have hprefix2 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix1 htailBridge
  have hprefix3 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix2 hbase
  have hprefix4 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix3 hbaseBridge
  have hprefix5 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix4 hraw
  have hprefix6 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix5 hactualBlockBridge
  have hprefix7 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix6 hactualBlock
  have hprefix8 :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix7 hactualHeaderBridge
  have hfull :=
    InitialMaterializer.FullMaterializerMachine.exactRun_trans
      M _ _ _ _ _ hprefix8 hactualHeader
  refine ⟨_, actualEndpoint, hfull, ?_, ?_⟩
  · exact hfinalState.symm
  · have hinserted :=
      InitialMaterializer.NonemptyFixedPrefix.endpoint_word_reverse
        M headSymbol rest
    change insertedRev.reverse = _ at hinserted
    rw [hinserted] at hfinalTape
    exact hfinalTape

end Full

end ProductContextual
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

