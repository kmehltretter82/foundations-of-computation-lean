import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Contextual.Raw

set_option doc.verso true

/-!
# Contextual product frame finishing

Preserve the retained outer call through fixed-prefix insertion, header
installation, and the empty-input writer/prepender path.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductContextual

namespace FixedPrefix

def baseCells
    (deepLeft : List (Option MachineCodeSymbol)) :
    List (Option MachineCodeSymbol) :=
  none :: none :: deepLeft

def sourceConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      (InitialMaterializer.VariableBlockInsert.Control
        (InitialMaterializer.NonemptyFixedPrefix.capacity M)) :=
  InitialMaterializer.VariableBlockInsert.config
    (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol) []
    (baseCells deepLeft)
    (InitialMaterializer.NonemptyRightRegion.region rest)

def endpointConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      (InitialMaterializer.VariableBlockInsert.Control
        (InitialMaterializer.NonemptyFixedPrefix.capacity M)) :=
  InitialMaterializer.VariableBlockInsert.haltConfig
    (InitialMaterializer.VariableBlockInsert.finalLeftRev
      (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol) []
      (InitialMaterializer.NonemptyRightRegion.region rest))
    (baseCells deepLeft)

theorem run_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    (InitialMaterializer.VariableBlockInsert.machine
        (InitialMaterializer.NonemptyFixedPrefix.capacity M)
        (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol)).runConfigExact?
      (InitialMaterializer.NonemptyFixedPrefix.runSteps M headSymbol rest)
      (sourceConfig M headSymbol rest deepLeft) =
    some (endpointConfig M headSymbol rest deepLeft) := by
  exact InitialMaterializer.VariableBlockInsert.run_exact
    (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol)
    (InitialMaterializer.NonemptyFixedPrefix.buffer M headSymbol) []
    (InitialMaterializer.NonemptyRightRegion.region rest)
    (baseCells deepLeft)
    (InitialMaterializer.NonemptyFixedPrefix.fixedPrefix_ne_nil M headSymbol)

theorem raw_done_equiv_source {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (deepLeft : List (Option MachineCodeSymbol)) :
    Tape.Equiv
      (Raw.doneConfigCells rest deepLeft).tape
      (sourceConfig M headSymbol rest deepLeft).tape := by
  have hnonempty :=
    InitialMaterializer.NonemptyRightRegion.region_ne_nil rest
  cases hregion : InitialMaterializer.NonemptyRightRegion.region rest with
  | nil => contradiction
  | cons first regionRest =>
      simp [Raw.doneConfigCells,
        InitialMaterializer.SeparatorRewind.gateTapeCells,
        sourceConfig, baseCells,
        InitialMaterializer.VariableBlockInsert.config,
        InitialMaterializer.InsertOneWithBoundary.cursorTape,
        Tape.Equiv, dropTrailingNone_append_none, hregion]

end FixedPrefix

namespace Header

def sourceConfig
    (outerRev wordRev fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.HeaderLeftInstaller.Control where
  state := .start
  tape :=
    { left := List.append (wordRev.map some)
        (none :: none :: List.append (fuelRev.map some)
          (none :: outerRev.map some))
      head := none
      right := [] }

def bodyTape
    (outerRev fuelRev remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := none :: List.append (fuelRev.map some)
          (none :: outerRev.map some)
        head := none
        right := List.append (crossed.map some) [none] }
  | current :: rest =>
      { left := List.append (rest.map some)
          (none :: none :: List.append (fuelRev.map some)
            (none :: outerRev.map some))
        head := some current
        right := List.append (crossed.map some) [none] }

def bodyConfig
    (outerRev fuelRev remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.HeaderLeftInstaller.Control where
  state := .body
  tape := bodyTape outerRev fuelRev remainingRev crossed

def secondBoundaryConfig
    (outerRev fuelRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.HeaderLeftInstaller.Control where
  state := .secondBoundary
  tape :=
    { left := List.append (fuelRev.map some)
        (none :: outerRev.map some)
      head := none
      right := none :: List.append (crossed.map some) [none] }

def fuelDoneConfig
    (outerRev ticksRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.HeaderLeftInstaller.Control where
  state := .fuelDone
  tape :=
    { left := List.append (ticksRev.map some)
        (none :: outerRev.map some)
      head := some MachineCodeSymbol.done
      right := none :: none :: List.append (crossed.map some) [none] }

def ticksTape
    (outerRev remainingRev crossed bodyWord : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := outerRev.map some
        head := none
        right := List.append (crossed.map some)
          (none :: none :: List.append (bodyWord.map some) [none]) }
  | current :: rest =>
      { left := List.append (rest.map some)
          (none :: outerRev.map some)
        head := some current
        right := List.append (crossed.map some)
          (none :: none :: List.append (bodyWord.map some) [none]) }

def ticksConfig
    (outerRev remainingRev crossed bodyWord : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.HeaderLeftInstaller.Control where
  state := .fuelTicks
  tape := ticksTape outerRev remainingRev crossed bodyWord

def haltTape
    (outerRev fuelWord bodyWord : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match fuelWord with
  | [] =>
      { left := some MachineCodeSymbol.header :: outerRev.map some
        head := none
        right := none :: none :: List.append (bodyWord.map some) [none] }
  | first :: rest =>
      { left := some MachineCodeSymbol.header :: outerRev.map some
        head := some first
        right := List.append (rest.map some)
          (none :: none :: List.append (bodyWord.map some) [none]) }

def haltConfig
    (outerRev fuelWord bodyWord : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.HeaderLeftInstaller.Control where
  state := .halt
  tape := haltTape outerRev fuelWord bodyWord

theorem start_step
    (outerRev wordRev fuelRev : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.stepConfig
        (sourceConfig outerRev wordRev fuelRev) =
      some (bodyConfig outerRev fuelRev wordRev []) := by
  cases wordRev <;> rfl

theorem body_step
    (outerRev fuelRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.stepConfig
        (bodyConfig outerRev fuelRev (current :: remainingRev) crossed) =
      some (bodyConfig outerRev fuelRev remainingRev
        (current :: crossed)) := by
  cases remainingRev <;> rfl

theorem body_finish
    (outerRev fuelRev crossed : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.stepConfig
        (bodyConfig outerRev fuelRev [] crossed) =
      some (secondBoundaryConfig outerRev fuelRev crossed) := by
  cases crossed <;> rfl

theorem body_run_exact
    (outerRev fuelRev remainingRev crossed : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.runConfigExact?
        (remainingRev.length + 1)
        (bodyConfig outerRev fuelRev remainingRev crossed) =
      some (secondBoundaryConfig outerRev fuelRev
        (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact body_finish outerRev fuelRev crossed
  | cons current remainingRev ih =>
      change
        InitialMaterializer.HeaderLeftInstaller.machine.runConfigExact?
            ((remainingRev.length + 1) + 1)
            (bodyConfig outerRev fuelRev (current :: remainingRev)
              crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [body_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem second_boundary_step
    (outerRev ticksRev bodyWord : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.stepConfig
        (secondBoundaryConfig outerRev
          (MachineCodeSymbol.done :: ticksRev) bodyWord) =
      some (fuelDoneConfig outerRev ticksRev bodyWord) := by
  cases bodyWord <;> rfl

theorem fuel_done_step
    (outerRev ticksRev bodyWord : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.stepConfig
        (fuelDoneConfig outerRev ticksRev bodyWord) =
      some (ticksConfig outerRev ticksRev [MachineCodeSymbol.done]
        bodyWord) := by
  cases ticksRev <;> cases bodyWord <;> rfl

theorem tick_step
    (outerRev remainingRev crossed bodyWord : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.stepConfig
        (ticksConfig outerRev
          (MachineCodeSymbol.tick :: remainingRev) crossed bodyWord) =
      some (ticksConfig outerRev remainingRev
        (MachineCodeSymbol.tick :: crossed) bodyWord) := by
  cases remainingRev <;> cases crossed <;> cases bodyWord <;> rfl

theorem tick_finish
    (outerRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol) (rest bodyWord : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.stepConfig
        (ticksConfig outerRev [] (first :: rest) bodyWord) =
      some (haltConfig outerRev (first :: rest) bodyWord) := by
  cases outerRev <;> cases rest <;> cases bodyWord <;> rfl

theorem ticks_replicate_run_exact
    (outerRev : Word MachineCodeSymbol) (count : Nat)
    (first : MachineCodeSymbol)
    (crossedRest bodyWord : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.runConfigExact?
        (count + 1)
        (ticksConfig outerRev
          (List.replicate count MachineCodeSymbol.tick)
          (first :: crossedRest) bodyWord) =
      some (haltConfig outerRev
        (List.append
          (List.replicate count MachineCodeSymbol.tick).reverse
          (first :: crossedRest)) bodyWord) := by
  induction count generalizing first crossedRest with
  | zero =>
      exact tick_finish outerRev first crossedRest bodyWord
  | succ count ih =>
      change
        InitialMaterializer.HeaderLeftInstaller.machine.runConfigExact?
            ((count + 1) + 1)
            (ticksConfig outerRev
              (MachineCodeSymbol.tick ::
                List.replicate count MachineCodeSymbol.tick)
              (first :: crossedRest) bodyWord) = _
      rw [TuringMachine.runConfigExact?]
      rw [tick_step]
      simp only
      rw [ih MachineCodeSymbol.tick (first :: crossedRest)]
      simp [List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem run_exact
    (outerRev : Word MachineCodeSymbol) (fuel : Nat)
    (wordRev : Word MachineCodeSymbol) :
    InitialMaterializer.HeaderLeftInstaller.machine.runConfigExact?
        (InitialMaterializer.HeaderLeftInstaller.runSteps fuel wordRev)
        (sourceConfig outerRev wordRev
          (MachineDescription.encodeNat fuel).reverse) =
      some (haltConfig outerRev
        (MachineDescription.encodeNat fuel) wordRev.reverse) := by
  unfold InitialMaterializer.HeaderLeftInstaller.runSteps
  rw [InitialMaterializer.ExactRun.append]
  rw [show
      InitialMaterializer.HeaderLeftInstaller.machine.runConfigExact? 1
          (sourceConfig outerRev wordRev
            (MachineDescription.encodeNat fuel).reverse) =
        some (bodyConfig outerRev
          (MachineDescription.encodeNat fuel).reverse wordRev []) by
    exact start_step outerRev wordRev
      (MachineDescription.encodeNat fuel).reverse]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [body_run_exact]
  simp only
  have hword : List.append wordRev.reverse [] = wordRev.reverse :=
    List.append_nil wordRev.reverse
  rw [hword]
  rw [InitialMaterializer.HeaderLeftInstaller.encodeNat_reverse_eq_done_ticks]
  rw [InitialMaterializer.ExactRun.append]
  rw [show
      InitialMaterializer.HeaderLeftInstaller.machine.runConfigExact? 1
          (secondBoundaryConfig outerRev
            (MachineCodeSymbol.done ::
              List.replicate fuel MachineCodeSymbol.tick)
            wordRev.reverse) =
        some (fuelDoneConfig outerRev
          (List.replicate fuel MachineCodeSymbol.tick)
          wordRev.reverse) by
    rw [TuringMachine.runConfigExact?]
    rw [second_boundary_step]
    simp only [TuringMachine.runConfigExact?]]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [show
      InitialMaterializer.HeaderLeftInstaller.machine.runConfigExact? 1
          (fuelDoneConfig outerRev
            (List.replicate fuel MachineCodeSymbol.tick)
            wordRev.reverse) =
        some (ticksConfig outerRev
          (List.replicate fuel MachineCodeSymbol.tick)
          [MachineCodeSymbol.done] wordRev.reverse) by
    exact fuel_done_step outerRev
      (List.replicate fuel MachineCodeSymbol.tick) wordRev.reverse]
  simp only
  have hticks := ticks_replicate_run_exact outerRev fuel
    MachineCodeSymbol.done [] wordRev.reverse
  simpa [InitialMaterializer.HeaderLeftInstaller.encodeNat_reverse_eq_done_ticks,
    InitialMaterializer.OneCellMachine.encodeNat_eq_ticks_done] using hticks

end Header

namespace EmptyWriter

def config
    (word : Word MachineCodeSymbol) (index : Nat)
    (hle : index ≤ word.length)
    (outerRev leftRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Fin (word.length + 1)) where
  state := InitialMaterializer.FixedWordWriter.stateAt word index hle
  tape := Parser.tape outerRev leftRev []

theorem step_of_split
    (word written rest : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (outerRev leftRev : Word MachineCodeSymbol)
    (hword : word = List.append written (current :: rest)) :
    (InitialMaterializer.FixedWordWriter.machine word).stepConfig
        (config word written.length (by rw [hword]; simp)
          outerRev leftRev) =
      some (config word (written.length + 1)
        (by rw [hword]; simp) outerRev (current :: leftRev)) := by
  subst word
  simp [TuringMachine.stepConfig,
    InitialMaterializer.FixedWordWriter.machine,
    InitialMaterializer.FixedWordWriter.transition,
    InitialMaterializer.FixedWordWriter.stateAt,
    config, Parser.tape,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_of_split
    (word written rest : Word MachineCodeSymbol)
    (outerRev leftRev : Word MachineCodeSymbol)
    (hword : word = List.append written rest) :
    (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
        rest.length
        (config word written.length (by rw [hword]; simp)
          outerRev leftRev) =
      some (config word word.length (by simp) outerRev
        (List.append rest.reverse leftRev)) := by
  induction rest generalizing written leftRev with
  | nil =>
      subst word
      simp [TuringMachine.runConfigExact?, config,
        InitialMaterializer.FixedWordWriter.stateAt]
  | cons current rest ih =>
      change
        (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
            (rest.length + 1)
            (config word written.length (by rw [hword]; simp)
              outerRev leftRev) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_of_split word written rest current outerRev leftRev hword]
      simp only
      have hword' :
          word = List.append (List.append written [current]) rest := by
        rw [hword]
        simp [List.append_assoc]
      have hrun := ih (List.append written [current])
        (current :: leftRev) hword'
      simpa [List.reverse_cons, List.append_assoc] using hrun

theorem run_exact
    (word outerRev leftRev : Word MachineCodeSymbol) :
    (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
        word.length (config word 0 (by simp) outerRev leftRev) =
      some (config word word.length (by simp) outerRev
        (List.append word.reverse leftRev)) := by
  exact run_of_split word [] word outerRev leftRev (by simp)

end EmptyWriter

namespace Prepend

def farRightTape
    (outerRev wordRev : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol where
  left := List.append (wordRev.map some)
    (none :: outerRev.map some)
  head := none
  right := []

def startConfig
    (outerRev wordRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.PrependHeader.Control where
  state := .start
  tape := farRightTape outerRev wordRev

def scanTape
    (outerRev remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := outerRev.map some
        head := none
        right := List.append (crossed.map some) [none] }
  | current :: rest =>
      { left := List.append (rest.map some)
          (none :: outerRev.map some)
        head := some current
        right := List.append (crossed.map some) [none] }

def scanConfig
    (outerRev remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.PrependHeader.Control where
  state := .scan
  tape := scanTape outerRev remainingRev crossed

def gateTape
    (outerRev word : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := some MachineCodeSymbol.header :: outerRev.map some
        head := none
        right := [] }
  | first :: rest =>
      { left := some MachineCodeSymbol.header :: outerRev.map some
        head := some first
        right := List.append (rest.map some) [none] }

def gateConfig
    (outerRev word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.PrependHeader.Control where
  state := .gate
  tape := gateTape outerRev word

theorem start_step
    (outerRev wordRev : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.stepConfig
        (startConfig outerRev wordRev) =
      some (scanConfig outerRev wordRev []) := by
  cases wordRev <;> rfl

theorem scan_step
    (outerRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.stepConfig
        (scanConfig outerRev (current :: remainingRev) crossed) =
      some (scanConfig outerRev remainingRev (current :: crossed)) := by
  cases remainingRev <;> rfl

theorem scan_finish
    (outerRev crossed : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.stepConfig
        (scanConfig outerRev [] crossed) =
      some (gateConfig outerRev crossed) := by
  cases outerRev <;> cases crossed <;> rfl

theorem scan_run_exact
    (outerRev remainingRev crossed : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.runConfigExact?
        (remainingRev.length + 1)
        (scanConfig outerRev remainingRev crossed) =
      some (gateConfig outerRev
        (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact scan_finish outerRev crossed
  | cons current remainingRev ih =>
      change
        InitialMaterializer.PrependHeader.machine.runConfigExact?
            ((remainingRev.length + 1) + 1)
            (scanConfig outerRev (current :: remainingRev) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_exact
    (outerRev wordRev : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.runConfigExact?
        (wordRev.length + 2) (startConfig outerRev wordRev) =
      some (gateConfig outerRev wordRev.reverse) := by
  change
    InitialMaterializer.PrependHeader.machine.runConfigExact?
        ((wordRev.length + 1) + 1) (startConfig outerRev wordRev) = _
  rw [TuringMachine.runConfigExact?]
  rw [start_step]
  simp only
  simpa using scan_run_exact outerRev wordRev
    ([] : Word MachineCodeSymbol)

end Prepend

end ProductContextual
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

